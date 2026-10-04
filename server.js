const http = require("http");
const WebSocket = require("ws");
const { Pool } = require("pg");
const bcrypt = require("bcryptjs");

const GRID_SIZE = 200;
const COOLDOWN_MS = 10 * 1000; // 10 saniye - client'taki süreyle eşleşmeli
const CHAT_COOLDOWN_MS = 2 * 1000; // spam'i onlemek icin kisa bir sohbet bekleme suresi
const CHAT_HISTORY_LIMIT = 50;
const HEX_COLOR_REGEX = /^#[0-9A-Fa-f]{6}$/;
const USERNAME_REGEX = /^[A-Za-z0-9ÇçĞğİıÖöŞşÜü_]{3,20}$/;
const AUTH_COOLDOWN_MS = 3 * 1000; // ayni IP'den art arda kayit/giris denemesini yavaslat

const pool = new Pool({
  connectionString: process.env.DATABASE_URL,
  ssl: { rejectUnauthorized: false }
});

// Basit bir HTTP sunucu: hem WebSocket'i taşımak hem de
// dış bir servisin (cron-job.org, UptimeRobot vb.) sunucuyu
// uyanık tutmak için "ping" atabileceği bir healthcheck sağlamak için.
const server = http.createServer((req, res) => {
  if (req.url === "/health") {
    res.writeHead(200, { "Content-Type": "text/plain" });
    res.end("ok");
    return;
  }
  res.writeHead(200, { "Content-Type": "text/plain" });
  res.end("PixelTur V2 backend calisiyor");
});

const wss = new WebSocket.Server({ server });

// IP başına son piksel basma zamanı (server tarafı cooldown - client tarafı
// atlatılamaz hale getirmek için). Basit bir bellek içi harita; sunucu
// yeniden başlarsa sıfırlanır, bu da bu ölçekte sorun değil.
const lastPlacedAt = new Map();

// Sohbet: sadece bellekte tutuluyor, kalici degil (sunucu yeniden
// baslarsa - orn. uykudan uyanirken - sifirlanir). Bu olcekte bir
// veritabani tablosuna gerek yok, basit ve yeterli.
let chatHistory = [];
const lastChatAt = new Map();
let nextChatId = 1;
// IP basina "ayni mesaji ust uste kac kez yazdi" takibi (spam tespiti icin)
const repeatTracker = new Map(); // ip -> { text, count, ids:[] }

// Kayit/giris denemelerini IP basina yavaslatmak icin (brute-force/spam onleme)
const lastAuthAt = new Map();

// Basit kufur/argo/+18 kelime filtresi. Kelime sinirlarina gore kontrol
// ediyoruz (orn. "sik" gecen "sikayet" gibi masum kelimeleri yanlislikla
// yakalamamak icin). Cekim/kisaltma varyasyonlarinin cogunu tek tek
// listeye ekliyoruz (kok bulma/stemming yapmiyoruz), bu yuzden %100
// kapsama garanti degil - yeni bir kelime/varyasyon fark edersen
// listeye eklemen yeterli.
const BANNED_WORDS = [
  // kisaltmalar
  "amk", "aq", "amq", "mk", "oç", "oc", "sg", "sgt", "oe",
  // kufur/hakaret kokleri ve cekimleri
  "orospu", "orospi", "piç", "pic", "piçkurusu", "kahpe", "pezevenk",
  "şerefsiz", "serefsiz", "namussuz", "yavşak", "yavsak", "sürtük",
  "surtuk", "kancık", "kancik", "kaltak", "ibne", "ibnelik",
  "gerizekalı", "gerizekali", "geri zekalı", "geri zekali", "mal",
  "embesil", "dangalak", "dallama", "aptal şey", "it", "köpek herif",
  "hayvan herif", "şerefsizlik", "serefsizlik",
  // cinsel organ / cinsel icerik kokleri ve cekimleri
  "yarrak", "yarak", "yarrağı", "yarragi", "yarrağım", "yarragim",
  "sik", "sikim", "sikik", "sikeyim", "sikerim", "sikiyim", "sikilmiş",
  "sikilmis", "siktir", "sikiş", "sikis", "sikişmek", "sikismek",
  "götveren", "gotveren", "göt", "got", "götü", "gotu", "amcık",
  "amcik", "am", "taşak", "tasak", "yumurta herif",
  "porno", "porn", "pornografik", "seks", "sex", "sekse", "sexe",
  "orgazm", "fetiş", "fetis",
  "düzüşmek", "duzusmek", "düzerim", "duzerim", "düzeyim", "duzeyim"
];
const BANNED_WORDS_REGEX = new RegExp(
  "(^|[^a-zçğıöşü0-9])(" + BANNED_WORDS.join("|") + ")([^a-zçğıöşü0-9]|$)",
  "i"
);
function containsBannedWord(text) {
  return BANNED_WORDS_REGEX.test(text.toLocaleLowerCase("tr"));
}

function broadcast(obj) {
  const payload = JSON.stringify(obj);
  wss.clients.forEach((client) => {
    if (client.readyState === WebSocket.OPEN) client.send(payload);
  });
}

// Sohbet gecmisini 24 saatte bir otomatik temizle (istek uzerine).
const CHAT_HISTORY_MAX_AGE_MS = 24 * 60 * 60 * 1000;
setInterval(() => {
  chatHistory = [];
  repeatTracker.clear();
  broadcast({ type: "chat_clear" });
  console.log("Sohbet gecmisi 24 saatlik periyotla temizlendi.");
}, CHAT_HISTORY_MAX_AGE_MS);

async function ensureSchema() {
  await pool.query(`
    CREATE TABLE IF NOT EXISTS pixels (
      x INT NOT NULL,
      y INT NOT NULL,
      color TEXT NOT NULL,
      PRIMARY KEY (x, y)
    );
  `);
  // Kullanicilar ayri bir tabloda tutuluyor (piksel verisiyle karismasin
  // diye). username_lower, "Ahmet" ile "ahmet"in ayni kisi sayilip
  // ikinci kez alinamamasini garanti eder; username ekranda gosterilen
  // orijinal (buyuk/kucuk harfli) haldir.
  await pool.query(`
    CREATE TABLE IF NOT EXISTS users (
      username_lower TEXT PRIMARY KEY,
      username TEXT NOT NULL,
      password_hash TEXT NOT NULL,
      created_at TIMESTAMPTZ DEFAULT NOW()
    );
  `);
}

async function loadBoard() {
  const res = await pool.query("SELECT x,y,color FROM pixels");
  return res.rows;
}

function getClientIp(req) {
  // Render/Railway gibi platformlarda proxy arkasında olduğumuz için
  // öncelikle x-forwarded-for başlığına bakıyoruz.
  const forwarded = req.headers["x-forwarded-for"];
  if (forwarded) return forwarded.split(",")[0].trim();
  return req.socket.remoteAddress;
}

wss.on("connection", async (ws, req) => {
  ws.clientIp = getClientIp(req);
  broadcast({ type: "online", count: wss.clients.size });

  ws.on("close", () => {
    // biraz gecikmeyle yayinlayalim ki ws zaten clients setinden cikmis olsun
    setTimeout(() => broadcast({ type: "online", count: wss.clients.size }), 0);
  });

  try {
    const board = await loadBoard();
    ws.send(JSON.stringify({ type: "init", board, chat: chatHistory, online: wss.clients.size }));
  } catch (err) {
    console.error("Tahta yuklenirken hata:", err);
  }

  ws.on("message", async (msg) => {
    let data;
    try {
      data = JSON.parse(msg);
    } catch {
      return; // gecersiz JSON, sessizce yoksay
    }

    if (data.type === "register" || data.type === "login") {
      const action = data.type;
      let { username, password } = data;
      username = typeof username === "string" ? username.trim() : "";
      password = typeof password === "string" ? password : "";

      const sendAuthError = (reason) => {
        if (ws.readyState === WebSocket.OPEN) {
          ws.send(JSON.stringify({ type: "auth_error", action, reason }));
        }
      };

      // --- IP basina kayit/giris hizini sinirla ---
      const now = Date.now();
      const lastAuth = lastAuthAt.get(ws.clientIp) || 0;
      if (now - lastAuth < AUTH_COOLDOWN_MS) {
        sendAuthError("Çok hızlı deniyorsun, birkaç saniye bekle.");
        return;
      }
      lastAuthAt.set(ws.clientIp, now);

      if (!USERNAME_REGEX.test(username)) {
        sendAuthError("Kullanıcı adı 3-20 karakter olmalı, sadece harf/rakam/_ içerebilir.");
        return;
      }
      if (password.length < 6 || password.length > 72) {
        sendAuthError("Şifre en az 6 karakter olmalı.");
        return;
      }

      const usernameLower = username.toLocaleLowerCase("tr");

      try {
        if (action === "register") {
          const hash = await bcrypt.hash(password, 10);
          const result = await pool.query(
            `INSERT INTO users (username_lower, username, password_hash)
             VALUES ($1, $2, $3)
             ON CONFLICT (username_lower) DO NOTHING
             RETURNING username`,
            [usernameLower, username, hash]
          );
          if (result.rows.length === 0) {
            sendAuthError("Bu kullanıcı adı zaten alınmış.");
            return;
          }
          ws.username = result.rows[0].username;
          ws.send(JSON.stringify({ type: "auth_ok", action, username: ws.username }));
        } else {
          const result = await pool.query(
            "SELECT username, password_hash FROM users WHERE username_lower = $1",
            [usernameLower]
          );
          if (result.rows.length === 0) {
            sendAuthError("Kullanıcı adı veya şifre hatalı.");
            return;
          }
          const row = result.rows[0];
          const ok = await bcrypt.compare(password, row.password_hash);
          if (!ok) {
            sendAuthError("Kullanıcı adı veya şifre hatalı.");
            return;
          }
          ws.username = row.username;
          ws.send(JSON.stringify({ type: "auth_ok", action, username: ws.username }));
        }
      } catch (err) {
        console.error(`${action} hatasi:`, err);
        sendAuthError("Sunucu hatası, tekrar dene.");
      }
      return;
    }

    if (data.type === "logout") {
      ws.username = null;
      return;
    }

    if (data.type === "chat") {
      // Sohbete artik sadece giris yapmis kullanicilar yazabiliyor -
      // isim her zaman hesabin gercek adi, baskasinin adini yazip o
      // kisi gibi gorunmek hic mumkun degil.
      if (!ws.username) {
        if (ws.readyState === WebSocket.OPEN) {
          ws.send(JSON.stringify({
            type: "chat_blocked",
            reason: "Sohbete yazabilmek için giriş yapmalısın."
          }));
        }
        return;
      }
      const name = ws.username;
      let { text } = data;
      if (typeof text !== "string") return;
      text = text.trim().slice(0, 200);
      if (!text) return;

      // --- Kufur/argo/+18 filtresi: bu kelimeler geciyorsa mesaj hic
      // yayinlanmiyor, gonderene de bir seffaflik icin bilgi gonderiliyor ---
      if (containsBannedWord(text) || containsBannedWord(name)) {
        if (ws.readyState === WebSocket.OPEN) {
          ws.send(JSON.stringify({
            type: "chat_blocked",
            reason: "Mesajın uygunsuz içerik nedeniyle gönderilemedi."
          }));
        }
        return;
      }

      // --- Sunucu tarafi sohbet cooldown'i (spam onleme) ---
      const now = Date.now();
      const lastChat = lastChatAt.get(ws.clientIp) || 0;
      if (now - lastChat < CHAT_COOLDOWN_MS) {
        return;
      }
      lastChatAt.set(ws.clientIp, now);

      // --- Ayni mesaji ust uste yazan kullanicilarin spam'ini temizle ---
      let tracker = repeatTracker.get(ws.clientIp);
      if (!tracker || tracker.text !== text) {
        tracker = { text, count: 0, ids: [] };
        repeatTracker.set(ws.clientIp, tracker);
      }
      tracker.count++;

      if (tracker.count >= 3) {
        // 3. tekrarda: onceki ayni mesajlari herkesin ekranindan da sil,
        // bu mesaji da hic eklemeden yoksay.
        tracker.ids.forEach((id) => {
          chatHistory = chatHistory.filter((m) => m.id !== id);
          broadcast({ type: "chat_delete", id });
        });
        tracker.ids = [];
        return;
      }

      const id = nextChatId++;
      const entry = { id, name, text, ts: now };
      chatHistory.push(entry);
      if (chatHistory.length > CHAT_HISTORY_LIMIT) chatHistory.shift();
      tracker.ids.push(id);

      broadcast({ type: "chat", id, name, text, ts: now });
      return;
    }

    if (data.type !== "place") return;

    const { x, y, color } = data;

    // --- Sunucu tarafi dogrulama ---
    if (
      !Number.isInteger(x) || !Number.isInteger(y) ||
      x < 0 || x >= GRID_SIZE || y < 0 || y >= GRID_SIZE
    ) {
      return; // sinir disi koordinat
    }
    if (typeof color !== "string" || !HEX_COLOR_REGEX.test(color)) {
      return; // gecersiz renk
    }

    // --- Sunucu tarafi cooldown ---
    const now = Date.now();
    const last = lastPlacedAt.get(ws.clientIp) || 0;
    if (now - last < COOLDOWN_MS) {
      return; // cooldown dolmamis, istegi yoksay
    }
    lastPlacedAt.set(ws.clientIp, now);

    try {
      await pool.query(
        "INSERT INTO pixels (x,y,color) VALUES ($1,$2,$3) ON CONFLICT (x,y) DO UPDATE SET color=$3",
        [x, y, color]
      );
    } catch (err) {
      console.error("Piksel yazilirken hata:", err);
      return;
    }

    broadcast({ type: "update", x, y, color });
  });
});

const PORT = process.env.PORT || 3000;

ensureSchema()
  .then(() => {
    server.listen(PORT, () => {
      console.log(`PixelTur V2 backend ${PORT} portunda calisiyor`);
    });
  })
  .catch((err) => {
    console.error("Veritabani semasi hazirlanirken hata:", err);
    process.exit(1);
  });
