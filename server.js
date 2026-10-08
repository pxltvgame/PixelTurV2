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
const CLAN_NAME_REGEX = /^[A-Za-z0-9ÇçĞğİıÖöŞşÜü_ ]{3,30}$/;
const DM_COOLDOWN_MS = 2 * 1000;
const CLAN_CHAT_COOLDOWN_MS = 2 * 1000;
const CLAN_CHAT_HISTORY_LIMIT = 50;
const MAX_CLAN_PHOTO_BYTES = 300 * 1024; // data URI olarak ~300KB sinir (depolamayi korumak icin)
const MAX_AVATAR_BYTES = 150 * 1024;
const CHANNELS = ["tr", "int", "europe", "asia", "america"];
// Moderatorler: kullanici adlari (buyuk/kucuk harf fark etmez). Render'da
// MODERATORS ortam degiskeniyle (virgulle ayirarak) degistirilebilir.
const MODERATORS = new Set(
  (process.env.MODERATORS || "PixelTurV2,Deneme")
    .split(",").map((x) => x.trim().toLocaleLowerCase("tr")).filter(Boolean)
);
const mutedUntil = new Map(); // usernameLower -> bitis zamani (ms)

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
// veritabani tablosuna gerek yok, basit ve yeterli. Her kanalin
// (tr/int/europe/asia/america) kendi ayri gecmisi var.
const chatHistoryByChannel = new Map(CHANNELS.map((c) => [c, []]));
const lastChatAt = new Map();
let nextChatId = 1;
// IP basina "ayni mesaji ust uste kac kez yazdi" takibi (spam tespiti icin)
const repeatTracker = new Map(); // ip -> { text, count, ids:[] }

// Kayit/giris denemelerini IP basina yavaslatmak icin (brute-force/spam onleme)
const lastAuthAt = new Map();

// --- DM ve Klan altyapisi icin bellek ici onbellekler ---
// usernameLower -> ws (DM yonlendirme ve "cevrimici mi" kontrolu icin)
const onlineByUsername = new Map();
// usernameLower -> clanNameLower (bir kullanicinin hangi klanda oldugunu
// her mesajda veritabanina sormadan hizlica bulmak icin)
const userClan = new Map();
// clanNameLower -> Set<usernameLower> (klan sohbetini sadece uyelere
// yollarken hizli filtrelemek icin)
const clanMembersCache = new Map();
// clanNameLower -> son mesajlar dizisi (bellekte, kalici degil)
const clanChatHistory = new Map();
const lastDmAt = new Map();
const lastClanChatAt = new Map();

async function loadClanCaches() {
  const members = await pool.query("SELECT clan_name_lower, username_lower FROM clan_members");
  userClan.clear();
  clanMembersCache.clear();
  for (const row of members.rows) {
    userClan.set(row.username_lower, row.clan_name_lower);
    if (!clanMembersCache.has(row.clan_name_lower)) clanMembersCache.set(row.clan_name_lower, new Set());
    clanMembersCache.get(row.clan_name_lower).add(row.username_lower);
  }
}

async function getClanFullInfo(nameLower) {
  const clanRes = await pool.query("SELECT * FROM clans WHERE name_lower=$1", [nameLower]);
  if (!clanRes.rows.length) return null;
  const clan = clanRes.rows[0];
  const membersRes = await pool.query(
    "SELECT username, role FROM clan_members WHERE clan_name_lower=$1 ORDER BY joined_at ASC",
    [nameLower]
  );
  return {
    name: clan.name,
    description: clan.description,
    photo_data: clan.photo_data,
    owner: clan.owner_username,
    members: membersRes.rows.map((m) => ({
      username: m.username,
      role: m.role,
      online: onlineByUsername.has(m.username.toLocaleLowerCase("tr"))
    }))
  };
}

async function sendMyClanInfo(ws) {
  if (!ws.username || ws.readyState !== WebSocket.OPEN) return;
  const meLower = ws.username.toLocaleLowerCase("tr");
  const nameLower = userClan.get(meLower);
  if (!nameLower) {
    ws.send(JSON.stringify({ type: "my_clan", clan: null }));
    return;
  }
  const info = await getClanFullInfo(nameLower);
  ws.send(JSON.stringify({
    type: "my_clan",
    clan: info,
    chatHistory: clanChatHistory.get(nameLower) || []
  }));
}

// Klan icine "X klana katildi/ayrildi" gibi sistem mesajlari yollar
function broadcastClanSystemMessage(nameLower, text) {
  const entry = { name: "🛡️ Sistem", text, ts: Date.now(), system: true };
  const hist = clanChatHistory.get(nameLower) || [];
  hist.push(entry);
  if (hist.length > CLAN_CHAT_HISTORY_LIMIT) hist.shift();
  clanChatHistory.set(nameLower, hist);
  const payload = JSON.stringify({ type: "clan_chat", ...entry });
  for (const memberLower of clanMembersCache.get(nameLower) || []) {
    const mWs = onlineByUsername.get(memberLower);
    if (mWs && mWs.readyState === WebSocket.OPEN) mWs.send(payload);
  }
}

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

function isModerator(ws) {
  return !!ws.username && MODERATORS.has(ws.username.toLocaleLowerCase("tr"));
}
// Susturulmus kullanici ise mesaji engeller ve bilgi verir
function checkMuted(ws, replyType) {
  const until = mutedUntil.get(ws.username.toLocaleLowerCase("tr"));
  if (until && until > Date.now()) {
    const mins = Math.ceil((until - Date.now()) / 60000);
    if (ws.readyState === WebSocket.OPEN) {
      ws.send(JSON.stringify({ type: replyType || "chat_blocked", reason: `Susturuldun, ${mins} dk sonra tekrar yazabilirsin.` }));
    }
    return true;
  }
  return false;
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
  for (const c of CHANNELS) chatHistoryByChannel.set(c, []);
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
  // Tablo zaten varolan kullanicilarla birlikte duruyor olabilir, o yuzden
  // yeni sutunlari ALTER ile (var olan veriyi bozmadan) ekliyoruz.
  await pool.query(`ALTER TABLE users ADD COLUMN IF NOT EXISTS avatar_data TEXT;`);
  await pool.query(`ALTER TABLE users ADD COLUMN IF NOT EXISTS bio TEXT NOT NULL DEFAULT '';`);
  // Arkadaslik: tek satirda yon bilgisi (kim istek atti) + durum tutuluyor.
  // accepted olunca iki yonlu arkadaslik anlamina geliyor.
  await pool.query(`
    CREATE TABLE IF NOT EXISTS friend_requests (
      from_lower TEXT NOT NULL,
      to_lower TEXT NOT NULL,
      status TEXT NOT NULL DEFAULT 'pending',
      created_at TIMESTAMPTZ DEFAULT NOW(),
      PRIMARY KEY (from_lower, to_lower)
    );
  `);
  // Klanlar da kendi tablosunda - piksel ve kullanici verisinden ayri.
  await pool.query(`
    CREATE TABLE IF NOT EXISTS clans (
      name_lower TEXT PRIMARY KEY,
      name TEXT NOT NULL,
      description TEXT NOT NULL DEFAULT '',
      photo_data TEXT,
      owner_username TEXT NOT NULL,
      created_at TIMESTAMPTZ DEFAULT NOW()
    );
  `);
  await pool.query(`
    CREATE TABLE IF NOT EXISTS clan_members (
      clan_name_lower TEXT NOT NULL REFERENCES clans(name_lower) ON DELETE CASCADE,
      username TEXT NOT NULL,
      username_lower TEXT NOT NULL,
      role TEXT NOT NULL DEFAULT 'member',
      joined_at TIMESTAMPTZ DEFAULT NOW(),
      PRIMARY KEY (clan_name_lower, username_lower)
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
    if (ws.username) {
      const lower = ws.username.toLocaleLowerCase("tr");
      if (onlineByUsername.get(lower) === ws) onlineByUsername.delete(lower);
    }
  });

  try {
    const board = await loadBoard();
    ws.send(JSON.stringify({
      type: "init",
      board,
      chatByChannel: Object.fromEntries(chatHistoryByChannel),
      online: wss.clients.size
    }));
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
          onlineByUsername.set(usernameLower, ws);
          ws.send(JSON.stringify({ type: "auth_ok", action, username: ws.username, moderator: isModerator(ws) }));
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
          onlineByUsername.set(usernameLower, ws);
          ws.send(JSON.stringify({ type: "auth_ok", action, username: ws.username, moderator: isModerator(ws) }));
        }
        // Giris/kayit basarili oldu: eger bir klana uyeyse, bilgisini hemen yolla
        await sendMyClanInfo(ws);
      } catch (err) {
        console.error(`${action} hatasi:`, err);
        sendAuthError("Sunucu hatası, tekrar dene.");
      }
      return;
    }

    if (data.type === "logout") {
      if (ws.username) onlineByUsername.delete(ws.username.toLocaleLowerCase("tr"));
      ws.username = null;
      return;
    }

    // --- Profil: baskasinin hesabini inceleme + kendi fotograf/bio'nu guncelleme ---
    if (data.type === "get_profile") {
      const targetUsername = typeof data.username === "string" ? data.username.trim() : "";
      const targetLower = targetUsername.toLocaleLowerCase("tr");
      try {
        const userRes = await pool.query(
          "SELECT username, avatar_data, bio FROM users WHERE username_lower=$1",
          [targetLower]
        );
        if (userRes.rows.length === 0) {
          ws.send(JSON.stringify({ type: "profile", username: targetUsername, found: false }));
          return;
        }
        const row = userRes.rows[0];
        const clanLower = userClan.get(targetLower);
        let clanName = null;
        if (clanLower) {
          const clanRes = await pool.query("SELECT name FROM clans WHERE name_lower=$1", [clanLower]);
          if (clanRes.rows.length) clanName = clanRes.rows[0].name;
        }
        let friendStatus = "none"; // none | pending_sent | pending_received | friends | self
        if (ws.username) {
          const meLower = ws.username.toLocaleLowerCase("tr");
          if (meLower === targetLower) {
            friendStatus = "self";
          } else {
            const fr = await pool.query(
              `SELECT from_lower, status FROM friend_requests
               WHERE (from_lower=$1 AND to_lower=$2) OR (from_lower=$2 AND to_lower=$1)`,
              [meLower, targetLower]
            );
            if (fr.rows.length) {
              const r = fr.rows[0];
              if (r.status === "accepted") friendStatus = "friends";
              else friendStatus = r.from_lower === meLower ? "pending_sent" : "pending_received";
            }
          }
        }
        ws.send(JSON.stringify({
          type: "profile", found: true, username: row.username,
          avatar_data: row.avatar_data, bio: row.bio,
          clan: clanName, friendStatus,
          online: onlineByUsername.has(targetLower)
        }));
      } catch (err) {
        console.error("get_profile hatasi:", err);
      }
      return;
    }

    if (data.type === "get_avatar") {
      const targetLower = (typeof data.username === "string" ? data.username : "").trim().toLocaleLowerCase("tr");
      if (!targetLower) return;
      try {
        const r = await pool.query("SELECT username, avatar_data FROM users WHERE username_lower=$1", [targetLower]);
        if (r.rows.length) {
          ws.send(JSON.stringify({ type: "avatar", username: r.rows[0].username, avatar_data: r.rows[0].avatar_data }));
        }
      } catch (err) {
        console.error("get_avatar hatasi:", err);
      }
      return;
    }

    if (data.type === "update_profile") {
      if (!ws.username) return;
      let { avatar_data, bio } = data;
      if (typeof avatar_data === "string" && avatar_data.length > MAX_AVATAR_BYTES) {
        ws.send(JSON.stringify({ type: "profile_error", reason: "Fotoğraf çok büyük, daha küçük bir resim dene." }));
        return;
      }
      bio = typeof bio === "string" ? bio.trim().slice(0, 150) : "";
      if (containsBannedWord(bio)) {
        ws.send(JSON.stringify({ type: "profile_error", reason: "Hakkında yazın uygunsuz içerik barındırıyor." }));
        return;
      }
      try {
        await pool.query(
          "UPDATE users SET avatar_data=COALESCE($1, avatar_data), bio=$2 WHERE username_lower=$3",
          [typeof avatar_data === "string" && avatar_data ? avatar_data : null, bio, ws.username.toLocaleLowerCase("tr")]
        );
        ws.send(JSON.stringify({ type: "profile_updated" }));
      } catch (err) {
        console.error("update_profile hatasi:", err);
        ws.send(JSON.stringify({ type: "profile_error", reason: "Kaydedilemedi, tekrar dene." }));
      }
      return;
    }

    // --- Arkadaslik ---
    if (data.type === "send_friend_request") {
      if (!ws.username) return;
      const meLower = ws.username.toLocaleLowerCase("tr");
      const targetLower = (typeof data.username === "string" ? data.username : "").trim().toLocaleLowerCase("tr");
      if (!targetLower || targetLower === meLower) return;
      try {
        const existing = await pool.query(
          `SELECT status FROM friend_requests WHERE (from_lower=$1 AND to_lower=$2) OR (from_lower=$2 AND to_lower=$1)`,
          [meLower, targetLower]
        );
        if (existing.rows.length) {
          ws.send(JSON.stringify({ type: "friend_error", reason: "Zaten arkadaşsınız ya da istek bekliyor." }));
          return;
        }
        await pool.query(
          "INSERT INTO friend_requests (from_lower, to_lower, status) VALUES ($1,$2,'pending')",
          [meLower, targetLower]
        );
        ws.send(JSON.stringify({ type: "friend_request_sent", username: data.username }));
        const targetWs = onlineByUsername.get(targetLower);
        if (targetWs && targetWs.readyState === WebSocket.OPEN) {
          targetWs.send(JSON.stringify({ type: "friend_request_received", from: ws.username }));
        }
      } catch (err) {
        console.error("send_friend_request hatasi:", err);
      }
      return;
    }

    if (data.type === "respond_friend_request") {
      if (!ws.username) return;
      const meLower = ws.username.toLocaleLowerCase("tr");
      const fromLower = (typeof data.username === "string" ? data.username : "").trim().toLocaleLowerCase("tr");
      const accept = !!data.accept;
      try {
        if (accept) {
          const r = await pool.query(
            "UPDATE friend_requests SET status='accepted' WHERE from_lower=$1 AND to_lower=$2 AND status='pending' RETURNING from_lower",
            [fromLower, meLower]
          );
          if (r.rows.length) {
            ws.send(JSON.stringify({ type: "friend_accepted", username: data.username }));
            const fromWs = onlineByUsername.get(fromLower);
            if (fromWs && fromWs.readyState === WebSocket.OPEN) {
              fromWs.send(JSON.stringify({ type: "friend_accepted", username: ws.username }));
            }
          }
        } else {
          await pool.query(
            "DELETE FROM friend_requests WHERE from_lower=$1 AND to_lower=$2 AND status='pending'",
            [fromLower, meLower]
          );
          ws.send(JSON.stringify({ type: "friend_declined", username: data.username }));
        }
      } catch (err) {
        console.error("respond_friend_request hatasi:", err);
      }
      return;
    }

    if (data.type === "list_friends") {
      if (!ws.username) return;
      const meLower = ws.username.toLocaleLowerCase("tr");
      try {
        const friends = await pool.query(
          `SELECT CASE WHEN from_lower=$1 THEN to_lower ELSE from_lower END AS friend_lower
           FROM friend_requests WHERE (from_lower=$1 OR to_lower=$1) AND status='accepted'`,
          [meLower]
        );
        const pending = await pool.query(
          "SELECT from_lower FROM friend_requests WHERE to_lower=$1 AND status='pending'",
          [meLower]
        );
        const lowers = [...friends.rows.map((r) => r.friend_lower), ...pending.rows.map((r) => r.from_lower)];
        let names = {};
        if (lowers.length) {
          const nameRes = await pool.query(
            "SELECT username_lower, username FROM users WHERE username_lower = ANY($1)",
            [lowers]
          );
          nameRes.rows.forEach((r) => { names[r.username_lower] = r.username; });
        }
        ws.send(JSON.stringify({
          type: "friends_list",
          friends: friends.rows.map((r) => ({
            username: names[r.friend_lower] || r.friend_lower,
            online: onlineByUsername.has(r.friend_lower)
          })),
          pendingIncoming: pending.rows.map((r) => names[r.from_lower] || r.from_lower)
        }));
      } catch (err) {
        console.error("list_friends hatasi:", err);
      }
      return;
    }

    // --- Ozel mesaj (DM) - kalici degil, sadece aninda iletilir ---
    if (data.type === "send_dm") {
      if (!ws.username) {
        ws.send(JSON.stringify({ type: "dm_error", reason: "DM göndermek için giriş yapmalısın." }));
        return;
      }
      if (checkMuted(ws, "dm_error")) return;
      let { to, text } = data;
      if (typeof to !== "string" || typeof text !== "string") return;
      text = text.trim().slice(0, 300);
      if (!text) return;
      if (containsBannedWord(text)) {
        ws.send(JSON.stringify({ type: "dm_error", reason: "Mesaj uygunsuz içerik nedeniyle gönderilemedi." }));
        return;
      }
      const dmNow = Date.now();
      const lastDm = lastDmAt.get(ws.clientIp) || 0;
      if (dmNow - lastDm < DM_COOLDOWN_MS) return;
      lastDmAt.set(ws.clientIp, dmNow);

      const toLower = to.trim().toLocaleLowerCase("tr");
      const targetWs = onlineByUsername.get(toLower);
      const payload = { type: "dm", from: ws.username, to, text, ts: dmNow };
      if (targetWs && targetWs.readyState === WebSocket.OPEN) {
        targetWs.send(JSON.stringify(payload));
        ws.send(JSON.stringify({ ...payload, self: true }));
      } else {
        ws.send(JSON.stringify({ type: "dm_error", reason: `${to} şu anda çevrimdışı.` }));
      }
      return;
    }

    // --- Klan ---
    if (data.type === "create_clan") {
      if (!ws.username) return;
      const meLower = ws.username.toLocaleLowerCase("tr");
      if (userClan.has(meLower)) {
        ws.send(JSON.stringify({ type: "clan_error", reason: "Zaten bir klana üyesin, önce ayrılmalısın." }));
        return;
      }
      const name = typeof data.name === "string" ? data.name.trim() : "";
      const description = typeof data.description === "string" ? data.description.trim().slice(0, 200) : "";
      if (!CLAN_NAME_REGEX.test(name)) {
        ws.send(JSON.stringify({ type: "clan_error", reason: "Klan adı 3-30 karakter olmalı." }));
        return;
      }
      if (containsBannedWord(name) || containsBannedWord(description)) {
        ws.send(JSON.stringify({ type: "clan_error", reason: "Klan adı/açıklaması uygunsuz içerik barındırıyor." }));
        return;
      }
      const nameLower = name.toLocaleLowerCase("tr");
      try {
        const result = await pool.query(
          `INSERT INTO clans (name_lower, name, description, owner_username) VALUES ($1,$2,$3,$4)
           ON CONFLICT (name_lower) DO NOTHING RETURNING name_lower`,
          [nameLower, name, description, ws.username]
        );
        if (!result.rows.length) {
          ws.send(JSON.stringify({ type: "clan_error", reason: "Bu klan adı zaten alınmış." }));
          return;
        }
        await pool.query(
          "INSERT INTO clan_members (clan_name_lower, username, username_lower, role) VALUES ($1,$2,$3,'owner')",
          [nameLower, ws.username, meLower]
        );
        userClan.set(meLower, nameLower);
        clanMembersCache.set(nameLower, new Set([meLower]));
        clanChatHistory.set(nameLower, []);
        await sendMyClanInfo(ws);
      } catch (err) {
        console.error("create_clan hatasi:", err);
        ws.send(JSON.stringify({ type: "clan_error", reason: "Sunucu hatası, tekrar dene." }));
      }
      return;
    }

    if (data.type === "list_clans") {
      try {
        const res = await pool.query(`
          SELECT c.name, c.description, c.photo_data, c.owner_username,
                 COUNT(m.username_lower) AS member_count
          FROM clans c LEFT JOIN clan_members m ON m.clan_name_lower = c.name_lower
          GROUP BY c.name_lower, c.name, c.description, c.photo_data, c.owner_username
          ORDER BY member_count DESC
          LIMIT 100
        `);
        ws.send(JSON.stringify({
          type: "clans_list",
          clans: res.rows.map((r) => ({
            name: r.name, description: r.description, photo_data: r.photo_data,
            owner: r.owner_username, memberCount: Number(r.member_count)
          }))
        }));
      } catch (err) {
        console.error("list_clans hatasi:", err);
      }
      return;
    }

    if (data.type === "join_clan") {
      if (!ws.username) return;
      const meLower = ws.username.toLocaleLowerCase("tr");
      if (userClan.has(meLower)) {
        ws.send(JSON.stringify({ type: "clan_error", reason: "Zaten bir klana üyesin." }));
        return;
      }
      const nameLower = (typeof data.name === "string" ? data.name : "").trim().toLocaleLowerCase("tr");
      try {
        const clanRes = await pool.query("SELECT name_lower FROM clans WHERE name_lower=$1", [nameLower]);
        if (!clanRes.rows.length) {
          ws.send(JSON.stringify({ type: "clan_error", reason: "Klan bulunamadı." }));
          return;
        }
        await pool.query(
          "INSERT INTO clan_members (clan_name_lower, username, username_lower, role) VALUES ($1,$2,$3,'member')",
          [nameLower, ws.username, meLower]
        );
        userClan.set(meLower, nameLower);
        if (!clanMembersCache.has(nameLower)) clanMembersCache.set(nameLower, new Set());
        clanMembersCache.get(nameLower).add(meLower);
        await sendMyClanInfo(ws);
        broadcastClanSystemMessage(nameLower, `${ws.username} klana katıldı.`);
      } catch (err) {
        console.error("join_clan hatasi:", err);
        ws.send(JSON.stringify({ type: "clan_error", reason: "Katılamadın, tekrar dene." }));
      }
      return;
    }

    if (data.type === "leave_clan") {
      if (!ws.username) return;
      const meLower = ws.username.toLocaleLowerCase("tr");
      const nameLower = userClan.get(meLower);
      if (!nameLower) return;
      try {
        const clanRes = await pool.query("SELECT owner_username FROM clans WHERE name_lower=$1", [nameLower]);
        const isOwner = clanRes.rows.length && clanRes.rows[0].owner_username.toLocaleLowerCase("tr") === meLower;
        await pool.query(
          "DELETE FROM clan_members WHERE clan_name_lower=$1 AND username_lower=$2",
          [nameLower, meLower]
        );
        userClan.delete(meLower);
        clanMembersCache.get(nameLower)?.delete(meLower);

        if (isOwner) {
          const remaining = await pool.query(
            "SELECT username, username_lower FROM clan_members WHERE clan_name_lower=$1 ORDER BY joined_at ASC LIMIT 1",
            [nameLower]
          );
          if (remaining.rows.length) {
            const newOwner = remaining.rows[0];
            await pool.query("UPDATE clans SET owner_username=$1 WHERE name_lower=$2", [newOwner.username, nameLower]);
            await pool.query(
              "UPDATE clan_members SET role='owner' WHERE clan_name_lower=$1 AND username_lower=$2",
              [nameLower, newOwner.username_lower]
            );
            broadcastClanSystemMessage(nameLower, `${ws.username} ayrıldı, yönetim ${newOwner.username}'e geçti.`);
          } else {
            await pool.query("DELETE FROM clans WHERE name_lower=$1", [nameLower]);
            clanMembersCache.delete(nameLower);
            clanChatHistory.delete(nameLower);
          }
        } else {
          broadcastClanSystemMessage(nameLower, `${ws.username} klandan ayrıldı.`);
        }
        ws.send(JSON.stringify({ type: "my_clan", clan: null }));
      } catch (err) {
        console.error("leave_clan hatasi:", err);
      }
      return;
    }

    if (data.type === "kick_clan_member") {
      if (!ws.username) return;
      const meLower = ws.username.toLocaleLowerCase("tr");
      const nameLower = userClan.get(meLower);
      if (!nameLower) return;
      try {
        const clanRes = await pool.query("SELECT owner_username FROM clans WHERE name_lower=$1", [nameLower]);
        if (!clanRes.rows.length || clanRes.rows[0].owner_username.toLocaleLowerCase("tr") !== meLower) {
          ws.send(JSON.stringify({ type: "clan_error", reason: "Sadece klan sahibi üye çıkarabilir." }));
          return;
        }
        const targetLower = (typeof data.username === "string" ? data.username : "").trim().toLocaleLowerCase("tr");
        if (!targetLower || targetLower === meLower) return;
        await pool.query(
          "DELETE FROM clan_members WHERE clan_name_lower=$1 AND username_lower=$2",
          [nameLower, targetLower]
        );
        userClan.delete(targetLower);
        clanMembersCache.get(nameLower)?.delete(targetLower);
        broadcastClanSystemMessage(nameLower, `${data.username} klandan çıkarıldı.`);
        const targetWs = onlineByUsername.get(targetLower);
        if (targetWs && targetWs.readyState === WebSocket.OPEN) {
          targetWs.send(JSON.stringify({ type: "my_clan", clan: null }));
          targetWs.send(JSON.stringify({ type: "clan_error", reason: "Klandan çıkarıldın." }));
        }
        await sendMyClanInfo(ws);
      } catch (err) {
        console.error("kick_clan_member hatasi:", err);
      }
      return;
    }

    if (data.type === "update_clan") {
      if (!ws.username) return;
      const meLower = ws.username.toLocaleLowerCase("tr");
      const nameLower = userClan.get(meLower);
      if (!nameLower) return;
      try {
        const clanRes = await pool.query("SELECT owner_username FROM clans WHERE name_lower=$1", [nameLower]);
        if (!clanRes.rows.length || clanRes.rows[0].owner_username.toLocaleLowerCase("tr") !== meLower) {
          ws.send(JSON.stringify({ type: "clan_error", reason: "Sadece klan sahibi ayarları değiştirebilir." }));
          return;
        }
        const description = typeof data.description === "string" ? data.description.trim().slice(0, 200) : undefined;
        const photo_data = typeof data.photo_data === "string" ? data.photo_data : undefined;
        if (description !== undefined && containsBannedWord(description)) {
          ws.send(JSON.stringify({ type: "clan_error", reason: "Açıklama uygunsuz içerik barındırıyor." }));
          return;
        }
        if (photo_data && photo_data.length > MAX_CLAN_PHOTO_BYTES) {
          ws.send(JSON.stringify({ type: "clan_error", reason: "Fotoğraf çok büyük." }));
          return;
        }
        await pool.query(
          "UPDATE clans SET description=COALESCE($1,description), photo_data=COALESCE($2,photo_data) WHERE name_lower=$3",
          [description, photo_data, nameLower]
        );
        for (const memberLower of clanMembersCache.get(nameLower) || []) {
          const mWs = onlineByUsername.get(memberLower);
          if (mWs) await sendMyClanInfo(mWs);
        }
      } catch (err) {
        console.error("update_clan hatasi:", err);
      }
      return;
    }

    if (data.type === "clan_chat") {
      if (!ws.username) return;
      if (checkMuted(ws)) return;
      const meLower = ws.username.toLocaleLowerCase("tr");
      const nameLower = userClan.get(meLower);
      if (!nameLower) return;
      let text = typeof data.text === "string" ? data.text.trim().slice(0, 200) : "";
      if (!text) return;
      if (containsBannedWord(text)) {
        ws.send(JSON.stringify({ type: "chat_blocked", reason: "Mesaj uygunsuz içerik nedeniyle gönderilemedi." }));
        return;
      }
      const ccNow = Date.now();
      const lastC = lastClanChatAt.get(ws.clientIp) || 0;
      if (ccNow - lastC < CLAN_CHAT_COOLDOWN_MS) return;
      lastClanChatAt.set(ws.clientIp, ccNow);

      const entry = { name: ws.username, text, ts: ccNow };
      const hist = clanChatHistory.get(nameLower) || [];
      hist.push(entry);
      if (hist.length > CLAN_CHAT_HISTORY_LIMIT) hist.shift();
      clanChatHistory.set(nameLower, hist);

      const payload = JSON.stringify({ type: "clan_chat", ...entry });
      for (const memberLower of clanMembersCache.get(nameLower) || []) {
        const mWs = onlineByUsername.get(memberLower);
        if (mWs && mWs.readyState === WebSocket.OPEN) mWs.send(payload);
      }
      return;
    }

    // --- Moderator islemleri ---
    if (data.type === "mod_delete") {
      if (!isModerator(ws)) return;
      const ch = CHANNELS.includes(data.channel) ? data.channel : "tr";
      const id = Number(data.id);
      chatHistoryByChannel.set(ch, chatHistoryByChannel.get(ch).filter((m) => m.id !== id));
      broadcast({ type: "chat_delete", id, channel: ch, by: "mod" });
      return;
    }
    if (data.type === "mod_clear_channel") {
      if (!isModerator(ws)) return;
      const ch = CHANNELS.includes(data.channel) ? data.channel : null;
      if (!ch) return;
      chatHistoryByChannel.set(ch, []);
      broadcast({ type: "chat_clear", channel: ch });
      return;
    }
    if (data.type === "mod_mute" || data.type === "mod_unmute") {
      if (!isModerator(ws)) return;
      const target = (typeof data.username === "string" ? data.username : "").trim().toLocaleLowerCase("tr");
      if (!target || MODERATORS.has(target)) return;
      const targetWs = onlineByUsername.get(target);
      if (data.type === "mod_mute") {
        const minutes = Math.min(Math.max(Number(data.minutes) || 10, 1), 1440);
        mutedUntil.set(target, Date.now() + minutes * 60000);
        ws.send(JSON.stringify({ type: "mod_info", text: `${data.username} ${minutes} dk susturuldu.` }));
        if (targetWs && targetWs.readyState === WebSocket.OPEN) {
          targetWs.send(JSON.stringify({ type: "chat_blocked", reason: `Moderatör tarafından ${minutes} dk susturuldun.` }));
        }
      } else {
        mutedUntil.delete(target);
        ws.send(JSON.stringify({ type: "mod_info", text: `${data.username} susturması kaldırıldı.` }));
      }
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
      if (checkMuted(ws)) return;
      const name = ws.username;
      let { text, channel } = data;
      if (typeof text !== "string") return;
      text = text.trim().slice(0, 200);
      if (!text) return;
      if (!CHANNELS.includes(channel)) channel = "tr";

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

      const channelHistory = chatHistoryByChannel.get(channel);

      if (tracker.count >= 3) {
        // 3. tekrarda: onceki ayni mesajlari herkesin ekranindan da sil,
        // bu mesaji da hic eklemeden yoksay.
        tracker.ids.forEach(({ id, ch }) => {
          const h = chatHistoryByChannel.get(ch);
          if (h) chatHistoryByChannel.set(ch, h.filter((m) => m.id !== id));
          broadcast({ type: "chat_delete", id, channel: ch });
        });
        tracker.ids = [];
        return;
      }

      const id = nextChatId++;
      const entry = { id, name, text, ts: now, channel };
      channelHistory.push(entry);
      if (channelHistory.length > CHAT_HISTORY_LIMIT) channelHistory.shift();
      tracker.ids.push({ id, ch: channel });

      broadcast({ type: "chat", id, name, text, ts: now, channel });
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
  .then(() => loadClanCaches())
  .then(() => {
    server.listen(PORT, () => {
      console.log(`PixelTur V2 backend ${PORT} portunda calisiyor`);
    });
  })
  .catch((err) => {
    console.error("Veritabani semasi hazirlanirken hata:", err);
    process.exit(1);
  });
