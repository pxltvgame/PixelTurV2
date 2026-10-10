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
const CLAN_HISTORY_PAGE = 100;   // klan sohbeti: bir seferde yuklenen mesaj
const MAX_CLANS_PER_USER = 5;
const RANK = { member: 0, senior: 1, mod: 2, owner: 3 }; // Uye < Kidemli Uye < Moderator < Kurucu
const CLAN_NEW_NAME_REGEX = /^[A-Za-z0-9._-]{2,30}$/;
const MAX_CLAN_PHOTO_BYTES = 120 * 1024; // data URI olarak ~300KB sinir (depolamayi korumak icin)
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

// maxPayload: avatar (base64) + biyografi sigacak, ama devasa mesajlar reddedilir.
const wss = new WebSocket.Server({ server, maxPayload: 256 * 1024 });

/* ================= BOT / DoS KORUMASI ================= */
const MAX_CONN_PER_IP = 6;          // ayni IP'den en fazla eszamanli baglanti
const MAX_NEW_CONN_PER_MIN = 20;    // ayni IP'den dakikada yeni baglanti
const MSG_BURST = 30;               // baglanti basina anlik mesaj hakki
const MSG_REFILL_PER_SEC = 10;      // saniyede dolan mesaj hakki
const IP_MSG_PER_SEC = 40;          // IP basina toplam mesaj/sn (tum baglantilar)
const STRIKE_LIMIT = 5;             // bu kadar ihlalde gecici ban
const BAN_MS = 10 * 60 * 1000;      // 10 dk

const bannedUntil = new Map();      // ip -> ts
const connCountByIp = new Map();    // ip -> sayi
const newConnLog = new Map();       // ip -> [ts,...]
const ipMsgBucket = new Map();      // ip -> {sec, n}
const strikesByIp = new Map();      // ip -> {n, ts}

function isBanned(ip) {
  const t = bannedUntil.get(ip);
  if (!t) return false;
  if (Date.now() > t) { bannedUntil.delete(ip); return false; }
  return true;
}
function banIp(ip, reason) {
  bannedUntil.set(ip, Date.now() + BAN_MS);
  console.warn(`[guard] ${ip} ${BAN_MS / 60000} dk banlandi: ${reason}`);
  for (const c of wss.clients) {
    if (c.clientIp === ip) { try { c.close(1008, "Cok fazla istek"); } catch {} setTimeout(() => { try { c.terminate(); } catch {} }, 1000); }
  }
}
function addStrike(ws, reason, weight = 1) {
  const ip = ws.clientIp;
  const now = Date.now();
  const st = strikesByIp.get(ip) || { n: 0, ts: now };
  if (now - st.ts > 60 * 1000) { st.n = 0; st.ts = now; } // 1 dk icinde say
  st.n += weight;
  strikesByIp.set(ip, st);
  if (st.n >= STRIKE_LIMIT) { strikesByIp.delete(ip); banIp(ip, reason); return true; }
  return false;
}
// Baglanti basina token bucket
function allowMessage(ws) {
  const now = Date.now();
  if (!ws.bucket) ws.bucket = { tokens: MSG_BURST, ts: now };
  const b = ws.bucket;
  b.tokens = Math.min(MSG_BURST, b.tokens + ((now - b.ts) / 1000) * MSG_REFILL_PER_SEC);
  b.ts = now;
  if (b.tokens < 1) return false;
  b.tokens -= 1;
  // IP basina toplam
  const sec = Math.floor(now / 1000);
  const ib = ipMsgBucket.get(ws.clientIp);
  if (!ib || ib.sec !== sec) ipMsgBucket.set(ws.clientIp, { sec, n: 1 });
  else if (++ib.n > IP_MSG_PER_SEC) return false;
  return true;
}
// Bellek temizligi
setInterval(() => {
  const now = Date.now();
  for (const [ip, t] of bannedUntil) if (now > t) bannedUntil.delete(ip);
  for (const [ip, arr] of newConnLog) {
    const f = arr.filter((t) => now - t < 60000);
    if (f.length) newConnLog.set(ip, f); else newConnLog.delete(ip);
  }
  for (const [ip, st] of strikesByIp) if (now - st.ts > 60000) strikesByIp.delete(ip);
  for (const [ip, b] of ipMsgBucket) if (Math.floor(now / 1000) - b.sec > 5) ipMsgBucket.delete(ip);
  for (const [ip, t] of lastPlacedAt) if (now - t > 5 * 60 * 1000) lastPlacedAt.delete(ip);
}, 60 * 1000).unref();


/* ================= INSAN DOGRULAMA (captcha) =================
   Disaridan hesap/anahtar gerektirmez; GitHub Pages ve exe'de de calisir.
   Kayit olurken ve (hesapsiz) ilk piksel basarken istenir.
   Dogrulanan IP 6 saat dogrulanmis sayilir; giris yapan hesap da dogrulanmistir. */
const CAPTCHA_TTL_MS = 3 * 60 * 1000;
const HUMAN_TTL_MS = 6 * 60 * 60 * 1000;
const CAPTCHA_CHARS = "ABCDEFGHJKLMNPRSTUVWXYZ23456789";
const captchas = new Map();      // id -> {answer, exp, tries}
const humanIps = new Map();      // ip -> expiry ts
const lastCaptchaAt = new Map(); // ip -> ts
const crypto = require("crypto");

function rnd(n) { return crypto.randomInt(n); }
function makeCaptcha() {
  let text = "";
  for (let i = 0; i < 5; i++) text += CAPTCHA_CHARS[rnd(CAPTCHA_CHARS.length)];
  const W = 190, H = 64;
  const colors = ["#c0392b", "#1f6fb2", "#1e8449", "#8e44ad", "#d35400", "#2c3e50"];
  let svg = `<svg xmlns="http://www.w3.org/2000/svg" width="${W}" height="${H}" viewBox="0 0 ${W} ${H}"><rect width="100%" height="100%" fill="#f1f1f1"/>`;
  for (let i = 0; i < 7; i++) {
    svg += `<path d="M${rnd(W)} ${rnd(H)} C${rnd(W)} ${rnd(H)},${rnd(W)} ${rnd(H)},${rnd(W)} ${rnd(H)}" stroke="${colors[rnd(colors.length)]}" stroke-width="${1 + rnd(2)}" fill="none" opacity="0.65"/>`;
  }
  for (let i = 0; i < 40; i++) {
    svg += `<circle cx="${rnd(W)}" cy="${rnd(H)}" r="${1 + rnd(2)}" fill="${colors[rnd(colors.length)]}" opacity="0.5"/>`;
  }
  for (let i = 0; i < text.length; i++) {
    const x = 18 + i * 32 + rnd(6);
    const y = 42 + rnd(12);
    const rot = rnd(50) - 25;
    const size = 30 + rnd(10);
    svg += `<text x="${x}" y="${y}" font-family="Arial,Helvetica,sans-serif" font-weight="bold" font-size="${size}" fill="${colors[rnd(colors.length)]}" transform="rotate(${rot} ${x} ${y})">${text[i]}</text>`;
  }
  for (let i = 0; i < 3; i++) {
    svg += `<path d="M0 ${10 + rnd(H - 20)} Q${W / 2} ${rnd(H)} ${W} ${10 + rnd(H - 20)}" stroke="#222" stroke-width="1.5" fill="none" opacity="0.55"/>`;
  }
  svg += "</svg>";
  const id = crypto.randomBytes(12).toString("hex");
  if (captchas.size > 3000) captchas.clear(); // asiri dolmaya karsi
  captchas.set(id, { answer: text, exp: Date.now() + CAPTCHA_TTL_MS, tries: 0 });
  return { id, svg };
}
function isHuman(ws) {
  if (ws.human) return true;
  const t = humanIps.get(ws.clientIp);
  if (t && Date.now() < t) { ws.human = true; return true; }
  return false;
}
setInterval(() => {
  const now = Date.now();
  for (const [id, c] of captchas) if (now > c.exp) captchas.delete(id);
  for (const [ip, t] of humanIps) if (now > t) humanIps.delete(ip);
  for (const [ip, t] of lastCaptchaAt) if (now - t > 60000) lastCaptchaAt.delete(ip);
}, 60 * 1000).unref();

// Olu baglantilari at (ping/pong)
setInterval(() => {
  for (const c of wss.clients) {
    if (c.isAlive === false) { c.terminate(); continue; }
    c.isAlive = false;
    try { c.ping(); } catch {}
  }
}, 30 * 1000).unref();

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
// usernameLower -> Set<clanNameLower>: bir kullanici en fazla MAX_CLANS_PER_USER klana uye olabilir
const userClans = new Map();
// clanNameLower -> Set<usernameLower> (klan sohbetini sadece uyelere yollamak icin)
const clanMembersCache = new Map();
const lastDmAt = new Map();
const lastClanChatAt = new Map();
const lastInviteAt = new Map();
const repClanByUser = new Map(); // usernameLower -> temsil edilen klan (piksel sayaci icin)

// Temsil edilen klana atilan pikseli say (sadece giris yapmis ve klan temsil eden kullanicilar)
function creditClanPixel(lower) {
  const nl = repClanByUser.get(lower);
  if (!nl || !myClanSet(lower).has(nl)) return;
  pool.query("UPDATE clans SET pixels_total = pixels_total + 1 WHERE name_lower=$1", [nl]).catch(() => {});
  pool.query(
    "INSERT INTO clan_daily (clan_name_lower, day, pixels) VALUES ($1, CURRENT_DATE, 1) ON CONFLICT (clan_name_lower, day) DO UPDATE SET pixels = clan_daily.pixels + 1",
    [nl]
  ).catch(() => {});
}
async function loadRepClan(ws) {
  const lower = ws.username.toLocaleLowerCase("tr");
  const r = await pool.query("SELECT rep_clan FROM users WHERE username_lower=$1", [lower]);
  if (r.rows.length && r.rows[0].rep_clan) repClanByUser.set(lower, r.rows[0].rep_clan);
  else repClanByUser.delete(lower);
}

function myClanSet(lower) { return userClans.get(lower) || new Set(); }
function cacheAddMember(clan, lower) {
  if (!userClans.has(lower)) userClans.set(lower, new Set());
  userClans.get(lower).add(clan);
  if (!clanMembersCache.has(clan)) clanMembersCache.set(clan, new Set());
  clanMembersCache.get(clan).add(lower);
}
function cacheRemoveMember(clan, lower) {
  userClans.get(lower)?.delete(clan);
  if (userClans.get(lower)?.size === 0) userClans.delete(lower);
  clanMembersCache.get(clan)?.delete(lower);
}
function normClan(v) { return (typeof v === "string" ? v : "").trim().toLocaleLowerCase("tr"); }
function sendTo(ws, obj) { if (ws && ws.readyState === WebSocket.OPEN) ws.send(JSON.stringify(obj)); }
function clanError(ws, reason) { sendTo(ws, { type: "clan_error", reason }); }

async function loadClanCaches() {
  const members = await pool.query("SELECT clan_name_lower, username_lower FROM clan_members");
  userClans.clear();
  clanMembersCache.clear();
  for (const row of members.rows) cacheAddMember(row.clan_name_lower, row.username_lower);
}

async function getClanFullInfo(nameLower, viewerLower) {
  const clanRes = await pool.query("SELECT * FROM clans WHERE name_lower=$1", [nameLower]);
  if (!clanRes.rows.length) return null;
  const clan = clanRes.rows[0];
  const membersRes = await pool.query(
    "SELECT username, role FROM clan_members WHERE clan_name_lower=$1 ORDER BY joined_at ASC",
    [nameLower]
  );
  const me = membersRes.rows.find((m) => m.username.toLocaleLowerCase("tr") === viewerLower);
  const myRank = me ? RANK[me.role] : 0;
  const bansRes = await pool.query("SELECT username FROM clan_bans WHERE clan_name_lower=$1 ORDER BY ts DESC", [nameLower]);
  let invites = [];
  if (myRank >= RANK.senior) {
    const inv = await pool.query(
      `SELECT COALESCE(u.username, i.to_lower) AS username, i.from_username
       FROM clan_invites i LEFT JOIN users u ON u.username_lower = i.to_lower
       WHERE i.clan_name_lower=$1 ORDER BY i.created_at DESC`,
      [nameLower]
    );
    invites = inv.rows.map((r) => ({ username: r.username, from: r.from_username }));
  }
  const today = await pool.query("SELECT pixels FROM clan_daily WHERE clan_name_lower=$1 AND day=CURRENT_DATE", [nameLower]);
  const pixelsToday = today.rows.length ? Number(today.rows[0].pixels) : 0;
  const pixelsTotal = Number(clan.pixels_total || 0);
  let rankTotal = null, rankDaily = null;
  if (pixelsTotal > 0) {
    const rt = await pool.query("SELECT COUNT(*) AS n FROM clans WHERE pixels_total > $1", [pixelsTotal]);
    rankTotal = Number(rt.rows[0].n) + 1;
  }
  if (pixelsToday > 0) {
    const rd = await pool.query("SELECT COUNT(*) AS n FROM clan_daily WHERE day=CURRENT_DATE AND pixels > $1", [pixelsToday]);
    rankDaily = Number(rd.rows[0].n) + 1;
  }
  return {
    key: nameLower,
    name: clan.name,
    title: clan.title || clan.name,
    description: clan.description,
    photo_data: clan.photo_data,
    owner: clan.owner_username,
    join_mode: clan.join_mode || "open",
    hidden: !!clan.hidden,
    members: membersRes.rows.map((m) => ({
      username: m.username,
      role: m.role,
      online: onlineByUsername.has(m.username.toLocaleLowerCase("tr"))
    })),
    bans: bansRes.rows.map((r) => r.username),
    invites,
    stats: { pixelsToday, pixelsTotal, rankDaily, rankTotal }
  };
}

async function getMyRole(nameLower, meLower) {
  const r = await pool.query(
    "SELECT role FROM clan_members WHERE clan_name_lower=$1 AND username_lower=$2",
    [nameLower, meLower]
  );
  return r.rows.length ? r.rows[0].role : null;
}

function wireClanMsg(nameLower, row) {
  return {
    id: row.id, clan: nameLower,
    name: row.system ? "Sistem" : row.username,
    text: row.text, ts: new Date(row.ts).getTime(), system: !!row.system
  };
}

// Klan sohbeti KALICI: veritabaninda saklanir, hicbir zaman otomatik silinmez.
async function sendClanHistory(ws, nameLower, beforeId, prepend) {
  const params = [nameLower, CLAN_HISTORY_PAGE + 1];
  let sql = "SELECT id, username, text, system, ts FROM clan_messages WHERE clan_name_lower=$1";
  if (beforeId) { params.push(beforeId); sql += " AND id < $3"; }
  sql += " ORDER BY id DESC LIMIT $2";
  const r = await pool.query(sql, params);
  const hasMore = r.rows.length > CLAN_HISTORY_PAGE;
  const rows = r.rows.slice(0, CLAN_HISTORY_PAGE).reverse();
  sendTo(ws, {
    type: "clan_history", clan: nameLower, prepend: !!prepend, hasMore,
    messages: rows.map((row) => wireClanMsg(nameLower, row))
  });
}

// history: false | "all" | [clanNameLower,...]
async function sendMyClanInfo(ws, history) {
  if (!ws.username || ws.readyState !== WebSocket.OPEN) return;
  const meLower = ws.username.toLocaleLowerCase("tr");
  const clans = [];
  for (const nl of myClanSet(meLower)) {
    const info = await getClanFullInfo(nl, meLower);
    if (info) clans.push(info);
  }
  const rep = repClanByUser.get(meLower);
  sendTo(ws, { type: "my_clans", clans, rep: rep && myClanSet(meLower).has(rep) ? rep : null });
  if (history) {
    const targets = history === "all" ? clans.map((c) => c.key) : history;
    for (const nl of targets) {
      try { await sendClanHistory(ws, nl, null, false); } catch (e) { console.error("klan gecmisi hatasi:", e); }
    }
  }
}

async function refreshClanMembers(nameLower) {
  for (const memberLower of clanMembersCache.get(nameLower) || []) {
    const mWs = onlineByUsername.get(memberLower);
    if (mWs) { try { await sendMyClanInfo(mWs); } catch {} }
  }
}

async function postClanMessage(nameLower, username, text, system = false) {
  const r = await pool.query(
    "INSERT INTO clan_messages (clan_name_lower, username, text, system) VALUES ($1,$2,$3,$4) RETURNING id, ts",
    [nameLower, username, text, system]
  );
  const payload = JSON.stringify({
    type: "clan_chat",
    ...wireClanMsg(nameLower, { id: r.rows[0].id, username, text, system, ts: r.rows[0].ts })
  });
  for (const memberLower of clanMembersCache.get(nameLower) || []) {
    const mWs = onlineByUsername.get(memberLower);
    if (mWs && mWs.readyState === WebSocket.OPEN) mWs.send(payload);
  }
}
async function clanSystem(nameLower, text) {
  try { await postClanMessage(nameLower, "Sistem", text, true); }
  catch (e) { console.error("klan sistem mesaji hatasi:", e); }
}

async function sendClanInvites(ws) {
  if (!ws.username || ws.readyState !== WebSocket.OPEN) return;
  const lower = ws.username.toLocaleLowerCase("tr");
  const r = await pool.query(
    `SELECT i.clan_name_lower, c.name, i.from_username
     FROM clan_invites i JOIN clans c ON c.name_lower = i.clan_name_lower
     WHERE i.to_lower=$1 ORDER BY i.created_at DESC LIMIT 50`,
    [lower]
  );
  sendTo(ws, {
    type: "clan_invites",
    invites: r.rows.map((x) => ({ key: x.clan_name_lower, clan: x.name, from: x.from_username }))
  });
}

// Bir kullaniciyi klana ekler (limit kontrolu cagirana ait degil, burada yapilir)
async function addMemberToClan(ws, nameLower) {
  const meLower = ws.username.toLocaleLowerCase("tr");
  if (myClanSet(meLower).has(nameLower)) { clanError(ws, "Zaten bu klanın üyesisin."); return false; }
  if (myClanSet(meLower).size >= MAX_CLANS_PER_USER) {
    clanError(ws, `En fazla ${MAX_CLANS_PER_USER} klana üye olabilirsin.`);
    return false;
  }
  const banned = await pool.query("SELECT 1 FROM clan_bans WHERE clan_name_lower=$1 AND username_lower=$2", [nameLower, meLower]);
  if (banned.rows.length) { clanError(ws, "Bu klandan yasaklısın."); return false; }
  await pool.query(
    "INSERT INTO clan_members (clan_name_lower, username, username_lower, role) VALUES ($1,$2,$3,'member') ON CONFLICT DO NOTHING",
    [nameLower, ws.username, meLower]
  );
  await pool.query("DELETE FROM clan_invites WHERE clan_name_lower=$1 AND to_lower=$2", [nameLower, meLower]);
  cacheAddMember(nameLower, meLower);
  await sendMyClanInfo(ws, [nameLower]);
  await clanSystem(nameLower, `${ws.username} klana katıldı.`);
  await refreshClanMembers(nameLower);
  return true;
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
  await pool.query(`ALTER TABLE clans ADD COLUMN IF NOT EXISTS join_mode TEXT NOT NULL DEFAULT 'open';`);
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
  // Klan sohbeti kalici: mesajlar hicbir zaman otomatik silinmez.
  await pool.query(`
    CREATE TABLE IF NOT EXISTS clan_messages (
      id SERIAL PRIMARY KEY,
      clan_name_lower TEXT NOT NULL REFERENCES clans(name_lower) ON DELETE CASCADE,
      username TEXT NOT NULL,
      text TEXT NOT NULL,
      system BOOLEAN NOT NULL DEFAULT FALSE,
      ts TIMESTAMPTZ NOT NULL DEFAULT NOW()
    );
  `);
  await pool.query(`CREATE INDEX IF NOT EXISTS clan_messages_clan_id ON clan_messages (clan_name_lower, id);`);
  await pool.query(`ALTER TABLE clans ADD COLUMN IF NOT EXISTS title TEXT NOT NULL DEFAULT '';`);
  await pool.query(`ALTER TABLE clans ADD COLUMN IF NOT EXISTS hidden BOOLEAN NOT NULL DEFAULT FALSE;`);
  await pool.query(`ALTER TABLE clans ADD COLUMN IF NOT EXISTS pixels_total BIGINT NOT NULL DEFAULT 0;`);
  await pool.query(`ALTER TABLE users ADD COLUMN IF NOT EXISTS rep_clan TEXT;`);
  await pool.query(`
    CREATE TABLE IF NOT EXISTS clan_daily (
      clan_name_lower TEXT NOT NULL REFERENCES clans(name_lower) ON DELETE CASCADE,
      day DATE NOT NULL DEFAULT CURRENT_DATE,
      pixels INTEGER NOT NULL DEFAULT 0,
      PRIMARY KEY (clan_name_lower, day)
    );
  `);
  await pool.query(`
    CREATE TABLE IF NOT EXISTS clan_bans (
      clan_name_lower TEXT NOT NULL REFERENCES clans(name_lower) ON DELETE CASCADE,
      username_lower TEXT NOT NULL,
      username TEXT NOT NULL,
      banned_by TEXT NOT NULL,
      ts TIMESTAMPTZ NOT NULL DEFAULT NOW(),
      PRIMARY KEY (clan_name_lower, username_lower)
    );
  `);
  await pool.query(`
    CREATE TABLE IF NOT EXISTS clan_invites (
      clan_name_lower TEXT NOT NULL REFERENCES clans(name_lower) ON DELETE CASCADE,
      to_lower TEXT NOT NULL,
      from_username TEXT NOT NULL,
      created_at TIMESTAMPTZ DEFAULT NOW(),
      PRIMARY KEY (clan_name_lower, to_lower)
    );
  `);
}

async function loadBoard() {
  const res = await pool.query("SELECT x,y,color FROM pixels");
  return res.rows;
}

function cleanIp(v) {
  if (typeof v !== "string") return null;
  v = v.trim().replace(/^::ffff:/, "");
  return /^[0-9a-fA-F:.]{3,45}$/.test(v) ? v : null;
}
function getClientIp(req) {
  // Render, Cloudflare arkasinda calisir. Cloudflare bu basliklari kendisi
  // yazar (istemci sahteleyemez). X-Forwarded-For'un ILK elemani ise
  // istemci tarafindan sahtelenebilir, bu yuzden sadece son care.
  const h = req.headers;
  return (
    cleanIp(h["cf-connecting-ip"]) ||
    cleanIp(h["true-client-ip"]) ||
    cleanIp((h["x-forwarded-for"] || "").split(",").pop()) ||
    cleanIp(req.socket.remoteAddress) ||
    "unknown"
  );
}

wss.on("connection", async (ws, req) => {
  ws.clientIp = getClientIp(req);
  ws.isAlive = true;
  ws.on("pong", () => { ws.isAlive = true; });
  ws.on("error", () => {});

  // --- Bot korumasi: ban / baglanti sayisi / baglanti hizi ---
  if (isBanned(ws.clientIp)) { ws.close(1008, "Gecici olarak engellendin"); return; }
  const cur = connCountByIp.get(ws.clientIp) || 0;
  if (cur >= MAX_CONN_PER_IP) { ws.close(1008, "Cok fazla baglanti"); return; }
  const nowC = Date.now();
  const log = (newConnLog.get(ws.clientIp) || []).filter((t) => nowC - t < 60000);
  log.push(nowC);
  newConnLog.set(ws.clientIp, log);
  if (log.length > MAX_NEW_CONN_PER_MIN) { banIp(ws.clientIp, "baglanti seli"); ws.close(1008, "Cok fazla baglanti"); return; }
  connCountByIp.set(ws.clientIp, cur + 1);
  ws.on("close", () => {
    const n = (connCountByIp.get(ws.clientIp) || 1) - 1;
    if (n <= 0) connCountByIp.delete(ws.clientIp); else connCountByIp.set(ws.clientIp, n);
  });
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
      online: wss.clients.size,
      version: 4 // 4 = klan penceresi: baslik/gizli/yasak/kidemli uye/temsil/istatistik
    }));
  } catch (err) {
    console.error("Tahta yuklenirken hata:", err);
  }

  ws.on("message", async (msg, isBinary) => {
    if (isBinary) { addStrike(ws, "binary mesaj", 2); return; }
    if (!allowMessage(ws)) { addStrike(ws, "mesaj seli"); return; }
    let data;
    try {
      data = JSON.parse(msg);
    } catch {
      addStrike(ws, "gecersiz JSON");
      return;
    }
    if (!data || typeof data !== "object" || typeof data.type !== "string") {
      addStrike(ws, "gecersiz mesaj");
      return;
    }

    if (data.type === "get_captcha") {
      const nowG = Date.now();
      if (nowG - (lastCaptchaAt.get(ws.clientIp) || 0) < 1200) { addStrike(ws, "captcha seli", 0.5); return; }
      lastCaptchaAt.set(ws.clientIp, nowG);
      const c = makeCaptcha();
      ws.send(JSON.stringify({ type: "captcha", id: c.id, svg: c.svg }));
      return;
    }
    if (data.type === "verify_human") {
      const c = typeof data.id === "string" ? captchas.get(data.id) : null;
      const ans = typeof data.answer === "string" ? data.answer.trim().toUpperCase() : "";
      if (!c || Date.now() > c.exp) {
        ws.send(JSON.stringify({ type: "human_fail", reason: "Kodun süresi doldu, yeni kod alındı." }));
        return;
      }
      c.tries++;
      if (ans && ans === c.answer) {
        captchas.delete(data.id);
        ws.human = true;
        humanIps.set(ws.clientIp, Date.now() + HUMAN_TTL_MS);
        ws.send(JSON.stringify({ type: "human_ok" }));
      } else {
        captchas.delete(data.id); // her kod tek kullanimlik
        addStrike(ws, "captcha denemesi", 0.5);
        ws.send(JSON.stringify({ type: "human_fail", reason: "Kod yanlış, yeni kod alındı." }));
      }
      return;
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

      if (action === "register" && !isHuman(ws)) {
        ws.send(JSON.stringify({ type: "need_human", reason: "register" }));
        return;
      }

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
          ws.human = true; // sifreyle giris yapan hesap dogrulanmis sayilir
          ws.send(JSON.stringify({ type: "auth_ok", action, username: ws.username, moderator: isModerator(ws) }));
        }
        // Giris/kayit basarili oldu: klan bilgisi + sohbet gecmisi + bekleyen davetler
        await loadRepClan(ws);
        await sendMyClanInfo(ws, "all");
        await sendClanInvites(ws);
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
        let clanNames = [];
        const clanLowers = [...myClanSet(targetLower)];
        if (clanLowers.length) {
          const clanRes = await pool.query("SELECT name FROM clans WHERE name_lower = ANY($1) ORDER BY name", [clanLowers]);
          clanNames = clanRes.rows.map((r) => r.name);
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
          clans: clanNames, friendStatus,
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

    // --- Klan (cok klanli, 4 rutbe, davet, yasak, kalici sohbet) ---
    if (data.type && String(data.type).includes("clan") && !ws.username && data.type !== "list_clans") {
      clanError(ws, "Oturumun düşmüş (bağlantı yenilenmiş olabilir). Hesabım'dan tekrar giriş yap.");
      return;
    }

    // Bir klanda islem yapanin ve hedefin rutbesini getirir
    const clanRanks = async (nameLower, aLower, tLower) => {
      const r = await pool.query(
        "SELECT username_lower, role FROM clan_members WHERE clan_name_lower=$1 AND username_lower = ANY($2)",
        [nameLower, [aLower, tLower]]
      );
      const m = {};
      r.rows.forEach((x) => (m[x.username_lower] = x.role));
      return { a: m[aLower] ?? null, t: m[tLower] ?? null };
    };

    if (data.type === "create_clan") {
      const meLower = ws.username.toLocaleLowerCase("tr");
      if (myClanSet(meLower).size >= MAX_CLANS_PER_USER) {
        clanError(ws, `En fazla ${MAX_CLANS_PER_USER} klana üye olabilirsin.`);
        return;
      }
      const name = typeof data.name === "string" ? data.name.trim() : "";
      const title = (typeof data.title === "string" ? data.title.trim() : "").slice(0, 40) || name;
      const description = typeof data.description === "string" ? data.description.trim().slice(0, 200) : "";
      const photo = typeof data.photo_data === "string" && data.photo_data ? data.photo_data : null;
      const hidden = !!data.hidden;
      const joinMode = data.open ? "open" : "invite";
      if (!CLAN_NEW_NAME_REGEX.test(name)) { clanError(ws, "Klan adı 2-30 karakter olmalı: harf, rakam ve . - _ kullanılabilir."); return; }
      if (containsBannedWord(name) || containsBannedWord(title) || containsBannedWord(description)) {
        clanError(ws, "Klan adı/başlığı/açıklaması uygunsuz içerik barındırıyor.");
        return;
      }
      if (photo && photo.length > MAX_CLAN_PHOTO_BYTES) { clanError(ws, "Avatar çok büyük."); return; }
      const nameLower = name.toLocaleLowerCase("tr");
      try {
        const result = await pool.query(
          `INSERT INTO clans (name_lower, name, title, description, owner_username, photo_data, join_mode, hidden)
           VALUES ($1,$2,$3,$4,$5,$6,$7,$8)
           ON CONFLICT (name_lower) DO NOTHING RETURNING name_lower`,
          [nameLower, name, title, description, ws.username, photo, joinMode, hidden]
        );
        if (!result.rows.length) { clanError(ws, "Bu klan adı zaten alınmış."); return; }
        await pool.query(
          "INSERT INTO clan_members (clan_name_lower, username, username_lower, role) VALUES ($1,$2,$3,'owner')",
          [nameLower, ws.username, meLower]
        );
        cacheAddMember(nameLower, meLower);
        await sendMyClanInfo(ws, [nameLower]);
        await clanSystem(nameLower, `${title} klanı ${ws.username} tarafından kuruldu.`);
      } catch (err) {
        console.error("create_clan hatasi:", err);
        clanError(ws, "Sunucu hatası, tekrar dene.");
      }
      return;
    }

    if (data.type === "list_clans") {
      const q = normClan(data.q);
      try {
        const esc = q.replace(/[\\%_]/g, "\\$&");
        const res = await pool.query(`
          SELECT c.name, c.title, c.description, c.photo_data, c.join_mode,
                 COUNT(m.username_lower) AS member_count
          FROM clans c LEFT JOIN clan_members m ON m.clan_name_lower = c.name_lower
          WHERE (c.hidden = FALSE OR c.name_lower = $1)
            AND ($1 = '' OR c.name_lower LIKE '%' || $2 || '%' OR LOWER(c.title) LIKE '%' || $2 || '%')
          GROUP BY c.name_lower, c.name, c.title, c.description, c.photo_data, c.join_mode
          ORDER BY member_count DESC
          LIMIT 50
        `, [q, esc]);
        sendTo(ws, {
          type: "clans_list",
          clans: res.rows.map((r) => ({
            name: r.name, title: r.title || r.name, description: r.description, photo_data: r.photo_data,
            join_mode: r.join_mode || "open", memberCount: Number(r.member_count)
          }))
        });
      } catch (err) {
        console.error("list_clans hatasi:", err);
      }
      return;
    }

    if (data.type === "refresh_clans") {
      try { await sendMyClanInfo(ws); await sendClanInvites(ws); } catch (err) { console.error("refresh hatasi:", err); }
      return;
    }

    if (data.type === "join_clan") {
      const nameLower = normClan(data.name);
      try {
        const clanRes = await pool.query("SELECT join_mode FROM clans WHERE name_lower=$1", [nameLower]);
        if (!clanRes.rows.length) { clanError(ws, "Klan bulunamadı."); return; }
        if ((clanRes.rows[0].join_mode || "open") !== "open") { clanError(ws, "Bu klan sadece davetle üye alıyor."); return; }
        await addMemberToClan(ws, nameLower);
      } catch (err) {
        console.error("join_clan hatasi:", err);
        clanError(ws, "Katılamadın, tekrar dene.");
      }
      return;
    }

    if (data.type === "leave_clan") {
      const meLower = ws.username.toLocaleLowerCase("tr");
      const nameLower = normClan(data.name || data.clan);
      if (!myClanSet(meLower).has(nameLower)) return;
      try {
        const role = await getMyRole(nameLower, meLower);
        await pool.query("DELETE FROM clan_members WHERE clan_name_lower=$1 AND username_lower=$2", [nameLower, meLower]);
        cacheRemoveMember(nameLower, meLower);
        if (role === "owner") {
          const next = await pool.query(
            `SELECT username, username_lower FROM clan_members WHERE clan_name_lower=$1
             ORDER BY (role='mod') DESC, (role='senior') DESC, joined_at ASC LIMIT 1`,
            [nameLower]
          );
          if (next.rows.length) {
            const n = next.rows[0];
            await pool.query("UPDATE clans SET owner_username=$1 WHERE name_lower=$2", [n.username, nameLower]);
            await pool.query("UPDATE clan_members SET role='owner' WHERE clan_name_lower=$1 AND username_lower=$2", [nameLower, n.username_lower]);
            await clanSystem(nameLower, `${ws.username} ayrıldı, klan sahipliği ${n.username} kullanıcısına geçti.`);
            await refreshClanMembers(nameLower);
          } else {
            await pool.query("DELETE FROM clans WHERE name_lower=$1", [nameLower]);
            clanMembersCache.delete(nameLower);
          }
        } else {
          await clanSystem(nameLower, `${ws.username} klandan ayrıldı.`);
          await refreshClanMembers(nameLower);
        }
        await sendMyClanInfo(ws);
      } catch (err) {
        console.error("leave_clan hatasi:", err);
      }
      return;
    }

    if (data.type === "kick_clan_member" || data.type === "ban_clan_member") {
      const ban = data.type === "ban_clan_member";
      const meLower = ws.username.toLocaleLowerCase("tr");
      const nameLower = normClan(data.clan);
      const targetLower = normClan(data.username);
      if (!myClanSet(meLower).has(nameLower) || !targetLower || targetLower === meLower) return;
      try {
        const { a, t } = await clanRanks(nameLower, meLower, targetLower);
        if (!t) return;
        if (RANK[a] < RANK.mod || RANK[a] <= RANK[t]) { clanError(ws, "Bu üyeye işlem yapma yetkin yok."); return; }
        await pool.query("DELETE FROM clan_members WHERE clan_name_lower=$1 AND username_lower=$2", [nameLower, targetLower]);
        cacheRemoveMember(nameLower, targetLower);
        if (ban) {
          await pool.query(
            "INSERT INTO clan_bans (clan_name_lower, username_lower, username, banned_by) VALUES ($1,$2,$3,$4) ON CONFLICT DO NOTHING",
            [nameLower, targetLower, data.username, ws.username]
          );
          await pool.query("DELETE FROM clan_invites WHERE clan_name_lower=$1 AND to_lower=$2", [nameLower, targetLower]);
        }
        await clanSystem(nameLower, ban ? `${data.username} klandan yasaklandı.` : `${data.username} klandan çıkarıldı.`);
        await refreshClanMembers(nameLower);
        const targetWs = onlineByUsername.get(targetLower);
        if (targetWs) {
          await sendMyClanInfo(targetWs);
          clanError(targetWs, ban ? "Bir klandan yasaklandın." : "Bir klandan çıkarıldın.");
        }
      } catch (err) {
        console.error("kick/ban hatasi:", err);
      }
      return;
    }

    if (data.type === "unban_clan_member") {
      const meLower = ws.username.toLocaleLowerCase("tr");
      const nameLower = normClan(data.clan);
      const targetLower = normClan(data.username);
      if (!myClanSet(meLower).has(nameLower) || !targetLower) return;
      try {
        const role = await getMyRole(nameLower, meLower);
        if (RANK[role] < RANK.mod) { clanError(ws, "Yasağı kaldırma yetkin yok."); return; }
        await pool.query("DELETE FROM clan_bans WHERE clan_name_lower=$1 AND username_lower=$2", [nameLower, targetLower]);
        await refreshClanMembers(nameLower);
      } catch (err) {
        console.error("unban hatasi:", err);
      }
      return;
    }

    if (data.type === "set_clan_role") {
      const meLower = ws.username.toLocaleLowerCase("tr");
      const nameLower = normClan(data.clan);
      const targetLower = normClan(data.username);
      const newRole = ["mod", "senior", "member"].includes(data.role) ? data.role : null;
      if (!newRole || !myClanSet(meLower).has(nameLower) || targetLower === meLower) return;
      try {
        const { a, t } = await clanRanks(nameLower, meLower, targetLower);
        if (!t) return;
        if (RANK[a] < RANK.mod || RANK[a] <= RANK[t] || RANK[a] <= RANK[newRole]) {
          clanError(ws, "Bu rütbeyi verme yetkin yok.");
          return;
        }
        await pool.query("UPDATE clan_members SET role=$3 WHERE clan_name_lower=$1 AND username_lower=$2", [nameLower, targetLower, newRole]);
        const label = { mod: "Moderatör", senior: "Kıdemli Üye", member: "Üye" }[newRole];
        await clanSystem(nameLower, `${data.username} kullanıcısının rütbesi: ${label}.`);
        await refreshClanMembers(nameLower);
      } catch (err) {
        console.error("set_clan_role hatasi:", err);
      }
      return;
    }

    if (data.type === "transfer_clan") {
      const meLower = ws.username.toLocaleLowerCase("tr");
      const nameLower = normClan(data.clan);
      const targetLower = normClan(data.username);
      if (!myClanSet(meLower).has(nameLower) || !targetLower || targetLower === meLower) return;
      try {
        if ((await getMyRole(nameLower, meLower)) !== "owner") { clanError(ws, "Sadece kurucu klanı devredebilir."); return; }
        const t = await pool.query("SELECT username FROM clan_members WHERE clan_name_lower=$1 AND username_lower=$2", [nameLower, targetLower]);
        if (!t.rows.length) { clanError(ws, "Bu kullanıcı klanın üyesi değil."); return; }
        const newOwner = t.rows[0].username;
        await pool.query("UPDATE clans SET owner_username=$1 WHERE name_lower=$2", [newOwner, nameLower]);
        await pool.query("UPDATE clan_members SET role='owner' WHERE clan_name_lower=$1 AND username_lower=$2", [nameLower, targetLower]);
        await pool.query("UPDATE clan_members SET role='mod' WHERE clan_name_lower=$1 AND username_lower=$2", [nameLower, meLower]);
        await clanSystem(nameLower, `${ws.username} klan sahipliğini ${newOwner} kullanıcısına devretti.`);
        await refreshClanMembers(nameLower);
      } catch (err) {
        console.error("transfer_clan hatasi:", err);
      }
      return;
    }

    if (data.type === "update_clan") {
      const meLower = ws.username.toLocaleLowerCase("tr");
      const nameLower = normClan(data.clan);
      if (!myClanSet(meLower).has(nameLower)) return;
      try {
        if ((await getMyRole(nameLower, meLower)) !== "owner") { clanError(ws, "Klanı sadece kurucu düzenleyebilir."); return; }
        const title = typeof data.title === "string" ? data.title.trim().slice(0, 40) : undefined;
        const description = typeof data.description === "string" ? data.description.trim().slice(0, 200) : undefined;
        const photo_data = typeof data.photo_data === "string" && data.photo_data ? data.photo_data : undefined;
        const join_mode = typeof data.open === "boolean" ? (data.open ? "open" : "invite") : undefined;
        const hidden = typeof data.hidden === "boolean" ? data.hidden : undefined;
        if ((title !== undefined && containsBannedWord(title)) || (description !== undefined && containsBannedWord(description))) {
          clanError(ws, "Başlık/açıklama uygunsuz içerik barındırıyor.");
          return;
        }
        if (title === "") { clanError(ws, "Başlık boş olamaz."); return; }
        if (photo_data && photo_data.length > MAX_CLAN_PHOTO_BYTES) { clanError(ws, "Avatar çok büyük."); return; }
        await pool.query(
          `UPDATE clans SET title=COALESCE($1,title), description=COALESCE($2,description), photo_data=COALESCE($3,photo_data),
           join_mode=COALESCE($4,join_mode), hidden=COALESCE($5,hidden) WHERE name_lower=$6`,
          [title, description, photo_data, join_mode, hidden, nameLower]
        );
        if (data.clear_photo === true) await pool.query("UPDATE clans SET photo_data=NULL WHERE name_lower=$1", [nameLower]);
        sendTo(ws, { type: "clan_notice", text: "Klan güncellendi." });
        await refreshClanMembers(nameLower);
      } catch (err) {
        console.error("update_clan hatasi:", err);
      }
      return;
    }

    if (data.type === "delete_clan") {
      const meLower = ws.username.toLocaleLowerCase("tr");
      const nameLower = normClan(data.clan);
      if (!myClanSet(meLower).has(nameLower)) return;
      try {
        if ((await getMyRole(nameLower, meLower)) !== "owner") { clanError(ws, "Klanı sadece kurucu silebilir."); return; }
        const members = [...(clanMembersCache.get(nameLower) || [])];
        await pool.query("DELETE FROM clans WHERE name_lower=$1", [nameLower]); // uye/sohbet/davet/yasak CASCADE
        await pool.query("UPDATE users SET rep_clan=NULL WHERE rep_clan=$1", [nameLower]);
        for (const m of members) {
          cacheRemoveMember(nameLower, m);
          if (repClanByUser.get(m) === nameLower) repClanByUser.delete(m);
        }
        clanMembersCache.delete(nameLower);
        for (const m of members) {
          const mWs = onlineByUsername.get(m);
          if (mWs) { await sendMyClanInfo(mWs); if (mWs !== ws) clanError(mWs, "Üyesi olduğun bir klan silindi."); }
        }
      } catch (err) {
        console.error("delete_clan hatasi:", err);
      }
      return;
    }

    if (data.type === "set_rep_clan") {
      const meLower = ws.username.toLocaleLowerCase("tr");
      const nameLower = normClan(data.clan);
      try {
        if (nameLower && !myClanSet(meLower).has(nameLower)) return;
        await pool.query("UPDATE users SET rep_clan=$1 WHERE username_lower=$2", [nameLower || null, meLower]);
        if (nameLower) repClanByUser.set(meLower, nameLower); else repClanByUser.delete(meLower);
        await sendMyClanInfo(ws);
      } catch (err) {
        console.error("set_rep_clan hatasi:", err);
      }
      return;
    }

    if (data.type === "invite_to_clan") {
      const meLower = ws.username.toLocaleLowerCase("tr");
      const nameLower = normClan(data.clan);
      const targetName = typeof data.username === "string" ? data.username.trim() : "";
      const targetLower = targetName.toLocaleLowerCase("tr");
      if (!myClanSet(meLower).has(nameLower) || !targetLower) return;
      const nowI = Date.now();
      if (nowI - (lastInviteAt.get(meLower) || 0) < 1500) { clanError(ws, "Çok hızlı davet gönderiyorsun."); return; }
      lastInviteAt.set(meLower, nowI);
      try {
        const role = await getMyRole(nameLower, meLower);
        if (RANK[role] < RANK.senior) { clanError(ws, "Davet göndermek için Kıdemli Üye veya üstü olmalısın."); return; }
        const u = await pool.query("SELECT username FROM users WHERE username_lower=$1", [targetLower]);
        if (!u.rows.length) { clanError(ws, "Böyle bir kullanıcı yok."); return; }
        if (clanMembersCache.get(nameLower)?.has(targetLower)) { clanError(ws, "Bu kullanıcı zaten klanda."); return; }
        const bn = await pool.query("SELECT 1 FROM clan_bans WHERE clan_name_lower=$1 AND username_lower=$2", [nameLower, targetLower]);
        if (bn.rows.length) { clanError(ws, "Bu kullanıcı klandan yasaklı, önce yasağı kaldır."); return; }
        const cnt = await pool.query("SELECT COUNT(*) AS n FROM clan_invites WHERE to_lower=$1", [targetLower]);
        if (Number(cnt.rows[0].n) >= 30) { clanError(ws, "Bu kullanıcının bekleyen davet kutusu dolu."); return; }
        await pool.query(
          "INSERT INTO clan_invites (clan_name_lower, to_lower, from_username) VALUES ($1,$2,$3) ON CONFLICT DO NOTHING",
          [nameLower, targetLower, ws.username]
        );
        sendTo(ws, { type: "clan_notice", text: `${u.rows[0].username} kullanıcısına davet gönderildi.` });
        await refreshClanMembers(nameLower);
        const tWs = onlineByUsername.get(targetLower);
        if (tWs) await sendClanInvites(tWs);
      } catch (err) {
        console.error("invite_to_clan hatasi:", err);
      }
      return;
    }

    if (data.type === "cancel_clan_invite") {
      const meLower = ws.username.toLocaleLowerCase("tr");
      const nameLower = normClan(data.clan);
      const targetLower = normClan(data.username);
      if (!myClanSet(meLower).has(nameLower)) return;
      try {
        const role = await getMyRole(nameLower, meLower);
        if (RANK[role] < RANK.mod) { clanError(ws, "Daveti iptal etme yetkin yok."); return; }
        await pool.query("DELETE FROM clan_invites WHERE clan_name_lower=$1 AND to_lower=$2", [nameLower, targetLower]);
        await refreshClanMembers(nameLower);
        const tWs = onlineByUsername.get(targetLower);
        if (tWs) await sendClanInvites(tWs);
      } catch (err) {
        console.error("cancel invite hatasi:", err);
      }
      return;
    }

    if (data.type === "list_clan_invites") {
      try { await sendClanInvites(ws); } catch (err) { console.error("invites hatasi:", err); }
      return;
    }

    if (data.type === "respond_clan_invite") {
      const meLower = ws.username.toLocaleLowerCase("tr");
      const nameLower = normClan(data.clan);
      try {
        const inv = await pool.query("SELECT 1 FROM clan_invites WHERE clan_name_lower=$1 AND to_lower=$2", [nameLower, meLower]);
        if (!inv.rows.length) { await sendClanInvites(ws); return; }
        if (data.accept) {
          await addMemberToClan(ws, nameLower);
        } else {
          await pool.query("DELETE FROM clan_invites WHERE clan_name_lower=$1 AND to_lower=$2", [nameLower, meLower]);
          await refreshClanMembers(nameLower);
        }
        await sendClanInvites(ws);
      } catch (err) {
        console.error("respond_clan_invite hatasi:", err);
        clanError(ws, "İşlem yapılamadı, tekrar dene.");
      }
      return;
    }

    if (data.type === "clan_chat") {
      if (checkMuted(ws)) return;
      const meLower = ws.username.toLocaleLowerCase("tr");
      const nameLower = normClan(data.clan);
      if (!myClanSet(meLower).has(nameLower)) return;
      const text = typeof data.text === "string" ? data.text.trim().slice(0, 200) : "";
      if (!text) return;
      if (containsBannedWord(text)) {
        ws.send(JSON.stringify({ type: "chat_blocked", reason: "Mesaj uygunsuz içerik nedeniyle gönderilemedi." }));
        return;
      }
      const ccNow = Date.now();
      const lastC = lastClanChatAt.get(ws.clientIp) || 0;
      if (ccNow - lastC < CLAN_CHAT_COOLDOWN_MS) return;
      lastClanChatAt.set(ws.clientIp, ccNow);
      try { await postClanMessage(nameLower, ws.username, text, false); }
      catch (err) { console.error("clan_chat hatasi:", err); }
      return;
    }

    if (data.type === "clan_history") {
      const meLower = ws.username.toLocaleLowerCase("tr");
      const nameLower = normClan(data.clan);
      if (!myClanSet(meLower).has(nameLower)) return;
      const before = Number.isInteger(data.before) ? data.before : null;
      try { await sendClanHistory(ws, nameLower, before, true); }
      catch (err) { console.error("clan_history hatasi:", err); }
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

    if (!ws.username && !isHuman(ws)) {
      ws.send(JSON.stringify({ type: "need_human", reason: "place", x, y, color }));
      return;
    }
    if (ws.username) ws.human = true;

    // --- Sunucu tarafi cooldown ---
    const now = Date.now();
    const last = lastPlacedAt.get(ws.clientIp) || 0;
    if (now - last < COOLDOWN_MS || now - (ws.lastPlace || 0) < COOLDOWN_MS) {
      // Gercek istemci cooldown bitmeden gondermez; tekrarlayan ihlal = bot
      if (now - last < COOLDOWN_MS - 1500) addStrike(ws, "cooldown ihlali");
      return;
    }
    ws.lastPlace = now;
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

    if (ws.username) creditClanPixel(ws.username.toLocaleLowerCase("tr"));
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
