'use strict';
/*
  Noxis Warriors — servidor PvP (Node.js 18+, SEM dependências: nada de npm install).
  Rodar:   node server.js
  Variáveis opcionais:
    PORT             porta (padrão 8080; Render/Railway/Fly já definem sozinhos)
    MAX_ROOM         máximo de jogadores por sala (padrão 100)
    ALLOWED_ORIGINS  lista separada por vírgula de sufixos de domínio aceitos (ex.: "itch.zone,itch.io").
                     Vazio = aceita qualquer origem.
  O servidor é a AUTORIDADE do PvP: ele valida posição e velocidade, guarda a vida e o escudo de cada jogador,
  confere cada acerto (alcance, direção, arma, taxa de dano) e decide sozinho quem morreu e quem ganha o abate.
  O que ele NÃO consegue controlar: o que acontece só no aparelho do jogador (meteoros, inimigos, progressão offline).
*/
const http = require('http'), crypto = require('crypto'), fs = require('fs'), path = require('path');
const PORT = +process.env.PORT || 8080, MAX_ROOM = +process.env.MAX_ROOM || 100, MAX_PER_IP = +process.env.MAX_PER_IP || 8;
const NEAR_R = 2200, FAR_MS = 400;   // quem está perto recebe tudo; quem está longe recebe a posição só a cada FAR_MS (poupa banda/CPU com 100 jogadores)
const TP_CD = 1800, WCELL = 2200;   // buraco de minhoca: intervalo mínimo entre saltos (o jogo usa 2 s) e tamanho da célula do mapa de buracos
const GUID = '258EAFA5-E914-47DA-95CA-C5AB0DC85B11';
const ORIGINS = (process.env.ALLOWED_ORIGINS || '').split(',').map(s => s.trim().toLowerCase()).filter(Boolean);
const rooms = new Map(), ipCount = new Map();

// ---- regras do jogo conhecidas pelo servidor (devem bater com o cliente) ----
const SHIPS = [{ hull: 70, sh: 0, v: 215 }, { hull: 100, sh: 50, v: 135 }, { hull: 150, sh: 0, v: 150 }, { hull: 100, sh: 20, v: 170 }, { hull: 130, sh: 30, v: 178, hg: 1 }];
const SAFE_R = 300, HGC = 5000, HULL_BONUS_MAX = 250, SH_CAP = 400, RESPAWN_MS = 2500, SPAWN_MAX = 1400, REVEAL_MS = 2500;   // SPAWN_MAX: raio máximo aceito para o renascimento; REVEAL_MS: quanto tempo quem ataca de dentro da nebulosa fica visível
const WEAPON = {                      // dano máximo por acerto e por segundo (já com o multiplicador PvP e poder máximo)
  b: { hit: 40, dps: 170 }, m: { hit: 70, dps: 130 }, l: { hit: 40, dps: 170 }, o: { hit: 40, dps: 270 }, p: { hit: 100, dps: 130 }
};
let W; try { W = require('./world.js') } catch (e) { console.error('ERRO: falta o arquivo world.js ao lado do server.js. Envie os DOIS arquivos para o servidor.'); process.exit(1) }   // regras do mundo (hash, nebulosas, buracos de minhoca, hangares): o MESMO arquivo que o jogo usa
const docksNear = (x, y) => W.hangarsAround(x, y, 1).map(q => [q.x - 175, q.y]);   // docas dos hangares
const wormPairs = W.wormPairs;       // buracos de minhoca fixos no mundo
const inNebula = W.hidden;           // quem está dentro de uma nebulosa some do radar e da tela dos outros
const nearDock = (x, y) => docksNear(x, y).some(d => Math.hypot(x - d[0], y - d[1]) < 130);
let nextId = 1;

const num = (v, d = 0, lo = -1e7, hi = 1e7) => { v = +v; return Number.isFinite(v) ? Math.max(lo, Math.min(hi, v)) : d };
const r1 = v => Math.round(v * 10) / 10;

function frame(op, buf) {
  const n = buf.length; let h;
  if (n < 126) { h = Buffer.alloc(2); h[1] = n }
  else if (n < 65536) { h = Buffer.alloc(4); h[1] = 126; h.writeUInt16BE(n, 2) }
  else { h = Buffer.alloc(10); h[1] = 127; h.writeBigUInt64BE(BigInt(n), 2) }
  h[0] = 0x80 | op;
  return Buffer.concat([h, buf]);
}

class Client {
  constructor(sock, ip) {
    Object.assign(this, { sock, ip, buf: Buffer.alloc(0), frag: [], fragLen: 0, alive: true, room: null, id: 0, name: '',
      tokens: 150, tl: Date.now(), drops: 0, st: null, k: 0, d: 0, dead: 0, lastDeath: 0, closed: false,
      x: 0, y: 0, vx: 0, vy: 0, a: 0, si: 0, hp: 100, hm: 100, sp: 0, deadAt: 0, hpInit: false, healB: 0, shB: 0, strikes: 0, posOk: false,
      lastSt: 0, lastShot: 0, lastPulse: 0, mHitT: 0, dockT: 0, still: 0, lz: 0, ob: 0, lzT: 0, obT: 0, ms: [], msT: 0, shots: [], pulse: null,
      lastDmg: null, dmgB: {}, kills: new Map(), corrT: 0, lastDead: 0, tpT: 0, farT: 0, neb: false, revealT: 0, hdn: false, hx: 0, hy: 0 });
  }
  send(o) { if (this.closed || this.sock.destroyed || !this.sock.writable) return; try { this.sock.write(frame(1, Buffer.from(JSON.stringify(o)))) } catch (e) { } }
  sendRaw(buf) { if (this.closed || this.sock.destroyed || !this.sock.writable) return; try { this.sock.write(buf) } catch (e) { } }
  close() { try { this.sock.write(frame(8, Buffer.alloc(0))) } catch (e) { } this.sock.end(); }
}

function bc(room, from, obj) { for (const c of room.clients.values()) if (c !== from) c.send(obj) }

function leave(c) {
  if (c.closed) return; c.closed = true;
  ipCount.set(c.ip, Math.max(0, (ipCount.get(c.ip) || 1) - 1));
  const r = c.room; if (!r) return;
  r.clients.delete(c.id); bc(r, null, { t: 'leave', id: c.id, n: c.name });
  if (!r.clients.size) rooms.delete(r.name);
}

const strike = (c, n = 1) => { c.strikes += n; if (c.strikes > 80) c.sock.destroy() };
const bound = (v, lo, hi) => Math.max(lo, Math.min(hi, v));
const angDiff = (a, b) => Math.abs(Math.atan2(Math.sin(a - b), Math.cos(a - b)));
const inSafe = c => Math.hypot(c.x, c.y) < SAFE_R;
const cloaked = (c, now) => c.si === 4 && c.still && now - c.still >= 15000;
const hiddenP = (c, now) => cloaked(c, now) || (c.neb && now - c.revealT >= REVEAL_MS);   // camuflagem da Aranha ou nebulosa (atacar revela por REVEAL_MS)
const targetable = (c, now) => !c.dead && !inSafe(c) && !hiddenP(c, now);

// ---------- PLACAR (pontos do PvP) ----------
// Os pontos só nascem aqui, de abates que o servidor validou (o cliente não manda pontuação).
// Cada abate vale 100 pontos + 25 por abate extra em sequência sem morrer (máx. +100).
// Anti-farm: abater várias vezes o mesmo nome em 10 min vale 100% / 50% / 25% / 5%.
// Pontos de PvE (meteoros, inimigos, níveis) NÃO podem ser validados aqui: o jogo roda no aparelho do jogador. O cliente manda
// lotes pequenos em POST /score e o servidor limita quanto cada nome pode receber (PVE_CAP pontos a cada 10 min), para a trapaça render pouco.
// Guardado por nome (sem contas): quem usa o mesmo nome soma na mesma linha. Nomes automáticos ("Piloto7") não entram.
// Persistência: arquivo local (BOARD_FILE) e, se configurado, Upstash Redis (UPSTASH_REDIS_REST_URL / UPSTASH_REDIS_REST_TOKEN).
// No Render grátis o disco é apagado quando o serviço reinicia, então use o Upstash para o placar não zerar.
const BOARD_FILE = process.env.BOARD_FILE || path.join(__dirname, 'leaderboard.json');
const KV_URL = (process.env.UPSTASH_REDIS_REST_URL || '').replace(/\/+$/, ''), KV_TOKEN = process.env.UPSTASH_REDIS_REST_TOKEN || '';
const KV_KEY = process.env.BOARD_KEY || 'noxis:leaderboard:v1';
const BOARD_MAX = 500, POINTS_KILL = 100, PVE_CAP = +process.env.PVE_CAP || 1500, PVE_POST_MAX = 600;   // PvE: no máximo PVE_CAP pontos por nome a cada 10 min
const board = new Map();   // nome em minúsculas -> { n, pts, k, d, t }
let boardTimer = null;
const autoName = n => /^Piloto\d+$/.test(n);
const boardRow = name => { const key = name.toLowerCase(); let e = board.get(key); if (!e) { e = { n: name, pts: 0, k: 0, d: 0, pve: 0, t: 0 }; board.set(key, e); if (board.size > BOARD_MAX * 2) boardPrune() } e.n = name; return e };
function boardPrune() { const keep = boardSorted().slice(0, BOARD_MAX); board.clear(); for (const e of keep) board.set(e.n.toLowerCase(), e) }   // nomes inventados em massa não enchem a memória
const safeName = v => String(v || '').replace(/[\u0000-\u001f<>&"']/g, '').trim().slice(0, 14);
const pveWin = new Map();   // nome -> { t, sum } janela de 10 min dos pontos PvE
function pveCredit(name, p, now) {   // devolve quantos pontos de PvE foram aceitos
  p = Math.floor(+p); if (!(p > 0)) return 0; p = Math.min(p, PVE_POST_MAX);
  const key = name.toLowerCase(); let w = pveWin.get(key); if (!w || now - w.t > 600000) { w = { t: now, sum: 0 }; pveWin.set(key, w) }
  const ok = Math.max(0, Math.min(p, PVE_CAP - w.sum)); if (!ok) return 0;
  w.sum += ok; const e = boardRow(name); e.pts += ok; e.pve = (e.pve || 0) + ok; e.t = now; boardTouch(); return ok;
}
const boardSorted = () => [...board.values()].sort((a, b) => b.pts - a.pts || b.k - a.k || a.d - b.d || a.t - b.t);
const boardJson = () => JSON.stringify(boardSorted().slice(0, BOARD_MAX));
function boardTouch() { if (!boardTimer) { boardTimer = setTimeout(() => { boardTimer = null; boardSave() }, 4000); boardTimer.unref() } }
async function kv(cmd) {
  const r = await fetch(KV_URL, { method: 'POST', headers: { Authorization: 'Bearer ' + KV_TOKEN, 'Content-Type': 'application/json' }, body: JSON.stringify(cmd) });
  if (!r.ok) throw new Error('KV ' + r.status);
  return (await r.json()).result;
}
async function boardSave() {
  const js = boardJson();
  try { fs.writeFileSync(BOARD_FILE + '.tmp', js); fs.renameSync(BOARD_FILE + '.tmp', BOARD_FILE) } catch (e) { console.log('placar: não consegui gravar o arquivo (' + e.message + ')') }
  if (KV_URL && KV_TOKEN && typeof fetch === 'function') { try { await kv(['SET', KV_KEY, js]) } catch (e) { console.log('placar: falha ao gravar no Upstash (' + e.message + ')') } }
}
async function boardLoad() {
  let txt = null;
  if (KV_URL && KV_TOKEN && typeof fetch === 'function') { try { txt = await kv(['GET', KV_KEY]) } catch (e) { console.log('placar: falha ao ler do Upstash (' + e.message + ')') } }
  if (!txt) { try { txt = fs.readFileSync(BOARD_FILE, 'utf8') } catch (e) { } }
  if (!txt) return;
  try {
    for (const e of JSON.parse(txt)) {
      const n = String(e.n || '').slice(0, 14); if (!n) continue;
      const row = boardRow(n); row.pts = Math.max(row.pts, e.pts | 0); row.k = Math.max(row.k, e.k | 0); row.d = Math.max(row.d, e.d | 0); row.pve = Math.max(row.pve || 0, e.pve | 0); row.t = e.t || 0;
    }
    console.log('placar carregado: ' + board.size + ' jogador(es)');
  } catch (e) { console.log('placar: arquivo inválido, começando vazio') }
}
function boardTop(n, name) {
  const all = boardSorted(), out = { top: all.slice(0, n).map(e => ({ n: e.n, pts: e.pts, k: e.k, d: e.d })), total: all.length };
  const q = String(name || '').trim().toLowerCase();
  if (q) { const i = all.findIndex(e => e.n.toLowerCase() === q); if (i >= 0) out.me = { rank: i + 1, n: all[i].n, pts: all[i].pts, k: all[i].k, d: all[i].d } }
  return out;
}
function awardKill(kl, v, now) {
  const key = v.name.toLowerCase(), pr = kl.pairs || (kl.pairs = new Map()), rec = pr.get(key);
  const n = rec && now - rec.t < 600000 ? rec.n : 0;
  pr.set(key, { n: n + 1, t: now });
  const mult = [1, 0.5, 0.25][n] ?? 0.05, bonus = Math.min(4, Math.max(0, kl.streak - 1)) * 25;
  const pts = Math.max(1, Math.round((POINTS_KILL + bonus) * mult));
  kl.pts = (kl.pts || 0) + pts;
  if (!autoName(kl.name)) { const e = boardRow(kl.name); e.pts += pts; e.k++; e.t = now; boardTouch() }
  return pts;
}
const limits = new Map();   // limite de consultas do placar por IP (60/min)
const tooMany = (ip, kind = 'lb') => { const now = Date.now(), k = kind + ip; let l = limits.get(k); if (!l || now - l.t > 60000) { l = { t: now, n: 0 }; limits.set(k, l) } return ++l.n > (kind === 'score' ? 30 : 60) };
setInterval(() => { const now = Date.now(); for (const [k, l] of limits) if (now - l.t > 60000) limits.delete(k); for (const [k, w] of pveWin) if (now - w.t > 600000) pveWin.delete(k) }, 120000).unref();

function kill(r, v, now, selfReport) {                   // o servidor decide a morte e o crédito do abate
  if (v.dead) return;
  v.dead = 1; v.deadAt = now; v.d++; v.hp = 0;
  let kl = null;
  if (v.lastDmg && now - v.lastDmg.t < 10000) { const o = r.clients.get(v.lastDmg.id); if (o && o !== v) kl = o }
  let pt = 0;
  if (kl) { const lk = kl.kills.get(v.id) || 0; if (now - lk >= 30000) { kl.kills.set(v.id, now); kl.k++; kl.streak = (kl.streak || 0) + 1; pt = awardKill(kl, v, now) } }   // o mesmo par só pontua a cada 30 s
  v.streak = 0;
  if (kl && !autoName(v.name)) { boardRow(v.name).d++; boardTouch() }
  v.send({ t: 'die', by: kl ? kl.id : 0 });
  for (const o of r.clients.values()) o.send({ t: 'kill', k: kl ? kl.id : 0, v: v.id, kn: kl ? kl.name : '', vn: v.name, kk: kl ? kl.k : 0, vd: v.d, pt, kp: kl ? kl.pts || 0 : 0 });
}

function takeDmg(r, tg, from, d, now) {                   // escudo absorve primeiro, depois o casco
  const ab = Math.min(tg.sp, d); tg.sp -= ab; tg.hp -= d - ab; tg.lastDmg = { id: from.id, t: now };
  tg.send({ t: 'hit', from: from.id, d: r1(d) });
  if (tg.hp <= 0) kill(r, tg, now);
}

function validHit(a, t, m, now) {                         // devolve o dano permitido (0 = acerto recusado)
  const w = String(m.w || ''), W = WEAPON[w], d0 = num(m.d); if (!W || !(d0 > 0)) return 0;
  if (a.si === 4) return 0;                               // a Aranha não tem armas de tiro
  const dist = Math.hypot(t.x - a.x, t.y - a.y), tx = t.x + t.vx * 0.1, ty = t.y + t.vy * 0.1;
  let ok = false;
  if (w === 'b') {
    a.shots = a.shots.filter(s => now - s.t < 1700 && s.n > 0);
    for (const s of a.shots) {                            // a bala (reta, 1,1 s de vida) precisa passar perto do alvo
      const sp2 = s.vx * s.vx + s.vy * s.vy, u = bound(((tx - s.x) * s.vx + (ty - s.y) * s.vy) / sp2, 0, 1.5);
      if (Math.hypot(tx - (s.x + s.vx * u), ty - (s.y + s.vy * u)) < 50) { s.n--; ok = true; break }
    }
  } else if (w === 'm') {
    ok = now - a.msT < 1500 && a.ms.some(q => Math.hypot(q[0] - tx, q[1] - ty) < 120) && now - a.mHitT > 120;
    if (ok) a.mHitT = now;
  } else if (w === 'l') {
    ok = a.lz > 0 && now - a.lzT < 800 && dist < 140 + 16 * a.lz + 50 && (dist < 40 || angDiff(a.a, Math.atan2(ty - a.y, tx - a.x)) < Math.asin(Math.min(1, 60 / dist)) + 0.25);
  } else if (w === 'o') {
    ok = a.ob > 0 && now - a.obT < 800 && dist < 26 + a.ob + 45;
  } else if (w === 'p') {
    const p = a.pulse; ok = !!p && now - p.t < 1000 && !p.ids.has(t.id) && Math.hypot(tx - p.x, ty - p.y) < p.R + 45;
    if (ok) p.ids.add(t.id);
  }
  if (!ok) return 0;
  const b = a.dmgB[w] || (a.dmgB[w] = { v: W.dps, t: now });
  b.v = Math.min(W.dps, b.v + (now - b.t) / 1000 * W.dps); b.t = now;   // limite de dano por segundo de cada arma
  const d = Math.min(d0, W.hit, b.v); if (d <= 0) return 0;
  b.v -= d; return d;
}

function handle(c, txt) {
  const now = Date.now();
  c.tokens = Math.min(150, c.tokens + (now - c.tl) / 1000 * 80); c.tl = now;
  if (c.tokens < 1) { if (++c.drops > 300) c.sock.destroy(); return }
  c.tokens--;
  let m; try { m = JSON.parse(txt) } catch (e) { return }
  if (!m || typeof m !== 'object') return;

  if (m.t === 'join') {
    if (c.room) return;
    const rn = String(m.room || 'global').toLowerCase().replace(/[^a-z0-9_-]/g, '').slice(0, 16) || 'global';
    let r = rooms.get(rn); if (!r) { r = { name: rn, clients: new Map() }; rooms.set(rn, r) }
    if (r.clients.size >= MAX_ROOM) { c.send({ t: 'full' }); c.close(); return }
    c.id = nextId++;
    c.name = String(m.name || '').replace(/[\u0000-\u001f<>&"']/g, '').trim().slice(0, 14) || 'Piloto' + c.id;
    const si = num(m.ship, 0, 0, 9) | 0; c.si = si < SHIPS.length && !SHIPS[si].hg ? si : 0;   // naves de hangar não entram por aqui
    c.hm = SHIPS[c.si].hull; c.hp = c.hm; c.sp = SHIPS[c.si].sh; c.st = { x: 0, y: 0 }; c.room = r;
    const list = [...r.clients.values()].map(o => ({ id: o.id, name: o.name, si: o.si, x: o.hdn ? o.hx : o.x, y: o.hdn ? o.hy : o.y, k: o.k, d: o.d, pts: o.pts || 0 }));
    r.clients.set(c.id, c);
    c.send({ t: 'welcome', id: c.id, room: rn, players: list });
    bc(r, c, { t: 'join', p: { id: c.id, name: c.name, si: c.si, x: 0, y: 0, k: 0, d: 0 } });
    return;
  }
  const r = c.room; if (!r) return;

  if (m.t === 'st') {
    if (now - c.lastSt < 40) return;
    const dt = c.lastSt ? bound((now - c.lastSt) / 1000, 0.04, 1) : 0.07; c.lastSt = now;   // 1ª atualização: sem cota de brinde
    c.strikes = Math.max(0, c.strikes - dt * 0.5);
    let revived = false;
    // nave: naves de hangar só depois de passar pela doca de um hangar
    let si = num(m.si, 0, 0, 9) | 0; if (si >= SHIPS.length) si = c.si;
    if (nearDock(c.x, c.y)) c.dockT = now;
    if (SHIPS[si].hg && !SHIPS[c.si].hg && now - c.dockT > 15000) { si = c.si; strike(c, 5) }
    c.si = si;
    // movimento: velocidade máxima da nave (com motor no nível máximo e folga); excesso é cortado e vira advertência
    let x = r1(num(m.x)), y = r1(num(m.y));
    if (c.dead) {
      if (!m.dd && now - c.deadAt >= RESPAWN_MS) {         // renascimento: volta com a vida cheia perto da estação
        revived = true; c.dead = 0; c.hm = SHIPS[c.si].hull; c.hp = c.hm; c.sp = Math.min(num(m.s, 0, 0, SH_CAP), SHIPS[c.si].sh + 60); c.healB = 0; c.lastDmg = null;
        if (Math.hypot(x, y) > SPAWN_MAX) { x = 0; y = 0 }
      } else { x = c.x; y = c.y }
    } else if (c.posOk) {
      const step = SHIPS[c.si].v * 1.7 * 1.4 * dt + 25, d = Math.hypot(x - c.x, y - c.y);
      if (d > step) { strike(c, 3); x = c.x + (x - c.x) / d * step; y = c.y + (y - c.y) / d * step; c.send({ t: 'fix', x: r1(x), y: r1(y) }) }
    }
    c.x = x; c.y = y; c.posOk = true;
    c.vx = r1(num(m.vx, 0, -700, 700)); c.vy = r1(num(m.vy, 0, -700, 700)); c.a = Math.round(num(m.a, 0, -20, 20) * 100) / 100;
    if (Math.hypot(c.vx, c.vy) < 12 && !m.th) { if (!c.still) c.still = now } else c.still = 0;
    // vida e escudo: o servidor só aceita aumentos dentro do que o jogo permite (reparo na estação, regeneração, bônus de nível)
    const hmCap = SHIPS[c.si].hull + HULL_BONUS_MAX, inZone = inSafe(c);
    c.hm = num(m.hm, 1, 1, hmCap) | 0;
    // cotas de cura: reparo na estação (o servidor sabe onde fica), um pouco fora dela (bônus de nível); escudo só regenera sem apanhar há 4 s
    c.healB = Math.min(40, c.healB + dt * (inZone ? c.hm * 0.07 + 4 : 4));
    c.shB = Math.min(100, c.shB + (!c.lastDmg || now - c.lastDmg.t > 4000 ? dt * 40 : 0));
    if (!c.dead && !revived) {
      if (!c.hpInit) { c.hpInit = true; c.hp = Math.min(num(m.h, c.hm), c.hm); c.sp = Math.min(num(m.s, 0, 0, SH_CAP), SH_CAP) }
      const h = num(m.h, 0, 0, hmCap), s = num(m.s, 0, 0, SH_CAP); let corr = false;
      if (h > c.hp) { const inc = Math.min(h - c.hp, c.healB); c.hp += inc; c.healB -= inc; if (h - c.hp > 1) corr = true } else c.hp = h;
      if (s > c.sp) { const inc = Math.min(s - c.sp, c.shB); c.sp += inc; c.shB -= inc; if (s - c.sp > 1) corr = true } else c.sp = s;
      c.hp = Math.min(c.hp, c.hm);
      if (corr && now - c.corrT > 250) { c.corrT = now; c.send({ t: 'hp', h: Math.round(c.hp), s: Math.round(c.sp) }) }
      if (c.hp <= 0) kill(r, c, now);
    }
    const noGun = c.si === 4;
    c.lz = noGun ? 0 : num(m.lz, 0, 0, 10) | 0; c.ob = noGun ? 0 : num(m.ob, 0, 0, 10) | 0;
    if (c.lz) c.lzT = now; if (c.ob) c.obT = now;
    c.ms = !noGun && Array.isArray(m.ms) ? m.ms.slice(0, 8).map(q => Array.isArray(q) ? q.slice(0, 5).map(v => r1(num(v))) : [0, 0, 0, 0, 0]) : [];
    if (c.ms.length) { c.msT = now; c.revealT = now }          // míssil no ar: quem atacou fica visível
    c.neb = inNebula(c.x, c.y);
    const hd = hiddenP(c, now); c.hdn = hd; if (!hd) { c.hx = c.x; c.hy = c.y }
    // escondido (nebulosa/camuflagem): os outros recebem só a última posição visível e nenhum rastro de movimento ou armas — nem um cliente adulterado vê onde ele está
    const out = frame(1, Buffer.from(JSON.stringify({ t: 'st', id: c.id, x: hd ? c.hx : c.x, y: hd ? c.hy : c.y, vx: hd ? 0 : c.vx, vy: hd ? 0 : c.vy, a: c.a, si: c.si, h: Math.round(c.hp), hm: c.hm, s: Math.round(c.sp), th: !hd && m.th ? 1 : 0,
      dd: c.dead ? 1 : 0, sf: inSafe(c) ? 1 : 0, hd: hd ? 1 : 0, lz: hd ? 0 : c.lz, ob: hd ? 0 : c.ob, ms: c.ms })));   // serializa UMA vez e reaproveita para todos
    const farTick = now - c.farT >= FAR_MS; if (farTick) c.farT = now;
    for (const o of r.clients.values()) if (o !== c && (farTick || Math.hypot(o.x - c.x, o.y - c.y) < NEAR_R)) o.sendRaw(out);
    return;
  }
  if (m.t === 'tp') {                                    // buraco de minhoca: só vale entre as DUAS pontas de um buraco que existe de verdade
    if (!c.posOk || c.dead) return;
    if (now - c.tpT < TP_CD) { strike(c, 3); return }
    const x = r1(num(m.x)), y = r1(num(m.y)); let to = null;
    for (const p of wormPairs(c.x, c.y, 2)) {            // entrada: ponta perto de onde o servidor vê a nave (folga para latência); saída: a outra ponta
      if (Math.hypot(p.a.x - c.x, p.a.y - c.y) < 300) to = p.b; else if (Math.hypot(p.b.x - c.x, p.b.y - c.y) < 300) to = p.a;
      if (to) break;
    }
    if (!to || Math.hypot(x - to.x, y - to.y) > 60) { strike(c, 3); return }
    c.tpT = now; c.x = x; c.y = y; c.lastSt = now; return;
  }
  if (m.t === 'shot') {
    if (!c.posOk || c.dead || c.si === 4 || inSafe(c) || now - c.lastShot < 55) return;
    if (Math.hypot(num(m.x) - c.x, num(m.y) - c.y) > 90) return;          // origem falsa
    c.lastShot = now; c.revealT = now; const n = num(m.n, 1, 1, 4) | 0, a = Math.round(num(m.a, 0, -20, 20) * 100) / 100;
    c.shots.push({ t: now, x: c.x, y: c.y, vx: (c.vx + Math.cos(a) * 280) * 1.1, vy: (c.vy + Math.sin(a) * 280) * 1.1, n }); if (c.shots.length > 30) c.shots.shift();
    bc(r, c, { t: 'shot', id: c.id, x: c.x, y: c.y, vx: c.vx, vy: c.vy, a, n }); return;
  }
  if (m.t === 'pulse') {
    if (!c.posOk || c.dead || inSafe(c) || now - c.lastPulse < 500) return; c.lastPulse = now; c.revealT = now;
    const R = num(m.R, 50, 10, 200); c.pulse = { t: now, x: c.x, y: c.y, R, ids: new Set() };
    bc(r, c, { t: 'pulse', id: c.id, x: c.x, y: c.y, R }); return;
  }
  if (m.t === 'hit') {
    if (c.dead || inSafe(c)) return; c.revealT = now;    // atacar revela quem está na nebulosa
    // quem ataca precisa estar vivo e fora da zona segura
    const tg = r.clients.get(num(m.to) | 0); if (!tg || tg === c || !targetable(tg, now)) return;
    const d = validHit(c, tg, m, now); if (d <= 0) { strike(c, 1); return }
    takeDmg(r, tg, c, d, now); return;
  }
  if (m.t === 'dead') {                                  // morte por conta própria (meteoro, inimigo): vale, mas sem crédito inventado
    if (c.dead || now - c.lastDead < 4000) return; c.lastDead = now; kill(r, c, now, true); return;
  }
}

function onData(c, chunk) {
  c.buf = Buffer.concat([c.buf, chunk]);
  if (c.buf.length > 70000) { c.sock.destroy(); return }
  for (; ;) {
    const b = c.buf; if (b.length < 2) return;
    const fin = !!(b[0] & 0x80), op = b[0] & 15, masked = !!(b[1] & 0x80);
    let len = b[1] & 0x7f, off = 2;
    if (len === 126) { if (b.length < 4) return; len = b.readUInt16BE(2); off = 4 }
    else if (len === 127) { if (b.length < 10) return; const big = b.readBigUInt64BE(2); if (big > 16384n) { c.sock.destroy(); return } len = Number(big); off = 10 }
    if (!masked || len > 16384) { c.sock.destroy(); return }
    if (b.length < off + 4 + len) return;
    const mk = b.subarray(off, off + 4), p = Buffer.from(b.subarray(off + 4, off + 4 + len));
    for (let i = 0; i < len; i++) p[i] ^= mk[i & 3];
    c.buf = b.subarray(off + 4 + len); c.alive = true;
    if (op === 8) { c.close(); return }
    if (op === 9) { try { c.sock.write(frame(10, p)) } catch (e) { } continue }
    if (op === 10) continue;
    if (op === 1 || op === 0) {
      if (op === 1) { c.frag = [p]; c.fragLen = len } else { c.frag.push(p); c.fragLen += len; if (c.fragLen > 16384) { c.sock.destroy(); return } }
      if (fin) { const txt = Buffer.concat(c.frag).toString('utf8'); c.frag = []; handle(c, txt) }
    }
  }
}

const CORS = { 'Access-Control-Allow-Origin': '*', 'Access-Control-Allow-Headers': 'Content-Type', 'Access-Control-Allow-Methods': 'GET, POST, OPTIONS' };
const server = http.createServer((req, res) => {
  const u = new URL(req.url || '/', 'http://x');
  if (u.pathname === '/score') {   // o jogo manda os pontos de PvE (meteoros, inimigos, níveis) em lotes
    if (req.method === 'OPTIONS') { res.writeHead(204, CORS); return res.end() }
    const ip = String(req.headers['x-forwarded-for'] || req.socket.remoteAddress || '').split(',')[0].trim();
    const done = (code, obj) => { res.writeHead(code, { ...CORS, 'Content-Type': 'application/json' }); res.end(JSON.stringify(obj)) };
    if (req.method !== 'POST') return done(405, { error: 'use POST' });
    if (tooMany(ip, 'score')) return done(429, { error: 'too many requests' });
    let body = '', big = false;
    req.on('data', d => { body += d; if (body.length > 512) { big = true; req.destroy() } });
    req.on('end', () => {
      if (big) return;
      let m; try { m = JSON.parse(body) } catch (e) { return done(400, { error: 'bad json' }) }
      const name = safeName(m && m.n);
      if (!name || autoName(name)) return done(200, { ok: true, credited: 0, why: 'name' });
      done(200, { ok: true, credited: pveCredit(name, m.p, Date.now()) });
    });
    return;
  }
  if (u.pathname === '/leaderboard') {   // público: qualquer pessoa (ou o jogo, de qualquer site) pode ler
    const ip = String(req.headers['x-forwarded-for'] || req.socket.remoteAddress || '').split(',')[0].trim();
    if (tooMany(ip)) { res.writeHead(429, { 'Access-Control-Allow-Origin': '*', 'Content-Type': 'application/json' }); return res.end('{"error":"too many requests"}') }
    const n = Math.max(1, Math.min(50, +u.searchParams.get('n') || 20));
    res.writeHead(200, { 'Content-Type': 'application/json; charset=utf-8', 'Access-Control-Allow-Origin': '*', 'Cache-Control': 'public, max-age=5' });
    return res.end(JSON.stringify(boardTop(n, u.searchParams.get('name'))));
  }
  res.writeHead(200, { 'Content-Type': 'text/plain; charset=utf-8' });
  let n = 0; for (const r of rooms.values()) n += r.clients.size;
  res.end('Noxis Warriors PvP server OK — ' + n + ' jogador(es) em ' + rooms.size + ' sala(s)\n');
});

server.on('upgrade', (req, sock, head) => {
  const key = req.headers['sec-websocket-key'];
  const ip = String(req.headers['x-forwarded-for'] || sock.remoteAddress || '').split(',')[0].trim();
  const bad = code => { try { sock.write('HTTP/1.1 ' + code + '\r\nConnection: close\r\n\r\n') } catch (e) { } sock.destroy() };
  if (String(req.headers.upgrade || '').toLowerCase() !== 'websocket' || !key || req.headers['sec-websocket-version'] !== '13') return bad('400 Bad Request');
  if (ORIGINS.length) {
    let host = ''; try { host = new URL(req.headers.origin || '').hostname.toLowerCase() } catch (e) { }
    if (!ORIGINS.some(o => host === o || host.endsWith('.' + o))) return bad('403 Forbidden');
  }
  if ((ipCount.get(ip) || 0) >= MAX_PER_IP) return bad('429 Too Many Requests');
  ipCount.set(ip, (ipCount.get(ip) || 0) + 1);
  const accept = crypto.createHash('sha1').update(key + GUID).digest('base64');
  sock.write('HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: ' + accept + '\r\n\r\n');
  sock.setNoDelay(true);
  const c = new Client(sock, ip);
  sock.on('data', d => onData(c, d));
  sock.on('close', () => leave(c)); sock.on('end', () => leave(c)); sock.on('error', () => { try { sock.destroy() } catch (e) { } leave(c) });
  if (head && head.length) onData(c, head);
  setTimeout(() => { if (!c.room) sock.destroy() }, 15000).unref();   // quem não entra em sala em 15 s é derrubado
});

// batimento: derruba conexões mortas (celular que sumiu, aba fechada sem aviso)
const clients = () => { const a = []; for (const r of rooms.values()) for (const c of r.clients.values()) a.push(c); return a };
setInterval(() => {
  for (const c of clients()) {
    if (!c.alive) { c.sock.destroy(); continue }
    c.alive = false; try { c.sock.write(frame(9, Buffer.alloc(0))) } catch (e) { }
  }
}, 20000).unref();

if (require.main === module) {
  boardLoad();
  server.listen(PORT, () => console.log('Noxis PvP server na porta ' + PORT));
  const bye = async () => { try { await boardSave() } catch (e) { } process.exit(0) };   // o Render avisa (SIGTERM) antes de reiniciar: grava o placar
  process.on('SIGTERM', bye); process.on('SIGINT', bye);
}
module.exports = server; module.exports.__t = { pveCredit, kill, board, boardTop, boardLoad, boardSave, handle, Client, rooms, SHIPS, nearDock, docksNear, wormPairs, inNebula };
