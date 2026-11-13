'use strict';
/*
  Noxis Warriors — servidor PvP (Node.js 18+, SEM dependências: nada de npm install).
  Rodar:   node server.js
  Variáveis opcionais:
    PORT             porta (padrão 8080; Render/Railway/Fly já definem sozinhos)
    MAX_ROOM         máximo de jogadores por sala (padrão 12)
    ALLOWED_ORIGINS  lista separada por vírgula de sufixos de domínio aceitos (ex.: "itch.zone,itch.io").
                     Vazio = aceita qualquer origem.
  O servidor só retransmite o estado entre os jogadores da mesma sala e confere o básico
  (limite de mensagens, limite de dano por segundo, tamanhos). Quem acerta calcula o dano
  e o alvo o aplica em si mesmo, então é um PvP "de amigos": não impede trapaça sofisticada.
*/
const http = require('http'), crypto = require('crypto');
const PORT = +process.env.PORT || 8080, MAX_ROOM = +process.env.MAX_ROOM || 12, MAX_PER_IP = 6;
const GUID = '258EAFA5-E914-47DA-95CA-C5AB0DC85B11';
const ORIGINS = (process.env.ALLOWED_ORIGINS || '').split(',').map(s => s.trim().toLowerCase()).filter(Boolean);
const rooms = new Map(), ipCount = new Map();
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
      tokens: 150, tl: Date.now(), budget: 150, bl: Date.now(), drops: 0, st: null, k: 0, d: 0, dead: 0, lastDeath: 0, closed: false });
  }
  send(o) { if (this.closed || this.sock.destroyed || !this.sock.writable) return; try { this.sock.write(frame(1, Buffer.from(JSON.stringify(o)))) } catch (e) { } }
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
    c.si = num(m.ship, 0, 0, 9) | 0; c.st = { x: 0, y: 0 }; c.room = r;
    const list = [...r.clients.values()].map(o => ({ id: o.id, name: o.name, si: o.si, x: o.st.x, y: o.st.y, k: o.k, d: o.d }));
    r.clients.set(c.id, c);
    c.send({ t: 'welcome', id: c.id, room: rn, players: list });
    bc(r, c, { t: 'join', p: { id: c.id, name: c.name, si: c.si, x: 0, y: 0, k: 0, d: 0 } });
    return;
  }
  const r = c.room; if (!r) return;

  if (m.t === 'st') {
    const o = { t: 'st', id: c.id, x: r1(num(m.x)), y: r1(num(m.y)), vx: r1(num(m.vx, 0, -2000, 2000)), vy: r1(num(m.vy, 0, -2000, 2000)),
      a: Math.round(num(m.a, 0, -20, 20) * 100) / 100, si: num(m.si, 0, 0, 9) | 0, h: num(m.h, 0, 0, 5000) | 0, hm: num(m.hm, 1, 1, 5000) | 0,
      s: num(m.s, 0, 0, 5000) | 0, th: m.th ? 1 : 0, dd: m.dd ? 1 : 0, sf: m.sf ? 1 : 0, hd: m.hd ? 1 : 0,
      lz: num(m.lz, 0, 0, 20) | 0, ob: num(m.ob, 0, 0, 20) | 0,
      ms: Array.isArray(m.ms) ? m.ms.slice(0, 8).map(q => Array.isArray(q) ? q.slice(0, 5).map(v => r1(num(v))) : [0, 0, 0, 0, 0]) : [] };
    c.st = { x: o.x, y: o.y }; c.si = o.si; c.dead = o.dd;
    bc(r, c, o); return;
  }
  if (m.t === 'shot') {
    bc(r, c, { t: 'shot', id: c.id, x: r1(num(m.x)), y: r1(num(m.y)), vx: r1(num(m.vx, 0, -2000, 2000)), vy: r1(num(m.vy, 0, -2000, 2000)),
      a: Math.round(num(m.a, 0, -20, 20) * 100) / 100, n: num(m.n, 1, 1, 6) | 0 }); return;
  }
  if (m.t === 'pulse') { bc(r, c, { t: 'pulse', id: c.id, x: r1(num(m.x)), y: r1(num(m.y)), R: num(m.R, 50, 10, 200) }); return }
  if (m.t === 'hit') {
    c.budget = Math.min(200, c.budget + (now - c.bl) / 1000 * 110); c.bl = now;     // no máx. ~110 de dano por segundo por atacante
    const d = num(m.d); if (!(d > 0 && d <= 100) || c.dead) return;
    const tg = r.clients.get(num(m.to) | 0); if (!tg || tg === c || tg.dead) return;
    if (c.budget < d) return; c.budget -= d;
    tg.send({ t: 'hit', from: c.id, d: r1(d) }); return;
  }
  if (m.t === 'dead') {
    if (now - c.lastDeath < 1500) return; c.lastDeath = now; c.d++; c.dead = 1;
    const by = r.clients.get(num(m.by) | 0), kl = by && by !== c ? by : null; if (kl) kl.k++;
    for (const o of r.clients.values()) o.send({ t: 'kill', k: kl ? kl.id : 0, v: c.id, kn: kl ? kl.name : '', vn: c.name, kk: kl ? kl.k : 0, vd: c.d });
    return;
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

const server = http.createServer((req, res) => {
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

if (require.main === module) server.listen(PORT, () => console.log('Noxis PvP server na porta ' + PORT));
module.exports = server;
