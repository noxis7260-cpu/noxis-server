// world.js - regras do MUNDO do Noxis Warriors, iguais no jogo (navegador) e no servidor (Node).
// Tudo aqui é determinístico: o mesmo (x, y) dá sempre o mesmo resultado, então todo jogador vê o mesmo mapa.
// Só funções puras e o estado do que foi destruído (createWorld). Nada de desenho, som ou rede.
(function (root, factory) {
  if (typeof module === 'object' && module.exports) module.exports = factory();
  else root.NoxisWorld = factory();
})(typeof self !== 'undefined' ? self : this, function () {
  'use strict';

  // ---------- constantes do mapa ----------
  const C = 300;                 // tamanho do bloco de asteroides
  const SAFE_R = 300;            // raio da zona segura da estação
  const STN = 640;               // raio visual da estação
  const WCELL = 2200;            // célula dos buracos de minhoca
  const HGC = 5000;              // célula dos hangares
  const HG_R = 260;              // raio de um hangar
  const ST = { OUT0: 200, OUT1: 232, IN0: 64, IN1: 82, GATE_O: 34, GATE_I: 24, REPAIR_R: 40 };

  // ---------- hash e ruído ----------
  function h(x, y, s) {
    let n = (Math.imul(x, 374761393) + Math.imul(y, 668265263) + Math.imul(s || 0, 2147483647)) | 0;
    n = Math.imul(n ^ (n >>> 13), 1274126177);
    return ((n ^ (n >>> 16)) >>> 0) / 4294967296;
  }
  function dens(cx, cy) {
    const gx = cx / 4, gy = cy / 4, x0 = Math.floor(gx), y0 = Math.floor(gy), fx = gx - x0, fy = gy - y0;
    const sx = fx * fx * (3 - 2 * fx), sy = fy * fy * (3 - 2 * fy);
    const a = h(x0, y0, 90), b = h(x0 + 1, y0, 90), c = h(x0, y0 + 1, 90), d = h(x0 + 1, y0 + 1, 90);
    return (a + (b - a) * sx) * (1 - sy) + (c + (d - c) * sx) * sy;
  }

  // ---------- nebulosas (escondem a nave do radar) ----------
  const nbc = new Map();
  function nebOf(cx, cy) {
    if (h(cx, cy, 70) >= 0.16) return null;
    const x = (cx + 0.25 + 0.5 * h(cx, cy, 71)) * C, y = (cy + 0.25 + 0.5 * h(cx, cy, 72)) * C;
    if (Math.hypot(x, y) < 520) return null;
    return { x, y, r: 75 + h(cx, cy, 73) * 45, s: Math.floor(h(cx, cy, 74) * 1e6) };
  }
  function nebBl(n) {
    let b = nbc.get(n.s);
    if (!b) {
      b = [];
      for (let k = 0; k < 7; k++) {
        const an = h(n.s, k, 1) * 6.283, d = h(n.s, k, 2) * n.r * 0.55;
        b.push([n.x + Math.cos(an) * d, n.y + Math.sin(an) * d, n.r * (0.4 + 0.35 * h(n.s, k, 3))]);
      }
      nbc.set(n.s, b);
    }
    return b;
  }
  function nebV(n, x, y) {
    let v = 0;
    for (const b of nebBl(n)) {
      const d2 = ((x - b[0]) * (x - b[0]) + (y - b[1]) * (y - b[1])) / (b[2] * b[2]);
      if (d2 < 1) v += 1 - d2;
    }
    return v;
  }
  function nebList(x, y, rad) {
    const a = [], c0 = Math.floor((x - rad - 170) / C), c1 = Math.floor((x + rad + 170) / C), d0 = Math.floor((y - rad - 170) / C), d1 = Math.floor((y + rad + 170) / C);
    for (let i = c0; i <= c1; i++) for (let j = d0; j <= d1; j++) { const n = nebOf(i, j); if (n) a.push(n); }
    return a;
  }
  function hidden(x, y) { return nebList(x, y, 0).some(n => nebV(n, x, y) > 0.45); }

  // ---------- buracos de minhoca (pares fixos) ----------
  function wormPairs(x, y, R) {
    const cx = Math.floor(x / WCELL), cy = Math.floor(y / WCELL), out = [];
    for (let gx = cx - R; gx <= cx + R; gx++) for (let gy = cy - R; gy <= cy + R; gy++) {
      if (h(gx, gy, 300) >= 0.6) continue;
      let ox = Math.floor(h(gx, gy, 305) * 3) - 1, oy = Math.floor(h(gx, gy, 306) * 3) - 1;
      if (!ox && !oy) ox = 1;
      const a = { x: Math.round((gx + .15 + .7 * h(gx, gy, 301)) * WCELL), y: Math.round((gy + .15 + .7 * h(gx, gy, 302)) * WCELL) },
        b = { x: Math.round((gx + ox + .15 + .7 * h(gx, gy, 303)) * WCELL), y: Math.round((gy + oy + .15 + .7 * h(gx, gy, 304)) * WCELL) };
      if (Math.hypot(a.x, a.y) > SAFE_R + 60 && Math.hypot(b.x, b.y) > SAFE_R + 60 && Math.hypot(a.x - b.x, a.y - b.y) > 1200) out.push({ a, b });
    }
    return out;
  }

  // ---------- hangares ----------
  function hangarsAround(x, y, n) {
    const cx = Math.floor(x / HGC), cy = Math.floor(y / HGC);
    const out = [{ id: 'h0', x: 1700, y: -1300, R: HG_R }];
    for (let gx = cx - n; gx <= cx + n; gx++) for (let gy = cy - n; gy <= cy + n; gy++) {
      if ((gx === 0 && gy === 0) || h(gx, gy, 200) >= 0.2) continue;
      out.push({ id: 'c' + gx + '_' + gy, x: Math.round((gx + 0.15 + 0.7 * h(gx, gy, 201)) * HGC), y: Math.round((gy + 0.15 + 0.7 * h(gx, gy, 202)) * HGC), R: HG_R });
    }
    return out;
  }

  // ---------- estação: formato sólido e colisão ----------
  function stSolid(x, y) {
    const d = Math.hypot(x, y), ay = Math.abs(y);
    if (d >= ST.OUT0 && d <= ST.OUT1 && ay >= ST.GATE_O) return true;
    if (d >= ST.IN0 && d <= ST.IN1 && ay >= ST.GATE_I) return true;
    for (let k = 0; k < 4; k++) { const a = Math.PI / 4 + k * Math.PI / 2; if (Math.hypot(x - Math.cos(a) * 140, y - Math.sin(a) * 140) <= 10) return true; }
    for (let k = 0; k < 4; k++) {
      const a = Math.PI / 4 + k * Math.PI / 2, ca = Math.cos(a), sa = Math.sin(a), lx = x * ca + y * sa, ly = -x * sa + y * ca;
      if (lx >= ST.OUT1 - 2 && lx <= ST.OUT1 + 36 && Math.abs(ly) <= 22) return true;
    }
    for (const sg of [-1, 1]) {
      const yy = y * sg, ax = Math.abs(x);
      if (ax <= 4 && yy >= ST.OUT1 - 2 && yy <= ST.OUT1 + 22) return true;
      if (ax <= 62 && yy >= ST.OUT1 + 20 && yy <= ST.OUT1 + 26) return true;
      if (ax >= 6 && ax <= 58 && yy >= ST.OUT1 + 22 && yy <= ST.OUT1 + 54) return true;
    }
    return false;
  }
  const STM = 2, STH = 300;
  let stMask = null;
  function stBuildMask() {
    const n = STH * 2 / STM; stMask = new Uint8Array(n * n);
    for (let j = 0; j < n; j++) for (let i = 0; i < n; i++) if (stSolid(-STH + (i + 0.5) * STM, -STH + (j + 0.5) * STM)) stMask[j * n + i] = 1;
  }
  // Empurra a nave p {x,y,vx,vy} para fora da estação (mesma conta do jogo). Devolve a última batida {nx,ny,vr} ou null.
  function stationCollide(p) {
    if (Math.abs(p.x) > STH - 8 || Math.abs(p.y) > STH - 8) return null;
    if (!stMask) stBuildMask();
    const n = STH * 2 / STM, sr = 7;
    let hit = null;
    for (let it = 0; it < 3; it++) {
      let nx = 0, ny = 0, md = 1e9, cnt = 0;
      const i0 = Math.max(0, Math.floor((p.x - sr + STH) / STM)), i1 = Math.min(n - 1, Math.floor((p.x + sr + STH) / STM)),
        j0 = Math.max(0, Math.floor((p.y - sr + STH) / STM)), j1 = Math.min(n - 1, Math.floor((p.y + sr + STH) / STM));
      for (let j = j0; j <= j1; j++) for (let i = i0; i <= i1; i++) {
        if (!stMask[j * n + i]) continue;
        const dx = p.x - (-STH + (i + 0.5) * STM), dy = p.y - (-STH + (j + 0.5) * STM), d = Math.hypot(dx, dy);
        if (d < sr) { const w = (sr - d) / (d || 1); nx += dx * w; ny += dy * w; cnt++; if (d < md) md = d; }
      }
      if (!cnt) break;
      const m = Math.hypot(nx, ny); if (m < 1e-6) break;
      nx /= m; ny /= m;
      const push = Math.min(sr - md + 0.3, 4); p.x += nx * push; p.y += ny * push;
      const vr = p.vx * nx + p.vy * ny;
      if (vr < 0) { p.vx -= 1.35 * vr * nx; p.vy -= 1.35 * vr * ny; }
      hit = { nx, ny, vr };
    }
    return hit;
  }

  // ---------- asteroides: gerados por bloco, com estado do que foi destruído ----------
  function createWorld() {
    const dead = new Set(), cache = new Map(), extra = [];   // extra: fragmentos criados quando um asteroide grande quebra
    let fid = 0;
    function chunk(cx, cy) {
      const key = cx + ',' + cy; let o = cache.get(key);
      if (o) return o;
      if (cache.size > 500) cache.clear();
      o = [];
      const dv = dens(cx, cy), n = Math.hypot((cx + 0.5) * C, (cy + 0.5) * C) < 450 ? 0 : dv < 0.4 ? 0 : dv < 0.6 ? Math.floor(h(cx, cy, 1) * 2.2) : 4 + Math.floor(h(cx, cy, 1) * 5);
      for (let i = 0; i < n; i++) {
        const id = key + ',' + i; if (dead.has(id)) continue;
        const r = 8 + h(cx, cy, 10 + i) * 12, ax = (cx + 0.1 + 0.8 * h(cx, cy, 20 + i)) * C, ay = (cy + 0.1 + 0.8 * h(cx, cy, 30 + i)) * C;
        if (Math.hypot(ax, ay) < SAFE_R + r + 30) continue;
        o.push({ id, x: ax, y: ay, r, hp: Math.ceil(r / 5), seed: Math.floor(h(cx, cy, 40 + i) * 1e6) });
      }
      const rid = key + ',R', rxp = (cx + 0.2 + 0.6 * h(cx, cy, 61)) * C, ryp = (cy + 0.2 + 0.6 * h(cx, cy, 62)) * C;
      if (!dead.has(rid) && Math.hypot(rxp, ryp) > SAFE_R + 130 && h(cx, cy, 60) < 0.2) o.push({ id: rid, red: true, x: rxp, y: ryp, r: 15, hp: 6, seed: Math.floor(h(cx, cy, 63) * 1e6) });
      cache.set(key, o); return o;
    }
    function near(x, y, rad) {
      const a = [], c0 = Math.floor((x - rad) / C), c1 = Math.floor((x + rad) / C), d0 = Math.floor((y - rad) / C), d1 = Math.floor((y + rad) / C);
      for (let i = c0; i <= c1; i++) for (let j = d0; j <= d1; j++) chunk(i, j).forEach(q => { if (!q.dead) a.push(q); });
      extra.forEach(q => { if (!q.dead && Math.abs(q.x - x) <= rad + q.r && Math.abs(q.y - y) <= rad + q.r) a.push(q); });
      return a;
    }
    function markDead(a) { dead.add(a.id); a.dead = true; }
    function addFragment(f) { f.id = 'f' + (fid++); extra.push(f); return f; }
    // ponto de nascimento perto da estação, fora da zona segura, longe de asteroides e de nebulosas
    function spawnPoint(rnd) {
      rnd = rnd || Math.random;
      for (let i = 0; i < 40; i++) {
        const a = rnd() * 6.2832, d = 400 + rnd() * 700, x = Math.round(Math.cos(a) * d), y = Math.round(Math.sin(a) * d);
        if (!hidden(x, y) && near(x, y, 90).every(q => Math.hypot(q.x - x, q.y - y) > q.r + 70)) return { x, y };
      }
      return { x: 0, y: 0 };
    }
    return { dead, cache, extra, chunk, near, markDead, addFragment, spawnPoint };
  }

  return { C, SAFE_R, STN, WCELL, HGC, HG_R, ST, h, dens, nebOf, nebBl, nebV, nebList, hidden, wormPairs, hangarsAround, stSolid, stationCollide, createWorld };
});
