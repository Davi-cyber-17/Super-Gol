(() => {
'use strict';

/* =========================================================
   FUTEBOL PIXEL
   HTML + CSS + JS puros. Online via PeerJS (WebRTC), sem servidor próprio.
   O host da sala roda a simulação; os outros jogadores enviam só os controles.
   ========================================================= */

/* ---------- utilitários ---------- */
const $  = (s, r = document) => r.querySelector(s);
const $$ = (s, r = document) => [...r.querySelectorAll(s)];
const clamp = (v, a, b) => Math.max(a, Math.min(b, v));
const rand  = (a, b) => a + Math.random() * (b - a);
const dist  = (a, b) => Math.hypot(a.x - b.x, a.y - b.y);
const r1 = v => Math.round(v * 10) / 10;
const r2 = v => Math.round(v * 100) / 100;
const angDiff = (a, b) => { let d = a - b; while (d > Math.PI) d -= Math.PI * 2; while (d < -Math.PI) d += Math.PI * 2; return d; };
const pad2 = n => String(n).padStart(2, '0');

/* ---------- constantes do jogo (unidades = pixels do canvas 480x300) ---------- */
const W = 480, H = 300;
const PITCH = { l: 36, r: 444, t: 44, b: 276 };
PITCH.w = PITCH.r - PITCH.l; PITCH.h = PITCH.b - PITCH.t;
PITCH.cx = (PITCH.l + PITCH.r) / 2; PITCH.cy = (PITCH.t + PITCH.b) / 2;
const GOAL = { h: 76, depth: 14 };
GOAL.t = PITCH.cy - GOAL.h / 2; GOAL.b = PITCH.cy + GOAL.h / 2;
const PR = 6, BR = 3.5;               // raio do jogador e da bola
const SPEED = 88, SPRINT = 1.38, BOT_SPEED = 0.88;
const STEP = 1 / 60;
const NET_RATE = 1 / 30;
const FONT = '"Press Start 2P", "Courier New", monospace';

const TEAMS = [
  { code: 'BRA', name: 'Brasil',     shirt: '#f4d318', alt: '#1d56c9', shorts: '#1d56c9', socks: '#f2f2f2' },
  { code: 'ARG', name: 'Argentina',  shirt: '#8fd0f5', alt: '#1a2a6b', shorts: '#f2f2f2', socks: '#8fd0f5' },
  { code: 'POR', name: 'Portugal',   shirt: '#c8102e', alt: '#f2f2f2', shorts: '#0a6b34', socks: '#c8102e' },
  { code: 'ITA', name: 'Itália',     shirt: '#1f5fd1', alt: '#f2f2f2', shorts: '#f2f2f2', socks: '#1f5fd1' },
  { code: 'FRA', name: 'França',     shirt: '#1b2f8a', alt: '#f2f2f2', shorts: '#f2f2f2', socks: '#c8102e' },
  { code: 'ALE', name: 'Alemanha',   shirt: '#f2f2f2', alt: '#0a6b34', shorts: '#1a1a1a', socks: '#f2f2f2' },
  { code: 'ESP', name: 'Espanha',    shirt: '#d6202a', alt: '#f4d318', shorts: '#1d2a6b', socks: '#1d2a6b' },
  { code: 'ING', name: 'Inglaterra', shirt: '#f2f2f2', alt: '#c8102e', shorts: '#1a2a6b', socks: '#f2f2f2' },
];
const GK_SHIRT = ['#ff9f1c', '#b46cff'];
const BOT_NAMES = ['CARLOS', 'LUCAS', 'MATEUS', 'DAVI', 'JOAO', 'PEDRO', 'RAFAEL', 'TIAGO'];
const NUMBERS   = [1, 5, 10, 7, 1, 4, 11, 9];
const SKIN = ['#f1c27d', '#c68642', '#8d5524', '#e0ac69', '#ffdbac', '#a56a3a', '#f1c27d', '#8d5524'];
const HAIR = ['#2b1a0e', '#111111', '#d9a441', '#6b3a12', '#1a1a1a', '#8a5a2b', '#e8c36a', '#222222'];
const SLOT_ORDER = [3, 2, 1, 0];       // humanos ocupam primeiro o atacante, o goleiro por último

const hexRGB = c => { const n = parseInt(c.slice(1), 16); return [n >> 16 & 255, n >> 8 & 255, n & 255]; };
const colorDist = (a, b) => { const x = hexRGB(a), y = hexRGB(b); return Math.hypot(x[0] - y[0], x[1] - y[1], x[2] - y[2]); };
const inkFor = c => { const [r, g, b] = hexRGB(c); return (r * 299 + g * 587 + b * 114) / 1000 > 140 ? '#050a18' : '#ffffff'; };
function getKits(ia, ib) {
  const A = TEAMS[ia], B = TEAMS[ib];
  const bShirt = colorDist(A.shirt, B.shirt) < 100 ? B.alt : B.shirt;
  return [
    { shirt: A.shirt, shorts: A.shorts, socks: A.socks, code: A.code, name: A.name },
    { shirt: bShirt,  shorts: B.shorts, socks: B.socks, code: B.code, name: B.name },
  ];
}

/* ---------- estado global ---------- */
const emptyRoster = () => Array.from({ length: 8 }, () => ({ ctrl: null, name: '', pn: 0 }));
const G = {
  mode: null,            // 'local' | 'host' | 'client'
  app: 'menu',
  roster: emptyRoster(),
  teamA: 2, teamB: 3, duration: 180,
  me: null, code: '',
  S: null,               // simulação (local e host)
  R: null,               // visão (cliente)
  paused: false,
  localPlayers: 1,
};
let peer = null, hostConn = null;
const conns = new Map();

/* =========================================================
   ÁUDIO (bipes simples via WebAudio)
   ========================================================= */
let actx = null, muted = false;
function tone(f, d = 0.08, type = 'square', vol = 0.05, slide = 0, delay = 0) {
  if (muted) return;
  try {
    actx = actx || new (window.AudioContext || window.webkitAudioContext)();
    if (actx.state === 'suspended') actx.resume();
    const t0 = actx.currentTime + delay;
    const o = actx.createOscillator(), g = actx.createGain();
    o.type = type; o.frequency.setValueAtTime(f, t0);
    if (slide) o.frequency.linearRampToValueAtTime(f + slide, t0 + d);
    g.gain.setValueAtTime(vol, t0);
    g.gain.exponentialRampToValueAtTime(0.0001, t0 + d);
    o.connect(g); g.connect(actx.destination);
    o.start(t0); o.stop(t0 + d);
  } catch (e) { /* sem áudio */ }
}
function unlockAudio() {
  try {
    actx = actx || new (window.AudioContext || window.webkitAudioContext)();
    if (actx.state === 'suspended') actx.resume();
  } catch (e) { /* sem áudio */ }
}
const sfx = {
  kick:    () => tone(200, 0.07, 'square', 0.05, -110),
  whistle: () => { tone(1900, 0.18, 'sine', 0.05); tone(1700, 0.3, 'sine', 0.05, 0, 0.2); },
  goal:    () => [392, 523, 659, 784, 1046].forEach((f, i) => tone(f, 0.16, 'square', 0.05, 0, i * 0.12)),
};

/* =========================================================
   SIMULAÇÃO (roda no host e no modo local)
   ========================================================= */
function kickoffPos(slot) {
  const { l, r, cx, cy } = PITCH;
  const team = slot < 4 ? 0 : 1, role = slot % 4;
  const L = [[l + 20, cy], [l + 88, cy - 54], [l + 88, cy + 54], [cx - 30, cy]][role];
  return { x: team === 0 ? L[0] : l + r - L[0], y: L[1] };
}

function newPlayer(slot) {
  const team = slot < 4 ? 0 : 1, pos = kickoffPos(slot);
  return {
    slot, team, role: slot % 4, ctrl: null, human: false, name: BOT_NAMES[slot], num: NUMBERS[slot],
    x: pos.x, y: pos.y, vx: 0, vy: 0, face: team ? Math.PI : 0, walk: 0, moving: false,
    charge: 0, shootHeld: false, stam: 1, kickCd: 0, holdT: 0, idleT: 0,
    input: { dx: 0, dy: 0, s: 0, r: 0 },
  };
}

function applyRoster(players) {
  players.forEach(p => {
    const r = G.roster[p.slot];
    const wasHuman = p.human;
    p.ctrl = r.ctrl; p.human = !!r.ctrl;
    p.name = r.ctrl ? (r.name || 'JOGADOR') : BOT_NAMES[p.slot];
    if (wasHuman && !p.human && p.input) { p.input = { dx: 0, dy: 0, s: 0, r: 0 }; p.charge = 0; p.shootHeld = false; }
  });
}

function newMatch() {
  const S = {
    phase: 'kick', phaseT: 3, time: 0, duration: G.duration, score: [0, 0],
    ev: { seq: 0, team: 0, name: '', num: 0, own: false }, kickSeq: 0,
    ball: { x: PITCH.cx, y: PITCH.cy, vx: 0, vy: 0, last: null, spd: 0 },
    players: Array.from({ length: 8 }, (_, i) => newPlayer(i)),
  };
  applyRoster(S.players);
  return S;
}

function resetPositions(S) {
  S.ball.x = PITCH.cx; S.ball.y = PITCH.cy; S.ball.vx = S.ball.vy = 0; S.ball.last = null;
  S.players.forEach(p => {
    const k = kickoffPos(p.slot);
    p.x = k.x; p.y = k.y; p.vx = p.vy = 0; p.face = p.team ? Math.PI : 0;
    p.charge = 0; p.shootHeld = false; p.kickCd = 0; p.holdT = 0; p.moving = false;
  });
}

function kick(S, p, ang, power) {
  const b = S.ball;
  if (dist(p, b) > PR + BR + 5) return false;
  b.vx = Math.cos(ang) * power + p.vx * 0.25;
  b.vy = Math.sin(ang) * power + p.vy * 0.25;
  b.last = p; p.kickCd = 0.25; S.kickSeq++;
  return true;
}

function humanKick(S, p) {
  let ang = p.face;
  const gx = p.team === 0 ? PITCH.r : PITCH.l;
  const toGoal = Math.atan2(PITCH.cy - p.y, gx - p.x);
  const d = angDiff(toGoal, ang);
  if (Math.abs(d) < 0.6 && Math.abs(gx - p.x) < 190) ang += d * 0.45;   // pequena ajuda de mira
  kick(S, p, ang, 125 + 205 * clamp(p.charge / 0.7, 0, 1));
}

function movePlayer(S, p, dt) {
  const inp = p.input;
  let dx = inp.dx, dy = inp.dy;
  const m = Math.hypot(dx, dy);
  if (m > 1) { dx /= m; dy /= m; }
  const mm = Math.min(1, m);
  const sprint = !!inp.r && p.stam > 0.04 && mm > 0.1;
  let max = SPEED * (p.human ? 1 : BOT_SPEED);
  if (sprint) { max *= SPRINT; p.stam = Math.max(0, p.stam - dt * 0.33); }
  else p.stam = Math.min(1, p.stam + dt * (mm > 0.1 ? 0.1 : 0.28));
  if (p.charge > 0) max *= 0.72;
  const k = Math.min(1, dt * 9);
  p.vx += (dx * max - p.vx) * k; p.vy += (dy * max - p.vy) * k;
  if (mm > 0.1) p.face = Math.atan2(dy, dx);
  p.x = clamp(p.x + p.vx * dt, PITCH.l - 4, PITCH.r + 4);
  p.y = clamp(p.y + p.vy * dt, PITCH.t - 4, PITCH.b + 4);
  const sp = Math.hypot(p.vx, p.vy);
  p.moving = sp > 9; p.walk += sp * dt * 0.11;
  p.kickCd = Math.max(0, p.kickCd - dt);
  if (p.human) {
    if (inp.s) { p.shootHeld = true; p.charge = Math.min(0.7, p.charge + dt); }
    else if (p.shootHeld) { p.shootHeld = false; humanKick(S, p); p.charge = 0; }
  }
}

function homePos(S, p) {
  const ball = S.ball;
  const fx = [0, 0.26, 0.26, 0.52][p.role], fy = [0.5, 0.3, 0.7, 0.5][p.role];
  const baseX = p.team === 0 ? PITCH.l + PITCH.w * fx : PITCH.r - PITCH.w * fx;
  return {
    x: clamp(baseX + (ball.x - PITCH.cx) * 0.5, PITCH.l + 18, PITCH.r - 18),
    y: clamp(PITCH.t + PITCH.h * fy + (ball.y - PITCH.cy) * 0.32, PITCH.t + 12, PITCH.b - 12),
  };
}

function botAI(S, p, dt, isChaser) {
  const b = S.ball, cy = PITCH.cy;
  const dirX = p.team === 0 ? 1 : -1;
  const gx = p.team === 0 ? PITCH.r : PITCH.l;
  const d = dist(p, b);
  const reach = PR + BR + 5;
  let tx, ty, sprint = false;

  if (p.role === 0) {                                   // goleiro
    const ownX = p.team === 0 ? PITCH.l : PITCH.r;
    const inZone = Math.abs(b.x - ownX) < 62 && Math.abs(b.y - cy) < 66;
    if (inZone && d < 50) { tx = b.x; ty = b.y; sprint = true; }
    else { tx = ownX + dirX * 13; ty = clamp(b.y, cy - 24, cy + 24); }
    if (d < reach && p.kickCd <= 0) kick(S, p, Math.atan2(rand(-0.7, 0.7), dirX), rand(200, 260));
  } else if (isChaser) {                                // quem vai na bola
    const ux0 = gx - b.x, uy0 = cy - b.y, m0 = Math.hypot(ux0, uy0) || 1;
    const ux = ux0 / m0, uy = uy0 / m0;
    const bx = b.x - ux * (PR + BR - 2), by = b.y - uy * (PR + BR - 2);   // ponto atrás da bola
    const dBehind = Math.hypot(bx - p.x, by - p.y);
    if (dBehind > 9 && d > PR + BR + 1.5) {
      const lead = Math.min(0.3, d / 220);
      tx = bx + b.vx * lead; ty = by + b.vy * lead; sprint = d > 45;
    } else { tx = gx; ty = cy; }                         // conduz a bola para o gol
    if (d < reach) {
      p.holdT += dt;
      if (p.kickCd <= 0) {
        const near = Math.abs(gx - p.x) < 135;
        const pressed = S.players.some(o => o.team !== p.team && dist(o, p) < 16);
        if ((near && (p.holdT > 0.35 || Math.random() < dt * 6)) || (pressed && Math.random() < dt * 5) || p.holdT > 1.8) {
          const aimY = cy + rand(-GOAL.h / 2 + 9, GOAL.h / 2 - 9);
          kick(S, p, Math.atan2(aimY - p.y, gx - p.x) + rand(-0.08, 0.08), near ? rand(230, 300) : rand(180, 240));
          p.holdT = 0;
        }
      }
    } else if (d > PR + BR + 12) p.holdT = 0;
  } else {                                              // posiciona no campo
    const h = homePos(S, p);
    tx = h.x; ty = h.y; sprint = Math.hypot(tx - p.x, ty - p.y) > 70;
  }

  let dx = tx - p.x, dy = ty - p.y;
  const m = Math.hypot(dx, dy);
  if (m < 2.5) dx = dy = 0;
  else { dx /= m; dy /= m; if (m < 10) { dx *= m / 10; dy *= m / 10; } }
  p.input.dx = dx; p.input.dy = dy; p.input.r = sprint ? 1 : 0; p.input.s = 0;
}

function botsThink(S, dt) {
  const b = S.ball, chaser = [null, null];
  for (const t of [0, 1]) {
    let best = null, bd = 1e9;
    for (const p of S.players) {
      if (p.team !== t || p.role === 0) continue;
      if (p.human && p.idleT > 4) continue;              // humano parado não segura os bots
      const d = dist(p, b);
      if (d < bd) { bd = d; best = p; }
    }
    chaser[t] = best;
  }
  for (const p of S.players) {
    if (p.human) {
      const moving = Math.abs(p.input.dx) + Math.abs(p.input.dy) > 0.1 || p.input.s;
      p.idleT = moving ? 0 : p.idleT + dt;
    } else botAI(S, p, dt, chaser[p.team] === p);
  }
}

function separatePlayers(S) {
  const ps = S.players, min = PR * 2 - 1;
  for (let i = 0; i < ps.length; i++) for (let j = i + 1; j < ps.length; j++) {
    const a = ps[i], c = ps[j];
    const dx = c.x - a.x, dy = c.y - a.y, d = Math.hypot(dx, dy);
    if (d < min && d > 0.01) {
      const push = (min - d) / 2, nx = dx / d, ny = dy / d;
      a.x -= nx * push; a.y -= ny * push; c.x += nx * push; c.y += ny * push;
    }
  }
}

function ballWalls(b) {
  const { l, r, t, b: bot } = PITCH;
  const inMouth = b.y > GOAL.t && b.y < GOAL.b;
  if (b.x < l) {                                          // dentro do gol esquerdo
    if (b.y < GOAL.t + BR) { b.y = GOAL.t + BR; b.vy = Math.abs(b.vy) * 0.5; }
    if (b.y > GOAL.b - BR) { b.y = GOAL.b - BR; b.vy = -Math.abs(b.vy) * 0.5; }
    if (b.x < l - GOAL.depth + BR) { b.x = l - GOAL.depth + BR; b.vx = Math.abs(b.vx) * 0.3; }
  } else if (b.x > r) {                                   // dentro do gol direito
    if (b.y < GOAL.t + BR) { b.y = GOAL.t + BR; b.vy = Math.abs(b.vy) * 0.5; }
    if (b.y > GOAL.b - BR) { b.y = GOAL.b - BR; b.vy = -Math.abs(b.vy) * 0.5; }
    if (b.x > r + GOAL.depth - BR) { b.x = r + GOAL.depth - BR; b.vx = -Math.abs(b.vx) * 0.3; }
  } else {
    if (b.y < t + BR)   { b.y = t + BR;   b.vy =  Math.abs(b.vy) * 0.8; }
    if (b.y > bot - BR) { b.y = bot - BR; b.vy = -Math.abs(b.vy) * 0.8; }
    if (b.x < l + BR && !inMouth) { b.x = l + BR; b.vx =  Math.abs(b.vx) * 0.8; }
    if (b.x > r - BR && !inMouth) { b.x = r - BR; b.vx = -Math.abs(b.vx) * 0.8; }
  }
}

function updateBall(S, dt) {
  const b = S.ball;
  b.x += b.vx * dt; b.y += b.vy * dt;
  const k = Math.exp(-0.85 * dt);
  b.vx *= k; b.vy *= k;
  const min = PR + BR;
  for (const p of S.players) {
    const dx = b.x - p.x, dy = b.y - p.y, d = Math.hypot(dx, dy);
    if (d < min) {
      let nx = 1, ny = 0;
      if (d > 0.001) { nx = dx / d; ny = dy / d; }
      b.x = p.x + nx * min; b.y = p.y + ny * min;
      const rel = (b.vx - p.vx) * nx + (b.vy - p.vy) * ny;
      if (rel < 0) { b.vx -= 1.55 * rel * nx; b.vy -= 1.55 * rel * ny; }
      const pv = p.vx * nx + p.vy * ny;
      if (pv > 0) { b.vx += nx * pv * 0.3; b.vy += ny * pv * 0.3; }
      b.last = p;
    }
  }
  ballWalls(b);
  let sp = Math.hypot(b.vx, b.vy);
  if (sp > 380) { b.vx *= 380 / sp; b.vy *= 380 / sp; sp = 380; }
  if (sp < 2) { b.vx = b.vy = 0; sp = 0; }
  b.spd = sp;
}

function checkGoal(S) {
  const b = S.ball;
  if (b.y > GOAL.t && b.y < GOAL.b) {
    if (b.x < PITCH.l - BR) return 1;      // bola no gol da esquerda: ponto do time 1
    if (b.x > PITCH.r + BR) return 0;      // bola no gol da direita: ponto do time 0
  }
  return -1;
}

function scoreGoal(S, team) {
  S.score[team]++;
  const last = S.ball.last;
  S.ev = { seq: S.ev.seq + 1, team, name: last ? last.name : '', num: last ? last.num : 0, own: !!(last && last.team !== team) };
  S.phase = 'goal'; S.phaseT = 2.8;
}

function freezePlayers(S, dt) {
  S.players.forEach(p => {
    p.charge = 0; p.shootHeld = false;
    p.input = { dx: 0, dy: 0, s: 0, r: 0 };
    movePlayer(S, p, dt);
  });
}

function stepSim(S, dt) {
  switch (S.phase) {
    case 'kick':
      S.phaseT -= dt; freezePlayers(S, dt);
      if (S.phaseT <= 0) S.phase = 'play';
      return;
    case 'goal':
      S.phaseT -= dt; freezePlayers(S, dt); updateBall(S, dt);
      if (S.phaseT <= 0) { resetPositions(S); S.phase = 'kick'; S.phaseT = 1.6; }
      return;
    case 'end':
      return;
  }
  S.time += dt;
  if (S.time >= S.duration) { S.time = S.duration; S.phase = 'end'; return; }
  botsThink(S, dt);
  S.players.forEach(p => movePlayer(S, p, dt));
  separatePlayers(S);
  updateBall(S, dt);
  const g = checkGoal(S);
  if (g >= 0) scoreGoal(S, g);
}

/* =========================================================
   CONTROLES (teclado + toque)
   ========================================================= */
const keys = new Set();
const touch = { dx: 0, dy: 0, s: 0, r: 0 };

function readInput(scheme, useTouch) {
  let dx = 0, dy = 0, s = 0, r = 0;
  const k = c => keys.has(c);
  if (scheme !== 'arrows') {
    dx += (k('KeyD') ? 1 : 0) - (k('KeyA') ? 1 : 0);
    dy += (k('KeyS') ? 1 : 0) - (k('KeyW') ? 1 : 0);
    if (k('Space')) s = 1;
    if (k('ShiftLeft')) r = 1;
  }
  if (scheme !== 'wasd') {
    dx += (k('ArrowRight') ? 1 : 0) - (k('ArrowLeft') ? 1 : 0);
    dy += (k('ArrowDown') ? 1 : 0) - (k('ArrowUp') ? 1 : 0);
    if (k('Enter') || k('NumpadEnter')) s = 1;
    if (k('ShiftRight')) r = 1;
  }
  if (useTouch) { dx += touch.dx; dy += touch.dy; s |= touch.s; r |= touch.r; }
  return { dx: clamp(dx, -1, 1), dy: clamp(dy, -1, 1), s: s ? 1 : 0, r: r ? 1 : 0 };
}

function applyLocalInputs(S) {
  for (const p of S.players) {
    if (p.ctrl === 'L1') p.input = readInput(G.localPlayers === 1 ? 'both' : 'wasd', true);
    else if (p.ctrl === 'L2') p.input = readInput('arrows', false);
    else if (p.ctrl === 'host') p.input = readInput('both', true);
  }
}

function setupKeyboard() {
  const GAME_KEYS = new Set(['Space', 'ArrowUp', 'ArrowDown', 'ArrowLeft', 'ArrowRight', 'Enter', 'ShiftLeft', 'ShiftRight']);
  addEventListener('keydown', e => {
    if (/^(INPUT|SELECT|TEXTAREA)$/.test(e.target.tagName)) return;
    if (G.app === 'game') {
      if (GAME_KEYS.has(e.code) || e.code.startsWith('Key')) e.preventDefault();
      if ((e.code === 'KeyP' || e.code === 'Escape') && G.mode === 'local' && !e.repeat) G.paused = !G.paused;
    }
    keys.add(e.code);
  });
  addEventListener('keyup', e => keys.delete(e.code));
  addEventListener('blur', () => keys.clear());
}

function setupTouch() {
  // celular/tablet: ponteiro principal é o dedo. Em notebook com tela de toque, os controles
  // aparecem só depois do primeiro toque na tela.
  const enable = () => document.body.classList.add('touch');
  if (matchMedia('(pointer: coarse)').matches) enable();
  addEventListener('touchstart', enable, { once: true, passive: true });
  const stick = $('#stick'), knob = $('#knob');
  let sid = null;
  const move = e => {
    const rc = stick.getBoundingClientRect();
    let dx = (e.clientX - (rc.left + rc.width / 2)) / (rc.width / 2);
    let dy = (e.clientY - (rc.top + rc.height / 2)) / (rc.height / 2);
    const m = Math.hypot(dx, dy);
    if (m > 1) { dx /= m; dy /= m; }
    touch.dx = Math.abs(dx) < 0.12 ? 0 : dx;
    touch.dy = Math.abs(dy) < 0.12 ? 0 : dy;
    knob.style.transform = `translate(${dx * rc.width * 0.3}px,${dy * rc.height * 0.3}px)`;
  };
  stick.addEventListener('pointerdown', e => { sid = e.pointerId; stick.setPointerCapture(e.pointerId); move(e); e.preventDefault(); });
  stick.addEventListener('pointermove', e => { if (e.pointerId === sid) move(e); });
  const end = e => { if (e.pointerId !== sid) return; sid = null; touch.dx = touch.dy = 0; knob.style.transform = ''; };
  stick.addEventListener('pointerup', end);
  stick.addEventListener('pointercancel', end);

  const hold = (el, key) => {
    const off = () => { touch[key] = 0; el.classList.remove('down'); };
    el.addEventListener('pointerdown', e => { touch[key] = 1; el.classList.add('down'); el.setPointerCapture(e.pointerId); e.preventDefault(); });
    el.addEventListener('pointerup', off);
    el.addEventListener('pointercancel', off);
  };
  hold($('#t-shoot'), 's');
  hold($('#t-run'), 'r');
  document.addEventListener('contextmenu', e => { if (G.app === 'game') e.preventDefault(); });
}

/* =========================================================
   DESENHO (canvas 480x300, ampliado com pixels nítidos)
   ========================================================= */
const cv = $('#cv');
const ctx = cv.getContext('2d');
ctx.imageSmoothingEnabled = false;

function mulberry32(a) {
  return function () {
    a |= 0; a = a + 0x6D2B79F5 | 0;
    let t = Math.imul(a ^ a >>> 15, 1 | a);
    t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t;
    return ((t ^ t >>> 14) >>> 0) / 4294967296;
  };
}

function plotCircle(g, cx, cy, r, color, filter) {
  g.fillStyle = color;
  const seen = new Set(), n = Math.ceil(r * 8);
  for (let i = 0; i < n; i++) {
    const a = i / n * Math.PI * 2;
    const x = Math.round(cx + Math.cos(a) * r), y = Math.round(cy + Math.sin(a) * r);
    const key = x + ',' + y;
    if (seen.has(key)) continue;
    seen.add(key);
    if (filter && !filter(x, y)) continue;
    g.fillRect(x, y, 1, 1);
  }
}

function buildPitch() {
  const c = document.createElement('canvas');
  c.width = W; c.height = H;
  const g = c.getContext('2d');
  g.imageSmoothingEnabled = false;
  const { l, r, t, b, cx, cy } = PITCH;
  const rnd = mulberry32(11);
  const LINE = '#8ff4ff';

  // arquibancada tecnológica: painéis escuros com torcida em LED
  g.fillStyle = '#060b1c'; g.fillRect(0, 0, W, H);
  const glow = ['#22e6ff', '#2f6bff', '#8b5cf6', '#ff3dcb', '#e8fbff', '#3dff9a'];
  const crowd = (x0, y0, x1, y1) => {
    for (let y = y0, row = 0; y < y1; y += 4, row++) {
      g.fillStyle = row % 2 ? '#0a1330' : '#0d1a3d'; g.fillRect(x0, y, x1 - x0, 4);
      for (let x = x0 + (row % 2) * 2; x < x1 - 1; x += 4) {
        if (rnd() < 0.12) continue;
        g.fillStyle = '#1b2a55'; g.fillRect(x, y, 2, 2);
        g.globalAlpha = 0.55 + rnd() * 0.4;
        g.fillStyle = glow[Math.floor(rnd() * glow.length)]; g.fillRect(x, y + 2, 2, 2);
        g.globalAlpha = 1;
      }
    }
  };
  crowd(0, 14, W, 40);
  crowd(0, 40, 18, 276);
  crowd(462, 40, W, 276);
  g.fillStyle = '#12335f'; g.fillRect(0, 40, W, 4);
  g.fillStyle = '#22e6ff'; g.fillRect(0, 40, W, 1);

  // gramado: faixas escuras com grade de luz
  const T = 24;
  for (let y = t, ty = 0; y < 276; y += T, ty++) for (let x = 18, tx = 0; x < 462; x += T, tx++) {
    g.fillStyle = (tx + ty) & 1 ? '#12694a' : '#0f5a3f';
    g.fillRect(x, y, Math.min(T, 462 - x), Math.min(T, 276 - y));
  }
  g.fillStyle = 'rgba(34,230,255,.07)';
  for (let x = 18; x < 462; x += T) g.fillRect(x, t, 1, 276 - t);
  for (let y = t; y < 276; y += T) g.fillRect(18, y, 444, 1);

  // placas de LED embaixo
  const ads = ['#22e6ff', '#2f6bff', '#8b5cf6', '#ff3dcb', '#3dff9a', '#ffd83d'];
  for (let x = 0, i = 0; x < W; x += 40, i++) {
    g.fillStyle = '#0a1230'; g.fillRect(x, 276, 40, 10);
    g.fillStyle = ads[i % ads.length];
    g.fillRect(x, 276, 40, 1);
    g.fillRect(x + 4, 279, 32, 2);
    g.globalAlpha = 0.55; g.fillRect(x + 4, 283, 18, 2); g.globalAlpha = 1;
  }

  // gols
  const net = (x0, x1) => {
    g.fillStyle = '#04121f'; g.fillRect(x0, GOAL.t, x1 - x0, GOAL.h);
    g.fillStyle = 'rgba(143,244,255,.4)';
    for (let x = x0; x < x1; x += 3) g.fillRect(x, GOAL.t, 1, GOAL.h);
    for (let y = GOAL.t; y < GOAL.b; y += 3) g.fillRect(x0, y, x1 - x0, 1);
  };
  net(l - GOAL.depth, l); net(r, r + GOAL.depth);

  // linhas
  g.fillStyle = LINE;
  const hl = (x1, x2, y) => g.fillRect(Math.round(x1), Math.round(y), Math.round(x2 - x1) + 1, 1);
  const vl = (x, y1, y2) => g.fillRect(Math.round(x), Math.round(y1), 1, Math.round(y2 - y1) + 1);
  hl(l, r, t); hl(l, r, b); vl(l, t, b); vl(r, t, b); vl(cx, t, b);
  const boxH = 58, areaH = 30, boxW = 50, areaW = 18;
  [[l, 1], [r, -1]].forEach(([x, s]) => {
    hl(Math.min(x, x + s * boxW), Math.max(x, x + s * boxW), cy - boxH); hl(Math.min(x, x + s * boxW), Math.max(x, x + s * boxW), cy + boxH);
    vl(x + s * boxW, cy - boxH, cy + boxH);
    hl(Math.min(x, x + s * areaW), Math.max(x, x + s * areaW), cy - areaH); hl(Math.min(x, x + s * areaW), Math.max(x, x + s * areaW), cy + areaH);
    vl(x + s * areaW, cy - areaH, cy + areaH);
    g.fillRect(x + s * 36 - 1, cy - 1, 2, 2);
    plotCircle(g, x + s * 36, cy, 26, LINE, (px) => s > 0 ? px > x + boxW : px < x - boxW);
  });
  plotCircle(g, cx, cy, 28, LINE);
  g.fillRect(cx - 1, cy - 1, 3, 3);

  // traves e fundo do gol
  g.fillStyle = '#ffffff';
  g.fillRect(l - GOAL.depth, GOAL.t - 1, GOAL.depth + 1, 2); g.fillRect(l - GOAL.depth, GOAL.b - 1, GOAL.depth + 1, 2);
  g.fillRect(l - GOAL.depth - 1, GOAL.t - 1, 2, GOAL.h + 2);
  g.fillRect(r, GOAL.t - 1, GOAL.depth + 1, 2); g.fillRect(r, GOAL.b - 1, GOAL.depth + 1, 2);
  g.fillRect(r + GOAL.depth - 1, GOAL.t - 1, 2, GOAL.h + 2);

  // bandeirinhas de escanteio
  [[l, t], [r, t], [l, b], [r, b]].forEach(([x, y]) => {
    g.fillStyle = '#e8fbff'; g.fillRect(x, y - 6, 1, 6);
    g.fillStyle = '#ff3dcb'; g.fillRect(x + 1, y - 6, 3, 2);
  });
  return c;
}
const PITCH_CANVAS = buildPitch();

/* camada final: linhas de varredura e vinheta (efeito de tela) */
function buildFx() {
  const c = document.createElement('canvas');
  c.width = W; c.height = H;
  const g = c.getContext('2d');
  const v = g.createRadialGradient(W / 2, H / 2, H * 0.45, W / 2, H / 2, W * 0.62);
  v.addColorStop(0, 'rgba(0,0,12,0)'); v.addColorStop(1, 'rgba(0,0,12,.42)');
  g.fillStyle = v; g.fillRect(0, 0, W, H);
  g.fillStyle = 'rgba(0,0,0,.09)';
  for (let y = 1; y < H; y += 2) g.fillRect(0, y, W, 1);
  return c;
}
const FX_CANVAS = buildFx();

function T(s, x, y, color, size = 8, align = 'left', outline = null) {
  ctx.font = `${size}px ${FONT}`;
  ctx.textAlign = align; ctx.textBaseline = 'middle';
  x = Math.round(x); y = Math.round(y);
  if (outline) {
    ctx.fillStyle = outline;
    for (const [ox, oy] of [[1, 0], [-1, 0], [0, 1], [0, -1], [1, 1], [-1, -1], [1, -1], [-1, 1]]) ctx.fillText(s, x + ox, y + oy);
  }
  ctx.fillStyle = color;
  ctx.fillText(s, x, y);
}

function drawLeg(x, y, len, skin, socks) {
  ctx.fillStyle = skin; ctx.fillRect(x, y + 1, 2, 1);
  if (len > 2) { ctx.fillStyle = socks; ctx.fillRect(x, y + 2, 2, len - 2); }
  ctx.fillStyle = '#111'; ctx.fillRect(x, y + len, 2, 1);
}

function drawPlayer(p, kit, markColor) {
  const x = Math.round(p.x), y = Math.round(p.y);
  const shirt = p.role === 0 ? GK_SHIRT[p.team] : kit.shirt;
  const skin = SKIN[p.slot], hair = HAIR[p.slot];
  const fc = Math.cos(p.face), fs = Math.sin(p.face);
  const step = p.moving ? (Math.floor(p.walk) & 1) : 0;

  ctx.fillStyle = 'rgba(0,0,0,.42)'; ctx.fillRect(x - 4, y + 2, 9, 3);
  if (markColor) { ctx.fillStyle = markColor; ctx.fillRect(x - 4, y + 5, 9, 1); }

  const ll = p.moving ? (step ? 2 : 4) : 3, rl = p.moving ? (step ? 4 : 2) : 3;
  drawLeg(x - 2, y, ll, skin, kit.socks);
  drawLeg(x + 1, y, rl, skin, kit.socks);

  ctx.fillStyle = kit.shorts; ctx.fillRect(x - 3, y - 1, 7, 2);
  ctx.fillStyle = shirt;      ctx.fillRect(x - 3, y - 6, 7, 5);
  const aL = p.moving && step ? 1 : 0, aR = p.moving && !step ? 1 : 0;
  ctx.fillStyle = shirt; ctx.fillRect(x - 4, y - 6, 1, 2); ctx.fillRect(x + 4, y - 6, 1, 2);
  ctx.fillStyle = skin;  ctx.fillRect(x - 4, y - 4 + aL, 1, 2); ctx.fillRect(x + 4, y - 4 + aR, 1, 2);

  ctx.fillStyle = skin; ctx.fillRect(x - 2, y - 11, 5, 5);
  ctx.fillStyle = hair;
  if (fs < -0.45) ctx.fillRect(x - 2, y - 11, 5, 4);
  else {
    ctx.fillRect(x - 2, y - 11, 5, 2);
    if (Math.abs(fc) > 0.5) ctx.fillRect(fc > 0 ? x - 2 : x + 2, y - 9, 1, 2);
    ctx.fillStyle = '#111';
    if (Math.abs(fc) > 0.6) ctx.fillRect(x + (fc > 0 ? 1 : -1), y - 8, 1, 1);
    else { ctx.fillRect(x - 1, y - 8, 1, 1); ctx.fillRect(x + 1, y - 8, 1, 1); }
  }
}

const BALL_PAT = [
  '..KKK..',
  '.KWWWK.',
  'KWWKWWK',
  'KWKKKWK',
  'KWWKWWK',
  '.KWWWK.',
  '..KKK..',
];
function drawBall(ball) {
  const x = Math.round(ball.x), y = Math.round(ball.y);
  ctx.fillStyle = 'rgba(0,0,0,.45)'; ctx.fillRect(x - 3, y + 3, 7, 2);
  for (let j = 0; j < 7; j++) for (let i = 0; i < 7; i++) {
    const c = BALL_PAT[j][i];
    if (c === '.') continue;
    ctx.fillStyle = c === 'K' ? '#161616' : '#fafafa';
    ctx.fillRect(x - 3 + i, y - 4 + j, 1, 1);
  }
}

const trail = [];
function drawTrail(ball, spd) {
  if (spd > 130) { trail.push({ x: ball.x, y: ball.y }); if (trail.length > 7) trail.shift(); }
  else if (trail.length) trail.shift();
  trail.forEach((pt, i) => {
    ctx.globalAlpha = (i + 1) / trail.length * 0.7;
    ctx.fillStyle = '#3df2ff';
    ctx.fillRect(Math.round(pt.x) - 1, Math.round(pt.y) - 1, 2, 2);
  });
  ctx.globalAlpha = 1;
}

function youSlots() {
  const s = new Set();
  G.roster.forEach((r, i) => {
    if (!r.ctrl) return;
    if (G.mode === 'local' ? (r.ctrl === 'L1' || r.ctrl === 'L2') : r.ctrl === G.me) s.add(i);
  });
  return s;
}

function drawLabel(p, you) {
  const pn = G.mode === 'local' ? (G.roster[p.slot].ctrl === 'L2' ? 2 : 1) : G.roster[p.slot].pn;
  if (!pn) return;
  T('P' + pn, p.x, p.y - 16, you ? '#ffe14a' : '#ffffff', 7, 'center', '#000000');
}

function drawAim(p) {
  const n = 1 + Math.floor(p.charge / 0.7 * 4);
  ctx.fillStyle = '#ff9a1f';
  for (let i = 1; i <= n; i++) {
    const d = 11 + i * 6;
    ctx.fillRect(Math.round(p.x + Math.cos(p.face) * d) - 1, Math.round(p.y - 3 + Math.sin(p.face) * d) - 1, 2, 2);
  }
}

function featured(R, team) {
  let best = null, bd = 1e9;
  for (const p of R.players) {
    if (p.team !== team) continue;
    const d = Math.hypot(p.x - R.ball.x, p.y - R.ball.y) + (p.role === 0 ? 40 : 0);
    if (d < bd) { bd = d; best = p; }
  }
  return best;
}

function box(x, y, w, h, color) { ctx.fillStyle = color; ctx.fillRect(x, y, w, h); }

function pingColor(ms) { return ms <= 80 ? '#3dff9a' : ms <= 160 ? '#ffd83d' : '#ff4d6d'; }

function drawHUD(R, kits) {
  box(0, 0, W, 14, '#060b1c'); box(0, 13, W, 1, '#22e6ff');
  ctx.font = `8px ${FONT}`;
  let x = 4;
  const wA = Math.ceil(ctx.measureText(kits[0].code).width) + 8;
  box(x, 2, wA, 10, kits[0].shirt); T(kits[0].code, x + wA / 2, 7.5, inkFor(kits[0].shirt), 8, 'center'); x += wA + 2;
  const sc = `${R.score[0]}-${R.score[1]}`;
  const wS = Math.ceil(ctx.measureText(sc).width) + 10;
  box(x, 2, wS, 10, '#e8fbff'); T(sc, x + wS / 2, 7.5, '#050a18', 8, 'center'); x += wS + 2;
  const wB = Math.ceil(ctx.measureText(kits[1].code).width) + 8;
  box(x, 2, wB, 10, kits[1].shirt); T(kits[1].code, x + wB / 2, 7.5, inkFor(kits[1].shirt), 8, 'center'); x += wB + 8;
  const gm = R.time / R.duration * 90, mm = Math.floor(gm), ss = Math.floor((gm - mm) * 60);
  T(`${pad2(mm)}:${pad2(ss)}`, x, 7.5, '#e8fbff', 8);
  if (G.mode !== 'local' && G.code) {
    // à direita, antes da área dos botões HTML: SALA XXXXX  42MS
    const ms = G.mode === 'client' ? (G.ping == null ? '--' : G.ping + 'MS') : 'HOST';
    const col = G.mode === 'client' ? (G.ping == null ? '#8aa4c8' : pingColor(G.ping)) : '#3dff9a';
    const rx = W - 96;
    T(ms, rx, 7.5, col, 8, 'right');
    const wm = Math.ceil(ctx.measureText(ms).width) + 8;
    T('SALA ' + G.code, rx - wm, 7.5, '#7fb2d9', 8, 'right');
  }

  box(0, 286, W, 14, '#060b1c'); box(0, 286, W, 1, '#22e6ff');
  const fa = featured(R, 0), fb = featured(R, 1);
  if (fa) {
    const s = `${fa.num} ${fa.name}`, w = Math.ceil(ctx.measureText(s).width) + 8;
    box(4, 288, w, 10, kits[0].shirt); T(s, 8, 293.5, inkFor(kits[0].shirt), 8);
  }
  if (fb) {
    const s = `${fb.num} ${fb.name}`, w = Math.ceil(ctx.measureText(s).width) + 8;
    box(W - 4 - w, 288, w, 10, kits[1].shirt); T(s, W - 8, 293.5, inkFor(kits[1].shirt), 8, 'right');
  }
}

function drawCenter(R) {
  const { cx, cy } = PITCH;
  if (R.phase === 'kick' && R.phaseT > 0) T(String(Math.ceil(R.phaseT)), cx, cy - 40, '#ffffff', 20, 'center', '#050a18');
  if (R.phase === 'goal') {
    const blink = Math.floor(performance.now() / 180) % 2;
    T('GOOOL!', cx, cy - 6, blink ? '#22e6ff' : '#ffffff', 22, 'center', '#050a18');
    const label = R.ev.own ? `GOL CONTRA ${R.ev.num} ${R.ev.name}` : `${R.ev.num} ${R.ev.name}`;
    T(label, cx, cy + 16, '#ffffff', 8, 'center', '#050a18');
  }
}

function draw(R) {
  ctx.drawImage(PITCH_CANVAS, 0, 0);
  const kits = getKits(G.teamA, G.teamB);
  const you = youSlots();
  const spd = R.ball.spd != null ? R.ball.spd : Math.hypot(R.ball.vx || 0, R.ball.vy || 0);
  drawTrail(R.ball, spd);

  const ents = R.players.map(p => ({ y: p.y, p }));
  ents.push({ y: R.ball.y, ball: true });
  ents.sort((a, b) => a.y - b.y);
  for (const e of ents) {
    if (e.ball) { drawBall(R.ball); continue; }
    const p = e.p;
    drawPlayer(p, kits[p.team], p.human ? (you.has(p.slot) ? '#ffe14a' : '#ffffff') : null);
    if (p.human && p.charge > 0.02) drawAim(p);
    if (you.has(p.slot) && p.stam < 0.98) {
      const x = Math.round(p.x) - 5, y = Math.round(p.y) + 7;
      box(x, y, 11, 2, '#140b2e'); box(x, y, Math.round(11 * p.stam), 2, p.stam < 0.25 ? '#ff4d5e' : '#ffd83d');
    }
  }
  for (const p of R.players) if (p.human) drawLabel(p, you.has(p.slot));

  drawHUD(R, kits);
  drawCenter(R);
  ctx.drawImage(FX_CANVAS, 0, 0);

  if (G.mode === 'client' && !R.got) {
    ctx.fillStyle = 'rgba(2,4,12,.7)'; ctx.fillRect(0, 14, W, 272);
    T('CONECTANDO...', W / 2, H / 2, '#22e6ff', 10, 'center');
  } else if (G.mode === 'client' && performance.now() - lastStateAt > 2500) {
    ctx.fillStyle = 'rgba(2,4,12,.55)'; ctx.fillRect(0, 14, W, 272);
    T('SEM SINAL DO HOST...', W / 2, H / 2, '#ffd83d', 10, 'center');
  }
  if (G.paused) {
    ctx.fillStyle = 'rgba(2,4,12,.62)'; ctx.fillRect(0, 14, W, 272);
    T('PAUSA', W / 2, H / 2 - 6, '#22e6ff', 20, 'center', '#050a18');
    T('Tecla P para voltar', W / 2, H / 2 + 16, '#ffffff', 8, 'center');
  }
}

function fit() {
  const rc = $('#app').getBoundingClientRect();
  const vw = rc.width || innerWidth, vh = rc.height || innerHeight;
  const sc = Math.min(vw / W, vh / H);
  cv.style.width = Math.floor(W * sc) + 'px';
  cv.style.height = Math.floor(H * sc) + 'px';
  $('#stage').style.setProperty('--s', sc.toFixed(3));
}

/* =========================================================
   EFEITOS SONOROS e CARTÃO DE FIM DE JOGO
   ========================================================= */
const fx = { ev: 0, ks: 0, ph: null };
function resetFx() { fx.ev = 0; fx.ks = 0; fx.ph = null; trail.length = 0; hideEnd(); }

function watchEffects(R) {
  if (R.ev.seq !== fx.ev) { if (R.ev.seq > 0) sfx.goal(); fx.ev = R.ev.seq; }
  if (R.kickSeq !== fx.ks) { fx.ks = R.kickSeq; sfx.kick(); }
  if (R.phase !== fx.ph) {
    if (fx.ph !== null && (R.phase === 'play' || R.phase === 'end')) sfx.whistle();
    fx.ph = R.phase;
    if (R.phase === 'end') showEnd(R); else hideEnd();
  }
}

function hideEnd() { const e = $('#endcard'); if (e) e.hidden = true; }

function showEnd(R) {
  const kits = getKits(G.teamA, G.teamB);
  const [a, b] = R.score;
  const myTeam = (() => {
    if (G.mode === 'local') return G.localPlayers === 1 ? 0 : -1;
    const i = G.roster.findIndex(r => r.ctrl === G.me);
    return i < 0 ? -1 : (i < 4 ? 0 : 1);
  })();
  let title;
  if (a === b) title = 'Empate';
  else {
    const win = a > b ? 0 : 1;
    title = myTeam < 0 ? `${kits[win].name} venceu` : (myTeam === win ? 'Vitória!' : 'Derrota');
  }
  $('#end-title').textContent = title;
  $('#end-sub').textContent = `${kits[0].code} ${a} x ${b} ${kits[1].code}`;
  const isClient = G.mode === 'client';
  $('#end-wait').hidden = !isClient;
  $('#btn-again').hidden = isClient;
  $('#btn-again').textContent = G.mode === 'host' ? 'Voltar à sala' : 'Jogar de novo';
  $('#endcard').hidden = false;
}

/* =========================================================
   TELAS / INTERFACE
   ========================================================= */
let wakeLock = null;
async function keepAwake(on) {
  try {
    if (on && 'wakeLock' in navigator) { if (!wakeLock) { wakeLock = await navigator.wakeLock.request('screen'); wakeLock.addEventListener('release', () => { wakeLock = null; }); } }
    else if (wakeLock) { await wakeLock.release(); wakeLock = null; }
  } catch (e) { /* sem suporte */ }
}
document.addEventListener('visibilitychange', () => { if (document.visibilityState === 'visible' && G.app === 'game') keepAwake(true); });

function show(id) {
  G.app = id;
  keepAwake(id === 'game');
  $$('.screen').forEach(s => s.classList.toggle('active', s.id === 'screen-' + id));
  document.body.classList.toggle('in-game', id === 'game');
  if (id === 'game') fit();
}

let toastTimer = null;
function toast(msg) {
  const t = $('#toast');
  t.textContent = msg; t.classList.add('show');
  clearTimeout(toastTimer);
  toastTimer = setTimeout(() => t.classList.remove('show'), 3200);
}

function setStatus(msg, err = false) {
  const s = $('#online-status');
  s.textContent = msg || ''; s.classList.toggle('err', !!err);
}

function fillTeamSelect(sel) {
  sel.innerHTML = '';
  TEAMS.forEach((t, i) => {
    const o = document.createElement('option');
    o.value = i; o.textContent = `${t.code} - ${t.name}`;
    sel.appendChild(o);
  });
}

function getName() {
  const raw = $('#player-name').value.toUpperCase().replace(/[^A-Z0-9ÀÁÂÃÇÉÊÍÓÔÕÚ _-]/g, '').trim();
  const name = raw || 'JOGADOR';
  try { localStorage.setItem('fpx-name', name); } catch (e) { /* ok */ }
  return name;
}

/* ---------- modo local ---------- */
function segValue(name) { return $(`.seg[data-seg="${name}"] button.on`).dataset.v; }

function setupLocalScreen() {
  const a = $('#loc-team-a'), b = $('#loc-team-b');
  fillTeamSelect(a); fillTeamSelect(b);
  a.value = G.teamA; b.value = G.teamB;
  const keep = side => {
    if (a.value === b.value) (side === 'a' ? b : a).value = (+a.value + 1) % TEAMS.length;
  };
  a.addEventListener('change', () => keep('a'));
  b.addEventListener('change', () => keep('b'));

  $$('.seg').forEach(seg => seg.addEventListener('click', e => {
    const btn = e.target.closest('button');
    if (!btn) return;
    $$('button', seg).forEach(x => x.classList.toggle('on', x === btn));
    updateLocalHint();
  }));
  updateLocalHint();
  $('#btn-local-start').addEventListener('click', startLocal);
}

function updateLocalHint() {
  const two = segValue('lp') === '2';
  $('#p2-field').hidden = !two;
  $('#local-controls').textContent = two
    ? 'Jogador 1: WASD, Espaço chuta, Shift esquerdo corre. Jogador 2: setas, Enter chuta, Shift direito corre.'
    : 'WASD ou setas para mover. Espaço ou Enter chuta e Shift corre.';
}

function startLocal() {
  G.mode = 'local';
  G.localPlayers = segValue('lp') === '2' ? 2 : 1;
  G.teamA = +$('#loc-team-a').value; G.teamB = +$('#loc-team-b').value;
  G.duration = +$('#loc-dur').value;
  G.roster = emptyRoster(); G.code = ''; G.me = 'L1';
  G.roster[freeSlot(0)] = { ctrl: 'L1', name: 'P1', pn: 1 };
  if (G.localPlayers === 2) {
    const team = segValue('p2team') === 'co' ? 0 : 1;
    G.roster[freeSlot(team)] = { ctrl: 'L2', name: 'P2', pn: 2 };
  }
  launchMatch();
}

function launchMatch() {
  G.S = newMatch(); G.R = null; G.paused = false;
  resetFx();
  show('game');
}

/* ---------- salas ---------- */
function humanCount() { return G.roster.filter(r => r.ctrl).length; }
function freeSlot(team) {
  for (const i of SLOT_ORDER) if (!G.roster[team * 4 + i].ctrl) return team * 4 + i;
  return -1;
}
function addHuman(ctrl, name) {
  const hc = [0, 1].map(t => G.roster.slice(t * 4, t * 4 + 4).filter(r => r.ctrl).length);
  let team = hc[0] <= hc[1] ? 0 : 1;
  let s = freeSlot(team);
  if (s < 0) s = freeSlot(1 - team);
  if (s < 0) return -1;
  const used = new Set(G.roster.map(r => r.pn));
  let pn = 1; while (used.has(pn)) pn++;
  G.roster[s] = { ctrl, name, pn };
  return s;
}
function removeHuman(ctrl) {
  G.roster.forEach((r, i) => { if (r.ctrl === ctrl) G.roster[i] = { ctrl: null, name: '', pn: 0 }; });
}
function switchTeam(ctrl) {
  const cur = G.roster.findIndex(r => r.ctrl === ctrl);
  if (cur < 0) return false;
  const s = freeSlot(1 - Math.floor(cur / 4));
  if (s < 0) return false;
  G.roster[s] = G.roster[cur];
  G.roster[cur] = { ctrl: null, name: '', pn: 0 };
  return true;
}

const roomMsg = t => ({ t, r: G.roster.map(x => [x.ctrl, x.name, x.pn]), ta: G.teamA, tb: G.teamB, d: G.duration, code: G.code });
function hostSend(msg) { conns.forEach(c => { if (c.open) { try { c.send(msg); } catch (e) { /* ignora */ } } }); }
function broadcastRoom() {
  if (G.S) applyRoster(G.S.players);
  hostSend(roomMsg('lobby'));
  if (G.app === 'lobby') renderLobby();
}

function renderLobby() {
  $('#room-code').textContent = G.code;
  const kits = getKits(G.teamA, G.teamB);
  const isHost = G.mode === 'host';
  [0, 1].forEach(t => {
    const ul = $('#slots-' + t);
    ul.innerHTML = '';
    for (let i = 0; i < 4; i++) {
      const slot = t * 4 + i, r = G.roster[slot];
      const li = document.createElement('li');
      li.className = 'slot' + (r.ctrl ? ' human' : '') + (r.ctrl && r.ctrl === G.me ? ' me' : '');
      const num = document.createElement('span'); num.className = 'num'; num.textContent = NUMBERS[slot];
      const who = document.createElement('span'); who.className = 'who'; who.textContent = r.ctrl ? r.name : BOT_NAMES[slot];
      const tag = document.createElement('span'); tag.className = 'tag';
      tag.textContent = r.ctrl ? (r.ctrl === G.me ? `P${r.pn} (você)` : `P${r.pn}`) : 'bot';
      li.append(num, who, tag);
      ul.appendChild(li);
    }
    $('#team-' + t).style.setProperty('--kit', kits[t].shirt);
  });
  $('#sel-a').value = G.teamA; $('#sel-b').value = G.teamB; $('#sel-dur').value = G.duration;
  ['#sel-a', '#sel-b', '#sel-dur'].forEach(s => { $(s).disabled = !isHost; });
  $('#btn-start').hidden = !isHost;
  $('#lobby-note').textContent = isHost
    ? `${humanCount()} de 8 jogadores. Vagas vazias viram bots. Mande o código ou o link: vale entrar de computador, celular ou tablet. Mantenha esta aba aberta, pois este aparelho roda a partida.`
    : 'Aguardando o host começar a partida.';
}

function setupLobby() {
  fillTeamSelect($('#sel-a')); fillTeamSelect($('#sel-b'));
  const changed = side => {
    if (G.mode !== 'host') return;
    const a = +$('#sel-a').value, b = +$('#sel-b').value;
    G.teamA = a; G.teamB = b;
    if (a === b) { if (side === 'a') G.teamB = (a + 1) % TEAMS.length; else G.teamA = (b + 1) % TEAMS.length; }
    G.duration = +$('#sel-dur').value;
    broadcastRoom(); renderLobby();
  };
  $('#sel-a').addEventListener('change', () => changed('a'));
  $('#sel-b').addEventListener('change', () => changed('b'));
  $('#sel-dur').addEventListener('change', () => changed('d'));

  $('#btn-switch').addEventListener('click', () => {
    if (G.mode === 'host') { if (switchTeam('host')) broadcastRoom(); else toast('O outro time está cheio.'); }
    else if (hostConn && hostConn.open) hostConn.send({ t: 'team' });
  });
  $('#btn-start').addEventListener('click', () => {
    if (G.mode !== 'host') return;
    launchMatch();
    hostSend(roomMsg('start'));
  });
  $('#btn-leave').addEventListener('click', () => exitToMenu());
  $('#btn-copy-link').addEventListener('click', async () => {
    const url = `${location.origin}${location.pathname}?sala=${G.code}`;
    if (navigator.share && matchMedia('(pointer: coarse)').matches) {
      try { await navigator.share({ title: 'Futebol Pixel', text: `Entre na minha sala: ${G.code}`, url }); return; }
      catch (e) { if (e && e.name === 'AbortError') return; }
    }
    try { await navigator.clipboard.writeText(url); toast('Link copiado.'); }
    catch (e) { window.prompt('Copie o link da sala:', url); }
  });
}

/* =========================================================
   ONLINE (PeerJS / WebRTC)
   ========================================================= */
const PEER_PREFIX = 'fpx-';
/* STUN descobre o endereço público; TURN retransmite quando o 4G/5G ou o roteador bloqueia a conexão direta
   (caso típico de "amigo no Wi-Fi e eu no celular"). Para uso sério, troque pelos seus próprios servidores TURN. */
const ICE_SERVERS = [
  { urls: ['stun:stun.l.google.com:19302', 'stun:stun1.l.google.com:19302'] },
  { urls: 'turn:eu-0.turn.peerjs.com:3478', username: 'peerjs', credential: 'peerjsp' },
  { urls: 'turn:us-0.turn.peerjs.com:3478', username: 'peerjs', credential: 'peerjsp' },
  { urls: ['turn:openrelay.metered.ca:80', 'turn:openrelay.metered.ca:443', 'turns:openrelay.metered.ca:443?transport=tcp'], username: 'openrelayproject', credential: 'openrelayproject' },
];
const PEER_OPTS = { debug: 0, config: { iceServers: ICE_SERVERS, iceCandidatePoolSize: 4 } };
let lastStateAt = 0, hostWatch = null, pingAcc = 0;
const CODE_CHARS = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789';
const randCode = () => Array.from({ length: 5 }, () => CODE_CHARS[Math.floor(Math.random() * CODE_CHARS.length)]).join('');

function netBusy(on) { $('#btn-create').disabled = on; $('#btn-join').disabled = on; }

function destroyPeer() {
  const p = peer;
  peer = null; hostConn = null; conns.clear();
  clearInterval(hostWatch); hostWatch = null;
  if (p) setTimeout(() => { try { p.destroy(); } catch (e) { /* ok */ } }, 250);
}

function createRoom(name, tries = 0) {
  if (typeof Peer === 'undefined') { setStatus('Não consegui carregar a biblioteca online. Verifique a internet.', true); return; }
  netBusy(true); setStatus('Criando sala...');
  const code = randCode();
  const pr = new Peer(PEER_PREFIX + code, PEER_OPTS);
  pr.on('open', () => {
    peer = pr; G.mode = 'host'; G.code = code; G.me = 'host';
    G.roster = emptyRoster(); G.S = null; G.R = null;
    addHuman('host', name);
    clearInterval(hostWatch);
    hostWatch = setInterval(() => {            // derruba quem sumiu (aba fechada, sem sinal)
      const now = performance.now();
      conns.forEach(c => { if (now - (c.lastSeen || now) > 30000) { try { c.send({ t: 'kicked' }); } catch (e) { /* ok */ } dropClient(c); } });
    }, 5000);
    netBusy(false); setStatus('');
    show('lobby'); renderLobby();
  });
  pr.on('connection', conn => {
    conn.on('data', m => hostReceive(conn, m));
    conn.on('close', () => dropClient(conn));
    conn.on('error', () => dropClient(conn));
  });
  pr.on('error', err => {
    if (err.type === 'unavailable-id' && tries < 5) { try { pr.destroy(); } catch (e) { /* ok */ } createRoom(name, tries + 1); return; }
    netBusy(false);
    if (G.mode === 'host') { exitToMenu('A conexão com o servidor de salas caiu.'); return; }
    setStatus('Não foi possível criar a sala. Tente de novo.', true);
  });
  pr.on('disconnected', () => { try { pr.reconnect(); } catch (e) { /* ok */ } });
}

function hostReceive(conn, m) {
  if (!m || typeof m !== 'object') return;
  conn.lastSeen = performance.now();
  if (m.t === 'bye') { dropClient(conn); return; }
  if (m.t !== 'hello' && !conns.has(conn.peer)) { try { conn.send({ t: 'kicked' }); } catch (e) { /* ok */ } return; }
  if (m.t === 'p') { try { conn.send({ t: 'q', n: m.n }); } catch (e) { /* ok */ } return; }
  if (m.t === 'hello') {
    if (conns.has(conn.peer)) return;
    if (humanCount() >= 8) { conn.send({ t: 'full' }); setTimeout(() => conn.close(), 300); return; }
    const name = String(m.name || 'JOGADOR').slice(0, 12);
    conns.set(conn.peer, conn);
    addHuman(conn.peer, name);
    if (G.app === 'game' && G.S) conn.send(roomMsg('start'));
    broadcastRoom();
  } else if (m.t === 'team') {
    if (G.app !== 'lobby') return;
    if (switchTeam(conn.peer)) broadcastRoom();
  } else if (m.t === 'in') {
    const p = G.S && G.S.players.find(q => q.ctrl === conn.peer);
    if (p && Array.isArray(m.i)) p.input = { dx: clamp(+m.i[0] || 0, -1, 1), dy: clamp(+m.i[1] || 0, -1, 1), s: m.i[2] ? 1 : 0, r: m.i[3] ? 1 : 0 };
  }
}

function dropClient(conn) {
  if (!conns.has(conn.peer)) return;
  conns.delete(conn.peer);
  removeHuman(conn.peer);
  broadcastRoom();
}

function joinRoom(code, name) {
  if (typeof Peer === 'undefined') { setStatus('Não consegui carregar a biblioteca online. Verifique a internet.', true); return; }
  netBusy(true); setStatus('Procurando a sala...');
  const pr = new Peer(undefined, PEER_OPTS);
  let joined = false;
  const fail = msg => { clearTimeout(timer); netBusy(false); setStatus(msg, true); if (!joined) { try { pr.destroy(); } catch (e) { /* ok */ } } };
  const timer = setTimeout(() => { if (!joined) fail('Sala não encontrada. Confira o código.'); }, 25000);
  pr.on('open', () => {
    const conn = pr.connect(PEER_PREFIX + code, { reliable: true });
    conn.on('open', () => conn.send({ t: 'hello', name }));
    conn.on('data', m => {
      if (!joined && (m.t === 'lobby' || m.t === 'start')) {
        joined = true; clearTimeout(timer);
        peer = pr; hostConn = conn; G.mode = 'client'; G.me = pr.id; G.code = code; G.S = null; G.R = null; G.ping = null; lastStateAt = performance.now();
        netBusy(false); setStatus('');
      }
      clientReceive(m);
    });
    conn.on('close', () => { if (joined) exitToMenu('A sala foi encerrada.'); else fail('Não foi possível entrar na sala.'); });
    conn.on('error', () => { if (!joined) fail('Não foi possível entrar na sala.'); });
  });
  pr.on('error', err => {
    if (joined) { exitToMenu('A conexão caiu.'); return; }
    fail(err.type === 'peer-unavailable' ? 'Sala não encontrada. Confira o código.' : 'Erro de conexão. Tente de novo.');
  });
}

function applyRoomMsg(m) {
  G.roster = m.r.map(a => ({ ctrl: a[0], name: a[1], pn: a[2] }));
  G.teamA = m.ta; G.teamB = m.tb; G.duration = m.d; G.code = m.code;
}

function buildClientView(d) {
  const players = Array.from({ length: 8 }, (_, i) => {
    const p = newPlayer(i);
    p.tx = p.x; p.ty = p.y;
    return p;
  });
  G.roster.forEach(() => {});
  const R = {
    got: false, phase: 'kick', phaseT: 3, time: 0, duration: d, score: [0, 0],
    ev: { seq: 0, team: 0, name: '', num: 0, own: false }, kickSeq: 0,
    ball: { x: PITCH.cx, y: PITCH.cy, tx: PITCH.cx, ty: PITCH.cy, spd: 0 },
    players,
  };
  applyRoster(players);
  return R;
}

function clientReceive(m) {
  if (!m || typeof m !== 'object') return;
  switch (m.t) {
    case 'lobby':
      applyRoomMsg(m);
      if (G.R) applyRoster(G.R.players);
      if (G.app !== 'game') { show('lobby'); renderLobby(); }
      break;
    case 'start':
      applyRoomMsg(m);
      G.R = buildClientView(m.d); G.paused = false; lastStateAt = performance.now();
      resetFx(); show('game');
      break;
    case 's': {
      const R = G.R; if (!R) return;
      lastStateAt = performance.now();
      m.p.forEach((a, i) => { const p = R.players[i]; p.tx = a[0]; p.ty = a[1]; p.face = a[2]; p.charge = a[3]; p.stam = a[4]; });
      R.ball.tx = m.b[0]; R.ball.ty = m.b[1];
      R.score = m.s; R.time = m.t2; R.phase = m.ph; R.phaseT = m.pt; R.ev = m.ev; R.kickSeq = m.ks; R.duration = m.d;
      if (m.ta !== G.teamA || m.tb !== G.teamB) { G.teamA = m.ta; G.teamB = m.tb; }
      if (!R.got) { R.got = true; R.players.forEach(p => { p.x = p.tx; p.y = p.ty; }); R.ball.x = R.ball.tx; R.ball.y = R.ball.ty; }
      break;
    }
    case 'q': {
      const ms = performance.now() - m.n;
      if (ms >= 0 && ms < 10000) G.ping = G.ping == null ? Math.round(ms) : Math.round(G.ping * 0.6 + ms * 0.4);
      break;
    }
    case 'kicked':
      exitToMenu('Você foi desconectado da sala por inatividade.');
      break;
    case 'toLobby':
      G.R = null; resetFx(); show('lobby'); renderLobby();
      break;
    case 'full':
      netBusy(false); setStatus('A sala está cheia (8 jogadores).', true);
      destroyPeer(); show('online');
      break;
    case 'closed':
      exitToMenu('A sala foi encerrada pelo host.');
      break;
  }
}

function encodeState(S) {
  return {
    t: 's',
    p: S.players.map(p => [r1(p.x), r1(p.y), r2(p.face), r2(p.charge), r2(p.stam)]),
    b: [r1(S.ball.x), r1(S.ball.y)],
    s: S.score, t2: r1(S.time), ph: S.phase, pt: r1(S.phaseT), ev: S.ev, ks: S.kickSeq, d: S.duration,
    ta: G.teamA, tb: G.teamB,
  };
}

function clientTick(dt) {
  const R = G.R; if (!R) return;
  const k = 1 - Math.exp(-dt * 20);
  const follow = o => {
    const ox = o.x, oy = o.y;
    if (Math.hypot(o.tx - o.x, o.ty - o.y) > 50) { o.x = o.tx; o.y = o.ty; }
    else { o.x += (o.tx - o.x) * k; o.y += (o.ty - o.y) * k; }
    return Math.hypot(o.x - ox, o.y - oy);
  };
  R.players.forEach(p => { const mv = follow(p); p.walk += mv * 0.11; p.moving = dt > 0 && mv / dt > 9; });
  R.ball.spd = dt > 0 ? follow(R.ball) / dt : 0;
}

let inAcc = 0, lastInKey = '', inHeartbeat = 0;
function clientSendInput(dt) {
  inAcc += dt; inHeartbeat += dt;
  if (inAcc < NET_RATE || !hostConn || !hostConn.open) return;
  inAcc = 0;
  const i = readInput('both', true);
  const arr = [r2(i.dx), r2(i.dy), i.s, i.r], key = arr.join();
  if (key !== lastInKey || inHeartbeat > 0.25) { hostConn.send({ t: 'in', i: arr }); lastInKey = key; inHeartbeat = 0; }
}

function exitToMenu(msg) {
  try {
    if (G.mode === 'host') hostSend({ t: 'closed' });
    if (G.mode === 'client' && hostConn && hostConn.open) hostConn.send({ t: 'bye' });
  } catch (e) { /* ok */ }
  destroyPeer();
  G.mode = null; G.S = null; G.R = null; G.roster = emptyRoster(); G.code = ''; G.paused = false; G.ping = null;
  netBusy(false); setStatus('');
  hideEnd(); show('menu');
  if (msg) toast(msg);
}

function endAction() {
  if (G.mode === 'local') { launchMatch(); }
  else if (G.mode === 'host') { G.S = null; resetFx(); hostSend({ t: 'toLobby' }); show('lobby'); renderLobby(); }
}

/* =========================================================
   LOOP PRINCIPAL
   ========================================================= */
let last = performance.now(), acc = 0, netAcc = 0;
function frame(now) {
  const dt = Math.min(0.1, (now - last) / 1000);
  last = now;
  if (G.mode === 'client' && hostConn && hostConn.open) {
    pingAcc += dt;
    if (pingAcc >= 2) { pingAcc = 0; try { hostConn.send({ t: 'p', n: performance.now() }); } catch (e) { /* ok */ } }
    if (G.app === 'game' && G.R && G.R.got && performance.now() - lastStateAt > 20000) { exitToMenu('Conexão perdida com o host.'); requestAnimationFrame(frame); return; }
  }
  if (G.app === 'game') {
    if (G.mode === 'client') {
      clientTick(dt); clientSendInput(dt);
      if (G.R) { watchEffects(G.R); draw(G.R); }
    } else if (G.S) {
      const S = G.S;
      if (!G.paused) {
        acc += dt;
        while (acc >= STEP) { applyLocalInputs(S); stepSim(S, STEP); acc -= STEP; }
        if (G.mode === 'host') {
          netAcc += dt;
          if (netAcc >= NET_RATE) { netAcc = 0; hostSend(encodeState(S)); }
        }
      }
      watchEffects(S); draw(S);
    }
  }
  requestAnimationFrame(frame);
}

/* =========================================================
   INICIALIZAÇÃO
   ========================================================= */
function init() {
  setupKeyboard(); setupTouch(); setupLocalScreen(); setupLobby();
  addEventListener('resize', fit); addEventListener('orientationchange', () => { setTimeout(fit, 150); setTimeout(fit, 500); });
  if (window.visualViewport) visualViewport.addEventListener('resize', fit);
  ['pointerdown', 'touchend', 'keydown'].forEach(ev => addEventListener(ev, unlockAudio, { passive: true }));
  const de = document.documentElement;
  if (!(de.requestFullscreen || de.webkitRequestFullscreen)) $('#btn-full').hidden = true;   // iPhone não tem tela cheia

  $('#btn-online').addEventListener('click', () => { setStatus(''); show('online'); });
  $('#btn-local').addEventListener('click', () => show('local'));
  $('#btn-help').addEventListener('click', () => show('help'));
  $$('[data-go]').forEach(b => b.addEventListener('click', () => show(b.dataset.go)));

  try { $('#player-name').value = localStorage.getItem('fpx-name') || ''; } catch (e) { /* ok */ }
  $('#btn-create').addEventListener('click', () => createRoom(getName()));
  const join = () => {
    const code = $('#join-code').value.trim().toUpperCase();
    if (code.length < 4) { setStatus('Digite o código da sala.', true); return; }
    joinRoom(code, getName());
  };
  $('#btn-join').addEventListener('click', join);
  $('#join-code').addEventListener('keydown', e => { if (e.key === 'Enter') join(); });

  $('#btn-mute').addEventListener('click', () => { muted = !muted; const b = $('#btn-mute'); b.classList.toggle('off', muted); b.setAttribute('aria-pressed', String(muted)); });
  $('#btn-full').addEventListener('click', () => {
    const el = document.documentElement;
    if (!document.fullscreenElement) {
      (el.requestFullscreen || el.webkitRequestFullscreen || (() => {})).call(el);
      try { screen.orientation.lock('landscape').catch(() => {}); } catch (e) { /* ok */ }
    } else if (document.exitFullscreen) document.exitFullscreen();
  });
  $('#btn-exit').addEventListener('click', () => { if (confirm('Sair da partida?')) exitToMenu(); });
  $('#btn-end-exit').addEventListener('click', () => exitToMenu());
  $('#btn-again').addEventListener('click', endAction);

  const sala = new URLSearchParams(location.search).get('sala');
  if (sala) { $('#join-code').value = sala.toUpperCase().slice(0, 5); show('online'); }

  if (document.fonts && document.fonts.load) document.fonts.load('8px "Press Start 2P"').catch(() => {});
  fit();
  requestAnimationFrame(frame);
}

init();

/* gancho para testes automáticos (não afeta o jogo) */
window.__fpx = { G, stepSim, newMatch, launchMatch, startLocal, clientReceive, encodeState, roomMsg };
})();
