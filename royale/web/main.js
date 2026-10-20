// Last Circle: the visual half. The rules are ../royale.bend, imported as a
// module: every def becomes a function on R. Health, ammo and kills only
// change through R.apply, a gun only fires when R.fired says so, and the safe
// circle is R.radius(second). This file moves fighters, steers the bots and
// draws the result.

import R from "../royale.bend";

// Bend bridge
// ===========
// A constructor is {$: "Name", field: value}, a Nat is a number.

const Hit   = (dmg) => ({ $: "Hit", dmg });
const Storm = (dmg) => ({ $: "Storm", dmg });
const Heal  = (amt) => ({ $: "Heal", amt });
const Loot  = (n) => ({ $: "Loot", n });
const FIRE  = { $: "Fire" };
const KILL  = { $: "Kill" };

const MAX_HP = Number(R.max_hp());
const DMG    = Number(R.bullet_dmg());
const MED    = Number(R.medkit_heal());
const BOX    = Number(R.ammo_box());

const hp    = (e) => Number(R.hp(e.f));
const ammo  = (e) => Number(R.ammo(e.f));
const kills = (e) => Number(R.kills(e.f));
const alive = (e) => R.alive(e.f) === true;

const radii = [];
const radiusAt = (t) => (radii[t] ??= Number(R.radius(t)));

// World
// =====

const MAP = 2000;
const BODY = 14;
const SPEED = 200;
const BOT_SPEED = 165;
const BULLET_SPEED = 950;
const BULLET_RANGE = 650;
const SIGHT = 560;
const NAMES = ["Kestrel", "Juniper", "Basalt", "Marrow", "Thistle", "Corvid", "Sable", "Rook",
  "Wren", "Flint", "Moss", "Talon", "Ember", "Quill", "Harrow"];
const COLORS = ["#e0b45a", "#d9775c", "#b98ad9", "#6fb7c9", "#c9c26f", "#d98aa6", "#8fc98f", "#c99a6f"];

function rng(seed) {
  return () => {
    seed |= 0; seed = (seed + 0x6d2b79f5) | 0;
    let t = Math.imul(seed ^ (seed >>> 15), 1 | seed);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

let rand = Math.random;
let G = null;

function inRect(x, y, r, pad = 0) {
  return x > r.x - pad && x < r.x + r.w + pad && y > r.y - pad && y < r.y + r.h + pad;
}

function solidAt(x, y) {
  for (const r of G.houses) if (inRect(x, y, r)) return true;
  for (const c of G.rocks) if ((x - c.x) ** 2 + (y - c.y) ** 2 < c.r * c.r) return true;
  for (const t of G.trees) if ((x - t.x) ** 2 + (y - t.y) ** 2 < 100) return true;
  return false;
}

function blocksSight(x, y) {
  for (const r of G.houses) if (inRect(x, y, r)) return true;
  for (const c of G.rocks) if ((x - c.x) ** 2 + (y - c.y) ** 2 < c.r * c.r) return true;
  return false;
}

function sees(a, b) {
  const d = Math.hypot(b.x - a.x, b.y - a.y);
  const n = Math.ceil(d / 18);
  for (let i = 1; i < n; i++) {
    if (blocksSight(a.x + (b.x - a.x) * i / n, a.y + (b.y - a.y) * i / n)) return false;
  }
  return true;
}

function canopyOver(e) {
  return G.trees.find((t) => (e.x - t.x) ** 2 + (e.y - t.y) ** 2 < (t.r - 6) ** 2);
}

function freeSpot(margin, minGap, taken) {
  for (let tries = 0; tries < 400; tries++) {
    const x = margin + rand() * (MAP - 2 * margin);
    const y = margin + rand() * (MAP - 2 * margin);
    let ok = true;
    for (const r of G.houses) if (inRect(x, y, r, 40)) ok = false;
    for (const c of G.rocks) if (Math.hypot(x - c.x, y - c.y) < c.r + 30) ok = false;
    for (const t of G.trees) if (Math.hypot(x - t.x, y - t.y) < 30) ok = false;
    for (const p of taken) if (Math.hypot(x - p.x, y - p.y) < minGap) ok = false;
    if (ok) return { x, y };
  }
  return { x: MAP / 2, y: MAP / 2 };
}

function newWorld() {
  const seed = (Math.random() * 1e9) | 0;
  rand = rng(seed);
  G = { houses: [], rocks: [], trees: [], loot: [], bullets: [], sparks: [], fighters: [],
    t: 0, sec: 0, zr: radiusAt(0), feed: [], over: false, result: null, hurt: 0 };
  G.zone = { x: 850 + rand() * 300, y: 850 + rand() * 300 };
  for (let i = 0; i < 16; i++) {
    const w = 120 + rand() * 150, h = 110 + rand() * 130;
    const x = 80 + rand() * (MAP - 160 - w), y = 80 + rand() * (MAP - 160 - h);
    if (G.houses.some((o) => x < o.x + o.w + 70 && x + w + 70 > o.x && y < o.y + o.h + 70 && y + h + 70 > o.y)) continue;
    G.houses.push({ x, y, w, h, tone: rand() });
  }
  for (let i = 0; i < 26; i++) {
    const p = freeSpot(60, 0, []);
    G.rocks.push({ x: p.x, y: p.y, r: 18 + rand() * 22, tone: rand() });
  }
  for (let i = 0; i < 70; i++) {
    const p = freeSpot(40, 0, []);
    G.trees.push({ x: p.x, y: p.y, r: 38 + rand() * 22, tone: rand() });
  }
  for (const h of G.houses) {
    const n = 1 + Math.floor(rand() * 2);
    for (let k = 0; k < n; k++) {
      G.loot.push({ x: h.x + h.w / 2 + (rand() - 0.5) * 60, y: h.y + h.h + 26, kind: rand() < 0.55 ? "ammo" : "med" });
    }
  }
  for (let i = 0; i < 48; i++) {
    const p = freeSpot(50, 0, []);
    G.loot.push({ x: p.x, y: p.y, kind: rand() < 0.6 ? "ammo" : "med" });
  }
  const spots = [];
  for (let i = 0; i < 16; i++) spots.push(freeSpot(120, 260, spots));
  spots.forEach((p, i) => {
    G.fighters.push({
      id: i, bot: i > 0, name: i === 0 ? "You" : NAMES[i - 1],
      color: i === 0 ? "#f4f7ee" : COLORS[i % COLORS.length],
      x: p.x, y: p.y, aim: rand() * Math.PI * 2, f: R.spawn(),
      cool: 0, think: rand() * 0.3, wp: null, enemy: null, react: 0, strafe: rand() < 0.5 ? 1 : -1,
      stuck: 0, flash: 0, diedAt: null,
    });
  });
  G.me = G.fighters[0];
}

function moveBody(e, dx, dy) {
  e.x = Math.max(BODY, Math.min(MAP - BODY, e.x + dx));
  e.y = Math.max(BODY, Math.min(MAP - BODY, e.y + dy));
  for (const r of G.houses) {
    const cx = Math.max(r.x, Math.min(e.x, r.x + r.w));
    const cy = Math.max(r.y, Math.min(e.y, r.y + r.h));
    const d = Math.hypot(e.x - cx, e.y - cy);
    if (d < BODY) {
      if (d === 0) { e.y = r.y - BODY; continue; }
      e.x = cx + (e.x - cx) / d * BODY;
      e.y = cy + (e.y - cy) / d * BODY;
    }
  }
  const round = (cx, cy, rr) => {
    const d = Math.hypot(e.x - cx, e.y - cy);
    if (d < rr + BODY && d > 0) {
      e.x = cx + (e.x - cx) / d * (rr + BODY);
      e.y = cy + (e.y - cy) / d * (rr + BODY);
    }
  };
  for (const c of G.rocks) round(c.x, c.y, c.r);
  for (const t of G.trees) round(t.x, t.y, 10);
}

// Rules, through Bend
// ===================

function say(text, kind = "") {
  G.feed.unshift({ text, kind, t: G.t });
  if (G.feed.length > 5) G.feed.pop();
}

function dropLoot(e) {
  if (ammo(e) > 0) G.loot.push({ x: e.x - 10, y: e.y, kind: "ammo" });
  if (rand() < 0.5) G.loot.push({ x: e.x + 12, y: e.y + 6, kind: "med" });
}

function died(victim, killer) {
  victim.diedAt = G.t;
  dropLoot(victim);
  if (killer) {
    killer.f = R.apply(killer.f, KILL);
    say(`${killer.name} eliminated ${victim.name}`, killer === G.me ? "mine" : victim === G.me ? "me" : "");
  } else {
    say(`${victim.name} was caught by the storm`, victim === G.me ? "me" : "");
  }
  if (victim === G.me) {
    G.result = { won: false, place: G.fighters.filter(alive).length + 1, by: killer ? killer.name : "the storm" };
  }
}

function strike(target, act, killer) {
  const was = alive(target);
  target.f = R.apply(target.f, act);
  target.flash = 0.18;
  if (target === G.me) G.hurt = 0.35;
  if (was && !alive(target)) died(target, killer);
}

function shoot(e) {
  if (Number(R.fired(e.f)) === 0) {
    if (e === G.me && e.cool <= 0) { say("Out of ammo. Find a yellow ammo box.", "me"); e.cool = 0.6; }
    return;
  }
  e.f = R.apply(e.f, FIRE);
  const a = e.aim;
  G.bullets.push({ x: e.x + Math.cos(a) * (BODY + 6), y: e.y + Math.sin(a) * (BODY + 6),
    vx: Math.cos(a) * BULLET_SPEED, vy: Math.sin(a) * BULLET_SPEED, owner: e, left: BULLET_RANGE });
}

function stormTick(sec) {
  const dmg = Number(R.storm_dmg(sec));
  for (const e of G.fighters) {
    if (alive(e) && Math.hypot(e.x - G.zone.x, e.y - G.zone.y) > G.zr) strike(e, Storm(dmg), null);
  }
}

function pickUp(e) {
  for (let i = G.loot.length - 1; i >= 0; i--) {
    const l = G.loot[i];
    if (Math.hypot(e.x - l.x, e.y - l.y) > 24) continue;
    if (l.kind === "med") {
      if (hp(e) >= MAX_HP) continue;
      e.f = R.apply(e.f, Heal(MED));
    } else {
      e.f = R.apply(e.f, Loot(BOX));
    }
    G.loot.splice(i, 1);
  }
}

// Bots
// ====

function nearestLoot(b, kind, range) {
  let best = null, bd = range;
  for (const l of G.loot) {
    if (l.kind !== kind) continue;
    const d = Math.hypot(l.x - b.x, l.y - b.y);
    if (d < bd) { bd = d; best = l; }
  }
  return best;
}

function wanderPoint() {
  const r = Math.max(40, G.zr * 0.6) * Math.sqrt(rand());
  const a = rand() * Math.PI * 2;
  return { x: Math.max(60, Math.min(MAP - 60, G.zone.x + Math.cos(a) * r)),
    y: Math.max(60, Math.min(MAP - 60, G.zone.y + Math.sin(a) * r)) };
}

function botThink(b) {
  let best = null, bd = Infinity;
  for (const o of G.fighters) {
    if (o === b || !alive(o)) continue;
    const d = Math.hypot(o.x - b.x, o.y - b.y);
    const range = canopyOver(o) ? 150 : SIGHT;
    if (d < range && d < bd && sees(b, o)) { bd = d; best = o; }
  }
  if (best && best !== b.enemy) b.react = 0.3 + rand() * 0.3;
  b.enemy = best;
  const dz = Math.hypot(b.x - G.zone.x, b.y - G.zone.y);
  const soon = Math.min(G.zr, radiusAt(G.sec + 12));
  if (dz > soon * 0.9) {
    b.wp = { x: G.zone.x + (b.x - G.zone.x) * 0.4, y: G.zone.y + (b.y - G.zone.y) * 0.4 };
  } else if (ammo(b) === 0 || (hp(b) < 60 && !best)) {
    b.wp = nearestLoot(b, ammo(b) === 0 ? "ammo" : "med", 800) || b.wp || wanderPoint();
  } else if (!b.wp || Math.hypot(b.wp.x - b.x, b.wp.y - b.y) < 30) {
    b.wp = nearestLoot(b, ammo(b) < 20 ? "ammo" : "med", 260) || wanderPoint();
  }
  if (rand() < 0.15) b.strafe = -b.strafe;
}

function botUpdate(b, dt) {
  b.think -= dt;
  if (b.think <= 0) { botThink(b); b.think = 0.18 + rand() * 0.15; }
  const x0 = b.x, y0 = b.y;
  let mx = 0, my = 0;
  const e = b.enemy && alive(b.enemy) ? b.enemy : null;
  const dz = Math.hypot(b.x - G.zone.x, b.y - G.zone.y);
  if (e && ammo(b) > 0 && dz < G.zr) {
    const dx = e.x - b.x, dy = e.y - b.y, d = Math.hypot(dx, dy) || 1;
    const push = d > 320 ? 0.7 : d < 200 ? -0.6 : 0;
    mx = dx / d * push - dy / d * b.strafe * 0.8;
    my = dy / d * push + dx / d * b.strafe * 0.8;
    const want = Math.atan2(dy, dx);
    b.aim += Math.atan2(Math.sin(want - b.aim), Math.cos(want - b.aim)) * Math.min(1, dt * 8);
    b.react -= dt;
    if (b.react <= 0 && b.cool <= 0) {
      const keep = b.aim;
      b.aim += (rand() - 0.5) * 0.24;
      shoot(b);
      b.aim = keep;
      b.cool = 0.5 + rand() * 0.35;
    }
  } else if (b.wp) {
    const dx = b.wp.x - b.x, dy = b.wp.y - b.y, d = Math.hypot(dx, dy) || 1;
    mx = dx / d; my = dy / d;
    const want = Math.atan2(dy, dx);
    b.aim += Math.atan2(Math.sin(want - b.aim), Math.cos(want - b.aim)) * Math.min(1, dt * 5);
  }
  const m = Math.hypot(mx, my);
  if (m > 0) moveBody(b, mx / Math.max(1, m) * BOT_SPEED * dt, my / Math.max(1, m) * BOT_SPEED * dt);
  const moved = Math.hypot(b.x - x0, b.y - y0);
  b.stuck = m > 0 && moved < BOT_SPEED * dt * 0.25 ? b.stuck + dt : 0;
  if (b.stuck > 0.5) { b.wp = wanderPoint(); b.stuck = 0; b.strafe = -b.strafe; }
}

// Input
// =====

const cv = document.getElementById("view");
const cx = cv.getContext("2d");
const keys = new Set();
const mouse = { x: 0, y: 0, down: false };
const touch = { move: null, aim: null };
let view = { scale: 1, w: 0, h: 0, ox: 0, oy: 0 };

addEventListener("keydown", (e) => {
  const k = e.key.toLowerCase();
  if (["w", "a", "s", "d", "arrowup", "arrowdown", "arrowleft", "arrowright"].includes(k)) {
    keys.add(k);
    if (G && !G.over) e.preventDefault();
  }
});
addEventListener("keyup", (e) => keys.delete(e.key.toLowerCase()));
addEventListener("blur", () => { keys.clear(); mouse.down = false; });

cv.addEventListener("contextmenu", (e) => e.preventDefault());
cv.addEventListener("pointerdown", (e) => {
  if (e.pointerType === "touch") {
    const slot = e.clientX < innerWidth / 2 ? "move" : "aim";
    touch[slot] = { id: e.pointerId, x0: e.clientX, y0: e.clientY, x: e.clientX, y: e.clientY };
  } else {
    mouse.down = true;
  }
  cv.setPointerCapture(e.pointerId);
});
cv.addEventListener("pointermove", (e) => {
  mouse.x = e.clientX; mouse.y = e.clientY;
  for (const s of ["move", "aim"]) if (touch[s] && touch[s].id === e.pointerId) { touch[s].x = e.clientX; touch[s].y = e.clientY; }
});
const release = (e) => {
  mouse.down = false;
  for (const s of ["move", "aim"]) if (touch[s] && touch[s].id === e.pointerId) touch[s] = null;
};
cv.addEventListener("pointerup", release);
cv.addEventListener("pointercancel", release);

function playerUpdate(me, dt) {
  let mx = 0, my = 0;
  if (keys.has("w") || keys.has("arrowup")) my -= 1;
  if (keys.has("s") || keys.has("arrowdown")) my += 1;
  if (keys.has("a") || keys.has("arrowleft")) mx -= 1;
  if (keys.has("d") || keys.has("arrowright")) mx += 1;
  if (touch.move) {
    const dx = touch.move.x - touch.move.x0, dy = touch.move.y - touch.move.y0, d = Math.hypot(dx, dy);
    if (d > 8) { mx = dx / Math.max(d, 50); my = dy / Math.max(d, 50); }
  }
  const m = Math.hypot(mx, my);
  if (m > 0) moveBody(me, mx / Math.max(1, m) * SPEED * dt, my / Math.max(1, m) * SPEED * dt);
  let firing = false;
  if (touch.aim) {
    const dx = touch.aim.x - touch.aim.x0, dy = touch.aim.y - touch.aim.y0;
    if (Math.hypot(dx, dy) > 10) me.aim = Math.atan2(dy, dx);
    firing = true;
  } else {
    const sx = (me.x - view.ox) * view.scale, sy = (me.y - view.oy) * view.scale;
    me.aim = Math.atan2(mouse.y - sy, mouse.x - sx);
    firing = mouse.down;
  }
  if (firing && me.cool <= 0) { shoot(me); me.cool = Math.max(me.cool, 0.24); }
}

// Simulation
// ==========

function update(dt) {
  G.t += dt;
  while (G.sec < Math.floor(G.t)) { G.sec++; stormTick(G.sec); }
  const k = G.t - G.sec;
  G.zr = radiusAt(G.sec) + (radiusAt(G.sec + 1) - radiusAt(G.sec)) * k;
  for (const e of G.fighters) {
    if (!alive(e)) continue;
    e.cool -= dt;
    e.flash = Math.max(0, e.flash - dt);
    if (e.bot) botUpdate(e, dt); else playerUpdate(e, dt);
    pickUp(e);
  }
  G.hurt = Math.max(0, G.hurt - dt);
  for (let i = G.bullets.length - 1; i >= 0; i--) {
    const b = G.bullets[i];
    const steps = Math.ceil(BULLET_SPEED * dt / 8);
    let gone = false;
    for (let s = 0; s < steps && !gone; s++) {
      b.x += b.vx * dt / steps; b.y += b.vy * dt / steps;
      b.left -= BULLET_SPEED * dt / steps;
      if (b.left <= 0 || b.x < 0 || b.y < 0 || b.x > MAP || b.y > MAP) { gone = true; break; }
      if (solidAt(b.x, b.y)) { G.sparks.push({ x: b.x, y: b.y, t: 0.25 }); gone = true; break; }
      for (const e of G.fighters) {
        if (e === b.owner || !alive(e)) continue;
        if ((e.x - b.x) ** 2 + (e.y - b.y) ** 2 < (BODY + 2) ** 2) {
          strike(e, Hit(DMG), b.owner);
          if (e.bot && !e.enemy) { e.enemy = b.owner; e.react = 0.2; }
          G.sparks.push({ x: b.x, y: b.y, t: 0.2, blood: true });
          gone = true; break;
        }
      }
    }
    if (gone) G.bullets.splice(i, 1);
  }
  for (let i = G.sparks.length - 1; i >= 0; i--) if ((G.sparks[i].t -= dt) <= 0) G.sparks.splice(i, 1);
  const left = G.fighters.filter(alive);
  if (!G.result && left.length === 1 && left[0] === G.me) G.result = { won: true, place: 1 };
  if (G.result && !G.over && (G.result.won || G.t - G.me.diedAt > 1.2)) finish();
}

// Drawing
// =======

function resize() {
  const dpr = Math.min(2, devicePixelRatio || 1);
  cv.width = innerWidth * dpr; cv.height = innerHeight * dpr;
  cv.style.width = innerWidth + "px"; cv.style.height = innerHeight + "px";
  cx.setTransform(dpr, 0, 0, dpr, 0, 0);
  view.w = innerWidth; view.h = innerHeight;
  view.scale = Math.max(0.7, Math.min(innerWidth, innerHeight * 1.2) / 900);
}
addEventListener("resize", resize);
resize();

function draw() {
  const { w, h, scale } = view;
  const me = G.me;
  view.ox = me.x - w / 2 / scale;
  view.oy = me.y - h / 2 / scale;
  cx.fillStyle = "#1a1f1b";
  cx.fillRect(0, 0, w, h);
  cx.save();
  cx.scale(scale, scale);
  cx.translate(-view.ox, -view.oy);

  cx.fillStyle = "#4f6640";
  cx.fillRect(0, 0, MAP, MAP);
  cx.strokeStyle = "rgba(255,255,255,0.045)";
  cx.lineWidth = 2;
  cx.beginPath();
  for (let g = 0; g <= MAP; g += 100) { cx.moveTo(g, 0); cx.lineTo(g, MAP); cx.moveTo(0, g); cx.lineTo(MAP, g); }
  cx.stroke();

  for (const r of G.houses) {
    cx.fillStyle = "rgba(0,0,0,0.25)";
    cx.fillRect(r.x + 8, r.y + 10, r.w, r.h);
    cx.fillStyle = r.tone < 0.5 ? "#8c7a63" : "#7d6f66";
    cx.fillRect(r.x, r.y, r.w, r.h);
    cx.fillStyle = r.tone < 0.5 ? "#a08b70" : "#91827a";
    cx.fillRect(r.x + 6, r.y + 6, r.w - 12, r.h / 2 - 6);
    cx.strokeStyle = "rgba(0,0,0,0.25)";
    cx.strokeRect(r.x + 0.5, r.y + 0.5, r.w - 1, r.h - 1);
  }
  for (const c of G.rocks) {
    cx.fillStyle = "rgba(0,0,0,0.22)";
    cx.beginPath(); cx.arc(c.x + 5, c.y + 6, c.r, 0, 7); cx.fill();
    cx.fillStyle = c.tone < 0.5 ? "#8b8d86" : "#7a7c76";
    cx.beginPath(); cx.arc(c.x, c.y, c.r, 0, 7); cx.fill();
    cx.fillStyle = "rgba(255,255,255,0.12)";
    cx.beginPath(); cx.arc(c.x - c.r * 0.3, c.y - c.r * 0.3, c.r * 0.45, 0, 7); cx.fill();
  }
  for (const l of G.loot) {
    if (l.kind === "ammo") {
      cx.fillStyle = "#3b3216"; cx.fillRect(l.x - 9, l.y - 7, 18, 14);
      cx.fillStyle = "#e8c547"; cx.fillRect(l.x - 7, l.y - 5, 14, 10);
      cx.fillStyle = "#3b3216"; cx.fillRect(l.x - 4, l.y - 2, 8, 4);
    } else {
      cx.fillStyle = "#f2f2ea"; cx.fillRect(l.x - 9, l.y - 9, 18, 18);
      cx.fillStyle = "#d8453a"; cx.fillRect(l.x - 2.5, l.y - 6, 5, 12); cx.fillRect(l.x - 6, l.y - 2.5, 12, 5);
    }
  }
  cx.strokeStyle = "#fff3c4";
  cx.lineWidth = 3;
  cx.beginPath();
  for (const b of G.bullets) { cx.moveTo(b.x, b.y); cx.lineTo(b.x - b.vx * 0.018, b.y - b.vy * 0.018); }
  cx.stroke();
  for (const s of G.sparks) {
    cx.fillStyle = s.blood ? `rgba(220,60,50,${s.t * 4})` : `rgba(255,230,160,${s.t * 4})`;
    cx.beginPath(); cx.arc(s.x, s.y, 6 - s.t * 10, 0, 7); cx.fill();
  }
  for (const e of G.fighters) {
    if (!alive(e)) {
      cx.strokeStyle = "rgba(20,20,20,0.5)"; cx.lineWidth = 4;
      cx.beginPath(); cx.moveTo(e.x - 8, e.y - 8); cx.lineTo(e.x + 8, e.y + 8); cx.moveTo(e.x + 8, e.y - 8); cx.lineTo(e.x - 8, e.y + 8); cx.stroke();
      continue;
    }
    cx.fillStyle = "rgba(0,0,0,0.25)";
    cx.beginPath(); cx.arc(e.x + 3, e.y + 4, BODY, 0, 7); cx.fill();
    cx.strokeStyle = "#20241f"; cx.lineWidth = 6;
    cx.beginPath(); cx.moveTo(e.x, e.y); cx.lineTo(e.x + Math.cos(e.aim) * (BODY + 12), e.y + Math.sin(e.aim) * (BODY + 12)); cx.stroke();
    cx.fillStyle = e.flash > 0 ? "#ff7a6b" : e.color;
    cx.beginPath(); cx.arc(e.x, e.y, BODY, 0, 7); cx.fill();
    cx.strokeStyle = e === me ? "#2b6cff" : "rgba(0,0,0,0.45)"; cx.lineWidth = e === me ? 3 : 2;
    cx.stroke();
    if (e !== me && hp(e) < MAX_HP) {
      cx.fillStyle = "rgba(0,0,0,0.5)"; cx.fillRect(e.x - 16, e.y - 26, 32, 5);
      cx.fillStyle = "#e9eedd"; cx.fillRect(e.x - 16, e.y - 26, 32 * hp(e) / MAX_HP, 5);
    }
  }
  const shade = canopyOver(me);
  for (const t of G.trees) {
    cx.globalAlpha = t === shade ? 0.4 : 0.92;
    cx.fillStyle = t.tone < 0.5 ? "#2f4a2a" : "#36532c";
    cx.beginPath(); cx.arc(t.x, t.y, t.r, 0, 7); cx.fill();
    cx.fillStyle = "rgba(255,255,255,0.06)";
    cx.beginPath(); cx.arc(t.x - t.r * 0.25, t.y - t.r * 0.25, t.r * 0.55, 0, 7); cx.fill();
  }
  cx.globalAlpha = 1;

  cx.fillStyle = "rgba(64, 86, 255, 0.26)";
  cx.beginPath();
  cx.rect(view.ox - 50, view.oy - 50, w / scale + 100, h / scale + 100);
  cx.arc(G.zone.x, G.zone.y, Math.max(0, G.zr), 0, Math.PI * 2, true);
  cx.fill("evenodd");
  cx.strokeStyle = "#7d8cff"; cx.lineWidth = 4;
  cx.beginPath(); cx.arc(G.zone.x, G.zone.y, Math.max(0, G.zr), 0, 7); cx.stroke();
  const next = radiusAt(G.sec + 30);
  if (next < G.zr - 1) {
    cx.setLineDash([16, 12]); cx.strokeStyle = "rgba(255,255,255,0.7)"; cx.lineWidth = 2;
    cx.beginPath(); cx.arc(G.zone.x, G.zone.y, next, 0, 7); cx.stroke();
    cx.setLineDash([]);
  }
  cx.restore();

  if (G.hurt > 0) {
    const g = cx.createRadialGradient(w / 2, h / 2, Math.min(w, h) * 0.3, w / 2, h / 2, Math.max(w, h) * 0.7);
    g.addColorStop(0, "rgba(200,30,30,0)"); g.addColorStop(1, `rgba(200,30,30,${G.hurt})`);
    cx.fillStyle = g; cx.fillRect(0, 0, w, h);
  }
  for (const s of ["move", "aim"]) {
    const p = touch[s];
    if (!p) continue;
    cx.strokeStyle = "rgba(255,255,255,0.35)"; cx.lineWidth = 2;
    cx.beginPath(); cx.arc(p.x0, p.y0, 46, 0, 7); cx.stroke();
    cx.fillStyle = "rgba(255,255,255,0.25)";
    cx.beginPath(); cx.arc(p.x, p.y, 20, 0, 7); cx.fill();
  }
  drawMinimap();
  drawHud();
}

const mm = document.getElementById("minimap");
const mx = mm.getContext("2d");
function drawMinimap() {
  const s = mm.width / MAP;
  mx.fillStyle = "#3f5434"; mx.fillRect(0, 0, mm.width, mm.height);
  mx.fillStyle = "#8c7a63";
  for (const r of G.houses) mx.fillRect(r.x * s, r.y * s, r.w * s, r.h * s);
  mx.fillStyle = "rgba(64,86,255,0.35)";
  mx.beginPath(); mx.rect(0, 0, mm.width, mm.height);
  mx.arc(G.zone.x * s, G.zone.y * s, Math.max(0, G.zr) * s, 0, Math.PI * 2, true); mx.fill("evenodd");
  mx.strokeStyle = "#9aa6ff"; mx.lineWidth = 2;
  mx.beginPath(); mx.arc(G.zone.x * s, G.zone.y * s, Math.max(0, G.zr) * s, 0, 7); mx.stroke();
  const next = radiusAt(G.sec + 30);
  if (next < G.zr - 1) {
    mx.setLineDash([4, 3]); mx.strokeStyle = "#fff"; mx.lineWidth = 1;
    mx.beginPath(); mx.arc(G.zone.x * s, G.zone.y * s, next * s, 0, 7); mx.stroke(); mx.setLineDash([]);
  }
  mx.fillStyle = "#fff"; mx.strokeStyle = "#2b6cff"; mx.lineWidth = 2;
  mx.beginPath(); mx.arc(G.me.x * s, G.me.y * s, 4, 0, 7); mx.fill(); mx.stroke();
}

const hud = {};
for (const id of ["alive", "zone", "hpbar", "hpnum", "ammo", "kills", "feed"]) hud[id] = document.getElementById(id);
const last = {};
function put(id, value, prop = "textContent") {
  if (last[id + prop] === value) return;
  last[id + prop] = value;
  if (prop === "width") hud[id].style.width = value; else hud[id][prop] = value;
}

function drawHud() {
  const me = G.me;
  put("alive", String(G.fighters.filter(alive).length));
  const wait = Number(R.next_shrink(G.sec));
  const out = Math.hypot(me.x - G.zone.x, me.y - G.zone.y) > G.zr;
  const zoneText = out ? `Outside the circle: −${Number(R.storm_dmg(G.sec))} hp every second`
    : G.zr <= 0 ? "The circle has closed"
    : wait > 0 ? `Circle closes in ${wait}s` : "Circle closing";
  put("zone", zoneText);
  hud.zone.dataset.out = out ? "1" : "";
  const h = hp(me);
  put("hpbar", `${(h / MAX_HP) * 100}%`, "width");
  hud.hpbar.dataset.low = h <= 35 ? "1" : "";
  put("hpnum", String(h));
  put("ammo", String(ammo(me)));
  put("kills", String(kills(me)));
  const feed = G.feed.filter((f) => G.t - f.t < 6).map((f) => `<li class="${f.kind}">${f.text}</li>`).join("");
  put("feed", feed, "innerHTML");
}

// Flow
// ====

const startEl = document.getElementById("start");
const endEl = document.getElementById("end");

function begin() {
  newWorld();
  startEl.hidden = true;
  endEl.hidden = true;
  cv.focus();
}

function finish() {
  G.over = true;
  const r = G.result;
  document.getElementById("end-title").textContent = r.won ? "Last one standing" : `You placed #${r.place}`;
  document.getElementById("end-detail").textContent = r.won
    ? `You outlasted 15 fighters with ${kills(G.me)} elimination${kills(G.me) === 1 ? "" : "s"}.`
    : `Eliminated by ${r.by} after ${Math.floor(G.t)} seconds, with ${kills(G.me)} elimination${kills(G.me) === 1 ? "" : "s"}.`;
  endEl.hidden = false;
  document.getElementById("again").focus();
}

document.getElementById("go").addEventListener("click", begin);
document.getElementById("again").addEventListener("click", begin);

let prev = performance.now();
function frame(now) {
  const dt = Math.min(0.05, (now - prev) / 1000);
  prev = now;
  if (!startEl.hidden) { G.t += dt * 0.3; G.me.x += Math.cos(G.t * 0.2) * 0.4; G.me.y += Math.sin(G.t * 0.17) * 0.4; }
  else if (!G.over || !G.result.won) update(dt);
  draw();
  requestAnimationFrame(frame);
}

newWorld();
requestAnimationFrame(frame);
