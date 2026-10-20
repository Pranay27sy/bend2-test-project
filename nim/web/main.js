// Nim: the visual half. The game itself is ../nim.bend, imported as a module:
// the bend loader compiles it on the fly, and every def becomes a function on
// Nim. Every move, yours and the computer's, goes through Nim.take and
// Nim.taken; the computer's choice is Nim.ai. This file only draws the board
// that comes back.

import Nim from "../nim.bend";

// Bend bridge
// ===========
// A constructor is {$: "Name", field: value}, a Nat is a number, and a list
// is a chain of {$: "Con", head, tail} ending in {$: "Nil"}.

const toList   = (a) => a.reduceRight((tail, head) => ({ $: "Con", head, tail }), { $: "Nil" });
const fromList = (l) => { const a = []; for (; l.$ === "Con"; l = l.tail) a.push(Number(l.head)); return a; };
const mkTake   = (pile, amt) => ({ $: "Take", pile, amt });

// State
// =====

let piles = [];      // stones per pile, as the last Nim.take answered
let fading = null;   // {pile, from, to, who} stones just taken, for the animation
let turn = "you";    // "you" | "cpu" | "over"
let firstPlayer = "you";
let log = [];
let score = { you: 0, cpu: 0 };

const $ = (id) => document.getElementById(id);
const board = $("board");
const reduceMotion = matchMedia("(prefers-reduced-motion: reduce)").matches;

function play(pile, amt, who) {
  const xs = toList(piles);
  const mv = mkTake(pile, amt);
  const got = Number(Nim.taken(xs, mv));
  if (got === 0) return false;                      // Bend rejected it
  const before = piles[pile];
  piles = fromList(Nim.take(xs, mv));
  fading = { pile, from: piles[pile], to: before, who };
  log.unshift({ who, pile, amt: got });
  if (Number(Nim.total(toList(piles))) === 0) {
    turn = "over";
    score[who]++;
    log[0].last = true;
  } else {
    turn = who === "you" ? "cpu" : "you";
  }
  render();
  if (turn === "cpu") setTimeout(cpuMove, reduceMotion ? 250 : 750);
  return true;
}

function cpuMove() {
  if (turn !== "cpu") return;
  const mv = Nim.ai(toList(piles));
  play(Number(mv.pile), Number(mv.amt), "cpu");
}

function newGame(sizes) {
  const n = 3 + Math.floor(Math.random() * 2);
  piles = sizes || Array.from({ length: n }, () => 1 + Math.floor(Math.random() * 7));
  fading = null;
  log = [];
  turn = firstPlayer;
  render();
  if (turn === "cpu") setTimeout(cpuMove, reduceMotion ? 250 : 900);
}

// Render
// ======

function bits(n, w) { return n.toString(2).padStart(w, "0"); }

function render() {
  board.innerHTML = "";
  piles.forEach((h, i) => {
    const row = document.createElement("div");
    row.className = "pile";
    const label = document.createElement("span");
    label.className = "pile-label";
    label.textContent = String.fromCharCode(65 + i);
    row.appendChild(label);
    const stones = document.createElement("div");
    stones.className = "stones";
    const shown = fading && fading.pile === i ? fading.to : h;
    for (let k = 0; k < shown; k++) {
      const s = document.createElement("button");
      s.className = "stone";
      s.style.setProperty("--k", k);
      s.style.setProperty("--tilt", ((i * 7 + k * 13) % 9 - 4) + "deg");
      const take = h - k;
      if (k >= h) {
        s.classList.add("gone", fading.who);
        s.tabIndex = -1;
        s.setAttribute("aria-hidden", "true");
      } else {
        s.setAttribute("aria-label", `Take ${take} from pile ${String.fromCharCode(65 + i)}`);
        s.disabled = turn !== "you";
        s.addEventListener("mouseenter", () => highlight(stones, k));
        s.addEventListener("focus", () => highlight(stones, k));
        s.addEventListener("mouseleave", () => highlight(stones, -1));
        s.addEventListener("blur", () => highlight(stones, -1));
        s.addEventListener("click", () => play(i, take, "you"));
      }
      stones.appendChild(s);
    }
    row.appendChild(stones);
    const count = document.createElement("span");
    count.className = "pile-count";
    count.textContent = h;
    row.appendChild(count);
    board.appendChild(row);
  });
  fading = null;

  const status = $("status");
  status.dataset.state = turn;
  if (turn === "you") status.textContent = log.length ? "Your move. Take one or more stones from a single pile." : "Your move. Click a stone to take it and every stone to its right.";
  else if (turn === "cpu") status.textContent = "The computer is thinking…";
  else status.textContent = log[0].who === "you" ? "You took the last stone. You win." : "The computer took the last stone. It wins.";

  $("score-you").textContent = score.you;
  $("score-cpu").textContent = score.cpu;
  $("stones-left").textContent = Number(Nim.total(toList(piles)));

  const w = Math.max(3, ...piles.map((h) => h.toString(2).length));
  const s = Number(Nim.nim_sum(toList(piles)));
  $("math").innerHTML =
    piles.map((h, i) => `<span>${String.fromCharCode(65 + i)}</span><code>${bits(h, w)}</code><span class="dec">${h}</span>`).join("") +
    `<span class="xor">⊕</span><code class="sum">${bits(s, w)}</code><span class="dec">${s}</span>`;
  $("math-note").textContent = s === 0
    ? "Nim-sum is 0: whoever moves now loses against perfect play."
    : "Nim-sum is not 0: the player to move can force a win.";

  $("log").innerHTML = log.slice(0, 6).map((e) =>
    `<li class="${e.who}"><b>${e.who === "you" ? "You" : "Computer"}</b> took ${e.amt} from ${String.fromCharCode(65 + e.pile)}${e.last ? " · last stone" : ""}</li>`
  ).join("");
}

function highlight(stones, k) {
  [...stones.children].forEach((s, j) => s.classList.toggle("doomed", k >= 0 && j >= k && !s.classList.contains("gone")));
}

$("new").addEventListener("click", () => newGame());
$("who").addEventListener("change", (e) => { firstPlayer = e.target.value; newGame(); });

newGame([3, 4, 5]);
