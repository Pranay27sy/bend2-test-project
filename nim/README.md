# Proven Nim

The game of [Nim](https://en.wikipedia.org/wiki/Nim) against the computer,
written in Bend 2, with **machine-checked proofs that the rules never cheat**.

There are a few piles of stones. On your turn you take one or more stones from
a single pile. Whoever takes the last stone wins.

| File             | What it is                                                     |
|------------------|----------------------------------------------------------------|
| `nim.bend`       | the game: piles, `take`, `taken`, the computer (`ai`), a demo  |
| `LAWS.bend`      | the rules the game must never break                            |
| `PROOF.bend`     | the proofs that every law holds                                |
| `web/`           | the browser front end; it imports `nim.bend` directly          |

## Run it

```bash
cd nim
bend PROOF.bend               # ALL PROOFS CHECK
bend nim.bend                 # the computer plays itself from 3 4 5
bend web/index.html -o dist   # bundle the browser game into dist/
```

Serve `dist/` with any static server (for example `npx http-server dist`) and
open it. The page draws the board; every move, yours and the computer's, is
judged by the compiled Bend code (`Nim.take`, `Nim.taken`, `Nim.ai`).

## The laws

```python
law take_conserves:     # a move, legal or rejected, never creates or
  for +xs: List<&2, Nat>  # destroys stones: what it takes plus what is
  for  mv: N.Take         # left is exactly what was there
  {Nat.add(N.taken(xs, mv), N.total(N.take(xs, mv))) == N.total(xs) : Nat}

law ai_takes:           # while a stone is left, the computer always
  for +xs  : List<&2, Nat>  # takes at least one: it never passes
  for  live: N.Live(xs)
  exs  k   : Nat
  {N.taken(xs, N.ai(xs)) == 1n+k : Nat}
```

Together they mean every computer move shrinks the board, so a game against
it always ends.

## The computer

It plays the classic winning strategy: xor all piles together (the
*nim-sum*); if that is not zero, shrink some pile `h` to `h xor s`, leaving the
opponent a zero nim-sum. That strategy is **not** proven, so `ai` only keeps
its move after checking that the move actually takes something. Otherwise it
takes one stone from the first pile that has any, and that fallback is what
`ai_takes` proves always works.

The laws catch real mistakes. Both of these edits still compile and run, but
`bend PROOF.bend` rejects them with SOME PROOFS FAIL:

- drop the check in `ai` and trust the strategy (`def ai(..): smart(xs)`):
  with a zero nim-sum it answers an empty move and passes its turn;
- remove one stone more than reported (`remove(xs, pile, 1n+amt)` in
  `take.go`): stones vanish from the board.
