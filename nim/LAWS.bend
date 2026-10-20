# The laws of Nim. The human states them; PROOF.bend must prove them.
# `bend PROOF.bend` fails while any of them is open or false.

import Base
import ./nim.bend as N

# LAW: a move never creates or destroys stones: whatever the board and
# whatever the move (legal or rejected), the stones it reports taking
# plus the stones left on the board are exactly the stones there before.
law take_conserves:
  for +xs: List<&2, Nat>
  for  mv: N.Take
  {Nat.add(N.taken(xs, mv), N.total(N.take(xs, mv))) == N.total(xs) : Nat}

# LAW: while any stone is left, the computer's move always takes at least
# one, so it never passes and never stalls the game.
law ai_takes:
  for +xs  : List<&2, Nat>
  for  live: N.Live(xs)
  exs  k   : Nat
  {N.taken(xs, N.ai(xs)) == 1n+k : Nat}
