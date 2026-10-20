# The proofs of LAWS.bend: `bend PROOF.bend` is the whole verification.
#
# take_conserves: a legal move is a checked remove of amt stones, which
# leaves total - amt behind; a rejected one takes 0n and leaves xs.
# ai_takes: the computer keeps the strategy's move only when it takes
# something; otherwise it takes one stone from the first live pile,
# which always goes through.

import Base
import ./nim.bend as N
import ./LAWS.bend as Laws

# Arithmetic
# ----------

def add_assoc(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(Nat.add(a, b), c) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_assoc(p, b, c) : {1n+Nat.add(p, Nat.add(b, c)) == 1n+_ : Nat}
      {==}

def add_succ(a: Nat, -b: Nat) -> {1n+Nat.add(a, b) == Nat.add(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, b) : {2n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

# the first two terms of a triple sum swap
def add_swap(x: Nat, +y: Nat, -z: Nat) -> {Nat.add(x, Nat.add(y, z)) == Nat.add(y, Nat.add(x, z)) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+q:
      %add_succ(y, Nat.add(q, z)) : {1n+Nat.add(q, Nat.add(y, z)) == _ : Nat}
      %add_swap(q, y, z) : {1n+Nat.add(q, Nat.add(y, z)) == 1n+_ : Nat}
      {==}

# taking a from h and adding it back gives h, when a <= h
def sub_add(a: Nat, h: Nat, le: N.LE(a, h)) -> {h == Nat.add(a, Nat.sub(h, a)) : Nat}:
  match a h:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({0n == Nat.add(1n+p, Nat.sub(0n, 1n+p)) : Nat}, le)
    case 1n+p 1n+q:
      %sub_add(p, q, le) : {1n+q == 1n+_ : Nat}
      {==}

# Board
# -----

# remove takes exactly a stones off the total when a <= count(xs, i)
def remove_total(xs: List<&2, Nat>, i: Nat, +a: Nat, le: N.LE(a, N.count(xs, i)))
  -> {Nat.add(a, N.total(N.remove(xs, i, a))) == N.total(xs) : Nat}:
  match xs i:
    case Nil{} _:
      match a:
        case 0n:
          {==}
        case 1n+p:
          Empty.absurd({Nat.add(1n+p, 0n) == 0n : Nat}, le)
    case +h <> t 0n:
      %Equal.sym(Nat, Nat.add(a, Nat.add(Nat.sub(h, a), N.total(t))), Nat.add(Nat.add(a, Nat.sub(h, a)), N.total(t)), add_assoc(a, Nat.sub(h, a), N.total(t))) : {_ == Nat.add(h, N.total(t)) : Nat}
      %sub_add(a, h, le) : {Nat.add(_, N.total(t)) == Nat.add(h, N.total(t)) : Nat}
      {==}
    case +h <> t 1n+j:
      %Equal.sym(Nat, Nat.add(a, Nat.add(h, N.total(N.remove(t, j, a)))), Nat.add(h, Nat.add(a, N.total(N.remove(t, j, a)))), add_swap(a, h, N.total(N.remove(t, j, a)))) : {_ == Nat.add(h, N.total(t)) : Nat}
      %Equal.sym(Nat, Nat.add(a, N.total(N.remove(t, j, a))), N.total(t), remove_total(t, j, a, le)) : {Nat.add(h, _) == Nat.add(h, N.total(t)) : Nat}
      {==}

# Moves
# -----

def take_go_total(+xs: List<&2, Nat>, +pile: Nat, +amt: Nat,
  c: Or(N.LE(amt, N.count(xs, pile)), N.LE(N.count(xs, pile), amt)))
  -> {Nat.add(N.taken.go(N.count(xs, pile), amt, c), N.total(N.take.go(xs, pile, amt, c))) == N.total(xs) : Nat}:
  match c:
    case Inl{e}:
      remove_total(xs, pile, amt, e)
    case Inr{e}:
      {==}

def Laws.take_conserves(xs, mv):
  match mv:
    case N.Take{+pile, amt}:
      match amt:
        case 0n:
          {==}
        case 1n++k:
          take_go_total(xs, pile, 1n+k, N.le_case(1n+k, N.count(xs, pile)))

# The computer
# ------------

# one stone from the first live pile always goes through
def first_live_takes(+xs: List<&2, Nat>, live: N.Live(xs))
  -> {N.taken(xs, N.Take{N.first_live(xs), 1n}) == 1n : Nat}:
  match xs:
    case Nil{}:
      Empty.absurd({N.taken(Nil{}, N.Take{N.first_live(Nil{}), 1n}) == 1n : Nat}, live)
    case h <> +t:
      match h:
        case 0n:
          first_live_takes(t, live)
        case 1n+p:
          {==}

# guard keeps m only when e says m takes 1n+p for some p
def guard_takes(+xs: List<&2, Nat>, +m: N.Take, k: Nat, live: N.Live(xs),
  e: {N.taken(xs, m) == k : Nat})
  -> &j: Nat -> {N.taken(xs, N.guard(xs, m, k)) == 1n+j : Nat}:
  match k:
    case 0n:
      (0n, first_live_takes(xs, live))
    case 1n+p:
      (p, e)

def Laws.ai_takes(xs, live):
  guard_takes(xs, N.smart(xs), N.taken(xs, N.smart(xs)), live, {==})
