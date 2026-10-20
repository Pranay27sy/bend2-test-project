# nim: the game of Nim, against the computer. A board is a list of piles
# of stones, indexed from 0n. On your turn you take one or more stones
# from a single pile; whoever takes the last stone wins. A move that is
# not legal (no stones, or more than the pile holds, or a pile that does
# not exist) is rejected: the board stays as it was and nothing is taken.
# LAWS.bend states that a move never creates or destroys stones, and that
# the computer always takes at least one; PROOF.bend proves it.
#
#   bend nim.bend           # the computer plays itself
#   cd web && bun index.html  # play it in the browser

import Base

# Evidence
# --------
# LE(a, b) is the type of proofs of a <= b: Unit when it holds, Empty
# when it fails. le_case hands back the verdict with its evidence, so a
# proof about a move can branch on the very fact the game checked.

def LE(a: Nat, b: Nat) -> Data:
  match a b:
    case 0n b0:
      Unit
    case 1n+a1 0n:
      Empty
    case 1n+a1 1n+b1:
      LE(a1, b1)

def le_case(a: Nat, b: Nat) -> Or(LE(a, b), LE(b, a)):
  match a b:
    case 0n b0:
      Inl{Unit{}}
    case 1n+a1 0n:
      Inr{Unit{}}
    case 1n+a1 1n+b1:
      le_case(a1, b1)

# Live(xs): some pile still has a stone (the game is not over)
def Live(xs: List<&2, Nat>) -> Data:
  match xs:
    case Nil{}:
      Empty
    case h <> t:
      match h:
        case 0n:
          Live(t)
        case 1n+p:
          Unit

# Board
# -----

# the stones left on the board
def total(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case h <> t:
      Nat.add(h, total(t))

# the stones in pile i (0n when it does not exist)
def count(xs: List<&2, Nat>, i: Nat) -> Nat:
  match xs i:
    case Nil{} _:
      0n
    case h <> t 0n:
      h
    case h <> t 1n+j:
      count(t, j)

# takes amt stones from pile i (Nat.sub stops at 0n: callers must check)
def remove(xs: List<&2, Nat>, i: Nat, amt: Nat) -> List<&2, Nat>:
  match xs i:
    case Nil{} _:
      Nil{}
    case h <> t 0n:
      Nat.sub(h, amt) <> t
    case h <> t 1n+j:
      h <> remove(t, j, amt)

def is_over(xs: List<&2, Nat>) -> Bool:
  Nat.is_eq(total(xs), 0n)

# Moves
# -----

type Take is Data:
  Take{pile: Nat, amt: Nat}

# a move of 1n+k stones goes through when the pile holds them (c is Inl)
def take.go(+xs: List<&2, Nat>, +pile: Nat, +amt: Nat,
  c: Or(LE(amt, count(xs, pile)), LE(count(xs, pile), amt))) -> List<&2, Nat>:
  match c:
    case Inl{e}:
      remove(xs, pile, amt)
    case Inr{e}:
      xs

def taken.go(-n: Nat, +amt: Nat, c: Or(LE(amt, n), LE(n, amt))) -> Nat:
  match c:
    case Inl{e}:
      amt
    case Inr{e}:
      0n

# the board after a move (unchanged when the move is rejected)
def take(+xs: List<&2, Nat>, mv: Take) -> List<&2, Nat>:
  match mv:
    case Take{+pile, amt}:
      match amt:
        case 0n:
          xs
        case 1n++k:
          take.go(xs, pile, 1n+k, le_case(1n+k, count(xs, pile)))

# the stones a move removes (0n when it is rejected)
def taken(+xs: List<&2, Nat>, mv: Take) -> Nat:
  match mv:
    case Take{+pile, amt}:
      match amt:
        case 0n:
          0n
        case 1n++k:
          taken.go(count(xs, pile), 1n+k, le_case(1n+k, count(xs, pile)))

# The computer
# ------------
# The winning strategy: the nim-sum is the xor of every pile. When it is
# not zero, some pile h has h xor s < h, and shrinking that pile to
# h xor s leaves the opponent a zero nim-sum, from which every move loses.
# The strategy is unproven, so `ai` only trusts it after checking the move
# is legal; otherwise it takes one stone from the first pile that has any.

def nim_sum(xs: List<&2, Nat>) -> U32:
  match xs:
    case Nil{}:
      0
    case h <> t:
      U32.xor(U32.from_nat(h), nim_sum(t))

def pick(-A: Type, c: Bool, a: A, b: A) -> A:
  match c:
    case True{}:
      a
    case False{}:
      b

# the first pile from i on that shrinks to h xor s, as that move
def smart.go(xs: List<&2, Nat>, +i: Nat, +s: U32) -> Take:
  match xs:
    case Nil{}:
      Take{0n, 0n}
    case +h <> t:
      +hu = U32.from_nat(h)
      +to = U32.xor(hu, s)
      pick(Take, U32.is_lt(to, hu), Take{i, Nat.sub(h, U32.to_nat(to))}, smart.go(t, 1n+i, s))

def smart(+xs: List<&2, Nat>) -> Take:
  smart.go(xs, 0n, nim_sum(xs))

# the first pile that has a stone
def first_live(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case h <> t:
      match h:
        case 0n:
          1n+first_live(t)
        case 1n+p:
          0n

# keeps m when it takes something (k is what it takes), else falls back
def guard(+xs: List<&2, Nat>, m: Take, k: Nat) -> Take:
  match k:
    case 0n:
      Take{first_live(xs), 1n}
    case 1n+p:
      m

def ai(+xs: List<&2, Nat>) -> Take:
  +m = smart(xs)
  guard(xs, m, taken(xs, m))

# Demo
# ----

def show(xs: List<&2, Nat>) -> String:
  match xs:
    case Nil{}:
      ""
    case h <> t:
      " " ++ Nat.show(h) ++ show(t)

def show_move(mv: Take) -> String:
  Take{p, a} = mv
  "takes " ++ Nat.show(a) ++ " from pile " ++ Nat.show(p)

def who(b: Bool) -> String:
  pick(String, b, "A", "B")

# the computer plays both sides for at most `fuel` turns; every turn it
# takes a stone or more, so total(start) turns always finish the game
def selfplay(fuel: Nat, +xs: List<&2, Nat>, +me: Bool) -> String:
  match fuel:
    case 0n:
      ""
    case 1n+f:
      +mv = ai(xs)
      +ys = take(xs, mv)
      +line = who(me) ++ " " ++ show_move(mv) ++ " ->" ++ show(ys) ++ "\n"
      pick(String, is_over(ys), line ++ who(me) ++ " takes the last stone and wins",
        line ++ selfplay(f, ys, Bool.not(me)))

def main() -> IO(Unit):
  +start = {[3n, 4n, 5n] : List<&2, Nat>}
  do IO<Unit>:
    IO.print("piles:" ++ show(start) ++ "  (" ++ Nat.show(total(start)) ++ " stones)")
    IO.print(selfplay(total(start), start, True{}))
