# The proofs. This file imports the ledger (as L) and the claims (as
# Laws) and fills every law they state, so `bend PROOF.bend` is the whole
# verification.
#
# The shape of the argument: debit(xs, i, a) removes exactly a from the
# total when a <= balance(xs, i), and credit(xs, i, a) adds exactly a
# when account i exists. An accepted transfer is a checked debit followed
# by a credit, so the two cancel; a rejected one returns xs itself.

import Base
import ./ledger.bend as L
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
def sub_add(a: Nat, h: Nat, le: L.LE(a, h)) -> {h == Nat.add(a, Nat.sub(h, a)) : Nat}:
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

# Accounts
# --------
# A rewrite %e : P needs e : {new == old}, where P marks old with _;
# Equal.sym flips a lemma stated the other way round.

# credit adds exactly a to the total of a ledger holding account i
def credit_total(xs: List<&2, Nat>, i: Nat, +a: Nat, hs: L.Has(xs, i))
  -> {L.total(L.credit(xs, i, a)) == Nat.add(a, L.total(xs)) : Nat}:
  match xs i:
    case Nil{} _:
      Empty.absurd({L.total(L.credit(Nil{}, i, a)) == Nat.add(a, 0n) : Nat}, hs)
    case +h <> t 0n:
      %add_assoc(h, a, L.total(t)) : {_ == Nat.add(a, Nat.add(h, L.total(t))) : Nat}
      add_swap(h, a, L.total(t))
    case +h <> t 1n+j:
      %Equal.sym(Nat, L.total(L.credit(t, j, a)), Nat.add(a, L.total(t)), credit_total(t, j, a, hs)) : {Nat.add(h, _) == Nat.add(a, Nat.add(h, L.total(t))) : Nat}
      add_swap(h, a, L.total(t))

# debit removes exactly a from the total when a <= balance(xs, i)
def debit_total(xs: List<&2, Nat>, i: Nat, +a: Nat, le: L.LE(a, L.balance(xs, i)))
  -> {Nat.add(a, L.total(L.debit(xs, i, a))) == L.total(xs) : Nat}:
  match xs i:
    case Nil{} _:
      match a:
        case 0n:
          {==}
        case 1n+p:
          Empty.absurd({Nat.add(1n+p, 0n) == 0n : Nat}, le)
    case +h <> t 0n:
      %Equal.sym(Nat, Nat.add(a, Nat.add(Nat.sub(h, a), L.total(t))), Nat.add(Nat.add(a, Nat.sub(h, a)), L.total(t)), add_assoc(a, Nat.sub(h, a), L.total(t))) : {_ == Nat.add(h, L.total(t)) : Nat}
      %sub_add(a, h, le) : {Nat.add(_, L.total(t)) == Nat.add(h, L.total(t)) : Nat}
      {==}
    case +h <> t 1n+j:
      %Equal.sym(Nat, Nat.add(a, Nat.add(h, L.total(L.debit(t, j, a)))), Nat.add(h, Nat.add(a, L.total(L.debit(t, j, a)))), add_swap(a, h, L.total(L.debit(t, j, a)))) : {_ == Nat.add(h, L.total(t)) : Nat}
      %Equal.sym(Nat, Nat.add(a, L.total(L.debit(t, j, a))), L.total(t), debit_total(t, j, a, le)) : {Nat.add(h, _) == Nat.add(h, L.total(t)) : Nat}
      {==}

# a debit keeps every account in place
def has_debit(xs: List<&2, Nat>, i: Nat, j: Nat, -a: Nat, hs: L.Has(xs, j)) -> L.Has(L.debit(xs, i, a), j):
  match xs i j:
    case Nil{} _ _:
      Empty.absurd(L.Has(L.debit(Nil{}, i, a), j), hs)
    case h <> t 0n 0n:
      Unit{}
    case h <> t 0n 1n+k:
      hs
    case h <> t 1n+i1 0n:
      Unit{}
    case h <> t 1n+i1 1n+k:
      has_debit(t, i1, k, a, hs)

# Transfers
# ---------

# an accepted transfer debits then credits the same amount; a rejected
# one hands back xs
def transfer_go_total(+xs: List<&2, Nat>, +from: Nat, +to: Nat, +amt: Nat,
  c: Or(L.LE(amt, L.balance(xs, from)), L.LE(L.balance(xs, from), amt)),
  d: Maybe<&2, L.Has(xs, to)>)
  -> {L.total(L.transfer.go(xs, from, to, amt, c, d)) == L.total(xs) : Nat}:
  match c d:
    case Inl{e} Some{h}:
      %Equal.sym(Nat, L.total(L.credit(L.debit(xs, from, amt), to, amt)), Nat.add(amt, L.total(L.debit(xs, from, amt))), credit_total(L.debit(xs, from, amt), to, amt, has_debit(xs, from, to, amt, h))) : {_ == L.total(xs) : Nat}
      debit_total(xs, from, amt, e)
    case Inl{e} None{}:
      {==}
    case Inr{e} Some{h}:
      {==}
    case Inr{e} None{}:
      {==}

def Laws.transfer_conserves(xs, tx):
  match tx:
    case L.Transfer{+from, +to, +amt}:
      transfer_go_total(xs, from, to, amt, L.le_case(amt, L.balance(xs, from)), L.has_case(xs, to))

# each step keeps the total, so the whole replay does
def Laws.replay_conserves(txs, xs):
  match txs:
    case Nil{}:
      {==}
    case +tx <> rest:
      %Equal.sym(Nat, L.total(L.replay(rest, L.transfer(xs, tx))), L.total(L.transfer(xs, tx)), Laws.replay_conserves(rest, L.transfer(xs, tx))) : {_ == L.total(xs) : Nat}
      Laws.transfer_conserves(xs, tx)
