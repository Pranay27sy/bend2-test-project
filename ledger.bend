# ledger: a tiny bank. A ledger is a list of balances, one per account,
# indexed from 0n. Balances are Nat, so they are unbounded (no overflow)
# and can never go negative. A transfer moves money between two accounts
# and is rejected (a no-op) unless the sender can cover it and the
# recipient exists. LAWS.bend states that no transfer, and no sequence of
# transfers, ever creates or destroys money; PROOF.bend proves it.
#
#   bend ledger.bend

import Base

# Evidence
# --------
# LE(a, b) is the type of proofs of a <= b, and Has(xs, i) the type of
# proofs that account i exists: Unit when it holds, Empty when it fails.
# The checks below hand back this evidence, so a proof about transfer
# can branch on the very fact the program checked.

def LE(a: Nat, b: Nat) -> Data:
  match a b:
    case 0n b0:
      Unit
    case 1n+a1 0n:
      Empty
    case 1n+a1 1n+b1:
      LE(a1, b1)

# the verdict of a comparison, with its evidence
def le_case(a: Nat, b: Nat) -> Or(LE(a, b), LE(b, a)):
  match a b:
    case 0n b0:
      Inl{Unit{}}
    case 1n+a1 0n:
      Inr{Unit{}}
    case 1n+a1 1n+b1:
      le_case(a1, b1)

def Has(xs: List<&2, Nat>, i: Nat) -> Data:
  match xs i:
    case Nil{} _:
      Empty
    case h <> t 0n:
      Unit
    case h <> t 1n+j:
      Has(t, j)

# whether account i exists, with its evidence
def has_case(xs: List<&2, Nat>, i: Nat) -> Maybe<&2, Has(xs, i)>:
  match xs i:
    case Nil{} _:
      None{}
    case h <> t 0n:
      Some{Unit{}}
    case h <> t 1n+j:
      has_case(t, j)

# Accounts
# --------

# the sum of every balance
def total(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case h <> t:
      Nat.add(h, total(t))

# the balance of account i (0n when it does not exist)
def balance(xs: List<&2, Nat>, i: Nat) -> Nat:
  match xs i:
    case Nil{} _:
      0n
    case h <> t 0n:
      h
    case h <> t 1n+j:
      balance(t, j)

# adds amt to account i
def credit(xs: List<&2, Nat>, i: Nat, amt: Nat) -> List<&2, Nat>:
  match xs i:
    case Nil{} _:
      Nil{}
    case h <> t 0n:
      Nat.add(h, amt) <> t
    case h <> t 1n+j:
      h <> credit(t, j, amt)

# takes amt from account i (Nat.sub stops at 0n: callers must check)
def debit(xs: List<&2, Nat>, i: Nat, amt: Nat) -> List<&2, Nat>:
  match xs i:
    case Nil{} _:
      Nil{}
    case h <> t 0n:
      Nat.sub(h, amt) <> t
    case h <> t 1n+j:
      h <> debit(t, j, amt)

# Transfers
# ---------

type Transfer is Data:
  Transfer{from: Nat, to: Nat, amt: Nat}

# moves amt from `from` to `to` when the sender can cover it (c is Inl)
# and the recipient exists (d is Some); otherwise leaves xs unchanged
def transfer.go(+xs: List<&2, Nat>, +from: Nat, +to: Nat, +amt: Nat,
  c: Or(LE(amt, balance(xs, from)), LE(balance(xs, from), amt)),
  d: Maybe<&2, Has(xs, to)>) -> List<&2, Nat>:
  match c d:
    case Inl{e} Some{h}:
      credit(debit(xs, from, amt), to, amt)
    case _ _:
      xs

def transfer(+xs: List<&2, Nat>, tx: Transfer) -> List<&2, Nat>:
  match tx:
    case Transfer{+from, +to, +amt}:
      transfer.go(xs, from, to, amt, le_case(amt, balance(xs, from)), has_case(xs, to))

# applies every transfer in order
def replay(txs: List<&2, Transfer>, +xs: List<&2, Nat>) -> List<&2, Nat>:
  match txs:
    case Nil{}:
      xs
    case tx <> rest:
      replay(rest, transfer(xs, tx))

# Demo
# ----

def show(xs: List<&2, Nat>) -> String:
  match xs:
    case Nil{}:
      ""
    case h <> t:
      " " ++ Nat.show(h) ++ show(t)

def main() -> IO(Unit):
  +start = {[100n, 50n, 0n] : List<&2, Nat>}
  txs : List<&2, Transfer> = [
    Transfer{0n, 1n, 30n},  # ok: alice pays bob 30
    Transfer{1n, 2n, 80n},  # ok: bob pays carol 80 (he has exactly 80)
    Transfer{2n, 0n, 500n}, # rejected: carol cannot cover 500
    Transfer{0n, 7n, 10n},  # rejected: account 7 does not exist
  ]
  +end = replay(txs, start)
  do IO<Unit>:
    IO.print("before:" ++ show(start) ++ "  (total " ++ Nat.show(total(start)) ++ ")")
    IO.print("after: " ++ show(end) ++ "  (total " ++ Nat.show(total(end)) ++ ")")
