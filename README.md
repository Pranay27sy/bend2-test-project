# Bend 2 Bank Ledger

A tiny bank written in [Bend 2](https://github.com/HigherOrderCo/Bend),
with a **machine-checked proof that money is never created or destroyed**.

| File         | Who owns it | What it is                                            |
|--------------|-------------|-------------------------------------------------------|
| `ledger.bend`| code        | accounts, `credit`, `debit`, `transfer`, `replay`, demo |
| `LAWS.bend`  | human       | the rules the ledger must never break                 |
| `PROOF.bend` | AI / code   | the proofs that every law holds                       |
| `AGENTS.md`  | human       | instructions for coding agents working on this repo   |
| `nim/`       | code + proofs | a playable Nim game with its own laws ([README](nim/README.md)) |

## The model

- A ledger is a list of balances (`List<&2, Nat>`), one per account, indexed
  from `0n`.
- Balances are `Nat`, so they are unbounded (no overflow) and can never go
  negative.
- `transfer(xs, Transfer{from, to, amt})` moves `amt` from `from` to `to`. It
  is **rejected** (leaves the ledger unchanged) unless the sender can cover the
  amount *and* the recipient exists. The checks return evidence (`LE`, `Has`),
  so the proof can branch on the very facts the program checked.
- `replay(txs, xs)` applies a list of transfers in order.

## The laws

```python
law transfer_conserves:              # one transfer, accepted or rejected,
  for +xs: List<&2, Nat>             # from any ledger,
  for  tx: L.Transfer                # never changes the total
  {L.total(L.transfer(xs, tx)) == L.total(xs) : Nat}

law replay_conserves:                # neither does any sequence of them
  for  txs: List<&2, L.Transfer>
  for +xs : List<&2, Nat>
  {L.total(L.replay(txs, xs)) == L.total(xs) : Nat}
```

These hold for **every** ledger and **every** sequence of transfers. They are
proved by induction, not by running examples.

## Run it

```bash
curl -fsSL https://bend-lang.com/install.sh | sh   # install Bend

bend ledger.bend     # run the demo
bend PROOF.bend      # check the proofs -> ALL PROOFS CHECK
bend PROOF.bend --verdict   # re-check with the Lean-verified kernel (needs Lean 4.34.0)
```

Demo output:

```
before: 100 50 0  (total 150)
after:  70 0 80  (total 150)
```

Two transfers go through. An overdraft and a payment to a missing account are
rejected, and the total stays at 150.

## Why the laws matter: a bug they catch

`Nat.sub` stops at `0n`. If you drop the balance check in `transfer.go`
(accept the transfer whether or not the sender can cover it), the program
still compiles and runs, but it prints money out of thin air:

```
before: 100 50 0  (total 150)
after:  570 0 0  (total 570)
```

`bend PROOF.bend` refuses that change with **SOME PROOFS FAIL** and points at
the exact case: an unchecked debit followed by a credit.

## Ideas for next laws

- `overdraft_rejected`: a transfer larger than the sender's balance leaves the
  ledger unchanged.
- `bystanders_untouched`: a transfer never changes an account other than `from`
  and `to`.
- Deposits and withdrawals, with `total(after) + withdrawn == total(before) + deposited`.
- A parallel `total` (split the list, sum both halves at once) with a law that
  it agrees with the sequential one.
