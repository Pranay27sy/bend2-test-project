# The laws. The human states them; PROOF.bend must prove them.
# `bend PROOF.bend` fails while any of them is open or false.

import Base
import ./ledger.bend as L

# LAW: a transfer never creates or destroys money: whatever the ledger
# and whatever the transfer (accepted or rejected), the total of all
# balances is the same before and after.
law transfer_conserves:
  for +xs: List<&2, Nat>
  for  tx: L.Transfer
  {L.total(L.transfer(xs, tx)) == L.total(xs) : Nat}

# LAW: neither does any sequence of transfers, from any ledger.
law replay_conserves:
  for  txs: List<&2, L.Transfer>
  for +xs : List<&2, Nat>
  {L.total(L.replay(txs, xs)) == L.total(xs) : Nat}
