When using Bend:
- run `bend guide` to learn it
- use `LAWS.bend` to keep important rules
- run `bend PROOF.bend` before committing
- parallelize the code whenever possible

In this project:
- `LAWS.bend` is the human-owned spec. Never edit, weaken or delete a law
  to make the proofs pass; change the code or the proofs instead.
- `bend PROOF.bend` must print ALL PROOFS CHECK before any commit.
- `bend ledger.bend` runs the demo; the total it prints must not change.
