# Public checked theorem composition

Date: 2026-08-20

## Result

The first native-library composition is no longer probe-local. ADR-0523's
public `axeyum-lean-import` boundary accepts a source kernel, a target kernel,
and explicit theorem roots, and returns an owned completed target only after
every missing theorem has passed the target kernel's ordinary trusted admission
gate.

The exact `r082` replay selected the eleven-declaration closure of
`Nat.add_comm`. Eight declarations already existed in the target. Two (`Nat`
and `Nat.zero`) had exact source/target declaration identities; six had
different declaration content but the same kernel-relevant type shape. The API
then independently admitted `Nat.zero_add`, `Nat.succ_add`, and `Nat.add_comm`,
all with empty kernel-derived axiom footprints.

The completed target changed from environment identity
`82ac7b0143bdd9891b666a37220fb91b86afc4af4b920d68773d80b5c9348855`
to
`bda5fa7e1660db1635ea2e019775ead03663cf3676e6a7695ea5352f8572c9bf`.
The canonical composition receipt is
`91e372a6217c7299c85ca0acdb29770d875200009282b41d33e29aaf56d30c7f`.

## Trust boundary

Type-shape compatibility authorizes only an admission attempt. It does not
authorize declaration replacement, proof grafting, or treating the source
identity as the target identity. The target is cloned privately, each proof is
rebuilt against target handles, and the clone is published only after the whole
slice succeeds. A receipt verifier recomposes from the original source and
target and requires both the receipt and completed environment identity to
match.

V1 intentionally admits only missing theorems. Missing definitions, axioms,
opaque declarations, and inductive declarations decline. Duplicate or missing
roots, non-theorem roots, free variables, incompatible reused types, and a
trusted-gate failure after partial staging also decline. Tests require the
caller's target to remain unchanged across failure and distinguish exact reuse
from binder-info-only type compatibility.

## Horizon and next step

This closes one architectural arrow, not the Fibonacci target. Six of the seven
required native roots still reach incompatible imported representations;
`Nat.dvd_add_iff_right` is the smallest remaining closure and reaches
`Nat.le_trans` and `Nat.zero_le`. The next bottom-up increment should select one
of those representation bridges by measured downstream unlock, state its
translation contract explicitly, and retry the original root. Expanding the
public API to definitions or inductives is justified only by that concrete
demand and requires a new reviewed boundary.

No proof search ran, no proof body was displayed, no held-out partition was
inspected, and no fact-ledger row changed. The three kernel submissions are
library-composition evidence, not target-proof or evaluation credit.

## Evidence

The immutable observation is:

`/nas3/data/axeyum/autogenesis/probes/0bcbe935d-nat-add-comm-public-api-receipt-v7/observation.json`

It is mode `0444` inside a mode `0555` directory. The tracked manifest binds
its SHA-256, the probe SHA-256, and the public API SHA-256. Verify the complete
boundary with:

```sh
python3 scripts/check-autogenesis-nat-fib-coprime-premise-plan.py
cargo test -p axeyum-lean-import --lib
```
