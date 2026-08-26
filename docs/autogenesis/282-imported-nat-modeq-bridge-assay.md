# Imported Nat.ModEq bridge assay

Date: 2026-08-26

## Result

The first source-to-source candidate transport assay converts **0 of 3** frozen
arithmetic `Nat.ModEq` siblings. This is not another representation guess: the
assay uses the exact Lean 4.30.0 / Mathlib `c5ea0035` environment that produced
the open facts, exports proof-free target adapters separately from eight public
candidate theorems, imports the original target capsules, and asks the existing
checked transport and bounded-application boundaries to compose them.

Six obvious shortcuts—including `Nat.ModEq.modulus_mul_add`, both additive
congruence lemmas, both modulus-add `Iff` lemmas, and
`Nat.modEq_zero_iff_dvd`—have a measured `propext` footprint. Axeyum therefore
rejects them rather than silently weakening the empty-footprint production
claim. `dvd_refl` is axiom-free but its source closure currently reaches a
recursive `List` declaration absent from the minimal target capsule, so checked
closure composition declines. Only `Nat.ModEq.refl` transports, and it cannot
close any of the three arithmetic targets by itself.

The durable measurement is
[`nat-modeq-imported-bridge-assay-v1.json`](../../artifacts/autogenesis/nat-modeq-imported-bridge-assay-v1.json).
The 2.39 MiB NDJSON remains outside Git at the hash-bound path recorded there.
[`imported_candidate_transport_probe.rs`](../../crates/axeyum-lean-import/examples/imported_candidate_transport_probe.rs)
is the reusable source-to-source control: it keeps target proof isolation,
checks each transported theorem closure and footprint, runs bounded application,
and independently admits any proposed term.

## What this rules out

The native existential relation and imported remainder equality must still not
be conflated. But merely switching to Mathlib's own public theorem names does
not solve the trust problem either: their proofs can carry assumptions Axeyum
does not credit. The system now measures both failures independently:

1. native-to-imported transport fails at the implementation identity boundary;
2. imported public shortcuts fail at their exact assumption or closure boundary.

Neither failure is permission to add `propext` to the trusted base, broaden the
candidate importer, or mark the facts proved.

## Next falsifiable step

Construct one target-local behavior theorem for the exact imported `Nat.mod`
implementation, using only empty-footprint dependencies. The best first shape
is a generic remainder law strong enough to specialize to all three siblings,
not three hand-written target proofs. Export it as an independent candidate,
rerun the unchanged transport probe over the frozen capsules, and require all
three terms to be independently admitted before registering an operation.

The likely construction boundary is the imported `Nat.modCore` recursion spine
already identified by the implementation-demand graph. A useful increment must
either normalize that spine proof-directedly or prove a behavioral contract for
it; another name-level correspondence is not enough.
