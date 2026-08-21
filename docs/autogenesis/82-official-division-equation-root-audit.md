# Official division equation root audit

Date: 2026-08-20

## Result

The first stage of the constructive Euclidean bridge passes. Pinned Lean 4.30
and lean4export 3.1.0 exported the three preregistered official computation
roots in one 186-declaration stream. Axeyum independently admitted the stream
without axioms and measured every selected theorem's complete footprint as
empty:

| Root | Declaration identity | Direct theorem dependencies |
|---|---|---|
| `Nat.div.go.eq_1` | `c31f2e764891ad2ce5d2d1e59638636302c236096f8fefd91dfaa9f289155763` | `Nat.div_rec_fuel_lemma` |
| `Nat.modCore.go.eq_1` | `aaf85a61edef7f6416bfccd8d817ca53c88cf7fe3d5b34bfbf166287e485448d` | `Nat.div_rec_fuel_lemma` |
| `Nat.mod.eq_2` | `47a0f25d2575086bb8d8ad687beca4e69ef71644bb6057f55ec052d5c2084610` | none |

The two remainder identities exactly match the earlier immutable equation pack.
The quotient root is the new evidence: it exposes the synchronized recursive
step needed for the joint invariant without importing the `propext`-bearing
official `Nat.div_add_mod` proof.

## Evidence boundary

The immutable pack is:

`/nas3/data/axeyum/autogenesis/reference-packs/62858ff72-lean430-div-mod-equations-v1/manifest.json`

Its manifest SHA-256 is
`3c53903f86a43e516751d6f440e2472bd987df799db3948ae8cd49754e28a130`.
The directory is mode `0555`; all files are mode `0444`. The tracked checker
binds the plan, producer, pinned tools, stream, audit, theorem identities,
dependencies, footprints, and no-credit counters.

No authored support theorem, exact target submission, executor call, proof
search, semantic receipt, evaluation credit, or ledger write occurred. This
audit establishes only that the planned constructive inputs are admissible.

## Next

Author `joint-div-mod-fuel-invariant-v1` against these roots. Reconstruct it
twice and stop immediately if either identity differs or its footprint is not
empty. Only then lift the invariant to the public official Euclidean equation.

## Verification

```sh
python3 scripts/check-autogenesis-nat-gcd-fib-add-self-euclidean-root-audit-result.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_nat_gcd_fib_add_self_euclidean_root_audit_result
```
