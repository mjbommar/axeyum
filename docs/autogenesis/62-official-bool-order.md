# Official Bool order

## Result

Axeyum's native Bool package now uses official Lean's constructor order:
`Bool.false`, then `Bool.true`. Every branch-sensitive native proof and
solver-side Lean reconstruction site migrated with it. The change preserves
the intended computation while removing a foundational representation mismatch
that blocked checked native-library composition over the Mathlib 4.30.0 r082
environment.

The measurable library result is exact: `Bool`, `Bool.false`, `Bool.rec`, and
`Bool.true` move into the exact-overlap class. The unchanged `Nat.dvd_gcd`
control passes Bool and reaches the next genuine statement mismatch,
`Nat.mod_lt`.

## Exact evidence

The implementation tree is
`772646c0d1a0c6ebca302c37a42cf2bb2f5030ee`; the focused commits are
`502184d3f`, `012c6b4f6`, and `866add778`. The native prelude source SHA-256 is
`8bc2090e18e8433234e9262a1d4e605ff84c448b79aebeef88153e1d0b3b7a0b`.

The immutable observation is:

`/nas3/data/axeyum/autogenesis/probes/772646c0d-official-bool-order-v11/observation.json`

| Artifact | SHA-256 |
|---|---|
| Mathlib r082 stream | `6afa79d79481403d3e3273ea3eea26b4d1194762f9bd623ec019f8e821323cfd` |
| Composition probe | `d67f884e8bf38ce1df694f43a1c3fa86fd9d0d329a01dc0e4324fa4cf21fda40` |
| Composition API | `3d5990a4a26162d9002d36125d4510cdf0965696679681cc265cce22dfa27fe7` |
| Native prelude | `8bc2090e18e8433234e9262a1d4e605ff84c448b79aebeef88153e1d0b3b7a0b` |
| Observation | `2f65c2c86e883269f60f96ba3e396f82ba044d1d99959a89bc47e2ada839c264` |

The overlap partition changes from `7 / 18 / 10 / 8` to
`11 / 15 / 10 / 7` for exact, alpha-compatible, kernel-shape-compatible, and
unresolved overlaps. Total overlaps remain 43. Imports remain 261 declarations
and 52 theorems; the native prelude remains 198 declarations. Authority remains
15 kernel submissions, zero proof-search invocations, and zero ledger writes.

## Blast radius and validation

The migration covered the native Bool declaration, Nat/Int/String prelude
proofs, and all current solver reconstruction sites for lexicographic,
regex, word, datatype, direct, quantified-BV, counterexample-cover, and
equality-partition evidence. Official-order fixtures and golden bodies were
regenerated only where their semantic branch order changed.

The first full gate was useful negative evidence: it found 18 missed
solver-side sites. After those were corrected, the authoritative pre-push gate
passed the 1,248-test solver sweep, 31 non-Lean kernel integration suites, all
six golden module suites, official-Lean evidence integration, and String
front-door suites. The complete ignored official-Lean crosscheck also passed,
as did replay of 15 committed Lean modules plus a rejecting mutation. Kernel
inventories report 139 Nat theorems and 57 derived, zero asserted Int theorems;
logic, Nat, Int, and String trusted surfaces remain empty.

## Trust boundary

[ADR-0527](../research/09-decisions/adr-0527-native-bool-follows-official-lean-constructor-order.md)
fixes the constructor order and requires semantic call-site migration. It does
not permit a composer to reorder arbitrary recursor branches, graft source
declarations, or accept alpha/shape compatibility as proof. Every added theorem
and definition still passes the ordinary target-kernel gates established by
the preceding composition decisions.

The manifest checker pins the implementation tree, prelude digest, exact Bool
package, complete overlap partition, immutable observation, unchanged
composition receipts, and exact fail-closed negative-control error. Mutation
tests break each new binding and require rejection.

## Next measured gap

The unchanged `Nat.dvd_gcd` control now declines with:

```text
TypeShapeMismatch {
  name: "Nat.mod_lt",
  source_sha256: "3db0db05b1489611b353bba15a67d2922c625d136e472e4d33d04a30597f8a41",
  target_sha256: "22c2f033e81299ffa23212d921c3e90552bfc1e5d310fbc7c12cfde5a6af6bc2"
}
```

The imported theorem says `0 < y -> x % y < y`; the native theorem says
`n % (k + 1) < k + 1`. This is a specialization relationship, not constructor
permutation. The next increment should construct the positive-successor premise
and apply the imported general theorem in the target kernel, or decline with an
equally exact blocker. It must remain theorem-specific until evidence supports
a reusable checked adapter contract.

## Reproduction

```sh
CARGO_TARGET_DIR=/data0/axeyum/codex-bool-order-target \
  cargo run -p axeyum-lean-import \
  --example nat_prelude_composition_probe -- \
  /nas3/data/axeyum/autogenesis/coverage/26fcc2c2f-mathlib-v4.30.0-reflexivity-train-development-v1/streams/r082.ndjson \
  /path/to/observation.json

python3 scripts/check-autogenesis-nat-fib-coprime-premise-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_nat_fib_coprime_premise_plan
```
