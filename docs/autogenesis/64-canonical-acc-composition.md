# Canonical Acc composition

## Result

Checked theorem composition now reconstructs the exact native accessibility
package atomically in a private target clone:

```text
Acc
Acc.intro
Acc.rec
```

The source recursor is not copied. The target kernel checks the family and
constructor through `Kernel::add_inductive`, regenerates `Acc.rec`, and the
composition layer requires all three canonical identities to match before it
can publish the completed clone.

This is deliberately not generic recursive-inductive support. The recursive
source package must equal the canonical package produced by Axeyum's checked
logic prelude. An independently checked recursive lookalike also named `Acc`
declines, as do incomplete and mutual packages.

## Exact evidence

The implementation is commit
`3d466b45cc34435702db09604f47d0362eb9d17b`. The immutable observation is:

`/nas3/data/axeyum/autogenesis/probes/3d466b45c-canonical-acc-composition-v14/observation.json`

| Artifact | SHA-256 |
|---|---|
| Mathlib r082 stream | `6afa79d79481403d3e3273ea3eea26b4d1194762f9bd623ec019f8e821323cfd` |
| Composition probe | `9767fd1df4edf4f21551b5b4043809fd3cfe513b342f16635914bcffda9180fe` |
| Composition API | `1ecde3d39ca9f87708d2ef00cac8b2afcb6cf8f9f82dddacbb069c3a0034a121` |
| Observation | `9ed5aceb87ffd73797b48069ba38c1f62db8c001f43aa2bb584b3060136076dd` |

Two executions were byte-identical. The observation directory is mode `0555`
and its file is mode `0444`.

## Package receipt

The dedicated root is the already checked native theorem `Acc.inv`. Against
the proof-isolated r082 target, receipt V5 records:

| Field | Value |
|---|---|
| Outcome | `composed` |
| Added theorem | `Acc.inv` |
| Axiom footprint | empty |
| Receipt | `f4652e351956ef0e2635433dd7cb96a1d4f45707504ec577d97812a192f8ae73` |
| Environment before | `82ac7b0143bdd9891b666a37220fb91b86afc4af4b920d68773d80b5c9348855` |
| Environment after | `c3b2d26b7639d60bde7bf2ab5f441e6acbc4e48b1cc782fe9bde98a2da6fb376` |

Source and independently regenerated target identities are equal:

| Declaration | SHA-256 |
|---|---|
| `Acc` | `a7f555ca45514f16479c09c35a226de796b93f9c023662a70b6ce0977cab9389` |
| `Acc.intro` | `355e47d711d54bd979a69cf06f7870dfde696721235e2b289bfaff844fbdecce` |
| `Acc.rec` | `d996fa21de5fff270d18473af734749f43cb3d2973db71ed0addac037883fc45` |

[ADR-0529](../research/09-decisions/adr-0529-canonical-native-acc-may-be-reconstructed-atomically.md)
defines the boundary. It checks the complete source package before staging and
requires exact regeneration afterward. Failed composition still returns no
owned target, and the caller kernel remains unchanged.

## Validation

The focused composition suite has 13 passing tests. New tests cover successful
regeneration and deterministic reverification, an incomplete package, and a
noncanonical recursive lookalike. The complete importer all-target suite
passes, including its 304-second real-Lean differential run. Importer Clippy
passes with warnings denied; formatting and diff checks are clean.

The manifest checker and its mutation suite additionally pin the immutable
package receipt, exact identity map, next rejection, authority counts, and
unchanged caller environment.

## Subsequent measured gap

The next increment completed that diagnostic. The durable rejection now
renders expected, inferred, weak-head-normal-form, and first-mismatch
expressions without retaining process-local arena IDs. It isolates official
`Nat.mod` versus the native Bool-rollover remainder and measures the complete
92-declaration closure. `Nat.mod_lt` is already reusable; the independent
missing direct consumer is `Nat.dvd_mod_iff`.

See the
[Nat division composition mismatch](65-nat-division-composition-mismatch.md)
for the exact evidence, the rejected zero-delta dependency-cut experiment, and
the Lean 4.30 support audit showing that the official helper proofs carry
`propext`.

## Reproduction

```sh
cargo test -p axeyum-lean-import theorem_composition --lib
cargo test -p axeyum-lean-import --all-targets
cargo clippy -p axeyum-lean-import --all-targets -- -D warnings

cargo run -p axeyum-lean-import \
  --example nat_prelude_composition_probe -- \
  /nas3/data/axeyum/autogenesis/coverage/26fcc2c2f-mathlib-v4.30.0-reflexivity-train-development-v1/streams/r082.ndjson \
  /path/to/observation.json

python3 scripts/check-autogenesis-nat-fib-coprime-premise-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_nat_fib_coprime_premise_plan
```
