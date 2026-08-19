# First proof-isolated statement adapter

Date: 2026-08-18

## Result

The frozen train fact `F:ml430-nat-ascfactorial-zero-fd183202` now crosses from
official Mathlib surface syntax into an independently checked Axeyum kernel
goal without importing the Mathlib theorem proof and without installing the
proposition as an axiom.

The proposition

```lean
∀ (n : ℕ), n.ascFactorial 0 = 1
```

is the value of a transparent `definition : Prop`. Official Lean 4.30.0
elaborates that definition in pinned Mathlib v4.30.0. Official `lean4export`
emits only the selected definition and its declaration closure. The independent
Rust importer then admits the complete stream and publishes the definition
value as a goal expression.

## Measured boundary

| Property | Result |
|---|---:|
| External stream | 52,474 bytes / 920 records |
| Independently admitted declarations | 55 |
| Target direct declaration dependencies | 5 |
| Axioms | 0 |
| Theorems, opaque declarations, quotient primitives | 0 |
| Checked goal SHA-256 | `87e37902bb8b3958514c5a6831b28ebff2824c8a30fb45601ff47736ee3853d7` |

The external stream remains immutable and content-addressed on `/nas3`; Git
stores the Lean adapter source, toolchain and exporter identities, result
manifest, generic importer boundary, and negative controls.

## Fail-closed controls

The Rust boundary rejects a target theorem, an unrelated smuggled axiom, a
non-`Prop` definition value, and a missing target name. The artifact checker
also rejects a changed goal digest, changed target declaration identity, or
extra receipt output. This distinction matters because a changed proposition
can remain perfectly well typed; type checking alone cannot bind it to the
frozen fact.

## Credit and next arrow

This is statement-adapter credit, not proof credit. The fact remains open, no
producer operation is registered, and the dispatch census classifies the row as
`statement-adapter-ready:no-authoritative-producer`.

The goal is intentionally a small definitional equation. The next bounded
increment should test whether a generic kernel reflexivity producer can build
`fun n => rfl` in the imported environment, independently check the candidate,
and emit a receipt that cannot reference the target definition as a proof.

## Reproduction

```sh
cargo test -p axeyum-lean-import --test statement_adapter
python3 -m unittest scripts.tests.test_check_autogenesis_statement_adapter
python3 scripts/check-autogenesis-statement-adapter.py
python3 scripts/create-autogenesis-nursery-dispatch-baseline.py --check
```
