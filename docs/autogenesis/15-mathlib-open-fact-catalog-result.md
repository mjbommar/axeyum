# Mathlib open-fact catalog result

Date: 2026-08-18

## Verdict

**All 214 reviewed source and mutation propositions are now honest open Axeyum
fact-ledger rows. None is proof credit.** The 202 Mathlib declarations are
explicitly external prior art; the twelve generated mutations have unknown
external status. Every evidence array is empty and no `proof_route` is set.

The [fact catalog](../../artifacts/autogenesis/mathlib-nat-int-fact-catalog-v1.json)
and its [generator](../../scripts/create-autogenesis-mathlib-fact-catalog.py)
bind each statement to a stable fact ID, provenance, its reviewed family and
dependency component, and a statement-derived shape label.

## Surface formalization

Mathlib's pretty-printed types are Lean surface propositions, not the
independent kernel's `render_lean` core language. Every new fact therefore uses
`formal.language: lean4-surface`; calling these strings `lean4` would falsely
claim they are kernel-core terms Axeyum can directly admit.

A generated module declares every proposition as an `axiom` after
`import Mathlib`. Exact Lean 4.30/Mathlib v4.30 accepted all 214 types. The
22,670-byte module is retained read-only outside Git at
`/nas3/data/axeyum/autogenesis/sources/mathlib-v4.30.0-nat-int-nursery-surface-v1.lean`
with SHA-256
`a4f51828c0b70709aeef3429400d8fac90f80d5d3164bd8259b1b5fd1fd5995d`.

This gate proves only that each string parses and elaborates as a proposition
in the exact source environment. It supplies no proof body. The first run
failed on `Nat.choose_mono`: standalone replay could not infer a pretty-printed
lambda's binder type. Four explicit binder annotations were added, and the
whole 214-row module was rerun rather than treating pretty-printer output as
portable by assumption.

## Ledger effect

The fact validator now checks 324 rows with zero errors: 220 are open, of which
214 are this catalog. The 202 source rows report `external_status: proved` and
name the pinned Mathlib declaration as prior art; this increases the explicit
import backlog, not the constructed theorem count. Mutations report
`external_status: unknown` and contain no expected truth value or witness.

Direct candidate-to-candidate source proof edges survive as `depends_on` only
when both endpoints passed review. ADR-0478 makes those edges curriculum and
leakage metadata: an accepted Axeyum proof must independently derive any edge
before it can earn admission credit. The machine frontier currently refuses all
214 facts with `no-registered-operation`, which is the correct state before the
nursery split and route experiments exist.

## Statement-shape census

The proof-free catalog labels surface form, not imported proof tactics:

| Statement shape | Count |
|---|---:|
| conditional proposition | 79 |
| unconditional equality | 56 |
| unconditional relation | 35 |
| biconditional | 29 |
| higher-order property | 12 |
| existential witness | 2 |
| negated proposition | 1 |

These broad shapes are diagnostic labels, not yet safe split keys. Joining all
facts that share one of them collapses the complete 214-row population into one
component, so the next increment must define a proof-template risk identity
that is neither vacuous nor so coarse that three partitions become impossible.

## Remaining boundary

The catalog state remains `open-facts-no-splits-no-outcomes`. The next step is a
preregistered split-feasibility analysis over dependency groups, theorem
families, mutation pairs, and family-scoped proof-template risks. Only after
that analysis demonstrates at least three indivisible units may the nursery
manifest freeze train, development, and held-out membership.
