# Proof-free type-slice feasibility

Date: 2026-08-19

## Result

The first bottom-up dependency measurement finds a clean proposition-facing
type boundary for all 138 unsealed Mathlib statements. In particular, all 114
rows rejected by the strict statement adapter have zero theorem, axiom, opaque,
or quotient declarations in their syntactic type closure. Their trusted
declarations enter only after following implementation bodies.

This is a feasibility result, not 114 newly admitted goals. The analyzer does
not rewrite a proposition or ask the independent kernel to check an abstraction.

| Boundary | Result |
|---|---:|
| Train/development targets | 138 |
| Prior trusted-declaration rejections | 114 |
| Type closures with a trusted declaration | 0 |
| Prior rejections with a syntactically clean type closure | 114 |
| Full implementation-closure declaration occurrences | 67,099 |
| Type-closure declaration occurrences | 1,806 |
| Type-closure declarations per target | 2 min / 8 median / 80 max |
| Definition occurrences at an abstraction boundary | 962 |
| Held-out targets inspected | 0 |

The full 1.0 MiB per-row observation is stored outside Git at
`/nas3/data/axeyum/autogenesis/type-slice/26fcc2c2f-mathlib-v4.30.0-feasibility-v1/observation.json`.
Its bytes, inner canonical identity, analyzer, source mapping, and earlier
coverage observation are bound by
[`mathlib-type-slice-feasibility-v1.json`](../../artifacts/autogenesis/mathlib-type-slice-feasibility-v1.json).

## What the measurement means

The current `lean4export` files are broad checked environments. For a target
`definition : Prop`, the analyzer starts from the definition's type and value.
The implementation closure follows both the type and body of every reached
declaration. The proposed type boundary follows the target proposition, then
only the declared types of constants it reaches. It never silently removes a
trusted declaration directly named by that boundary; the negative control
keeps such a declaration visible and rejecting.

The 67,099-to-1,806 reduction explains the prior failure mode. It does not yet
settle how a concrete Mathlib constant is represented after its body is
excluded. That is the semantic seam, not a serialization detail.

## Top-down trust contract for the checked slice

A public type-slice operation should be accepted only if all of the following
hold:

1. The original stream digest, target, exporter/Lean identities, and every
   abstracted constant's instantiated type identity are in a receipt.
2. A fresh kernel, not the broad source environment, checks the sliced goal.
3. A constant whose instantiated type itself inhabits `Prop` is rejected. A
   theorem cannot become an unnamed premise by being relabeled as a parameter.
4. Universe instances are distinct identities; abstraction by rendered name
   alone is insufficient.
5. Required inductive packages and transparent computation are copied in
   dependency order. Missing reduction behavior yields a decline, never a
   guessed equivalence.
6. The generalized sliced proposition and the original concrete proposition
   have an independently checked specialization relation before the latter can
   receive ledger credit.
7. The producer sees only the fresh sliced kernel. Final proof closure remains
   axiom-free and theorem-dependency-free under the ordinary audit.

This contract needs an ADR before it becomes public authority because it changes
the meaning of “the imported statement” from a concrete environment expression
to an explicitly generalized proposition plus a specialization receipt.

## Sequencing

### T1 — freeze the diagnostic boundary

- Keep the source archive immutable and the observation separate.
- Gate the 138-row population, stream identities, held-out exclusion, exact
  114/138 counts, and analyzer identity.
- Keep malformed topology, duplicate targets, direct theorem references, and
  helper-body theorem references as adversarial tests.

Exit: the syntactic opportunity is reproducible and cannot be mistaken for
proof credit. This document and its manifest satisfy T1.

### T2 — specify the semantic operation

- Write an ADR for explicit parameter abstraction and specialization.
- Define a versioned receipt with `(name, universe arguments, type identity)`
  for every abstracted constant.
- Decide which checked inductive/definition declarations are copied and which
  are abstracted; state the reduction budget and fail-closed cases.
- Add a proposition-valued-assumption control and an identity-collision control.

Exit: two independent implementations can agree on the sliced goal and receipt
without consulting a proof outcome.

### T3 — construct a fresh checked slice

- Add kernel support to clone the required name/level/expression/declaration
  subgraph into a fresh arena, or equivalently reconstruct it from a canonical
  slice artifact.
- Replace eligible body-bearing constants by explicit `Pi` parameters in
  dependency order and independently infer the closed result as `Prop`.
- Reject direct proposition assumptions, quotient leakage, unsupported
  projections, cyclic abstraction types, and missing transparent reduction.
- Prove determinism with record-order and unused-environment mutations.

Exit: at least one formerly rejected train row enters the bounded producer from
a fresh proof-free kernel; its held-out analogue remains unopened.

### T4 — validate specialization and useful coverage

- Construct and check a proof that specializes the generalized theorem back to
  the exact source proposition without importing an answer theorem.
- Re-run the 138-row census and report adapter, producer, kernel, and assurance
  outcomes separately.
- Freeze policy on train/development, then open held-out exactly once under the
  preregistered operation and budgets.

Exit: the flywheel receives exact-fact evidence, not merely a stronger but
different generalized theorem, and no trusted dependency is hidden by the
slice.

## Reproduction

```sh
python3 -m unittest scripts.tests.test_analyze_autogenesis_type_slices
python3 scripts/check-autogenesis-type-slice-feasibility.py
```
