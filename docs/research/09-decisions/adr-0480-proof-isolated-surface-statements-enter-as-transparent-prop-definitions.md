# ADR-0480: Proof-isolated surface statements enter as transparent `Prop` definitions

Status: accepted
Date: 2026-08-18
Index-summary: Elaborate a nursery proposition as the value of a transparent definition, then reject any statement stream containing an axiom, theorem, opaque declaration, quotient primitive, or changed goal identity

## Context

The frozen Mathlib nursery stores propositions as `lean4-surface`. The first
dispatch census found that all 138 train/development rows decline before
execution because authoritative operations consume `lean4` kernel terms or
`smtlib2`, not surface syntax. Proof search cannot be measured until a checked
goal crosses that boundary.

The obvious encoding is unsafe: exporting `axiom target : P` gives the imported
environment an inhabitant of `P`. A producer could close the goal by referring
to the adapter axiom, and the infrastructure would have converted a source
statement into its own answer. Exporting the original Mathlib theorem is worse:
it exposes exactly the held-back proof value.

## Decision

Encode a proposition `P` as the value of a transparent definition:

```lean
def target : Prop := P
```

Official Lean elaborates `P`; official `lean4export` emits the selected
definition and its dependency closure; `axeyum-lean-import` translates and
independently checks the stream. The adapter publishes `target`'s definition
value as the goal expression, not as a declaration that proves the goal.

The stronger `import_statement_ndjson` boundary rejects the whole stream when:

- the exact target is absent, duplicated, universe-polymorphic, or not a
  transparent definition;
- its value does not independently infer to `Prop`; or
- any axiom, theorem, opaque declaration, or quotient primitive appears
  anywhere in the delivered stream.

The external artifact, tracked Lean source, exporter/toolchain identity,
target declaration content identity, and rendered goal digest are bound in one
manifest. A changed proposition may still be a valid `Prop`, so the manifest's
exact goal and declaration identities—not type checking alone—reject that
mutation.

## Evidence

The first train probe adapts
`F:ml430-nat-ascfactorial-zero-fd183202`. The official stream is 52,474 bytes
and 920 records. It contains 55 independently admitted declarations, no axiom,
theorem, opaque, or quotient record, and no imported axiom identity. The target
has five direct declaration dependencies. The checked goal digest is
`87e37902bb8b3958514c5a6831b28ebff2824c8a30fb45601ff47736ee3853d7`.

Five Rust controls cover successful publication, a proof-bearing target, an
unrelated smuggled axiom, a non-`Prop` value, and the wrong target name. Four
manifest-checker controls cover the exact receipt, a changed rendered goal, a
changed target declaration identity, and extra output.

## Consequences

- One nursery proposition now has a real, proof-isolated kernel goal input.
- This is adapter credit only. It does not register a proof producer, establish
  the fact, or change the theorem-count metric.
- Each additional statement shape must pass the same generic boundary; family
  special cases belong in the Lean elaboration source, not the Rust trusted
  checker.
- Proof search and reconstruction should now be exercised on this goal before
  broadening the adapter population.

## Alternatives rejected

- **Export the Mathlib theorem.** Rejected because its value is an answer leak
  and imported proof is not autonomous construction.
- **Export an axiom of the target proposition.** Rejected because it installs
  the answer as an assumption.
- **Trust pretty-printed text.** Rejected because syntax acceptance does not
  create a kernel term or bind elaboration choices.
- **Accept a stream with unrelated proofs.** Rejected because a producer could
  retrieve those proofs even if the target itself were encoded safely.
