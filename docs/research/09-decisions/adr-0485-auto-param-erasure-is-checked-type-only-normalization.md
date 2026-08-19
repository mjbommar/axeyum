# ADR-0485: `autoParam` erasure is checked type-only normalization

Status: accepted
Date: 2026-08-19
Index-summary: Strip only canonically defined saturated autoParam annotations from retained declaration types after source-kernel defeq checking; never erase arbitrary defaults or values

## Context

The first semantic Mathlib type-slice replay accepts 128 of 138 frozen
train/development statements. All ten declines are
`TrustedRetainedClosure`: the exact atomic closure of `Semiring`, `Preorder`,
or `Monoid` reaches a theorem through a structure constructor field annotated
with `autoParam`.

This is a serialization boundary, not yet a mathematical dependency. Lean
4.30.0 commit `d024af099ca4bf2c86f649261ebf59565dc8c622` defines

```lean
abbrev autoParam.{u} (α : Sort u) (tactic : Lean.Syntax) : Sort u := α
```

and documents that the gadget affects elaboration only. Lean's own
`Expr.consumeTypeAnnotations` replaces a saturated `autoParam α tactic` with
`α`. Structure elaboration removes the annotation when it consumes inherited
fields, then deliberately restores it on constructor binders so the surface
elaborator can run the recorded tactic when an argument is omitted.

The independent kernel correctly follows the serialized tactic expression.
For the measured structures that path runs through `Lean.Syntax`, `String`,
UTF-8 helpers, and `Nat` decision procedures before reaching a theorem. Simply
excluding those dependencies would make the exported constructor type refer to
missing declarations. General delta reduction would be much broader than the
measured problem and could silently change computation or proof dependencies.

This closes the follow-up question in the
[research register](../08-planning/research-questions.md) and narrows
[ADR-0484](adr-0484-proof-free-type-slices-are-generalized-and-exactly-specialized.md)
without weakening its atomic-retention rule.

## Decision

The proof-free type-slice route may erase a saturated `autoParam α tactic`
application **only inside a retained declaration type**, replacing it with
`α`, under all of these fail-closed conditions:

1. the referenced declaration is exactly the root name `autoParam`;
2. it is one transparent `abbrev` with one universe parameter and the canonical
   dependent type and lambda body above;
3. the occurrence is a fully applied two-argument annotation with the matching
   universe instance;
4. the source kernel infers both original and replacement expressions and
   checks their types and values definitionally equal; and
5. the normalized atomic unit is independently admitted by the ordinary fresh
   importer before any producer runs.

Dependency selection and wire emission must share one normalization result.
The tactic argument and `autoParam` declaration disappear from reachability
only for occurrences actually rewritten. Partial applications, malformed
universe applications, a noncanonical declaration with the same name, or an
occurrence in a definition value or recursor rule remain exact and may still
decline.

Each receipt records the policy version, canonical `autoParam` declaration
identity, source and normalized declaration identities, rewritten occurrence
count, and fresh retained-environment identity. Exact specialization continues
in the unmodified source kernel. No normalized declaration is treated as the
same content identity as its source declaration merely because it has the same
name.

This policy is qualified only for Lean 4.30.0. A new Lean version must rerun the
declaration-shape control and train/development regression before reuse.

`optParam`, `outParam`, `semiOutParam`, metadata nodes, arbitrary reducible
definitions, declaration values, theorem bodies, and quotient packages are out
of scope. Lean's helper handles several of those annotations, but this decision
does not inherit authority from a broader upstream convenience function.

The normalized environment is a kernel-term producer environment, not a
surface-elaboration environment. A producer must supply explicit terms; it may
not rely on the erased tactic to synthesize a missing constructor field.

## Evidence

- The immutable checked replay contains 128 accepted receipts and ten exact
  typed declines, with no held-out read, proof execution, or ledger write.
- In `r057.ndjson`, the `Semiring` inductive record's constructor type contains
  `autoParam`; its family and recursor types do not. The same measured pattern
  occurs in the relevant `AddMonoid`, `Monoid`, `Semiring`,
  `NonAssocSemiring`, and `AddMonoidWithOne` constructor records.
- Lean 4.30.0's `Init/Tactics.lean` calls `autoParam` an elaboration-only gadget;
  `Lean/Expr.lean` supplies the exact annotation consumption rule; and
  `Lean/Elab/Structure.lean` removes and restores the annotation specifically
  around constructor elaboration.
- The source hashes used for this decision are
  `3f6b6e0855d14e26d9122fd9dd7af1eec10cb5874628fed96f0e2cbe4b888009`,
  `517126a4dd21436963fa35548e1a1e52d3c5c7c2aa5feecf6cfc78e9272d5945`,
  and `0871762b96558d31554d23f62493f2bc7dfdee69d7c5180a2bfedae7808db596`
  for those three files respectively.

The implementation gate must add positive controls for canonical nested
annotations and official structure constructors, plus negative controls for a
same-named noncanonical definition, partial application, wrong universe arity,
value-position occurrence, unrelated abbreviations, and a normalization whose
fresh import or source-kernel definitional equality fails.

## Alternatives

- **Retain the entire tactic closure.** Rejected because it exposes proof-bearing
  elaborator machinery to a producer that consumes only kernel terms.
- **Drop dependencies without rewriting the constructor type.** Rejected
  because the emitted declaration would be incomplete.
- **Normalize every reducible definition.** Rejected because it changes a
  narrow evidence-driven exception into an unbounded partial evaluator.
- **Apply Lean's full annotation cleanup wholesale.** Rejected because
  `optParam`, output-parameter annotations, and metadata have not caused this
  measured boundary and carry distinct elaboration contracts.
- **Give all ten structures hand-authored clean replacements.** Rejected because
  name-based replicas would hide the semantic relation and would not generalize
  to future measured structures.

## Consequences

- The next code boundary is small: canonical annotation recognition, checked
  type normalization, shared normalized reachability/emission, and receipts.
- Atomic inductive packages remain atomic. Only their checked declaration types
  may differ, and every difference is explicit in evidence.
- The ten declines become a regression population, not an assumed 10-row gain.
  Coverage changes only after all previous 128 receipts remain valid.
- Surface elaboration and kernel production are now explicitly distinct. A
  future producer that needs elaboration must receive a separate, audited
  environment rather than silently reusing this normalized one.
