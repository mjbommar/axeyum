# ADR-0486: `autoParam` normalization includes checked recursor binder domains

Status: accepted
Date: 2026-08-19
Index-summary: Extend canonical autoParam normalization only to lambda and Pi binder domains in recursor rules, checking each complete rule defeq before fresh admission

## Context

[ADR-0485](adr-0485-auto-param-erasure-is-checked-type-only-normalization.md)
authorized canonical `autoParam` erasure in retained declaration types. The
implementation independently admits its synthetic normalized stream, but the
complete train/development replay remains 128/138.

The negative result localizes the remaining edge. After type-only
normalization, the exact `Semiring` closure still reaches `autoParam` only from
the RHS of the first reduction rule for `AddMonoid.rec`, `Monoid.rec`, and
`Semiring.rec`. Lean's structure elaborator copies the constructor fields into
the generated recursor rule lambdas; their binder domains retain the same
elaboration-only annotation. For `r057`, type-only normalization changes six
declarations and twelve unique nodes, while the rule RHS retains another twelve
annotations and the entire `Lean.Syntax` theorem-bearing closure.

This is narrower than arbitrary value normalization. A recursor rule is kernel
computation data emitted atomically with its inductive group. Changing it
without checking the complete rule could change reduction semantics.

## Decision

ADR-0485's canonical Lean 4.30 declaration-shape and saturated-application
requirements also apply to `autoParam` occurrences in **lambda and Pi binder
domains inside recursor-rule RHS expressions**.

For each changed rule, the source kernel must:

1. rewrite only binder-domain annotations, traversing rule bodies solely to
   find nested binders;
2. leave direct value-position applications, ordinary definition values,
   recursor applications, constructor names, field counts, and non-binder
   expression nodes exact;
3. infer the complete source and normalized RHS expressions;
4. check both their inferred types and complete values definitionally equal;
5. use the same normalized RHS for dependency selection and wire emission; and
6. require the ordinary importer to re-admit the complete normalized atomic
   inductive package.

The transport receipt binds the source and fresh canonical identities of every
changed constructor or recursor declaration, the canonical source `autoParam`
identity, and the total rewritten-node count. Exact specialization still runs
in the unmodified source kernel.

Direct `autoParam` terms in a rule body, let-declaration type annotations,
ordinary definition/theorem/opaque values, quotient rules, other annotations,
and arbitrary delta normalization remain out of scope. This refines rather than
supersedes ADR-0485.

## Evidence

- The type-only 138-row replay remains exactly 128 accepted and ten typed
  selection declines; it issues no normalized receipt.
- A direct normalized `Semiring` closure probe shows the surviving shortest
  path as `Semiring.rec` rule 0 to `autoParam`, `Lean.Syntax`, `String`, UTF-8
  helpers, `Nat.decLe`, and theorem dependencies.
- Binder-domain normalization rewrites 24 unique nodes across
  `AddMonoid.mk/rec`, `Monoid.mk/rec`, and `Semiring.mk/rec`. The resulting
  84-declaration `Semiring` closure is independently imported with zero axioms.
- The full opt-in v3 train/development replay accepts 138/138. Ten v2 receipts
  bind 164 rewrites across eight changed declaration names; the prior 128 rows
  remain accepted with their v1 receipt shape. This observation remains a probe
  until rerun from committed tooling and bound by an immutable checker.

Positive controls cover type-only normalization, binder-domain-only
normalization, fresh independent import, and the exact official `Semiring`
closure. Negative controls retain same-named noncanonical definitions,
value-position applications, and direct rule-body applications.

## Alternatives

- **Stop at type-only normalization.** Rejected because the measured remaining
  dependency is the same copied elaboration annotation in generated rule
  binders, not a distinct mathematical dependency.
- **Rewrite every recursor RHS occurrence.** Rejected because term-position
  occurrences have not been shown elaboration-only.
- **Regenerate recursors from normalized constructors.** Rejected because that
  introduces a second recursor generator and a larger equivalence obligation;
  the existing complete-rule defeq check is smaller.
- **Treat recursor rules as proof bodies and omit them.** Rejected because they
  define kernel computation and are part of the atomic inductive package.

## Consequences

- The ten declines become accepted proof-free goal boundaries without changing
  any source proposition or granting proof credit.
- Transport evidence must distinguish declaration-type rewrites from
  recursor-rule binder rewrites even when both contribute to one fresh
  declaration identity.
- Future Lean versions must requalify both the `autoParam` definition and the
  generated structure/recursor shape.
- The next flywheel measurement can finally attach proof producers across the
  entire unsealed 138-row population; held-out remains sealed until producer
  policy and budgets freeze.
