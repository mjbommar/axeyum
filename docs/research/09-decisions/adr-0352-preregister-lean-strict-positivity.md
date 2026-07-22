# ADR-0352: Preregister Lean 4.30 strict positivity before recursive admission widens

Status: proposed

Date: 2026-07-22

## Context

TL2.11 and T6.0.2 require a real strict-positivity checker before TL2.12 admits
recursive-indexed or reflexive/higher-order fields. Today those families decline
for unrelated feature-support reasons. That is safe while the deferrals remain,
but it is not a positivity argument: removing either deferral without a separate
guard would turn a completeness change into a soundness change.

The completed
[official construct matrix](../../plan/lean-official-construct-matrix-final-2026-07-22.md)
freezes the exact `MiniVector` and `MiniAcc` positive forms and one official
non-positive source rejection. The next step must turn that ordering constraint
into a trusted, independently tested kernel invariant without admitting either
positive deferred family yet.

This closes the open strict-positivity question in
[`research-questions.md`](../08-planning/research-questions.md) only after the
exit gates below pass.

## Decision

Implement Lean 4.30's safe single-family constructor-field positivity rule as a
separate fail-closed preflight in `Kernel::add_inductive`, before the provisional
inductive declaration is inserted into the environment.

For each non-parameter constructor field, after WHNF:

1. a field with no occurrence of the family is positive;
2. a `Pi` field is positive only when its domain contains no family occurrence
   and its instantiated codomain is recursively positive;
3. a non-`Pi` field containing the family is positive only when it is the exact
   declared family application at the declared universe levels, with the fixed
   parameters in order, exactly the declared number of indices, and no family
   occurrence inside an index;
4. an occurrence in a `Pi` domain returns a typed non-positive error;
5. every other occurrence returns a distinct typed invalid-occurrence error.

The initial checker is deliberately single-family because `add_inductive`
currently admits one family at a time. TL2.13 must generalize the occurrence set
atomically to the complete mutual group before mutual admission. Unsafe Lean
inductives are out of scope; Axeyum has no unsafe-inductive admission mode.

The checker does not generate induction hypotheses, recursors, or computation
rules. Existing positive-but-unsupported recursive-indexed and reflexive fields
must pass positivity and then stop at their existing typed feature declines.
Direct-recursive families must continue to admit and compute byte-for-byte as
before.

## Evidence

The pinned authority is Lean 4.30 commit
`d024af099ca4bf2c86f649261ebf59565dc8c622`, specifically
[`is_valid_ind_app` and `check_positivity`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/src/kernel/inductive.cpp#L339-L409).
The same source shows the guard runs on every non-parameter constructor field
before constructors and recursors are declared.

Existing preregistered evidence supplies:

- accepted direct-recursive, recursive-indexed, and reflexive official source
  families;
- exact exported `MiniVector` and `MiniAcc` core shapes;
- an official rejection of `NonPositive.mk : (NonPositive -> Atom) ->
  NonPositive` with the kernel's non-positive-occurrence diagnostic;
- completion-only importer publication and an immutable direct-recursive
  control.

The implementation/result plan is
[`lean-strict-positivity-tl2.11-plan-2026-07-22.md`](../../plan/lean-strict-positivity-tl2.11-plan-2026-07-22.md).

## Exit gates

This ADR may be accepted only when:

1. the exact Lean commit, rule, case grammar, resources, and stop conditions are
   committed before product implementation;
2. positivity runs before provisional inductive environment insertion;
3. non-positive and invalid occurrences have stable, separate `KernelError`
   variants with exact constructor and field identity;
4. direct-recursive positives still admit and compute;
5. valid recursive-indexed and reflexive official shapes pass positivity but
   retain their existing feature declines;
6. negative domain, mixed-polarity, deep-negative, wrong-parameter, nested-
   application, and self-referential-index families reject transactionally;
7. a deterministic generated polarity grammar repeats byte-identically and
   exercises every rule/decline edge;
8. pinned Lean and Axeyum agree on the registered positive/negative source
   population at the appropriate assurance layer;
9. focused tests, clippy, rustdoc, parity/document, foundational-resource, and
   link gates pass under the repository's bounded-resource policy;
10. PLAN, STATUS, both Lean roadmaps, T6.0.2, and the research question are
    synchronized before the final push and local/tracking/remote refs agree.

## Alternatives

### Admit recursive-indexed fields and rely on recursor self-checking

Rejected. A generated recursor type can be well-typed even when the inductive
declaration itself violates strict positivity. Positivity is an admission
condition, not a consequence of recursor generation.

### Keep relying on `ReflexiveOrNestedNotSupported`

Rejected. That error is a feature boundary whose removal is already scheduled.
It cannot remain the soundness mechanism for the feature it blocks.

### Check only syntactic negative arrows

Rejected. Lean checks WHNF, recursively traverses positive `Pi` codomains, fixes
parameters, checks exact index arity, and rejects family occurrences inside
indices. A surface arrow scan would miss invalid applications and reduction.

### Insert provisionally, then roll back on positivity failure

Rejected for this slice. Existing later constructor checks still need a private
provisional declaration for type inference, but positivity itself can and must
finish before that mutation. This gives TL2.11's ordering claim a direct test.

### Implement mutual positivity now

Rejected. The current public admission API cannot represent a mutual group.
Pretending otherwise would test an unused abstraction. ADR-0352 freezes the
single-family rule and requires TL2.13 to lift its occurrence set to the entire
group before mutual admission.

## Consequences

- TL2.12 can widen induction-hypothesis generation without silently removing
  the only barrier against negative occurrences.
- Positive deferred families gain a two-stage result: positivity accepted,
  semantics still unsupported.
- Diagnostics distinguish polarity violations from malformed recursive
  applications, improving importer and fuzz triage.
- Positivity becomes a small trusted traversal and must remain covered by the
  generated grammar whenever expression or inductive representation widens.
