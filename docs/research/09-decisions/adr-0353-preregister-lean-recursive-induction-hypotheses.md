# ADR-0353: Preregister one Lean recursive induction-hypothesis rule for indexed and higher-order fields

Status: proposed

Date: 2026-07-22

Execution plan:
[TL2.12 recursive induction-hypothesis plan](../../plan/lean-recursive-induction-hypotheses-tl2.12-plan-2026-07-22.md)

Implementation checkpoint:
[M1](../../plan/lean-recursive-induction-hypotheses-m1-2026-07-22.md) now routes
direct recursion through the shared WHNF classifier/reopener and stable field
metadata without changing admission. Exact direct declaration identities,
computation controls, both feature declines, and the 840-case positivity
summary remain unchanged. M2 generalized native semantics is next; neither M0
computation stream has received Axeyum product observation.

## Context

TL2.11 now checks Lean 4.30 strict positivity before any provisional inductive
environment insertion. TL2.12 may therefore widen the admitted recursive
profile without using a feature decline as an accidental soundness barrier.

Two current declines share one missing semantic rule:

- an indexed recursive field such as `tail : MiniVector alpha n`; and
- a higher-order/reflexive field such as
  `h : (y : alpha) -> r y x -> MiniAcc r y`.

They are not separate algorithms. After opening zero or more field-local
binders, both end in an exact positive application of the family. Lean gives
the minor premise an induction hypothesis over the same binder telescope and
applies the motive at the recursive occurrence's indices and value. Axeyum's
current direct-recursive implementation is the zero-index, zero-binder special
case of that rule.

The exact official `MiniVector` and `MiniAcc` source and format-3.1 streams are
already frozen by ADR-0351. The implementation authority is pinned Lean 4.30
commit `d024af099ca4bf2c86f649261ebf59565dc8c622`, especially
`is_rec_argument`, `mk_rec_infos`, and `mk_rec_rules` in
`src/kernel/inductive.cpp`.

## Decision

Generalize all currently representable positive recursive constructor fields
through one telescope-based induction-hypothesis rule.

For a checked single-family constructor field

```text
u : Pi (x_1 : D_1) ... (x_n : D_n), I P j_1 ... j_k
```

where TL2.11 has already proved that no `D_i` contains `I`, the tail is the
exact family application at the declared universe levels and fixed parameters
`P`, every `j_i` is occurrence-free, and `k` is the declared index count,
generate:

```text
u_ih : Pi (x_1 : D_1) ... (x_n : D_n),
         motive j_1 ... j_k (u x_1 ... x_n)
```

and pass this computation-rule value to the constructor minor:

```text
fun x_1 ... x_n =>
  I.rec P motive minors j_1 ... j_k (u x_1 ... x_n)
```

The constructor minor binds all original constructor fields first, in source
order, then one explicit induction-hypothesis argument for each recursive field,
also in source order. The inner telescope preserves the original binder names,
types, dependencies, and binder information. Direct recursion uses an empty
telescope; non-indexed recursion uses an empty index vector.

Use one private recursive-field classifier/reopener for minor types and rule
right-hand sides. It must WHNF at each telescope step and return the exact tail
indices; the two paths may not maintain separate approximations. Store only
stable field identity in checked constructor metadata and rederive context-
specific locals in the recursor context, so fresh-variable identities cannot
leak across local contexts.

Once native admission and exact recursor self-checks pass, remove the importer's
blanket `isReflexive=true` policy decline for this supported single-family,
`numNested=0` profile. Keep mutual groups, `numNested>0`, unsafe inductives,
invalid recursive applications, and frontend nested/well-founded lowering
fail-closed under their existing typed boundaries.

`isReflexive` is official descriptive metadata, not permission to admit a
family. Flipping it must not override the kernel's structural classification;
the field type and generated recursor remain authoritative.

## Evidence

Pinned Lean constructs the same shape in two places:

- `mk_rec_infos` WHNFs each recursive argument, opens its `Pi` telescope,
  extracts the terminal family's indices, and builds the corresponding
  telescope-shaped motive application for the minor premise;
- `mk_rec_rules` repeats that traversal, supplies the extracted indices and
  applied recursive value to the recursor, and abstracts the result over the
  same telescope.

Frozen official inputs:

- `lean4export-v4.30-construct-matrix-recursive-indexed.ndjson`, SHA-256
  `df1e82fa72eac9f2a37cdf3b0eb8044f118489c51f76ab14b9af06c3f4cf11de`,
  9,899 bytes / 175 records;
- `lean4export-v4.30-construct-matrix-reflexive-higher-order.ndjson`, SHA-256
  `a2dc21e61e6938bd5eb5d8c4032c7d6197e312c7a617b8bd33388f2e46db0ec3`,
  10,583 bytes / 196 records;
- their common source
  `lean4export-v4.30-construct-matrix.lean`, SHA-256
  `08c6eeaed9d980a631dff14b30de1e3d8da37011b8ad03b84dbdc03c90bff13d`.

The current product gives `MiniVector` a typed kernel decline and stops
`MiniAcc` at the importer's reflexive metadata policy. The importer already
regenerates recursors and compares their types and rules definitionally against
the official declarations, so successful import is an exact compatibility
gate rather than parser-only credit.

## Exit gates

This ADR may be accepted only when:

1. the exact Lean revision, executable rule, frozen fixtures, case matrix,
   mutation families, resources, and stop conditions are committed before
   recursive admission changes;
2. one implementation path handles direct, indexed, higher-order, and combined
   indexed+higher-order fields without duplicated semantics;
3. generated minor types and rules preserve field order, recursive-field order,
   binder dependency/information, motive indices, and recursive major values;
4. direct-recursive recursor types, rules, and computation remain unchanged;
5. native `Vector`-, higher-order tree-, and `Acc`-shaped families admit and
   their selected recursor applications reduce to preregistered normal forms;
6. both frozen official streams complete twice, publish only complete imports,
   and their generated recursor types/rules compare definitionally with Lean;
7. a supplemental pinned-Lean computation source and Axeyum agree on selected
   `Vector` and `Acc` recursor reductions; constructor-only witnesses receive no
   computation credit;
8. type/rule/index/telescope mutations reject, and every rejection leaves the
   environment unpublished or unchanged;
9. the completed 840-case TL2.11 positivity grammar and all non-positive,
   invalid-application, direct-recursive, construct-matrix, and importer
   publication controls remain mandatory and unchanged;
10. a new deterministic recursive-profile grammar repeats byte-identically,
    covers every supported shape and mutation class, and stays within the
    bounded resource policy;
11. kernel/importer tests, focused clippy/rustdoc/rustfmt, parity documents,
    foundational resources, links, and staged-file audit pass;
12. PLAN, STATUS, both Lean roadmaps, P6.0, the research question, and the docs
    index are synchronized before the final push, with local/tracking/remote
    refs equal.

## Alternatives

### Implement indexed and reflexive recursion as separate features

Rejected. Lean's construction and the mathematical rule differ only in whether
the recursive field telescope and index vector are empty. Separate paths would
duplicate the load-bearing motive/index logic and invite drift.

### Admit the official constructors and trust recursor self-checking alone

Rejected. Self-checking is necessary but does not establish agreement with the
official recursor, computation behavior, rollback, or mutation sensitivity.
The exact importer comparison and explicit iota computations remain required.

### Treat constructor-valued witnesses as computation evidence

Rejected. `recursiveIndexedWitness` and `reflexiveWitness` prove constructor
admission but do not force recursor reduction. TL2.12 adds a dedicated official
computation source and native normal-form assertions.

### Implement mutual or nested inductives in the same slice

Rejected. Mutual admission changes the family occurrence set, motives, minor
premise collection, and recursor group atomically; it remains TL2.13. Nested and
well-founded source definitions are frontend lowering work after that core and
remain TL2.14.

### Remove the importer's reflexive decline first

Rejected. Policy may widen only after the independent kernel implements and
tests the exact supported semantics. Parsing metadata is not admission.

## Consequences

- TL2.12 becomes one reviewable semantic widening rather than two partially
  overlapping projects.
- The existing direct-recursive route becomes an explicitly tested special case
  of the general rule.
- Official `MiniVector` and `MiniAcc` imports can advance from measured declines
  to independent admission and exact recursor comparison.
- The trusted surface grows in recursor generation and therefore gains both
  deterministic generated tests and pinned-Lean differential obligations.
- TL2.13 must still generalize positivity and recursor construction to a whole
  mutual family group; TL2.14 still owns frontend lowering.
