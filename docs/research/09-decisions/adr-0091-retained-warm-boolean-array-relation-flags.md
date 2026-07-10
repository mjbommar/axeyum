# ADR-0091: Retained Warm Boolean Array Relation Flags

Status: accepted
Date: 2026-07-10

## Context

ADR-0089 and ADR-0090 make literal warm array relations useful: top-level
positive equality can merge projection owners and realize supported structural
parents, while top-level disequality has an exact private diff witness. The
remaining Boolean gap was relation atoms under scalar structure, such as:

```text
or(g, store(a, i, v) = b)
not(f(x) = a)
```

Treating such atoms as unconditional array equalities would be unsound because
the SAT candidate may assign the Boolean relation false. Deferring the entire
assertion loses the retained warm path for common branch conditions.

## Decision

`IncrementalBvSolver` admits supported array equality atoms nested under scalar
Boolean structure by replacing each atom with a private Boolean flag.

Each flag carries both guarded semantics:

- if the flag is true, paired reads at retained equality-observation indices
  must agree;
- if the flag is false, one private diff index witnesses unequal paired reads.

The true branch reuses ADR-0090 equality metadata, but model projection only
adds a flagged equality to the owner-merge/structural-realization set when the
candidate assigns that private flag `true`. False flags do not merge owners;
their guarded diff witness plus retained exact read summaries make replayed
disequality possible.

When later assertions or one-shot assumptions introduce new read indices, every
active relation flag receives a guarded `flag -> read-equality` observation at
the new compatible index. New flags also observe already-active compatible
indices. All private flags, diff indices, read owners, and structural owners are
filtered from public models and cores.

Literal top-level array equality/disequality keeps the ADR-0089/0090 route
instead of being rewritten through a flag.

## Soundness Argument

Replacing an array equality atom by a flag is a relaxation. The two guarded
directions only add valid consequences of the intended Boolean meaning:
`flag -> a = b` is enforced through observed read equality, and
`not flag -> a != b` is enforced through one exact diff witness. Structural reads
still close through ADR-0087 exact summaries before a candidate can be accepted.

SAT is accepted only after projection evaluates candidate-true flags into actual
array equality classes, realizes structural owners, filters private symbols, and
replays every original assertion or assumption with the ground evaluator. A
missing flag value, failed realization, resource exhaustion, or replay failure
can only return `Unknown`.

UNSAT derives from the scalar Boolean encoding plus guarded valid array
consequences. Selector scoping applies to every root introduced for assertions
and one-shot assumptions, so popped or one-shot relation flags cannot leak into
later checks.

## Validation

- New focused tests cover forced-true structural equality under `or`, total-model
  projection with no explicit reads, forced-false disequality, conflict with an
  active equality, push/pop, one-shot cores, private-symbol filtering, and replay.
- Existing ADR-0088/0089/0090 suites were updated so formerly deferred nested
  relation cases are now positive warm coverage while depth and admission caps
  remain enforced.
- Targeted gates pass:
  `cargo fmt --all --check`;
  `cargo test -p axeyum-solver --test warm_array_relation_flags -j1`;
  `cargo test -p axeyum-solver --test warm_structural_array_equality -j1`;
  `cargo test -p axeyum-solver --test warm_array_relations -j1`;
  `cargo test -p axeyum-solver --test warm_array_uf_parents -j1`.

## Consequences

Nested Boolean uses of supported array relation atoms can now stay on the
retained warm path with candidate-sensitive model projection and replay. This
removes the ADR-0089/0090 nested-Boolean deferral without changing top-level
literal relation handling.

ADR-0092 subsequently uses these relation flags to admit direct finite-array UF
parameters on the retained warm path. Structural array-valued parameter
expressions, memory BMC/k-induction, online array proof logging, nested/extended
array components, and broader low-load aggregate timing remain future work.
