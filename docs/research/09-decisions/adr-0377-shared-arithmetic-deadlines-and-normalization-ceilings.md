# ADR-0377: Shared arithmetic deadlines and deterministic normalization ceilings

Status: accepted
Date: 2026-08-05

## Context

Arithmetic dispatch treated `SolverConfig::timeout` as a per-route allowance
rather than a query deadline. On the public `QF_NIA`
`cli__regress1__nl__ext-rew-aggr-test.smt2`, real relaxation consumed its share,
then NIA linearization received the original timeout again. A 250 ms request
returned after 1.10 s and a 3 s request after 4.11 s. Profiling also located a
smaller cancellation gap inside solver-local multivariate polynomial arithmetic.

Separately, `LraTheory`'s `AtomBuilder` memoized a full `BTreeMap` coefficient
vector for every intermediate term. Nested dense sums therefore retained
quadratic data. Raising the online atom cap made the 1,492-atom, roughly
700-variable public `QF_LRA/sc/sc-39.base.cvc.smt2` abort at the 8 GiB memory
limit. A wall-clock deadline is not a sufficient allocation policy: memory can
be exhausted before the next clock poll, and machine speed would change which
term graphs are admitted.

## Decision

1. `check_auto_dispatch` owns one absolute deadline. Every sequential real and
   nonlinear-integer route receives only the remaining duration. After a route
   declines, an expired shared deadline returns `Unknown(Timeout)` instead of
   entering another route with a fresh timeout.
2. The existing solver-local `ISOLATE_DEADLINE` is polled inside multivariate
   polynomial addition, negation, multiplication, substitution, exact division,
   coprime splitting, determinant expansion, projection, and rational-cell
   traversal. Expiry returns `None`, which is the existing conservative decline.
   No foundational `axeyum-ir` API or clock dependency is added.
3. LRA atom normalization has deterministic ceilings of 1,000,000 node visits,
   4,000,000 coefficient operations, and 262,144 retained memoized coefficient
   entries. Once the cache ceiling is reached, further expressions are not
   memoized. Exceeding a work ceiling stops construction and production LRA
   front doors return `Unknown(ResourceLimit)`; deadline expiry remains
   `Unknown(Timeout)`.
4. The existing 1,024-atom online CDCL(T) admission cap remains. The new limits
   protect `LraTheory` itself and sibling/direct consumers; they are not grounds
   for raising the measured front-door cap.

## Soundness and determinism

All three mechanisms only remove work. They cannot manufacture a model or a
refutation. A `sat` result still requires replay against the original terms;
`unsat` still comes only from an existing exact arithmetic proof path. CAD
cancellation maps to the established `None` decline, and incomplete LRA
construction is never exposed as a usable theory by production solver routes.

The normalization counters depend only on the stable term traversal and exact
coefficient-map sizes. They therefore make admission reproducible across
machines, unlike a memory watermark or elapsed-time-only policy.

## Evidence

- Pre-fix public QF_NIA timings under the 8 GiB wrapper were 1.10 s, 1.60 s,
  2.10 s, and 4.11 s for 250 ms, 500 ms, 1 s, and 3 s requests.
- With the shared deadline and inner CAD polls, the same optimized binary
  returns `unknown` in 0.30 s, 0.60 s, 1.10 s, and 3.10 s respectively. The
  250 ms debug regression completes in 0.28 s and reports `Unknown(Timeout)`.
- `deadline_honored` passes 6/6, including the new public QF_NIA regression.
- Online-LRA integration tests pass 7/7; the deterministic exhausted/near-miss
  normalization test passes; multivariate real-root tests pass 37/37.
- `cargo clippy -p axeyum-solver --all-targets --all-features -- -D warnings`
  passes.
- `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --all-features --quiet --
  --test-threads=2` is terminal green: 1,073 library tests and every integration
  and doctest binary passed. This includes the 397.85-second UFLIA differential
  test and the 286.00-second word-equation differential test.
- `just parity-docs` is independently green at 35 rows, 24 logics, 992 files,
  762 decided, 674 oracle-compared, and zero disagreements. Its load-sensitive
  frontier refresh was intentionally not retained by this resource-policy slice.
- GitHub CI `31066926771` and docs `31066926761` for the preceding code merge,
  plus docs `31067318237` for its canonical-plan descendant, are terminal green.

The retained six-division arithmetic corpus gate remains an integration exit
criterion in `PLAN.md`; focused evidence does not substitute for it.

## Consequences

- Arithmetic timeout means a query-level deadline across fallback routes.
- LRA normalization can decline a large but semantically supported query due to
  a documented deterministic resource ceiling. This is preferable to process
  abort and is visible through `UnknownKind::ResourceLimit`.
- A future ceiling change requires corpus A/B evidence and an ADR update. Do not
  raise limits to hide a residual or infer completeness from available RAM.
- The disjunction-split work that depended on honest branch budgets may now be
  remeasured, but is not accepted by this ADR.
