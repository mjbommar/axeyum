# ADR-0377: Shared arithmetic deadlines and deterministic normalization ceilings

Status: accepted
Date: 2026-08-05
Amended: 2026-08-08, 2026-08-10

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
5. The legacy Boolean-structured linear-arithmetic loop may retain at most
   8,192 literals across dynamically learned, unminimized (`Large`) theory
   cores. Reaching the ceiling returns `Unknown(ResourceLimit)` before starting
   another warm propositional-SAT round. Small and deterministically minimized
   cores do not consume this ceiling. This 2026-08-08 amendment repairs the
   QF_LRA `sal/tgc/tgc_io-safe-20.smt2` 8 GiB process abort exposed by A5; it
   does not raise a timeout, memory limit, normalization cap, or route budget.
6. The joint 1,024-arithmetic-atom/4,096-CNF-variable pre-SAT trigger admits one
   additional conjunctive moderate envelope: at most 1,280 arithmetic atoms and
   at most 8,192 CNF variables. Outside that rectangle, the existing trigger
   still declines before the first SAT round. This 2026-08-10 amendment restores
   the historical QF_LRA UNSAT control `windowreal-no_t_deadlock-17.smt2`
   without admitting either known allocation-abort control or the nearest
   low-atom/very-wide IDL control.

## Soundness and determinism

All three mechanisms only remove work. They cannot manufacture a model or a
refutation. A `sat` result still requires replay against the original terms;
`unsat` still comes only from an existing exact arithmetic proof path. CAD
cancellation maps to the established `None` decline, and incomplete LRA
construction is never exposed as a usable theory by production solver routes.

The normalization counters depend only on the stable term traversal and exact
coefficient-map sizes. They therefore make admission reproducible across
machines, unlike a memory watermark or elapsed-time-only policy.
The large-core counter likewise depends only on the stable conflict-core source
classification and literal count. It removes a future SAT round but cannot add
a model, clause, proof, or verdict.
The moderate envelope is likewise a pure predicate over stable pre-solve
counts. It permits existing exact search only inside both bounds; SAT still
requires original-term model replay, and UNSAT still comes from the existing
refutation route. A query outside either moderate bound receives the same typed
pre-SAT decline as before.

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
- The 2026-08-08 A5 attempt at exact pushed revision `1de737488` failed closed
  after 172 QF_LRA rows when `sal/tgc/tgc_io-safe-20.smt2` aborted at the 8 GiB
  process ceiling. The repaired merged release returns a typed schema-1
  `lira-dpll` budget decline in 6.08 seconds with 8,224 retained large-core
  literals and 1,777,884 KiB peak RSS. Strict solver Clippy, 1,079 all-feature
  library tests, 16 deep-input tests, five QF_LRA differential fuzz tests, and
  the 114.81-second simplex fallback differential are green. Complete-corpus
  monotonicity and the new exact-commit full gate remain required before
  integration; see the
  [A5 repair record](../../plan/qf-linear-a5-wide-core-memory-repair-2026-08-08.md).
- The complete V2 derivation at exact pushed `5a53012e1` stopped on one
  historical-decision loss: `windowreal-no_t_deadlock-17` changed from UNSAT to
  the 1,024/4,096 pre-SAT decline at 1,217 atoms and 6,526 CNF variables. Under
  the bounded moderate-envelope candidate it returned UNSAT in 3/3 observations
  in 0.10--0.20 seconds at 16,920--17,468 KiB peak RSS. The 1,447/4,733
  `pursuit`, 1,411/6,774 `tgc`, and 1,084/31,944 IDL controls all retained typed
  declines before the first SAT round. Strict Clippy, all 1,091 solver-library
  tests, 16 deep-input tests, 41 online arithmetic/CDCL(T) integrations, the
  1,500-case QF_LRA differential, and the 1,200-case simplex differential are
  green with zero disagreement. See the
  [bounded repair result](../../plan/qf-linear-a5-pre-sat-boundary-monotonicity-v1-result-2026-08-10.md).

The retained six-division arithmetic corpus gate remains an integration exit
criterion in `PLAN.md`; focused evidence does not substitute for it.

## Consequences

- Arithmetic timeout means a query-level deadline across fallback routes.
- LRA normalization can decline a large but semantically supported query due to
  a documented deterministic resource ceiling. This is preferable to process
  abort and is visible through `UnknownKind::ResourceLimit`.
- A future ceiling change requires corpus A/B evidence and an ADR update. Do not
  raise limits to hide a residual or infer completeness from available RAM.
- Repeated wide cores are a named allocation boundary: once their literal
  budget is exhausted, returning `unknown` is preferable to relying on a
  cooperative clock callback while the SAT allocator approaches a hard process
  ceiling.
- The moderate pre-SAT envelope is conjunctive. Raising either bound, removing
  the other dimension, or adding another envelope requires fresh target/control
  evidence and another ADR amendment; available host RAM is not evidence.
- The disjunction-split work that depended on honest branch budgets may now be
  remeasured, but is not accepted by this ADR.
