# ADR-0083: Deadline-Aware Bit-Vector Lowering

Status: accepted
Date: 2026-07-10

## Context

`SolverConfig::timeout` was enforced by the SAT adapters and by the outer
canonical UFBV/AUFBV search, but term-to-AIG lowering had no cancellation
boundary. A single admitted wide operator could therefore construct its full
circuit before the caller observed that the query deadline had elapsed.

The public cvc5 QF_AUFBV regression `unconstrained__array1.smt2` exposed the
failure sharply: five 1024-bit `bvudiv` terms made a benchmark configured with a
1 second timeout return after 437.5 seconds. The canonical BV theory passed a
shrinking timeout to each warm SAT check, but `IncrementalBvSolver::assert`
performed deadline-blind lowering first. The one-shot SAT-BV backend had the
same gap after its conservative size preflight.

## Decision

Bit-vector lowering accepts an optional absolute monotonic deadline and polls it
throughout circuit construction.

- `axeyum-bv` exposes deadline-aware one-shot and incremental entry points.
  The lowerer polls between DAG nodes and inside wide multiplier, divider,
  shift, equality, comparison, mux, and ripple-adder construction. Native builds
  use `std::time::Instant`; browser builds use the existing `web-time` clock.
- Expiry is represented as `BitLowerError::DeadlineExceeded`. The one-shot
  SAT-BV backend and canonical UFBV/AUFBV theory boundary translate it to
  `CheckResult::Unknown(Timeout)`, never `SolverError` and never a guessed
  satisfiability verdict.
- Interrupted incremental lowering may retain completed child terms and
  structurally hashed orphan AIG gates, but it does not memoize the interrupted
  root or install a CNF root/frame assertion. The enclosing canonical query
  stops with `Unknown`.
- The existing conservative projected-clause estimator is shared with the
  canonical incremental BV theory. It checks the cumulative set of roots ever
  encoded by that warm solver against `cnf_clause_budget`, or the existing
  64-million-clause default ceiling when no explicit budget is set. Popped roots
  remain in this accounting because their AIG/CNF encoding remains resident.
- Estimation is admission control, not a completeness claim. An over-budget
  query returns `Unknown(EncodingBudget)` before allocation; admitted queries
  remain protected by deadline polling.

This decision does not add asynchronous cancellation, reclaim partially built
incremental AIG state, change the bit-vector encoding, or raise any existing
resource cap.

## Soundness Argument

Deadline expiry and projected-size refusal can only replace an attempted solve
with a classified `Unknown`. They cannot create `Sat` or `Unsat`. A completed
lowering uses the unchanged AIG semantics, CNF encoding, model lifting, and
original-term replay gate.

Retained partial incremental state is inert: completed memo entries still denote
their original terms, structural hashing preserves gate denotation, and no root
clause activates the interrupted assertion. A later query may reuse that valid
prefix, while the interrupted query has already terminated as `Unknown`.

The projected-clause estimator is deliberately conservative. Refusing an
over-estimated query sacrifices completeness only through `Unknown`; it cannot
make a wrong decision. Counting all resident incremental roots also
over-approximates active work after `pop`, which is safe for admission.

## Consequences

Positive:

- `SolverConfig::timeout` now bounds the expensive pre-SAT BV construction that
  caused the measured 437.5x overrun.
- Canonical and one-shot BV paths share the same classified timeout behavior and
  the same oversized-encoding policy.
- Polling is deterministic in placement and adds no thread, signal, or unsafe
  cancellation mechanism.

Costs:

- Wide-circuit loops perform periodic monotonic-clock reads.
- Interrupted incremental AIG allocations are not reclaimed immediately.
- The conservative cumulative estimator may decline a query whose structurally
  hashed final CNF would fit below the configured limit.

## Validation

- `axeyum-bv`: 17 tests pass, including interruption inside one admitted
  1024-bit restoring divider.
- Canonical UFBV/AUFBV: all 53 focused unit tests pass.
- Deadline and SAT-BV integrations: 4 and 28 tests pass. Admitted scalar BV and
  AUFBV single-divider cases return `Unknown(Timeout)` within a 20 ms budget;
  the exact public five-divider row returns `Unknown(EncodingBudget)`.
- Exact-SHA pre-push validation at `85e007b2` passes all 809 solver tests and its
  corpus/unit gates.
- Fresh 1 second `cvc5-regress-clean` QF_AUFBV run versus Z3: 9 files, 7 SAT,
  1 `EncodingBudget`, 1 unsupported, 0 disagreements, and 0 replay failures.
  The formerly 437.5-second row returns in 1 ms with a projected 157,298,694
  clauses against the 64,000,000 ceiling.

## Alternatives Considered

### Rely only on SAT-adapter timeouts

Rejected: SAT is invoked after lowering, so it cannot interrupt AIG
construction.

### Rely only on projected-size admission

Rejected: the estimator is intentionally approximate. Queries below its ceiling
still need a real wall-clock bound, and future encodings may change construction
cost without changing the estimate immediately.

### Run lowering in a cancellable worker

Deferred: thread/process cancellation complicates deterministic incremental
state ownership and browser support. Cooperative polling closes the measured gap
with a much smaller trust and implementation surface.

## Next Work

ADR-0084 subsequently closed the array-valued UF/select projection target.
Structural store/ITE/default class ownership, warm reuse, broader measurement,
and online proof logging remain. Extend deadline polling to any newly introduced
superlinear preprocessing or encoding loop at the time that loop is added; do
not defer cancellation to a downstream solver.
