# ADR-0367: Narrow shared-guard disjunction splitting in SAT-BV

Status: accepted

Date: 2026-07-27

## Context

After batched value propagation removed the QF_BVFP ESBMC conversion outlier,
four declared-UNSAT rows remained above the five-second pure-Rust budget:
`Float4{,_1}-main.smt2` and `Float-no-simp2{,_1}-main.smt2`. Z3 4.13.3 decides
all four UNSAT. Profiling attributed only tens of milliseconds to word-level
preprocessing and bit lowering, while the two resulting CNF pairs contained
439,234 clauses / 118,037 variables and 921,561 clauses / 247,458 variables.
The default BatSat search was the dominant cost.

Each post-policy formula has one exact shape: a disjunction of four to fourteen
counterexample obligations,

```text
(or (not (=> A C_0)) ... (not (=> A C_n)))
```

where every branch has the same antecedent `A`. False branches and duplicate
branches are also present. Solving each unique non-false branch independently
was materially cheaper than solving the monolithic Tseitin CNF.

ADR-0065 records an important negative result: broad top-level disjunction
splitting multiplied hard sub-solves and roughly doubled corpus PAR-2. A default
SAT-BV route therefore needs an exact structural admission rule, a shared
deadline, and replay protection rather than a general `or` heuristic.

## Decision

**Before monolithic SAT-BV lowering, split only a large, single-assertion
disjunction whose unique non-false leaves are all negated implications with one
identical antecedent. Solve those leaves under one shared deadline and transfer
only logically justified, replay-safe verdicts.**

Admission is fail-closed and requires all of the following:

1. a configured timeout and no query replay plan at this internal boundary;
2. exactly one Boolean assertion with at least 5,000 reachable DAG nodes;
3. a binary `BoolOr` tree which, after dropping literal `false` leaves and
   deterministically deduplicating by `TermId`, has 4 through 16 leaves; and
4. every leaf is exactly `not(implies(A, C_i))`, with the same `TermId` for `A`.

Any shape mismatch uses the unchanged monolithic route. Branches are visited in
deterministic `TermId` order. Recursive splitting is disabled in branch
backends. Before each branch, the remaining global wall-clock budget is divided
fairly over the remaining branches, capped by the actual remaining duration;
expiration or any branch `unknown` returns `unknown`.

The verdict transfer follows directly from disjunction semantics:

- all branches UNSAT implies the original disjunction is UNSAT;
- one SAT branch may imply SAT, but its partial model is first completed with
  well-founded defaults and evaluated against the complete original assertion;
- a missing default or failed original-term replay returns `unknown`, never
  `sat`; and
- a branch error remains an error rather than being converted into a verdict.

Branch solve statistics are accumulated and stable split-progress counters are
recorded. This route does not add a trusted proof: UNSAT still has the existing
default BatSat assurance level, while any SAT result retains mandatory
original-term replay.

## Evidence

The fixed 34-file public `QF_BVFP/ramalho/esbmc` population, run serially with a
five-second per-instance budget and Z3 comparison, returns 34 UNSAT, zero
unknown, zero disagreement, zero errors, and zero model-replay failures. The
four former residuals complete in 1.609 s, 1.624 s, 3.752 s, and 3.948 s. The
immediate predecessor returned 30 UNSAT and four timeout unknowns on the same
population and budget.

The serial run is the authoritative current-host timing result. Two four-worker
runs were stopped at outer ceilings while an unrelated multi-process workload
was active; no artifact was produced, so they are not used for a parallel
speedup or regression claim. A separately instrumented single-row execution
showed five branch decisions, no recursion, and a 1.812 s total.

Focused tests cover exact admission, the DAG floor, mismatched antecedent
decline, all-branch UNSAT transfer, SAT model completion, and original-root
replay. Warning-denied solver Clippy and the solver test suites are required
before the containing commit is accepted.

## Alternatives

### Split every top-level disjunction

Rejected by ADR-0065 and not reconsidered. Region and inequality branches can
retain the original hard search while multiplying it. This decision admits one
measured shared-antecedent counterexample shape only.

### Factor the common antecedent into a new rewrite

Rejected for this increment. Rewriting the source expression can improve
sharing but does not remove the hard disjunction from the final SAT search, and
would widen the public rewriting/evidence surface. The branch equivalence is
local to the backend and its verdict transfer is checked directly.

### Change BatSat options or enable existing inprocessing by default

Rejected by measurement. The baseline, native core, inprocessing,
vivification, and combinations did not close the four-row five-second gap; a
representative 20-second run was 9.672 s at baseline, 10.670 s with
vivification, and 18.076 s with inprocessing.

### Run branches concurrently

Deferred. It would introduce scheduler-sensitive ordering, peak-memory growth,
and more complicated global-deadline and deterministic-result accounting. The
bounded serial route already closes the measured population.

## Consequences

The selected ESBMC population rises from 30/34 to 34/34 decided at five seconds
without changing any verdict. The backend gains a small portfolio path, but
only behind an exact structural and size gate; widening branch syntax, branch
count, or the DAG threshold requires a fresh no-loss population measurement.
Parallel throughput remains unclaimed on the loaded development host. This
does not close the selected QF_FP/QF_BVFP/QF_ABVFP full-library rerun, general
FP parity, proof-producing UNSAT, or the custom-CDCL performance program.

## Backlinks

- Code: `crates/axeyum-solver/src/sat_bv_backend.rs`
  (`shared_guard_split_branches`, `check_shared_guard_split`).
- Result: `docs/plan/fp-shared-guard-split-result-2026-07-27.md`.
- Related: ADR-0065 (narrow finite-domain equality split after broad-split
  rejection), ADR-0034 (word-level preprocessing policy).
