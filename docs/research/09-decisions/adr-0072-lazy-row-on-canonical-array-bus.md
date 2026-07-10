# ADR-0072: Lazy Read-Over-Write on the Canonical Array Bus

Status: accepted
Date: 2026-07-09

## Context

ADR-0071 put base-array select congruence on canonical `CdclT`, but its
production route still called the eager array rewriter first. Every
`select(store(a,i,v),j)` therefore expanded to an `ite` before search, so deep
store chains still paid the exact mountain-building cost that P2.2 is intended
to remove.

The separate lazy-ROW CEGAR route already had the required semantics: one fresh
result per read site, exact store hit/miss metadata, candidate-violation checks,
and replayable base-array projection. Duplicating that logic in the canonical
route would create two definitions of array semantics. The recorded P1.6
`str.len` blocker was also re-audited before choosing the next increment: its
exact marker and differential gates already pass, and the P2.7 plan records it
as closed by ADR-0052. T1.6.4 is OBE, not the next implementation target.

## Decision

Reuse the existing lazy-ROW abstraction as the array preparation boundary for
canonical QF_ABV/QF_AUFBV, and materialize violated store axioms in the same
replay-guided rounds as select and UF congruence.

- `abv` exposes crate-internal `OnlineRowAbstraction`/`RowSite` metadata and a
  base-array projection helper. The one-shot CEGAR route and canonical route now
  share `RowCtx::abstract_term`; there is one ROW semantics implementation.
- A base select, and each read through a store, receives a fresh scalar result.
  Constant-array reads are folded or constrained unconditionally. Array-valued
  `ite` reads retain the existing scalar branch rewrite. Bare stores and array
  equalities outside this fragment decline to the existing portfolio.
- Function abstraction runs after ROW abstraction. ROW metadata terms are added
  as auxiliary abstraction roots so UF applications that occur only in store
  indices/elements/inner reads still receive aligned projection metadata.
- After a SAT candidate, every unmaterialized store site computes the expected
  result: the stored element when read and write indices agree, otherwise the
  inner read. An unequal fresh result materializes the exact axiom
  `(j=i -> r=v) and (j!=i -> r=inner)`.
- Each ROW site contributes three semantic interface atoms (index equality,
  hit-result equality, miss-result equality) to the shared 512-equality cap.
  Existing 64-round, theory-atom, Boolean, site, and deadline bounds remain.
- Partial-round UNSAT transfers because omitted ROW and congruence axioms form a
  relaxation. SAT still requires no candidate violations, function projection,
  base-array reconstruction from variable-read sites, and original-query replay.
- Every array-route `Unknown` falls through to the pre-existing array portfolio;
  eager/certifying reductions and evidence routes are unchanged.

## Soundness Argument

Every array model satisfies every deferred ROW axiom. Replacing a store read by
an unconstrained fresh scalar and asserting only a subset of ROW instances
therefore weakens the original formula. UNSAT of a partial round implies UNSAT
of the original.

A SAT candidate is checked against every unmaterialized store site using the
exact evaluator values of its rewritten index, element, inner read, and fresh
result. Violations add valid total-array consequences and force another solve.
At convergence, base arrays are reconstructed from consistent variable-read
sites; materialized ROW axioms determine store reads. Function interpretations
are projected first so UF-bearing indices can be evaluated. Original replay is
the final SAT acceptance gate. Missing values, unsupported shape, cap, timeout,
projection failure, or replay failure returns/falls through as Unknown.

## Evidence

- A same-index store hit and a proved-different-index miss each take two rounds,
  one candidate, and exactly one ROW axiom before UNSAT.
- A store whose read/write indices are `f(x)`/`f(y)` with `x=y` refutes through
  the shared e-graph/BV atoms, proving auxiliary ROW roots retain UF semantics.
- A 24-write concrete-address chain read at a key constrained distinct from all
  writes returns replayed SAT in one round with zero ROW or select interfaces.
- The canonical online module passes 25 focused tests. The existing base-select,
  route, array, AUFBV, and lazy-ROW suites remain green.
- The deterministic 256-case direct online/eager, front-door/eager, and direct
  online/Z3 matrix remains clean: 768 comparisons, no disagreements.
- Single-run public measurements at a 1 s cap remain sound and show bounded
  coverage movement:

| corpus | ADR-0071 decisions | lazy-ROW decisions | disagreements | replay failures | PAR-2 mean |
|---|---:|---:|---:|---:|---:|
| QF_ABV (193) | 185 | 187 | 0 | 0 | 77 ms (was 72 ms) |
| QF_AUFBV (53) | 48 | 49 | 0 | 0 | 155 ms (was 172 ms) |

QF_ABV gains `arraycond10` SAT and `ext7` UNSAT because the online probe now
declines unsupported array equalities without first constructing bounded
extensionality. QF_AUFBV gains two UNSAT rows and loses one SAT row at the tight
cap in this single sample. These timings are noisy portfolio measurements, not a
general performance claim.

## Alternatives

- **Keep eager ROW before the canonical bus.** Rejected because store-chain
  construction remains depth-proportional before search and cannot become warm.
- **Copy the ROW logic into `ufbv_online`.** Rejected because semantic drift
  between one-shot and canonical array routes would be a soundness risk.
- **Materialize every ROW axiom at construction.** Exact but defeats the purpose;
  the 24-write miss gate proves many chains need none.
- **Add only the candidate-selected hit or miss equality.** Sound for that model
  but creates avoidable rounds when index polarity changes. The full total ROW
  axiom is added once.
- **Add extensionality in the same increment.** Rejected. Array equality needs
  diff skolems, equality flags, model merging, and separate evidence work.

## Consequences

- Canonical QF_ABV/QF_AUFBV no longer requires eager read-over-write expansion
  for the admitted store/read fragment.
- Store sites, base-select congruence, UF congruence, and exact BV now refine in
  one deterministic outer loop with function-then-array replay.
- T1.6.4 is marked done/OBE under ADR-0052. The remaining array depth is P2.2
  extensionality, merge-triggered axiom queue state, scalable default/majority
  models, and eventual warm cross-check reuse rather than another `str.len`
  bridge.
