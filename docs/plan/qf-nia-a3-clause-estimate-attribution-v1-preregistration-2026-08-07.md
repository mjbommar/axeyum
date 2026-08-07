# QF_NIA A3 clause-estimate attribution v1 preregistration — 2026-08-07

## Question and non-production boundary

The accepted A3 budget partition selects the two smallest reference-SAT rows
that the production SAT/BV backend refuses before lowering because its
conservative estimate exceeds the immutable 64,000,000-clause safety ceiling.
This diagnostic asks which shared blasted terms pay that estimate and whether
structural bit demand can reduce it without constructing an AIG or CNF.

The diagnostic is analysis-only. It may add a reproducible example under
`axeyum-bench`, tests for that example's accounting, and evidence/result notes.
It must not change the solver, bit lowerer, integer blaster, route ordering,
width ladder, budgets, deadlines, verdicts, or replay policy. No production
mechanism is authorized by this preregistration.

The clean code boundary is
`6d881816c5669d049a97b62d6e495109b53b876b`. The implementation must begin from
that exact object and remain in the isolated
`agent/nia/a3-clause-estimate-attribution` worktree until its focused gates and
result are complete.

## Frozen targets

Both inputs are from the retained 2026-08-06 200-row QF_NIA population and have
Axeyum `unsolved`, reference `sat`, and retained production traces ending in a
pre-lowering estimate refusal at width 32.

| Stable suffix | Expected estimate | Source SHA-256 |
|---|---:|---|
| `From_AProVE_2014__juHashMapCreateContainsKey.jar-obl-11__p31818_safety_0.smt2` | 81,482,280 | `a746f09965b418b961a77ec34a869381e4453719b936d5aaee0975050fed3d34` |
| `From_AProVE_2014__juHashMapCreateRemove.jar-obl-11__p6984_safety_0.smt2` | 82,590,729 | `730a2c10adde08316d7e3de2a2ad190d1c343623dc7b37145d7ab246d07d4828` |

The tool must reject a source digest mismatch. It must parse the ordinary flat
view, blast integers at exactly width 32, and analyze the resulting assertion
roots. It may not call a lowering or SAT entry point.

## Frozen measurements

Emit one deterministic JSON object per target with at least:

1. source identity and digest, blast width, original/blasted assertion counts,
   restricting no-overflow constraint count, and reachable shared-node count;
2. the exact production-formula estimate, recomputed as one shared-DAG walk and
   checked against the retained estimate above;
3. stable per-operator and per-result-width contributions whose clause totals
   sum exactly to the estimate;
4. every reachable `bvmul` classified as constant/constant,
   constant/nonconstant, or nonconstant/nonconstant, including operand side,
   result width, constant zero/one/all-ones status and population count;
5. the estimate fraction attributable to each multiplication class; and
6. a memory-bounded structural-demand projection stating how many reachable
   multiplier result bits can be proved narrower than full width under the
   existing demand-local rules, plus any analysis-budget fallback.

“Constant” means an immediate `BvConst` or `WideBvConst` operand in the blasted
shared DAG. This diagnostic does not claim algebraic constancy through other
operators. The production estimate formula remains exactly `8*w*w` gates for
`bvmul`, `10*w*w` for division/remainder, `w*log2(w)` for shifts, `max(w,1)`
otherwise, followed by a saturating factor of three for clauses.

## Work and safety bounds

The analyzer may retain only term IDs and aggregate counters in addition to the
already parsed/blasted arena. It must walk each shared node at most once per
analysis phase, cap reachable nodes at 2,000,000, cap structural demand work at
8,000,000 term-bit requests, and fail closed with a nonzero exit on source,
parse, blast, accounting, or work-limit failure. No AIG literals, gates, CNF
variables, clauses, solver state, or models may be allocated.

Unit tests must cover shared-node single charging, all multiplier classes,
width grouping, exact total reconciliation, and deterministic serialization.

## Decision and stop rules

This diagnostic succeeds only if both targets reproduce their retained exact
estimates and all accounting invariants hold. Its result must distinguish:

- **demand candidate**: at least 20% of current estimated clauses lie behind
  multiplier result bits that existing structural rules prove are not demanded;
- **constant-aware candidate**: at least 20% lie in immediate-constant
  multipliers, while demand projection does not clear the threshold; or
- **no bounded candidate**: neither threshold is met or analysis is incomplete.

The 20% threshold is attribution, not permission to admit a query. If a
constant-aware candidate wins, the next step is a separate preregistration for
an additive, fail-closed upper bound derived from actual constant-folding
semantics. If a demand candidate wins, the next preregistration must prove an
analysis-only admission bound. In either case the 64,000,000 absolute ceiling,
original-term SAT replay, and remove-on-failed-target-gate conditions remain
unchanged. A wrong retained estimate, digest drift, budget fallback, accounting
mismatch, or attempt to materialize the circuit stops this slice without a
production edit.
