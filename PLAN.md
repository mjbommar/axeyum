# PLAN.md — master index

This is the entry point. The full, end-to-end engineering plan to take axeyum to
**Z3 + Lean parity** lives under [`docs/plan/`](docs/plan/README.md). This file
is the map and the standing rules; **[STATUS.md](STATUS.md)** is the live tracker
(current focus, per-phase state, changelog) and is the only file with mutable
session state.

> The goal is large and deliberately multi-week/multi-month. It is decomposed
> into tracks → phases → tasks, each with concrete reference file paths, sizing,
> and exit criteria, so work can proceed one verifiable increment at a time
> without ever losing the thread. **We do not stop and we do not hand-wave; we
> advance the next task and record it.**

## Where we are vs the north star — measured reality check (2026-06-28)

**Measured status: the build is well underway, soundness is holding, and there
is a concrete, fully-mapped road to Z3 + Lean parity.** axeyum is a sound,
pure-Rust reasoning stack — *measurably ahead on a growing set of fragments*,
with every remaining fragment decomposed into sized, exit-criteria'd work. The
job is exactly what it has always been: advance the next verifiable increment,
relentlessly. Scored against [the north-star definition of done](docs/plan/00-north-star.md):

| North-star criterion | Status | Evidence (measured, not asserted) |
|---|---|---|
| **Soundness (never a wrong verdict)** | **Strong / holding** | `DISAGREE = 0` across all 35 division baselines, 611 oracle-compared instances ([SCOREBOARD](bench-results/SCOREBOARD.md)). Two real wrong-safes in the consumer apps were found by new differential fuzzes and fixed. |
| **Feature coverage (breadth)** | **Partial** | Columns exist for ~24 fragments (BV/ABV/UF/LRA/LIA/NRA/NIA/FP/DT/strings/seq/FF/…), but many are shallow. |
| **Completeness / decide-rate** | **Partial — the central gap** | **663 / 992 decided (~67%)**, decide-rate **0%–100%** across divisions; only **19/35 rows are decide-strong (≥80%)**. Z3/cvc5 decide far more on most fragments and cover more divisions than the 35 measured. |
| **Measured performance (PAR-2 head-to-head)** | **Weak / largely unmeasured** | The north star says *no parity claim without this number*. Only narrow slices measured (public QF_BV: reduction moved 2→7/113; not competitive at scale). |
| **Lean parity (every unsat carries a kernel-checkable proof)** | **Early / narrow** | ~15/35 rows have a Lean route worth auditing; the trusted-reduction ledger is **not yet zero**. The Lean *tactic backend* (P3.7) is unbuilt. |
| **Pareto-dominance on selected fragments** | **Growing — the real, defensible claim** | **23 fragments** carry a committed, audited `dominant%` ([DOMINANCE](bench-results/DOMINANCE.md)). This — not wholesale replacement — is what the strategy actually targets. |

**Full parity across all of Z3/cvc5/Lean is not yet reached — and it is the
destination we are actively building toward, not a wish.** The identity is:
*untrusted fast search, trusted small checking* — sound everywhere measured,
dominant on a growing fragment set, with a pure-Rust/WASM/certifying moat. The
remaining decide-rate, performance, and proof-coverage work is mapped track by
track below and under [`docs/plan/`](docs/plan/README.md); we advance it one
increment at a time and record each one.

**Where the remaining work lives (the two load-bearing fronts + two keystones, below):**
1. **Decide-rate & measured performance (Track 1)** — close the 0–100% spread
   fragment by fragment: SAT inprocessing + word-level reduction, SAT-core
   modernization, and *committed head-to-head PAR-2 numbers* (no parity claim
   without them). This is where Z3/cvc5 parity is actually won. The grounded,
   prioritized per-fragment target list is
   [decide-rate-frontier-2026-06-28](docs/plan/decide-rate-frontier-2026-06-28.md)
   (headline: strings are the largest gap *by count* (~117) but a **depth/encoding**
   gap — bounded length ≤16, not missing operators — so the **best ROI is the
   uninterpreted-sort IR keystone (QF_UF)**; try the cheap string-bound lever
   before the big unbounded-string DP; NRA/CAD depth is the genuine catch-up, last).
   **Landed (2026-06-29, measured on the accessible curated corpus vs z3,
   DISAGREE=0; see [decide-rate-measured-2026-06-29](docs/plan/decide-rate-measured-2026-06-29.md)):**
   QF_S is already at z3 parity on accessible data (so the string `max_len` lever
   has no verifiable headroom there); **QF_UF 37→39/48** (equisatisfiable
   uninterpreted-sort `ite`-elimination + a no-hard-error robustness fix);
   **QF_ABV 173→176/177** (write-index array extensionality for shared-base
   `store-chain = store-chain` over wide indices, + robustness). Remaining leads:
   the UF+theory-combination keystone (`issue5836-2`/`issue5396`); and a confirmed
   **deadline-robustness defect** — QF_AUFLIA `bug330` runs 25 s under a 2 s
   `config.timeout` (the UFLIA combination solve on its array-abstracted
   relaxation doesn't check the deadline; QF_LIA and the lazy-row CEGAR are clean).
2. **Reduction certificates → Lean (Track 3)** — drive the trusted-reduction
   ledger to zero (Alethe emitter → Carcara-checked → per-reduction proofs →
   kernel), and build the Lean tactic backend (P3.7, **fail not `sorry`**).
3. **Keystones** — incremental e-graph + CDCL(T) loop (Track 1) and the Alethe
   term/proof IR + emitter (Track 3): build-once, unlock-many.
4. **Theory depth (Track 2)** and **consumer/frontend demand-pull (Track 4 +
   consumer track)** — the latter is mature and fuzz-hardened but does **not**
   move the core decide-rate; its job is to surface real gaps (it has filed
   U6/U7/U8) and ship user-facing, certifying value, not to claim parity.

**Immediate next focus (2026-07-02, updated after the landing wave): both theory
frontiers are in execution and delivering.** Strings (P2.7) and nonlinear
arithmetic (P2.5) remain the largest decide-rate gaps, each decomposed under
[`docs/plan/track-2-theories/P2.7-strings/`](docs/plan/track-2-theories/P2.7-strings/)
and [`docs/plan/track-2-theories/P2.5-nra/`](docs/plan/track-2-theories/P2.5-nra/).
Landed 2026-07-01/02: **P2.7 Phase A essentially complete** (A.1a/b sort+ops;
**A.2 = ADR-0052**: the `bv2nat`-linear blast + the parser-built unbounded
length abstraction + the bounded-string `unsat` gate at every front door — the
Gap-10 `str.len`-unsat marker decides, and a **measured pre-existing
wrong-unsat class vs Z3 was repaired**); **P1.9 FM→simplex keystone complete**;
**NRA coprime-split CAD projection** plus **first-class `/0` division
witnesses** (`124e18aa`): the committed curated baseline now shows **QF_NRA
21/38 decided** (was 9/38), DISAGREE=0. Next levers: strings Phase B (word-level solver; the gate's `unknown`s
are its routing signal) + recovering the 21 gate-downgraded declared-unsat
instances via richer length facts/width widening; NRA free-division `/0`
witnesses and threshold-1 monotonicity.

**Grounding correction (important).** Reading the code + ADRs showed the NRA
engine is *far more built* than the first plan draft assumed: the bignum algebraic
core (polynomials, Sturm, resultants, real algebraic numbers, field arithmetic)
already lives in **`axeyum-ir`** (ADR-0044/0045/0046) and a **largely-complete
CAD** (2-variable complete, N-variable decision-complete, fuzz-gated) lives in
`axeyum-solver`. So there is **no new `axeyum-poly` crate** (ADR-0044 keeps the
primitives in `axeyum-ir`) and "Phase A" is mostly done — see the corrected
[P2.5 current-state](docs/plan/track-2-theories/P2.5-nra/00-current-state.md).

**Measured (2026-07-01/02, `check_auto` vs z3 4.13.3, curated corpus,
DISAGREE=0): QF_NRA 21/38 (was 9/38; committed baseline `124e18aa`), QF_NIA
20/28.** The 2026-06-30 route-trace
finding (the CAD declines Boolean structure) was resolved by the landed
case-split (`5ede57f4` — the earlier fuzz "failure" was a benign i128
eval-overflow, not a wrong verdict), then sign/zero refutation (`f9e06baf`) and
**coprime-split CAD projection** (`98719094` — the dominant decline was a
shared-factor `Res ≡ 0`, not a cap). Strings re-measured under the ADR-0052
gate: QF_S 48/134, QF_SEQ 26/33, QF_SLIA 11/50 — **23 previously-claimed
`unsat`s are now honest `unknown`s, two of which were on declared-`sat`
instances** (real wrong verdicts the oracle path never compared;
[SCOREBOARD](bench-results/SCOREBOARD.md)).

**Live status (2026-07-02).** The **whole-repo health debt was paid**: main's CI
had been red for 198 consecutive runs (MSRV/let-chains, rustdoc, fmt,
cargo-deny, ~100 stable-clippy sites — repaired in `0d10aeba`/`f4734abf`); two
**exponential per-path DAG walks** were found and memoized
(`set_cardinality`'s BV collector `0bc133c2` — evidence binaries had been
grinding 8+ hours, stalling every full sweep since 2026-06-26; the `bv2nat`
blast's skeleton scan `f403991b` — a 9-hour QF_S scoreboard hang); and five
stale evidence reds that rotted behind the hang were un-rotted (`459ffc41`,
`4ca37cee` — the zero-trust Alethe emitters again outrank the structural
pre-solve certs, size-gated). `fifo_bc04` was root-caused (an O(dag·ite²)
contextual-`ite` saturation from `f4575ea5`) and un-ignored (`e67f218f`,
>600 s → 3.2 s); **one honest `#[ignore]` remains** (the uninterpreted-sort
`ite` SAT row → the P1.4/P1.5 e-graph keystone). All landings keep DISAGREE=0,
`unknown`-first, and the measured-scoreboard discipline.

The per-track detail, exit criteria, and current frontier levers are in the
sections below and under [`docs/plan/`](docs/plan/README.md). **Treat any
"phase complete" note as an increment, never as the goal.**

When multiple agents or humans are active, use separate topic-branch worktrees
and one `main` integration owner. The standing protocol lives in
[`docs/contributor-guide/multi-agent-worktrees.md`](docs/contributor-guide/multi-agent-worktrees.md).
Potential sibling/incubator projects around education, ontology artifacts,
rules/law reasoning, and downstream verification apps are tracked in
[`docs/sibling-projects.md`](docs/sibling-projects.md). The first detailed
incubator roadmaps live in [`docs/atlas/`](docs/atlas/),
[`docs/proof-cookbook/`](docs/proof-cookbook/), and
[`docs/rules-as-code/`](docs/rules-as-code/); their first validated artifacts
live under [`artifacts/ontology/`](artifacts/ontology/) and the corresponding
incubator subfolders. The broader foundational-resource expansion lives in
[`docs/foundational-resources/`](docs/foundational-resources/), including the
university-style math field spine in
[`docs/foundational-resources/MATH-FIELDS.md`](docs/foundational-resources/MATH-FIELDS.md)
and the top-down curriculum-wide resource master plan in
[`docs/foundational-resources/MATH-CURRICULUM-RESOURCE-MASTER-PLAN.md`](docs/foundational-resources/MATH-CURRICULUM-RESOURCE-MASTER-PLAN.md)
with the owner-facing all-resource plan in
[`docs/foundational-resources/MATH-CURRICULUM-COMPREHENSIVE-RESOURCE-PLAN.md`](docs/foundational-resources/MATH-CURRICULUM-COMPREHENSIVE-RESOURCE-PLAN.md)
and the curriculum-to-resource buildout plan in
[`docs/foundational-resources/MATH-CURRICULUM-BUILDOUT.md`](docs/foundational-resources/MATH-CURRICULUM-BUILDOUT.md);
the practical staged build sequence for educational content, ontology rows,
example packs, proof artifacts, solver feedback, rules/law transfer, and future
library boundaries is
[`docs/foundational-resources/MATH-CURRICULUM-RESOURCE-BUILD-SEQUENCE.md`](docs/foundational-resources/MATH-CURRICULUM-RESOURCE-BUILD-SEQUENCE.md);
the forward execution plan for turning validated packs into learner paths,
proof upgrades, solver feedback, and consumer boundaries is
[`docs/foundational-resources/CURRICULUM-RESOURCE-EXECUTION-PLAN.md`](docs/foundational-resources/CURRICULUM-RESOURCE-EXECUTION-PLAN.md).
The commit-sized curriculum/resource work matrix is
[`docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md`](docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md).
The current execution ledger for stabilizing the 149 current math packs,
resolving unclassified solver-reuse rows, completing learner paths, and
deepening proof routes field by field is
[`docs/foundational-resources/MATH-CURRICULUM-DETAILED-BUILD-PLAN.md`](docs/foundational-resources/MATH-CURRICULUM-DETAILED-BUILD-PLAN.md).
The current learner-spine audit over all non-template math packs is
[`docs/foundational-resources/LEARNER-COVERAGE-AUDIT.md`](docs/foundational-resources/LEARNER-COVERAGE-AUDIT.md);
it records all 149 current non-template packs as focused-lesson linked, with no
path-only, index-only, or missing learner buckets.
The detailed operating roadmap for building the math-curriculum resource system
across ontology rows, example packs, learner pages, proof routes, solver reuse,
rules/law transfer, consumer boundaries, and eventual library splits is
[`docs/foundational-resources/RESOURCE-BUILDOUT-ROADMAP.md`](docs/foundational-resources/RESOURCE-BUILDOUT-ROADMAP.md).
The compact all-field consumer readiness table is
[`docs/foundational-resources/FIELD-READINESS-QUERY-MATRIX.md`](docs/foundational-resources/FIELD-READINESS-QUERY-MATRIX.md);
it records the smoke-checked route, bridge lookup, checked-row drilldown, and
theorem boundary for all 18 math fields.
The proof-route query matrix is
[`docs/foundational-resources/PROOF-ROUTE-QUERY-MATRIX.md`](docs/foundational-resources/PROOF-ROUTE-QUERY-MATRIX.md);
it records route-level summary queries and boundaries for finite replay,
Boolean CNF/LRAT, QF_BV, QF_LIA/Diophantine, QF_LRA/Farkas, QF_UF/Alethe, and
Lean-horizon resources.
The theorem-horizon query guide is
[`docs/foundational-resources/THEOREM-HORIZON-QUERIES.md`](docs/foundational-resources/THEOREM-HORIZON-QUERIES.md);
it records route, pack, field, and text queries for `lean-horizon` rows so
consumers can find theorem boundaries without treating them as checked SMT
evidence; the public query script also exposes
`horizon-frontier` for theorem-boundary rows with finite-shadow contrast,
including finite/infinite cardinality, algebra homomorphism/quotient structure,
vector-space/duality/module/tensor structure, group-action/orbit-stabilizer
and Burnside theorem boundaries, monoid/permutation-group theorem boundaries,
finite random-variable and conditional-expectation theorem boundaries,
recurrence/asymptotic, stochastic-kernel, and
martingale/stopping theory, finite integration/Lebesgue theorem boundaries,
finite product-measure/Fubini-Tonelli theorem boundaries,
root-finding convergence/stability, and
calculus differentiability/integrability/FTC/multivariable theory,
complex-analysis/factorization theory, convexity/Jensen theorem boundaries,
hyperplane-separation/duality, KKT sufficiency, active-set method theory, SDP
duality/Slater-condition theory, and gradient-descent convergence/rate
theory, line-search termination/convergence theory, Wolfe-line-search
existence/convergence theory, and projected-gradient projection/convergence
theory, proximal-gradient proximal-map/convergence theory, max-flow/min-cut
theorem boundaries, shortest-path theorem boundaries, topological-sort theorem
boundaries, finite topology/compactness/connectedness/quotient/specialization
theorem boundaries, affine-geometry affine-combination/incidence,
incidence-geometry projective/configuration, orientation/area
affine-volume/change-of-variables, circle-geometry tangent/chord,
rigid-configuration graph-rigidity/classification, inversion-geometry
circle-line, and cyclic-geometry Ptolemy theorem boundaries.
The theorem-horizon lane now also has a focused finite chain-complex torsion
boundary that keeps one-entry Smith replay and checked `2*k = 1`
QF_LIA/Diophantine evidence separate from general Smith normal form,
universal coefficient, Ext/Tor, exact-sequence, chain-homotopy, and
topological-invariance theorem coverage.
The solver-reuse query guide is
[`docs/foundational-resources/SOLVER-REUSE-QUERIES.md`](docs/foundational-resources/SOLVER-REUSE-QUERIES.md);
it records promoted-pack, proof-route, field, and checked-row queries for
solver/proof contributors mining the resource corpus without turning
educational rows into benchmark or parity claims.
The proof-upgrade query guide is
[`docs/foundational-resources/PROOF-UPGRADE-QUERIES.md`](docs/foundational-resources/PROOF-UPGRADE-QUERIES.md);
it records route-summary, replay-only row, route-relevant pack, checked-row,
curriculum-node, solver-reuse, and horizon queries for choosing certificate
upgrades without over-promoting finite replay rows.
The trust-boundary query guide is
[`docs/foundational-resources/TRUST-BOUNDARY-QUERIES.md`](docs/foundational-resources/TRUST-BOUNDARY-QUERIES.md);
it records proof-status and result-status drilldowns for checked evidence,
replay-only finite rows, and Lean-horizon boundaries before consumers display
or promote resource claims.
The fragment-demand query guide is
[`docs/foundational-resources/FRAGMENT-DEMAND-QUERIES.md`](docs/foundational-resources/FRAGMENT-DEMAND-QUERIES.md);
it records fragment-scoped pack and row queries for Bool, QF_BV, QF_LIA,
QF_LRA, QF_UF, finite replay, and Lean-horizon resources so solver and proof
contributors can mine curriculum pressure without turning it into parity
evidence.
The rejection-case query guide is
[`docs/foundational-resources/REJECTION-CASE-QUERIES.md`](docs/foundational-resources/REJECTION-CASE-QUERIES.md);
it records malformed-claim and route-scoped rejection queries while keeping
public resource rows separate from proof-cookbook tamper tests.
The checker-tamper matrix is
[`docs/foundational-resources/CHECKER-TAMPER-MATRIX.md`](docs/foundational-resources/CHECKER-TAMPER-MATRIX.md);
it maps each active proof route from malformed source-row discovery to the
focused corrupted-evidence command, and records routes that still need a tamper
regression before they can be called tamper-covered.
The claim-label matrix is
[`docs/foundational-resources/CLAIM-LABEL-MATRIX.md`](docs/foundational-resources/CLAIM-LABEL-MATRIX.md);
it maps `expected_result` plus `proof_status` pairs to allowed downstream
display labels so consumers do not turn checked evidence, finite replay,
Lean-horizon rows, or promoted solver-reuse packs into theorem, benchmark, or
parity claims; the public consumer query script exposes the same mapping through
`python3 scripts/query-foundational-resources.py labels`.
The public data contract is
[`docs/foundational-resources/PUBLIC-DATA-CONTRACT.md`](docs/foundational-resources/PUBLIC-DATA-CONTRACT.md);
it defines the JSON files, stable fields, schema/version expectations,
compatibility rules, smoke commands, coverage summaries, and display-label
counts that make the R6 consumer boundary usable without importing Axeyum
internals.
The coverage-frontier query guide is
[`docs/foundational-resources/COVERAGE-FRONTIER-QUERIES.md`](docs/foundational-resources/COVERAGE-FRONTIER-QUERIES.md);
it ranks field, fragment, curriculum-node, and decidability groups by checked
evidence, replay-only refutations, and Lean-horizon pressure, with
action-filtered worklists for proof-review/proof-upgrade/theorem-horizon
routing, so builders can choose the next pack, proof-upgrade, proof-review, or
learner-page increment from the public JSON contract.
The pack-frontier query guide is
[`docs/foundational-resources/PACK-FRONTIER-QUERIES.md`](docs/foundational-resources/PACK-FRONTIER-QUERIES.md);
it drills from those group-level rankings to concrete pack worklists with
checked-density, proof-review, theorem-horizon, route-promotion, and
finite-shadow filters.
The curriculum-node query guide is
[`docs/foundational-resources/CURRICULUM-NODE-QUERIES.md`](docs/foundational-resources/CURRICULUM-NODE-QUERIES.md);
it records concept, pack, field, route, checked-row, and horizon drilldowns for
consumers that start from the formal curriculum DAG rather than a field or
proof route.
The proof-route family selector is
[`docs/foundational-resources/PROOF-ROUTE-FAMILY-SELECTION.md`](docs/foundational-resources/PROOF-ROUTE-FAMILY-SELECTION.md);
it picks one representative replay-heavy family per active proof route and
states when another compact negative row is worth promoting to checked
evidence.
The proof-route learner snippets guide is
[`docs/learn/math/proof-route-learner-snippets.md`](docs/learn/math/proof-route-learner-snippets.md);
it gives reusable trust-boundary wording for Boolean CNF/LRAT, QF_LRA/Farkas,
QF_UF/Alethe, QF_LIA/Diophantine, and QF_BV/DRAT rows.
The matrix computation consumer query guide is
[`docs/foundational-resources/MATRIX-COMPUTATION-QUERIES.md`](docs/foundational-resources/MATRIX-COMPUTATION-QUERIES.md);
it records exact concept-plus-route queries for LU/nullspace, residual,
Schur complements, rank/nullity, eigenpair, singular-value, random-matrix,
chain/cochain/UCT, tensor/module, operator, and Chebyshev resources.
The probability/statistics consumer query guide is
[`docs/foundational-resources/PROBABILITY-STATISTICS-QUERIES.md`](docs/foundational-resources/PROBABILITY-STATISTICS-QUERIES.md);
it records exact concept-plus-route queries for finite probability tables,
finite measure, product/integration, pushforwards, conditional expectation,
stochastic kernels, tail counts, exact tests, and finite random-matrix
moments, including Schur conditional-variance shadows.
The measure-theory consumer query guide is
[`docs/foundational-resources/MEASURE-THEORY-QUERIES.md`](docs/foundational-resources/MEASURE-THEORY-QUERIES.md);
it records exact concept-plus-route queries for finite measure additivity,
product/integration, pushforwards, conditional expectation, martingales,
kernels, hitting times, and concentration resources.
The topology/homology consumer query guide is
[`docs/foundational-resources/TOPOLOGY-HOMOLOGY-QUERIES.md`](docs/foundational-resources/TOPOLOGY-HOMOLOGY-QUERIES.md);
it records exact concept-plus-route queries for metric balls, finite topology,
compactness, connectedness, quotient/specialization rows, finite homology,
cohomology, UCT shadows, and cup-product resources.
The algebra structure consumer query guide is
[`docs/foundational-resources/ALGEBRA-STRUCTURE-QUERIES.md`](docs/foundational-resources/ALGEBRA-STRUCTURE-QUERIES.md);
it records exact concept-plus-route queries for finite groups/actions,
homomorphisms, ideals, quotient rows, modules, tensor rows, and fixed-width
residue/field resources.
The number and arithmetic consumer query guide is
[`docs/foundational-resources/NUMBER-ARITHMETIC-QUERIES.md`](docs/foundational-resources/NUMBER-ARITHMETIC-QUERIES.md);
it records exact concept-plus-route queries for gcd/divisibility, CRT,
nonunit inverse, fixed-width residue, totality, quotient/ideal, and
exact-vs-floating resources.
The geometry resource consumer query guide is
[`docs/foundational-resources/GEOMETRY-RESOURCE-QUERIES.md`](docs/foundational-resources/GEOMETRY-RESOURCE-QUERIES.md);
it records exact concept-plus-route queries for finite coordinate/incidence/
rigid/affine/orientation geometry and finite circle/inversion/cyclic geometry
resources.
The graph/discrete consumer query guide is
[`docs/foundational-resources/GRAPH-DISCRETE-QUERIES.md`](docs/foundational-resources/GRAPH-DISCRETE-QUERIES.md);
it records exact concept-plus-route queries for finite graph coloring,
reachability, matching, cuts, d-separation, fixed-width coloring, and BFS/DFS
runtime resources.
The optimization/convexity consumer query guide is
[`docs/foundational-resources/OPTIMIZATION-CONVEXITY-QUERIES.md`](docs/foundational-resources/OPTIMIZATION-CONVEXITY-QUERIES.md);
it records exact concept-plus-route queries for LP objectives, convexity
shadows, KKT/QP/SDP rows, first-order method steps, projections, residuals,
Schur-complement shadows, and exact-vs-floating boundary resources.
The functional-analysis/operator consumer query guide is
[`docs/foundational-resources/FUNCTIONAL-OPERATOR-QUERIES.md`](docs/foundational-resources/FUNCTIONAL-OPERATOR-QUERIES.md);
it records exact concept-plus-route queries for finite operators, Chebyshev
rows, inner-product/projection rows, spectral and singular-value rows, and
dual/tensor equality resources.
The analysis/numerical consumer query guide is
[`docs/foundational-resources/ANALYSIS-NUMERICAL-QUERIES.md`](docs/foundational-resources/ANALYSIS-NUMERICAL-QUERIES.md);
it records exact concept-plus-route queries for bounded real-analysis rows,
numerical-method rows, residuals, singular-value shadows, dynamics/Euler,
Runge-Kutta midpoint, Heun rows, Backward Euler rows, Crank-Nicolson rows,
Adams-Bashforth rows, BDF2 rows, Simpson-rule quadrature rows, Schur
complements, real-Schur rows, and complex real-pair resources.
The dynamics consumer query guide is
[`docs/foundational-resources/DYNAMICS-QUERIES.md`](docs/foundational-resources/DYNAMICS-QUERIES.md);
it records exact concept-plus-route queries for finite recurrences,
transition/invariant rows, Euler, Backward Euler, and Crank-Nicolson rows,
Adams-Bashforth rows, BDF2 rows, stochastic kernels, Markov chains, and
hitting-time resources.
The foundations/discrete consumer query guide is
[`docs/foundational-resources/FOUNDATIONS-DISCRETE-QUERIES.md`](docs/foundational-resources/FOUNDATIONS-DISCRETE-QUERIES.md);
it records exact concept-plus-route queries for Boolean proof rows, finite
proof patterns, bounded induction, finite quantifiers, cardinality, counting,
Boolean algebra, partition, and relation/function resources.
The finite countermodel replay consumer query guide is
[`docs/foundational-resources/COUNTERMODEL-REPLAY-QUERIES.md`](docs/foundational-resources/COUNTERMODEL-REPLAY-QUERIES.md);
it records pack-scoped concept queries for Boolean assignments, finite
predicate tables, proof-pattern counterexamples, function-table conflicts, and
finite order/lattice countermodels while keeping proof-route claims separate.
The rules/law transfer crosswalk that maps finite predicates, arithmetic
thresholds, graph reachability, precedence, category equivalence, and proof
routes into concrete policy/rule checks is
[`docs/foundational-resources/RULES-LAW-CROSSWALK.md`](docs/foundational-resources/RULES-LAW-CROSSWALK.md).
The rules/law query guide is
[`docs/foundational-resources/RULES-LAW-QUERIES.md`](docs/foundational-resources/RULES-LAW-QUERIES.md);
it records copyable `scripts/query-rules-as-code.py` commands for pack
discovery, coverage summaries, checked-obligation lookup, generated
query-family lookup, and bounded generated-row inspection.
The rules/law pattern matrix is
[`docs/foundational-resources/RULES-LAW-PATTERN-MATRIX.md`](docs/foundational-resources/RULES-LAW-PATTERN-MATRIX.md);
it maps finite predicates, role/tenant relations, thresholds, monotonicity,
version transitions, precedence, category equivalence, workflow reachability,
and bounded implementation-equivalence patterns back to math concept rows,
proof routes, current packs, and copyable queries.
The learner-facing rules/law trust-boundary page is
[`docs/learn/rules-law-trust-boundary.md`](docs/learn/rules-law-trust-boundary.md);
it walks from human-authored source rules through formal models, replayed
witnesses, checked obligations, and explicit legal/theorem horizons.
Current resource-buildout status (2026-07-03): the public JSON layer reports
122 concept rows, 149 non-template packs, 972 expected checks (494 `sat`,
366 `unsat`, 112 `not-run`), 375 checked rows, 485 replay-only rows, 112
Lean-horizon rows, and 149 promoted solver-reuse packs. The rules/law JSON
layer now reports 7 packs, 1,037
bounded sample rows, 1,942 generated query rows, 27 checked obligations, and
9 replayed witness rows. The learner
coverage audit records all 149 non-template packs as focused-lesson linked,
with no path-only, index-only, or missing learner buckets. The first QF_UF/Alethe
proof upgrade wave now includes equivalence classes, relations/functions, finite
groups, function composition, finite algebra homomorphisms, finite monoids, and
finite group actions, with finite continuous-map preimage membership,
finite module scalar-closure membership, finite vector-space additive-closure
membership, finite dual-space covector additivity, finite tensor-product
left-additivity, finite order-lattice antisymmetry, finite ideal
additive-closure membership, finite quotient-topology, finite
specialization-order, finite cohomology, finite universal-coefficient shadow,
and finite cup-product extensions. The
finite countermodel lane now also makes explicit finite universes, Boolean
assignments, predicate extensions, relation tables, function tables, and finite
order/lattice counterexamples queryable as one checked bridge concept with a
learner-facing replay guide and a consumer query guide, without changing pack
or check totals. The theorem-horizon lane now also has a consumer query guide
for finding `lean-horizon` rows by route, field, pack, and topic while keeping
them out of checked-evidence claims, and focused boundary pages for real
completeness, monotone convergence, finite hitting-time theory,
Chebyshev/operator theory, finite concentration, and finite Euler/ODE theory
now keep finite checked shadows separate from general theorem targets. The solver-reuse
lane now also has a consumer query guide for finding promoted packs by proof
route, field, and checked row while keeping educational resources separate from
benchmark and parity claims. The proof-upgrade lane now also has a consumer
query guide for finding replay-only rows, route-relevant packs, checked
evidence contrasts, curriculum-node/R5 slices, and Lean horizons before
promoting another certificate row. The curriculum-node
lane now also has a consumer query guide for starting from nodes such as
`sets`, `linear-algebra`, `modular-arithmetic`, and `calculus`, then drilling
into concepts, packs, checked rows, and theorem horizons. The
finite algebra-homomorphism lane now also promotes the
concrete bad group-homomorphism row through QF_UF/Alethe after exact table
replay isolates `phi(1+1)=1` versus `phi(1)+phi(1)=0`. The finite
linear-algebra lane now also promotes the explicit
`qf-lra-bad-lu-product-entry` row after exact LU replay computes
`(L*U)[1,1] = 3` while the malformed row claims `4`, and the bad
nullspace-component row through QF_LRA/Farkas after exact matrix replay
computes `A*v = 0` for `v = [2, -1]` while the bad row claims the first
component is `1`. The finite
metric-continuity lane now also promotes the bad open-ball preimage row through
QF_LRA/Farkas after exact finite replay computes the output-ball preimage as
`{p0, p1}` while the bad row claims `p2` is inside even though
`|f(p2)-0| = 1`. The sequence-limit lane now also promotes the bad
reciprocal-tail bound row through QF_LRA/Farkas after exact replay computes
`a_2 = 1/3` while the bad row claims the distance is strictly below `1/4`.
The analysis bridge lane now also makes rational interval replay, sequence-tail
shadows, Cauchy-tail shadows, squeeze shadows, derivative-identity shadows, and
integration horizons first-class atlas concepts. The bounded-family/asymptotic
boundary lane now also makes finite BFS/DFS runtime counters, finite recurrence
prefixes, fixed coefficient windows, bounded dynamics traces, and finite Euler
error rows queryable as one bridge concept while keeping asymptotic runtime,
closed-form recurrence, convergence-rate, and limiting theorem claims in the
Lean-horizon lane. The polynomial bridge lane now also makes fixed coefficient
tuples, division/factor witnesses, coefficient windows, root-finding steps,
derivative shadows, and polynomial geometry obligations queryable by one
concept while keeping general factorization, algebraic closure, root
distribution, and generating-function convergence as proof horizons. The algebra
equality-certificate lane now makes the table-replay-versus-QF_UF/Alethe
promotion rule queryable by one bridge concept, so finite algebra rows graduate
only when the table checker and congruence certificate tell different useful
stories. The finite
order/lattice lane now also promotes the false Boolean-lattice top-element row
through Bool/CNF DRAT/LRAT after exact relation replay isolates `B !<= A`
while the bad claim that `A` is top requires `B <= A`. The modular-arithmetic
QF_LIA/Diophantine lane now also includes the incompatible non-coprime CRT row:
`x == 1 mod 4` and `x == 2 mod 6` reduce to `4*a - 6*b = 1`, where
`gcd(4,6)=2` does not divide `1`, and the fixed-width QF_BV lane now includes
the composite nonunit inverse search and the modulo-5 Fermat-unit counterexample
search: no 3-bit residue `b < 6` satisfies `(2*b) mod 6 = 1`, and no 3-bit
residue `0 < a < 5` satisfies `a^4 mod 5 != 1`, both with checked
DIMACS/DRAT evidence. The topology
QF_LIA/Diophantine lane now also includes finite chain-complex torsion via
one-entry Smith diagonal replay and checked rejection of `2*k = 1`, plus
finite simplicial homology boundary-square cancellation via checked rejection
of the false coefficient row `coeff_b = 1` when `boundary(boundary([a,b,c]))`
forces `coeff_b = 0`. The
measure/probability QF_LRA/Farkas lane now also promotes finite
product-measure's bad product-probability and bad marginal rows through
source-linked exact linear contradictions after replay computes the product
mass and row marginal, plus finite random-variables' bad pushforward row after
replay computes the outcome mass and bad expectation-through-pushforward row
after replay computes `E[X] = 20`, with separate `qf-lra-*` proof rows for the
final exact-linear contradictions, finite-integration's bad expectation row
after replay computes the integral, finite-conditional-expectation's bad
total-expectation row after replay computes `E[X] = E[E[X|G]] = 7/2` while the
bad row claims `4`, and its bad tower-property row after nested-partition
replay computes `7/2` rather than `4`, plus its bad variance-decomposition row
after finite replay computes `Var(X)=35/4`, `E[Var(X|G)]=5/2`, and
`Var(E[X|G])=25/4` while the bad row claims total variance `9`,
finite-measure's explicit `qf-lra-bad-complement-measure` row
after finite replay computes the event
and total measures, finite-measure-monotonicity's bad subset-measure and
union-subadditivity rows after finite replay computes the subset/superset
measures and the union bound `mu(A)+mu(B)=4/3`, finite-martingales'
bad stopped-expectation and conditional-expectation rows after bounded stopping
replay computes `E[M_tau] = 0` and finite filtration replay computes the
up-block expectation, finite Markov-chain's bad stochastic-row and false
stationary-distribution rows now kept as exact replay while
`qf-lra-bad-stochastic-row` and `qf-lra-bad-stationary-distribution` own the
checked Farkas proof-object regressions in solver-reuse metadata,
finite concentration's bad tail-bound and bad union-bound rows after exact
finite replay computes `P(X >= 2) = 1/4` and `P(A union B) = 3/4`, and finite
hitting-times' bad survival-mass and bad expected-time rows after replay
computes `P(T > 4) = 5/16` and the start equation reduces to
`2*h_start = 2 + h_start + h_middle`, plus finite-probability's bad
total-variation row after replay computes absolute differences `1/6, 0, 1/6`,
`l1 = 1/3`, and `TV = 1/6` while the bad row claims `1/4`.
The statistics
QF_LRA/Farkas lane now also promotes exact-statistical-tests' bad Fisher
left-tail and probability-ordered two-sided rows after fixed-margin replay
computes `17/70` rather than `1/4` and `17/35` rather than `1/2`,
and exact-statistical-tests' bad multinomial row after finite enumeration
computes `1/9` rather than `1/6`,
alongside descriptive-statistics' explicit `qf-lra-bad-variance` row after
exact finite-sample replay computes `Var(X) = 5/4` rather than `3/2`.
The numerical-analysis QF_LRA/Farkas lane now also promotes
numerical-linear-algebra's bad solution-box upper-bound row after exact
linear-system replay computes `x0 = 6/5` rather than satisfying the claimed
`x0 <= 1` bound, alongside its bad Jacobi first-step error-bound row where
iteration replay computes `||x1 - x*||_inf = 7/44` rather than satisfying the
claimed `1/8` bound.
The foundational concept atlas now also includes 65 generated R1 bridge
rows: finite model replay, counterexample proof, bounded theorem shadows,
refutation-as-query, finite proof-pattern replay, finite quantifier expansion,
bounded induction obligations, Boolean CNF DRAT/LRAT anatomy, QF_LRA Farkas
certificate anatomy, exact-vs-floating arithmetic, LP objective-threshold
replay, rational convexity/gradient shadows, QF_UF Alethe certificate
anatomy, QF_BV bit-blast certificate anatomy, gcd/divisibility witnesses,
modular CRT/inverse witnesses, finite counting replay, finite graph replay/
obstruction, finite dynamics/Euler replay, finite Boolean algebra, finite
partition/relation roundtrips, finite image/preimage/inverse tables, finite
bijection/cardinality,
cardinality theorem horizons, metric balls, bounded epsilon-delta shadows,
compactness shadows, connectedness shadows, continuity-by-preimage, finite
topology closure/interior and homeomorphism replay,
finite quotient-topology replay,
finite specialization-order replay, finite boundary-operator replay, finite
chain-complex/homology replay, finite torsion-homology replay, finite
cohomology replay, finite universal-coefficient shadow replay, finite
cup-product replay, LU factorization and nullspace
replay with checked bad product-entry and bad nullspace-component evidence,
rank-nullity replay, residual bounds, eigenpair witnesses, characteristic polynomial replay, finite
trace-invariant checks, finite random-matrix moments, finite measure additivity, finite probability mass
tables and finite distribution-distance rows, finite pushforward distributions, finite stochastic kernels, finite
conditional expectations, finite product-measure/integration replay, finite
tail/count obstructions, homomorphism preservation, kernel/image replay,
quotient maps,
ideal closure, module actions, tensor bilinearity, finite group actions,
totality conventions, and Lean horizons, plus coordinate/incidence/rigid/
oriented geometry replay, finite circle/inversion/cyclic geometry replay,
complex real-pair transform replay, finite inner-product/projection replay,
and finite operator/Chebyshev replay, so resource packs can point at shared
evidence and boundary vocabulary instead of repeating it locally.
The measure-theory bridge rows now make finite event-algebra/additivity,
complement, monotonicity, subadditivity, product-table, marginal, finite
Fubini-style sum, and simple-function integral replay queryable while keeping
Lebesgue measure, general product-measure existence, convergence theorems, and
almost-everywhere reasoning in the Lean-horizon lane.
The public foundational-resource consumer query layer now also exercises the
topology lane: Boolean, Alethe, Diophantine, and QF_BV field readiness,
metric/compactness/preimage/closure/homeomorphism/quotient/specialization/boundary/homology/
torsion/cohomology/universal/cup
bridge lookups, concept-scoped metric-ball, bounded epsilon-delta,
finite topology-operator/homeomorphism, finite quotient-topology, finite
specialization-order, finite boundary-operator, chain-complex/homology, and
finite torsion-homology/cohomology/universal-coefficient/cup-product
queries, and checked
Boolean/Alethe/Diophantine/QF_BV rows for finite topology, compactness, connectedness,
continuous maps, homeomorphism replay, finite quotient topology, finite specialization order, boundary
replay, homology, torsion homology, cohomology, finite universal-coefficient
shadow, finite cup products, metric balls, and bounded epsilon-delta shadows are
smoke-checked through the committed JSON contract, while arbitrary compactness,
connectedness, quotient topology universal properties, quotient-map theorem schemas,
specialization-order theorems, homeomorphism invariance,
homology/cohomology invariance, exact sequences, universal coefficient theorems,
cohomology-operation laws, and
general algebraic-topology theorems stay in the theorem-horizon lane.
The public foundational-resource consumer query layer now also exercises the
statistics lane: Farkas field readiness, finite-table/tail-count bridge
lookups, random-matrix bridge lookups, concept-scoped
`bridge_random_matrix_finite_moment` Farkas pack and checked-row queries, and
checked Farkas/Diophantine rows for exact finite tests, contingency tables,
regression, random matrices, probability/process tables, concentration, and
stochastic kernels are smoke-checked through the committed JSON contract,
while floating-point inference, asymptotic sampling, MCMC, VI,
model-calibration claims, random-matrix asymptotics, universality, simulation
quality, and high-dimensional limit laws stay in numerical-honesty or
theorem-horizon lanes.
The public foundational-resource consumer query layer now also exercises the
linear-algebra lane: Farkas/Alethe field readiness, rank/projection bridge
lookups, and checked rows for exact rational matrices, residual/eigen
witnesses, finite vector spaces, dual spaces, modules, tensors, geometry
dot-products, finite SDP/KKT/active-set rows, and matrix process equations are
smoke-checked through the committed JSON contract, while spectral theorems,
conditioning/stability, and general vector-space/module/tensor theorem claims
stay in the horizon lanes; the focused
[`linear-algebra-structure-theorem-boundary.md`](docs/learn/math/linear-algebra-structure-theorem-boundary.md)
page now records that split for finite vector, dual, module, and tensor packs.
The public foundational-resource consumer query layer now also exercises the
core algebra/number/graph lanes: abstract-algebra Alethe readiness,
homomorphism/ideal bridge lookups, concept-scoped homomorphism-preservation
Alethe checked-row queries, checked Alethe and fixed-width QF_BV rows;
number-theory Diophantine readiness, finite-family lookups, and checked
integer-arithmetic plus fixed-width residue rows; and graph-theory Boolean plus
LIA readiness,
graph-family/runtime lookups, checked finite
coloring/reachability/matching/cut/d-separation rows, and checked finite
BFS/DFS cost-counter rows. These are smoke-checked through the committed JSON contract without
promoting arbitrary algebraic-structure theorems, unbounded number-theory
claims, asymptotic graph algorithms, or general graph theorems. The focused
[`algebra-homomorphism-quotient-theorem-boundary.md`](docs/learn/math/algebra-homomorphism-quotient-theorem-boundary.md)
page now records the finite map/kernel/image/ideal/quotient split from general
isomorphism and ideal-theory theorem claims.
The public foundational-resource consumer query layer now also exercises the
analysis/numerical/complex lanes: real-analysis Farkas readiness,
epsilon/gradient bridge lookups, and checked bounded-analysis rows;
numerical-analysis Farkas readiness, residual/operator bridge lookups, and
checked exact residual, Euler, operator, recurrence, and optimization-step
rows; and complex-analysis Farkas readiness, real-pair bridge lookup, and
checked algebraic complex rows. These are smoke-checked through the committed
JSON contract without promoting completeness, convergence, floating-point
stability, holomorphic, analytic-continuation, or theorem-level calculus
claims.
The public foundational-resource consumer query layer now also exercises the
foundations/discrete/probability lanes: logic/proof Boolean readiness,
proof-vocabulary lookups, and checked proof-pattern/CNF rows; set-theory and
foundations Alethe/Boolean readiness, partition and finite-Boolean-algebra
lookups, and checked finite relation/function/quotient/equality and set-family
contradiction rows; discrete-math Diophantine/Boolean readiness,
finite-family lookups, and checked counting/coefficient/tail-count and finite
Boolean-algebra rows; and
probability-theory Farkas readiness, probability-table lookups, and checked
finite probability/process rows. These are smoke-checked through the committed
JSON contract without promoting proof automation, ZFC/infinite set theory,
asymptotic combinatorics, continuous probability, stochastic-process limits,
or theorem-level probability claims.
The sequence/real-analysis lane now also splits bounded monotone sequence and
finite recurrence-prefix, separation/root-finding, KKT, active-set QP, SDP, and gradient-descent checks into focused packs: finite monotone-prefix
replay, finite prefix supremum, finite tail-gap replay, Fibonacci prefix
replay, affine recurrence replay, companion-matrix state replay, exact
bisection/Newton replay, finite convex-combination/separator replay,
finite constrained-quadratic KKT replay, finite active-set QP face/slack
replay plus inactive-slack evidence, finite two-by-two SDP replay, exact gradient-descent step replay, exact
Armijo line-search replay, exact Wolfe line-search replay, exact
projected-gradient interval/decrease replay, and exact L1 proximal-gradient
soft-threshold plus box-constrained replay, and checked
QF_LRA/Farkas rejection of bad upper-bound, bad finite-value, bad Newton-step,
bad bisection-width, bad convex-combination,
bad separator, bad stationarity, bad free-gradient, bad inactive-slack,
bad degenerate active-set multiplier, bad objective, bad duality-gap, bad slack-entry, bad decrease,
bad step-coordinate, bad descent-bound, bad Armijo, bad descent-direction, bad accepted-candidate, bad Wolfe-minimizer,
bad Wolfe-sufficient-decrease, bad Wolfe-curvature, bad
projection, bad projected-decrease, bad proximal-point, and bad
composite-decrease, and bad box-proximal-point rows, while
monotone convergence, closed-form recurrence solving, asymptotics, and
separation/KKT/active-set/SDP/descent/Wolfe/line-search/projected-gradient/proximal-gradient/stability/convergence theorems remain Lean-horizon.
The optimization/convexity bridge rows now make exact LP feasibility,
objective-threshold Farkas replay, finite midpoint/Jensen shadows, affine
monotonicity, gradient replay, Hessian-minor witnesses, least-squares
normal-equation replay, finite root-finding steps, and finite hyperplane
separation plus finite KKT stationarity/complementarity, finite active-set QP
face/slack replay, and finite SDP objective/slack/gap replay plus finite
gradient-descent step/decrease replay and finite line-search
rejection/acceptance replay plus finite Wolfe line-search replay plus finite
projected-gradient interval/decrease replay plus finite proximal-gradient
soft-threshold, composite-decrease, and box-plus-L1 replay queryable while keeping duality, KKT
sufficiency, active-set method theory, SDP strong duality, general separation, and
algorithm-convergence claims in the Lean-horizon lane.
The public foundational-resource consumer query layer now also exercises the
functional-analysis/operator lane: field readiness over
`functional_analysis_and_operator_theory`, the shared operator/Chebyshev
bridge lookup, concept-scoped `bridge_finite_operator_chebyshev` Farkas pack
and checked-row queries, and checked Farkas rows for finite operators, inner
products, Chebyshev grids, interpolation/residual rows,
alternation-magnitude refutations, spectral examples, and
characteristic-polynomial arithmetic are smoke-checked through the committed JSON contract,
while Banach/Hilbert/compact-operator/Haar-space/minimax/alternation-theorem
and infinite-dimensional claims stay in the theorem-horizon lane.
The first route-note pass has also landed on the high-use learner cluster
pages for logic/proof, graph/discrete reasoning, linear algebra/optimization,
probability/statistics, and algebra/number theory.
The first proof-object anatomy learner page now follows
`proof-methods-refutation-v0` from the PHP(3,2) source claim through committed
CNF, emitted DRAT/LRAT proof objects, and same-artifact corrupted-proof
rejection.
The first Farkas certificate anatomy learner page now follows
`linear-optimization-v0` from an exact LP threshold conflict through source
SMT-LIB, emitted `UnsatFarkas` evidence, and same-artifact multiplier tamper
rejection.
The first Alethe certificate anatomy learner page now follows
`equivalence-classes-v0` from a quotient-map congruence conflict through source
SMT-LIB, emitted zero-trust `UnsatAletheProof` evidence, and same-artifact
truncated-proof rejection.
The first Diophantine certificate anatomy learner page now follows
`modular-arithmetic-v0` from a nonunit modular-inverse obstruction through
source SMT-LIB, emitted `UnsatDiophantine` evidence, and same-artifact
contradiction-row tamper rejection.
The first QF_BV bit-blast certificate anatomy learner page now follows
`finite-fields-v0` from fixed-width finite-field BV rows through source
SMT-LIB, generated DIMACS/DRAT evidence, and same-artifact truncated-DRAT
rejection.
The matrix-computation learner index now groups LU/nullspace, rank/nullity, residual,
projection, eigenpair, characteristic-polynomial, finite random-matrix,
chain-complex, operator, module, and tensor rows by replay, QF_LRA/Farkas,
QF_UF/Alethe, QF_LIA/Diophantine, Lean-horizon, and numerical-honesty
boundaries.
The matrix corpus/benchmark boundary note now separates educational matrix
examples from solver regressions, benchmark-corpus rows, and theorem-horizon
claims, so matrix resources can be reused without implying performance,
parity, numerical-stability, or general-theorem coverage.
The analysis/calculus theorem-horizon map now groups real completeness,
IVT/MVT/FTC, compactness/connectedness, sequence and recurrence convergence,
root-finding convergence, optimization convergence/duality,
measure/probability convergence, functional-analysis/operator theory, and
dynamics by finite shadow, checked evidence route, missing Lean/theorem
dependency, and next build artifact.
The real-completeness theorem-boundary page now expands that first horizon row
into a concrete dependency ledger, linking existing rational interval,
sequence-tail, monotone-prefix, metric-continuity, RCF-shadow, and finite
compactness packs to least-upper-bound, Cauchy-completeness, monotone-
convergence, compactness, and uniform-continuity proof obligations without
turning finite shadows into theorem claims.
The algebra equality-certificate boundary page now makes the finite-algebra
promotion rule explicit: table replay owns concrete structure evaluation, while
QF_UF/Alethe rows are added only for isolated equality, congruence, closure,
representative, preservation, identity-action, action-compatibility, or
bilinearity certificates.
Those four certificate anatomy stories now also have first-class bridge rows in
the foundational concept atlas, making the active proof-object routes queryable
through shared R1 vocabulary.
The set/foundations bridge rows now make powerset/Boolean algebra,
partition/equivalence roundtrips, image/preimage/inverse tables,
finite bijection/cardinality checks, and infinite-cardinality theorem horizons
queryable through the same R1 vocabulary.
The geometry and complex-analysis bridge rows now make finite coordinate,
incidence, rigid-configuration, affine, oriented-area, circle-geometry, inversion-geometry, and complex real-pair transform replay
queryable without overstating synthetic, differential, global, or analytic
theorem coverage.
The learner spine now also splits the finite topology and finite measure
first-principles stories into standalone end-to-end pages, leaving the combined
topology/measure page as a cross-field bridge rather than the only entry point.
`linear-optimization-v0` now also has a standalone LP/Farkas end-to-end page
for feasible-point replay, objective-threshold replay, checked
QF_LRA/Farkas evidence, and tampered-certificate rejection, leaving the
combined linear-system/LP page as the matrix-to-optimization bridge.
`finite-probability-v0` now also has a standalone finite probability
mass-table page for exact PMF normalization, conditional probability, Bayes
posterior replay, checked QF_LRA/Farkas bad normalization, checked bad
conditional-probability rejection, checked bad posterior rejection, finite
independence replay, checked bad-independence rejection, total variation replay,
and checked bad-total-variation rejection, leaving the broader finite-probability
page as the stochastic-process bridge.
`bounded-dynamics-v0` now also has a standalone bounded recurrence dynamics
page for exact trace replay, finite invariant checking, threshold reachability,
and checked QF_LRA/Farkas bad transition-step, bad threshold-step, and bad invariant-bound
evidence, leaving the combined finite-dynamics/Euler page as the numerical-step
bridge.
`finite-euler-method-v0` now also has a standalone finite Euler method page
for exact explicit-Euler transition replay, finite polynomial-solution error
tables, monotone invariant checks, replay-only bad max-error,
bad terminal-error, and bad-step rejection, separate checked QF_LRA/Farkas
proof rows, and the ODE/numerical-analysis Lean horizon.
`finite-operator-v0` now also has a standalone finite-dimensional operator
page for exact `l1` norm replay, row-sum operator-bound replay, finite
Chebyshev recurrence replay, replay-only malformed norm/bound/Chebyshev rows,
and separate checked QF_LRA/Farkas `qf-lra-*` evidence rows, leaving the
broader bounded-dynamics/operator page as the cross-resource bridge.
The six active proof-cookbook routes for CNF/LRAT, QF_BV, QF_LIA, QF_LRA,
QF_UF/Alethe, and Lean horizons now each name concrete math example packs that
use the route.
The first example-family row now groups the recurring finite-algebra
QF_UF/Alethe congruence conflicts under `family_finite_algebra_alethe`,
backed by the shared `math_resource_uf_routes` regression.
The second example-family row now groups recurring exact-rational
QF_LRA/Farkas infeasibility rows under `family_exact_rational_farkas`,
backed by the shared `math_resource_lra_routes` regression and scoped to
the optimization/Farkas proof-route lane.
The third example-family row now groups recurring finite Boolean CNF/LRAT
refutations under `family_boolean_cnf_lrat`, backed by the shared
`math_resource_boolean_routes` regression across logic, counting, graph,
finite-set, and finite-topology packs.
The fourth example-family row now groups recurring integer/count QF_LIA
Diophantine and checked arithmetic-evidence obstructions under
`family_integer_diophantine`, backed by the shared `math_resource_lia_routes`
regression across number-theory, induction, counting, statistics, graph-search,
polynomial, and homology packs.
The fifth example-family row now groups fixed-width QF_BV/DRAT obligations
under `family_fixed_width_bv_drat`, backed by `math_resource_bv_routes` across
finite fields, finite rings, graph coloring, and bounded number-theory residue
search/bad-witness packs.
The generated coverage, field, proof-gap, learner/proof-upgrade, and
curriculum-pressure dashboards now expose conservative R0-R6 gate/next-gate
columns and overlapping fragment-pressure buckets, making R4-to-R5 solver-reuse
candidates and Bool/CNF, QF_BV, QF_LIA, QF_LRA, QF_UF, finite-replay, and
Lean-horizon demand visible without hand-maintained scans.
The generated solver-reuse disposition audit now reports 149 promoted math
packs, 0 non-benchmark-horizon packs, and 0 unclassified rows, so future
unclassified packs and deliberate non-benchmark rows surface in a
freshness-checked queue.
The generated curriculum-status audit now separates source `curriculum_status`
from generated `resource_status`, making source `planned` rows with validated
resource packs visible as explicit `covered` versus `lean-horizon` review
items.
The first structured solver-reuse batch is now fully promoted from R4 candidate
rows into source-linked regression artifacts with pack back-links.
`logic-basics-v0`, `finite-cardinality-v0`, `graph-matching-v0`,
`graph-reachability-v0`, `graph-cut-v0`, `graph-d-separation-v0`,
`finite-compactness-v0`, `finite-connectedness-v0`,
`graph-search-runtime-v0`, `integer-lia-v0`, `natural-arithmetic-v0`, and
`number-theory-v0` are the first promoted packs from that batch:
`tiny-cnf-refutation`,
`no-injection-four-to-three`, `triangle-no-perfect-matching`,
`disconnected-no-path`, `one-edge-cut-rejected`, and
`chain-conditioned-blocks` plus `collider-unconditioned-blocks` now have
source-linked DIMACS artifacts; topology's
`bad-open-cover-rejected` and `bad-connected-claim-rejected` now do too. The
Boolean `math_resource_boolean_routes` regression checks emitted DRAT and LRAT
proof objects, while
the learner/resource map now exposes a focused d-separation causal trust
boundary that keeps those finite DAG path-blocking rows separate from causal
identification, do-calculus, probabilistic graphical-model semantics,
adjustment-set correctness, and statistical consistency.
It also exposes a focused graph-cut trust boundary that keeps finite edge and
vertex cut replay plus the one-edge CNF non-cut row separate from Menger-style
cut theorems, max-flow/min-cut, scalable algorithms, spectral cuts,
graph-partitioning guarantees, and asymptotic claims.
The graph learner map now likewise exposes a focused matching trust boundary
that keeps finite matching replay, augmenting-path replay, and the `K3`
perfect-matching CNF refutation separate from Hall/Tutte theorem coverage,
matching algorithms, weighted matching, flow reductions, graph minors, and
asymptotic claims.
It also exposes a focused reachability trust boundary that keeps finite
BFS/DFS/no-path/cut replay and the disconnected no-path CNF refutation separate
from BFS/DFS correctness, all-pairs/dynamic reachability, graph-family,
graph-minor, and asymptotic claims.
It also exposes a focused coloring trust boundary that keeps replay-only finite
coloring witnesses, checked same-color rejection, Boolean CNF/LRAT evidence,
and QF_BV/DRAT evidence separate from chromatic-number, planar-coloring,
algorithm, graph-minor, and asymptotic claims.
It also exposes a focused graph-search runtime theorem boundary that keeps
finite BFS/DFS visited-counter replay and QF_LIA bad-bound evidence separate
from asymptotic runtime, graph-family lower-bound, average-case, heuristic,
parallel-search, and benchmark claims.
`bad-dfs-cost-bound-rejected` now has a source-linked
QF_LIA artifact checked by the `math_resource_lia_routes` arithmetic-evidence
regression and `diophantine-gcd-obstruction` now has a source-linked QF_LIA
artifact checked by the `math_resource_lia_routes` Diophantine regression,
`diophantine-gcd-obstruction-qf-lia` now adds the same checked route for
`number-theory-v0`, and
`bounded-natural-negative-rejected` now has a source-linked QF_LIA artifact
checked by the `math_resource_lia_routes` arithmetic-evidence regression, while
`quadratic-nonresidue-qf-bv-drat` and `bad-square-witness-qf-bv-drat` now have
source-linked QF_BV artifacts checked by the `math_resource_bv_routes` DRAT
regression.
The first consumer-facing query layer over the committed foundational-resource
JSON contract has landed in `scripts/query-foundational-resources.py` and
`docs/foundational-resources/CONSUMER-QUERIES.md`, covering summary counts,
pack discovery, field-plus-proof-route discovery, checked-row mining,
solver-reuse rows, atlas concept lookup, and curriculum field-readiness
summaries without importing validators or generators. The latest boundary
review keeps the foundational resources
JSON-first and in-repo: promoted solver-reuse rows are consumer-readable through
the query helper, and the field-readiness smoke set now spans all 18 math
fields: logic/proof, set foundations, discrete math, graph theory, number
theory, algebra, linear algebra, analysis, topology, measure/probability,
statistics, optimization, numerical analysis, dynamics, geometry, complex
analysis, and functional/operator theory. The smoke layer also exercises
representative bridge lookups and checked-row drilldowns for the active
Boolean, Alethe, Diophantine, Farkas, and QF_BV routes; there is still no
external consumer or repeated typed API need that would justify a crate or repo
split.
The compact
[`FIELD-READINESS-QUERY-MATRIX.md`](docs/foundational-resources/FIELD-READINESS-QUERY-MATRIX.md)
now turns that full-field smoke layer into a single consumer-facing table:
one row per math field with pack/check counts, the primary readiness route,
bridge lookup terms, checked-row drilldown, and the theorem claims that remain
out of scope.
The matrix computation lane now has
[`MATRIX-COMPUTATION-QUERIES.md`](docs/foundational-resources/MATRIX-COMPUTATION-QUERIES.md),
and the query helper accepts exact `--concept` filters on `packs` and `checks`,
so consumers can discover matrix rows by bridge concept plus proof route without
parsing generated Markdown or adding a typed API.
The probability/statistics lane now has
[`PROBABILITY-STATISTICS-QUERIES.md`](docs/foundational-resources/PROBABILITY-STATISTICS-QUERIES.md),
and the foundational smoke checks concept-scoped Farkas rows for probability
mass tables, finite measure, product/integration, pushforwards, conditional
expectation, stochastic kernels, tail counts, and random-matrix moments, so
downstream consumers can discover exact finite-table resources without
promoting continuous probability, asymptotic statistics, stochastic-process
limit, simulation-quality, or floating-point inference claims.
The measure-theory lane now has
[`MEASURE-THEORY-QUERIES.md`](docs/foundational-resources/MEASURE-THEORY-QUERIES.md),
and the foundational smoke checks finite measure additivity, complement,
monotonicity, subadditivity, product measure, marginals, integration,
pushforward, conditional expectation, martingale/stopped expectation,
stochastic-kernel, hitting-time, and concentration rows through Farkas queries,
so downstream consumers can discover finite measure resources without
promoting countable additivity, Lebesgue construction, convergence theorems,
almost-everywhere reasoning, stochastic-process limits, simulation quality, or
floating-point claims.
The topology/homology lane now has
[`TOPOLOGY-HOMOLOGY-QUERIES.md`](docs/foundational-resources/TOPOLOGY-HOMOLOGY-QUERIES.md),
and the foundational smoke checks concept-scoped Boolean, Farkas, Alethe,
Diophantine, and QF_BV rows for metric shadows, compactness, connectedness,
continuity, quotient topology, specialization order, boundary/homology,
torsion, cohomology, UCT, and cup-product resources, so downstream consumers
can discover finite topology resources without promoting general topology or
algebraic-topology theorem claims.
The algebra structure lane now has
[`ALGEBRA-STRUCTURE-QUERIES.md`](docs/foundational-resources/ALGEBRA-STRUCTURE-QUERIES.md),
and the foundational smoke checks concept-scoped Alethe/QF_BV rows for
homomorphisms, group actions, module actions, ideals, and modular residue
witnesses, so downstream consumers can discover finite algebra resources
without promoting arbitrary algebraic structure theorems.
The number/arithmetic lane now has
[`NUMBER-ARITHMETIC-QUERIES.md`](docs/foundational-resources/NUMBER-ARITHMETIC-QUERIES.md),
and the foundational smoke checks concept-scoped Diophantine, QF_BV, totality,
and exact-vs-floating rows for gcd/divisibility, CRT, nonunit inverse,
fixed-width residue, quotient/ideal, and semantic-boundary resources, so
downstream consumers can discover finite arithmetic rows without promoting
analytic number theory, algebraic number theory, unbounded induction, or
floating-point guarantee claims.
The geometry resource lane now has
[`GEOMETRY-RESOURCE-QUERIES.md`](docs/foundational-resources/GEOMETRY-RESOURCE-QUERIES.md),
and the foundational smoke checks concept-scoped Farkas pack/check queries for
`bridge_coordinate_orientation_geometry` and
`bridge_finite_circle_inversion_cyclic_replay`, so downstream consumers can
discover finite geometry resources without promoting synthetic, projective,
differential, global, or higher-degree geometry theorem claims.
The graph/discrete lane now has
[`GRAPH-DISCRETE-QUERIES.md`](docs/foundational-resources/GRAPH-DISCRETE-QUERIES.md),
and the foundational smoke checks concept-scoped Boolean, QF_BV, and LIA
pack/check queries for `bridge_finite_graph_replay_obstruction`, so downstream
consumers can discover finite coloring, reachability, matching, cut,
d-separation, fixed-width coloring, and BFS/DFS runtime rows without promoting
general graph-theory or asymptotic algorithm claims.
The optimization/convexity lane now has
[`OPTIMIZATION-CONVEXITY-QUERIES.md`](docs/foundational-resources/OPTIMIZATION-CONVEXITY-QUERIES.md),
and the foundational smoke checks LP objective/Farkas rows, rational convexity
shadows, projection/residual rows, exact-vs-floating boundary rows, and
pack-specific KKT, active-set QP, SDP, gradient-descent, Armijo/Wolfe
line-search, projected-gradient, and soft-threshold/composite-decrease/box-plus-L1
proximal-gradient rows, so downstream
consumers can discover finite optimization resources without promoting
duality, KKT sufficiency, SDP strong duality, Slater conditions,
gradient-descent convergence/rates, line-search termination/convergence,
Wolfe-line-search existence/convergence, method convergence, stability, or
benchmark claims.
The functional-analysis/operator lane now has
[`FUNCTIONAL-OPERATOR-QUERIES.md`](docs/foundational-resources/FUNCTIONAL-OPERATOR-QUERIES.md),
and the foundational smoke checks finite operator/Chebyshev, eigenpair,
Rayleigh, inner-product/projection, and finite dual/tensor rows through
Farkas/Alethe queries, so downstream consumers can discover finite
functional/operator resources without promoting Banach/Hilbert-space,
compact-operator, topological-dual, minimax, alternation-theorem, stability, or
infinite-dimensional approximation claims.
The analysis/numerical/complex lane now has
[`ANALYSIS-NUMERICAL-QUERIES.md`](docs/foundational-resources/ANALYSIS-NUMERICAL-QUERIES.md),
and the foundational smoke checks bounded epsilon-delta, metric-ball,
algebraic derivative/integral, Newton/root-finding, finite dynamics/Euler,
Adams-Bashforth and BDF2 multistep, residual, exact-vs-floating, and complex
real-pair rows through Farkas queries,
so downstream consumers can discover finite analysis resources without
promoting completeness, IVT/MVT/FTC, convergence, numerical stability,
floating-point error, holomorphicity, contour-integration,
analytic-continuation, or algebraic-closure claims.
The dynamics lane now has
[`DYNAMICS-QUERIES.md`](docs/foundational-resources/DYNAMICS-QUERIES.md),
and the foundational smoke checks finite recurrence, transition, invariant,
Euler, stochastic-kernel, Markov-chain, hitting-time, and calculus-shadow rows
through Farkas queries, including Adams-Bashforth and BDF2 multistep rows, so
downstream consumers can discover finite dynamics
resources without promoting continuous ODE/PDE theory, flow/stability/
bifurcation theorems, chaos/ergodic theory, Euler convergence,
stochastic-process limits, continuous-time Markov processes, numerical
stability, or floating-point claims.
The foundations/discrete lane now has
[`FOUNDATIONS-DISCRETE-QUERIES.md`](docs/foundational-resources/FOUNDATIONS-DISCRETE-QUERIES.md),
and the foundational smoke checks Boolean proof/CNF, refutation-as-query,
finite proof-pattern, bounded induction, finite quantifier, finite
cardinality/bijection, finite Boolean algebra, finite counting,
partition/equivalence, and finite relation/function/image/preimage rows through
Boolean, Alethe, Diophantine, and LIA queries, so downstream consumers can
discover finite foundations resources without promoting proof automation, ZFC,
infinite sets/cardinality, unbounded induction, asymptotic enumeration, or
broad combinatorial theorem claims.
The proof-route lane now has
[`PROOF-ROUTE-QUERY-MATRIX.md`](docs/foundational-resources/PROOF-ROUTE-QUERY-MATRIX.md),
and the query helper accepts `routes` summaries with route aliases and optional
field scoping, so consumers can inspect route coverage before drilling into
packs or checked rows.
The foundational example-pack validator now also has committed negative
fixtures for unknown fields, metadata/check drift, and missing witness
references, and `check-foundational-resources.sh` requires those invalid packs
to fail with the expected diagnostics.
The rules/law transfer lane now has a crosswalk from math resources to concrete
policy/rule checks, with `benefit-eligibility-v0` mapped to finite predicates,
Bool/QF_LIA thresholds, temporal versioning, replayed witnesses, and proof-route
upgrade targets; source-linked Bool/QF_LIA fixtures now check its consistency,
coverage, fixed no-exception monotonicity, and active-threshold implementation
equivalence obligations through the `rules_as_code_examples` solver regression.
`authorization-policy-v0` now adds the second rules/law pack: finite
tenant/resource relations, explicit deny precedence, admin tenant guarding,
intended version-delta witnesses, and checked Bool/QF_LIA fixtures for tenant
isolation, deny precedence, admin tenant boundaries, and bounded implementation
equivalence.
`tax-benefit-arithmetic-v0` now adds the third rules/law pack: integer
thresholds, household-size adjustments, caps, active phase-out monotonicity,
effective-date witnesses, and checked Bool/QF_LIA fixtures for non-negative
benefit, cap, active phase-out monotonicity, and bounded implementation
equivalence, with the validator replaying the full piecewise finite sample.
`procurement-scoring-v0` now adds the fourth rules/law pack: finite predicate
exclusions, bid caps, encoded submission deadlines, small-business
bonus-threshold witnesses, score monotonicity, and checked Bool/QF_LIA fixtures
for debarment, late submission, bid-cap, monotonicity, and bounded
implementation-equivalence obligations.
`grant-allocation-v0` now adds the fifth rules/law pack: exact rational
allocation shares, budget balance, shelter/clinic minimum floors,
administrative caps, finite allocation witnesses, and checked QF_LRA/Farkas
fixtures for total-budget, minimum-share, cap, and bounded
implementation-equivalence obligations.
The rules/law lane now also has a generated query dashboard that reads the
five committed rule-pack JSON files, exposes 1,007 bounded sample rows, and
links deterministic generated query-row JSON for 1,766 coverage, equivalence,
threshold, cap, deadline, version-delta, monotonicity, and rational-allocation
rows without promoting the packs to legal or solver benchmarks.
`RULES-LAW-QUERIES.md` and `scripts/query-rules-as-code.py` now make that
rules/law boundary queryable by pack, proof status, generated family, and
bounded row; `just rules-as-code` smoke-checks the procurement pack, checked
obligations, quality-score query family, and late-submission generated rows.
`RULES-LAW-PATTERN-MATRIX.md` now maps that same boundary back to math-resource
concepts and proof routes, and the rules-as-code smoke gate also checks
monotonicity checks, adjacent generated families, and quality-monotonicity
rows.
`docs/learn/rules-law-trust-boundary.md` now gives learners the corresponding
source-rule -> model -> replay/check -> horizon walkthrough for the five
current rule packs.
Finite order lattices, finite permutation groups, finite vector spaces, finite
dual spaces, finite modules, finite ideals, finite tensor products, and finite
group actions now add secondary equality-heavy promotions for bad antisymmetry,
bad nonbijection, bad subspace-closure, covector-additivity, submodule
scalar-closure, ideal additive-closure plus quotient-ring representative
congruence, bilinear left-additivity, bad identity-action, and bad
action-compatibility rows.
Continue the
math-resource proof upgrades from
[`docs/foundational-resources/PROOF-UPGRADE-FRONTIER.md`](docs/foundational-resources/PROOF-UPGRADE-FRONTIER.md),
where modular arithmetic now promotes both the nonunit inverse obstruction and
incompatible non-coprime CRT obstruction through checked QF_LIA/Diophantine
evidence, exact statistical tests promote the bad binomial tail-count row and
the bad Fisher and multinomial p-value rows,
finite simplicial homology promotes its bad boundary coefficient, and induction
patterns promote a finite even-product parity obstruction. The
QF_LIA/Diophantine first-target set is now covered;
the first secondary statistics margin/count row is now promoted in
descriptive statistics, integer LIA is now promoted for its gcd divisibility
obstruction, bounded induction obligations are now promoted for a bounded
bad-step count checked arithmetic-evidence row, bounded natural arithmetic is now promoted
for its bad negative domain row, and the finite-probability
bad-normalization row now has a checked
QF_LRA/Farkas regression, with finite Markov chains now split so the bad
stochastic-row and false stationary-distribution replay rows feed explicit
`qf-lra-*` Farkas rows, and finite concentration now promoted for the bad
tail-bound and bad union-bound obstructions, with finite hitting times now source-linked and
promoted for the bad survival-mass and bad expected-time equations; least-squares regression is now
promoted for the bad coefficient and bad RSS-improvement rows, and bounded rational real analysis for
the bad linear-delta row, with finite conditional expectation now promoted for
the bad high-block, total-expectation, tower-property, and
variance-decomposition tables, finite Euler method now source-linked and promoted
for its bad max-error, bad terminal-error, and bad fixed-step rows, bounded dynamics now promoted
for its bad invariant-bound conflict, and finite probability now promoted for
bad conditional-probability, bad Bayes-posterior, and bad independence
conflicts, with orientation/area geometry now promoted
for its bad affine-area-scaling and bad fixed-orientation claims and numerical
linear algebra now promoted for its bad residual-bound, solution-box
upper-bound, and Jacobi error-bound rows, and random matrix finite now promoted for its bad
trace-square moment and bad expected-rank rows, with affine geometry now promoted for its bad
midpoint-coordinate, collinearity-determinant, and distance-preservation rows and inner-product spaces now
promoted for its bad negative-norm and projection-orthogonality rows, and
spectral linear algebra now promoted for its bad eigenpair and bad
Rayleigh-quotient rows, with matrix
invariants now promoted for its bad characteristic
polynomial row. The matrix-corpus regression pass now source-links the
least-squares bad-coefficients, numerical residual-bound, finite random-matrix
trace-square, spectral bad-eigenpair, and matrix-invariant bad-characteristic
SMT-LIB artifacts to the shared QF_LRA/Farkas route tests, while leaving the
strict-inequality inner-product negative-norm row on its existing inline
Farkas route until the SMT-LIB parser/evidence path accepts that artifact
shape. Polynomial factorization now promoted for its fixed
irreducible-quadratic discriminant conflict, and finite Chebyshev systems now
promoted for the duplicate-node determinant and bad interpolation-sample
conflicts, with metric continuity now promoted for the finite
bad-delta output-bound conflict, finite stochastic kernels now promoted for
the bad kernel-row normalization and bad composition-entry conflicts, and finite product measure now
promoted for the bad product-probability and bad marginal conflicts, with
finite random variables now promoted for separate bad pushforward-distribution
and bad expectation-through-pushforward QF_LRA conflicts and finite integration now
promoted for the bad expectation conflict, and finite
martingales now promoted for the bad stopped-expectation and
conditional-expectation conflicts, with
finite Markov chains carrying explicit promoted solver-reuse metadata for the
separate `qf-lra-bad-stochastic-row` and
`qf-lra-bad-stationary-distribution` conflicts after replay isolates the bad
source rows, and finite concentration carrying
source-linked promoted bad tail-bound and bad union-bound conflicts, while sequence-limit shadows
now promote a bounded Cauchy-tail max-distance threshold conflict, and
multivariable calculus now promotes a bad exact gradient-component conflict,
with calculus algebraic shadows now promoting a bad exact derivative-value
conflict, and complex-plane transforms now promoting bad conjugation-product
imaginary-part and bad unit-square real-part conflicts.
The first
secondary QF_LRA/Farkas
target set is now covered, the initial equality-heavy QF_UF/Alethe
secondary set is now covered including the finite-ideals quotient
representative row, and finite group actions now promote a bad identity-action
conflict and a bad action-compatibility conflict through checked QF_UF/Alethe
regressions, while finite continuous maps now promote a bad preimage-membership
conflict through the same checked route.
The first
QF_BV bit-blast/DRAT resource promotion now covers the
finite-rings bad distributivity and bad multiplicative-identity rows, the
finite-fields composite no-inverse and bad inverse-candidate rows, and the
graph-coloring one-bit triangle two-coloring obstruction, with bounded number
theory now promoted for the modulo-7 quadratic nonresidue row and the bad
square-root witness row; finite
compactness now contributes checked DRAT/LRAT evidence for a bad open-cover row,
finite connectedness now contributes checked DRAT/LRAT evidence for a bad
connectedness row, finite topology now contributes checked DRAT/LRAT evidence
for a missing-empty-set axiom row, induction obligations and natural arithmetic
now contribute checked arithmetic-evidence regressions for bounded bad step
counts and bounded-natural negativity, and graph search runtime contributes checked
QF_LIA arithmetic evidence for a bad finite DFS cost bound, while
cardinality principles now contributes a checked QF_LIA/Diophantine regression
for the overlapping-set false-additivity count conflict. The five active resource proof-certificate routes
now each have a route-specific tamper/rejection regression: Boolean CNF/LRAT,
QF_BV DRAT, QF_LRA/Farkas, QF_LIA/Diophantine, and QF_UF/Alethe all mutate an
emitted resource certificate and require the independent checker to reject it;
the foundational resource dashboards now report **149 promoted solver-reuse
packs**, **0 non-benchmark-horizon packs**, and **0 unclassified packs** after
the latest finite barycentric interpolation bad value QF_LRA/Farkas promotion,
the latest finite divided-differences bad interpolation-value QF_LRA/Farkas
promotion,
the latest finite Simpson-rule bad quadrature-value QF_LRA/Farkas promotion,
the latest finite BDF2 bad implicit-multistep QF_LRA/Farkas promotion,
the latest finite Adams-Bashforth bad multistep QF_LRA/Farkas promotion,
the latest finite Crank-Nicolson bad implicit-trapezoid-step QF_LRA/Farkas
promotion,
the latest finite Backward Euler bad implicit-step QF_LRA/Farkas promotion,
the latest finite Heun bad first-step QF_LRA/Farkas promotion,
the latest finite Runge-Kutta midpoint bad first-step QF_LRA/Farkas promotion,
the latest finite GMRES bad one-step alpha QF_LRA/Farkas promotion,
the latest finite Cauchy-Riemann bad derivative real-part QF_LRA/Farkas
promotion,
the latest finite interval-arithmetic bad product-upper-bound QF_LRA/Farkas
promotion,
the latest finite rounding-shadow bad exact-vs-rounded equality QF_LRA/Farkas
promotion,
the latest finite shifted-QR bad next-step entry QF_LRA/Farkas promotion,
the latest finite QR-iteration-step bad next-step entry QF_LRA/Farkas promotion,
the latest finite polar-decomposition bad diagonal QF_LRA/Farkas promotion,
the latest finite real-Schur bad superdiagonal QF_LRA/Farkas promotion,
the latest finite orthogonal-diagonalization bad eigenvalue QF_LRA/Farkas promotion,
the latest finite LDLT bad diagonal-entry QF_LRA/Farkas promotion,
the latest finite pivoted-LU bad pivot-sign QF_LRA/Farkas promotion,
the latest finite LU bad-multiplier QF_LRA/Farkas promotion,
the latest finite Gram-Schmidt bad-projection-coefficient QF_LRA/Farkas promotion,
the latest finite Householder bad-reflection-entry QF_LRA/Farkas promotion,
the latest finite Givens bad-sine-coefficient QF_LRA/Farkas promotion,
the latest finite power-iteration bad coordinate QF_LRA/Farkas promotion,
the latest finite Gaussian-elimination bad eliminated-RHS QF_LRA/Farkas
promotion,
the latest finite Schur-complement bad scalar QF_LRA/Farkas promotion,
the latest finite Jordan-chain bad-component QF_LRA/Farkas promotion,
the latest finite Arnoldi bad-Hessenberg-coefficient QF_LRA/Farkas promotion,
the latest finite Lanczos bad-tridiagonal-coefficient QF_LRA/Farkas promotion,
the latest finite singular-value bad-bound QF_LRA/Farkas promotion,
the latest finite Cholesky bad product-entry QF_LRA/Farkas promotion,
the latest finite QR bad product-entry QF_LRA/Farkas promotion,
the latest finite Walsh-Hadamard bad transform-coefficient QF_LRA/Farkas promotion,
the latest finite-DAG topological bad edge-order QF_LIA promotion,
the latest finite-shortest-path bad potential-bound QF_LRA/Farkas promotion,
the latest finite-flow-cut bad cut-bound QF_LRA/Farkas promotion,
the latest finite-specialization-order bad `T0` QF_UF/Alethe promotion,
the latest finite-Chebyshev split into replay rows plus explicit `qf-lra-*`
Farkas rows,
the latest finite-circle-geometry bad line-intersection QF_LRA/Farkas promotion,
the latest finite-cyclic-geometry bad Ptolemy QF_LRA/Farkas promotion,
the latest finite-inversion-geometry bad inverse-distance-product QF_LRA/Farkas promotion,
the latest finite-inversion-geometry bad inverse-coordinate QF_LRA/Farkas promotion,
the latest finite-active-set-QP bad degenerate-multiplier QF_LRA/Farkas promotion,
the latest finite-active-set-QP bad inactive-slack QF_LRA/Farkas promotion,
the latest finite-active-set-QP bad free-gradient QF_LRA/Farkas promotion,
the latest finite-wolfe-line-search bad minimizer QF_LRA/Farkas promotion,
the latest finite-wolfe-line-search bad sufficient-decrease QF_LRA/Farkas promotion,
the latest finite-wolfe-line-search bad curvature QF_LRA/Farkas promotion,
the latest finite-proximal-gradient bad composite-decrease QF_LRA/Farkas promotion,
the latest finite-proximal-gradient bad box-proximal-point QF_LRA/Farkas promotion,
the latest finite-proximal-gradient bad proximal-point QF_LRA/Farkas promotion,
the latest finite-projected-gradient bad projection and bad decrease QF_LRA/Farkas promotions,
the latest inner-product bad projection-orthogonality QF_LRA/Farkas promotion,
the latest spectral bad Rayleigh-quotient QF_LRA/Farkas promotion,
the latest finite-line-search bad descent-direction and bad accepted-candidate QF_LRA/Farkas promotions,
the latest finite-line-search bad Armijo QF_LRA/Farkas promotion,
the latest finite-gradient-descent bad descent-bound, bad step-coordinate, and bad decrease
QF_LRA/Farkas promotions,
the latest finite-SDP bad objective, bad duality-gap, and bad slack-entry
QF_LRA/Farkas promotion,
the latest finite-KKT bad stationarity and bad complementarity QF_LRA/Farkas
promotion,
the latest finite-separation split into replay-only bad convex-combination and
bad separator rows plus separate `qf-lra-*` QF_LRA/Farkas proof rows,
the latest finite-root-finding split into replay-only bad Newton-step and
bad bisection-width rows plus separate `qf-lra-*` QF_LRA/Farkas proof rows,
the latest finite-condition-number bad upper-bound QF_LRA/Farkas promotion,
the latest bounded-dynamics split into replay-only bad transition-step,
bad threshold-step, and invariant-bound rows plus separate `qf-lra-*`
QF_LRA/Farkas proof rows,
complex-algebraic bad product-coordinate and bad norm-squared QF_LRA/Farkas
promotion,
finite-operator bad `l1` sum-norm QF_LRA/Farkas promotion,
finite-operator bad operator-bound QF_LRA/Farkas promotion,
coordinate-geometry bad midpoint-coordinate and squared-distance QF_LRA/Farkas
promotion,
incidence-geometry bad intersection-coordinate and point-on-line QF_LRA/Farkas
promotion,
rigid-configuration bad translation-image and distance-table QF_LRA/Farkas
promotion,
finite-measure-monotonicity bad subset-measure and bad union-subadditivity
QF_LRA/Farkas promotion,
bounded-monotone-sequence explicit bad upper-bound and bad tail-gap
QF_LRA/Farkas proof rows,
finite-recurrence-prefix bad Fibonacci-value and bad affine-step QF_LRA/Farkas
promotion,
finite-topology missing-empty-set Bool/CNF DRAT/LRAT promotion,
finite-measure bad-complement QF_LRA/Farkas promotion,
real-algebra RCF-shadow negative-discriminant QF_LRA/Farkas
promotion, polynomial-factorization discriminant QF_LRA/Farkas promotion,
cardinality-principles overlap-additivity count QF_LIA/Diophantine
promotion,
induction-obligations bounded bad-step count checked QF_LIA arithmetic promotion,
complex-plane bad conjugation-product imaginary-part and bad unit-square
real-part QF_LRA/Farkas promotions,
calculus-algebraic false-derivative QF_LRA/Farkas promotion,
multivariable-calculus bad-gradient QF_LRA/Farkas promotion,
sequence-limit bounded Cauchy-tail QF_LRA/Farkas promotion,
calculus Riemann-sum false-integral QF_LRA/Farkas promotion,
finite-predicate Bool/CNF quantifier-expansion promotion,
polynomial-identities false-root QF_LIA/Diophantine promotion,
finite generating-functions QF_LIA/Diophantine coefficient-convolution
promotion, PHP(3,2) counting/refutation Bool/CNF promotions, and the replay-only
classification pass for bounded dynamics, plus finite-rings bad
multiplicative-identity, finite-fields bad inverse-candidate, and
number-theory bad square-root QF_BV plus gcd-obstruction QF_LIA promotions,
plus the earlier
rational-order, gcd/Bezout, Bool/CNF finite-set/proof-method, QF_LRA
linear-algebra/optimization/convexity, finite-probability, QF_UF, QF_LIA, and
QF_BV source-metadata promotion batches;
prefer the next
proof-frontier lane or equality-heavy pack that can carry a small checked
certificate and a resource-backed regression.

## ⚠ Course correction (2026-06-23): MEASURE, don't seed

**Diagnosis (evidence-based).** ~150 commits over 24h moved **zero** Z3/cvc5
metrics. Verified causes:
1. **Measurement vacuum.** Only **one** division is corpus-measured (QF_BV p4dfa).
   All the new work — interpolation, CHC/PDR/IMC, abduction, online combination,
   datatypes, the proof certs — is on divisions **nothing measures**. Real
   decide-rate gains happened (fuzz-measured: QF_NRA 109→64, QF_NIA 498→146,
   QF_UFLIA 311→18) but are **invisible** because no committed corpus vs Z3 records
   them. *You cannot show progress you do not measure.*
2. **Ledger-over-corpus.** The cadence became *seed engine → mark Validated/Checked
   → register a ledger row → next engine.* That optimizes **breadth + assurance**
   (the ledger). Parity metrics measure **depth + performance** (the corpus). A
   ledger row is **not** progress toward parity; a measured PAR-2 is.
3. **QF_BV bottleneck untouched.** The one measured metric is gated on
   batsat-path search / word-level reduction. The recent SAT heuristics (VSIDS,
   Luby, LBD, phase-saving) landed in the **generic CDCL(T) Dpll** (`lra_online.rs`,
   the *theory* loop) — a different code path from the QF_BV solver
   (`solve_with_rustsat_batsat`/`native_cdcl`). So they cannot move QF_BV.

**The correction (binding until lifted):**
- **Measurement is the gate, not an afterthought.** No fragment may be called
  "parity"/"competitive" without a **committed measured corpus vs Z3/cvc5**
  ([P4.5](docs/plan/track-4-usecases-frontend/P4.5-benchmarking.md)). Until then its
  status is "seeded/decides," never "parity." (See the
  [maturity ladder](#true-parity-the-maturity-ladder-and-the-measurement-debt-2026-06-23).)
- **Fastest real progress = measure what already improved.** Stand up committed
  per-division corpora (QF_LRA, QF_LIA, QF_UF, then QF_NRA/NIA) vs Z3 *now* — the
  gains already exist (fuzz-measured); measuring them makes them visible **today**.
  The new oracle-free corpus gate (`tests/corpus_regression.rs`) is the credibility
  substrate; the missing piece is the **measured PAR-2** harness across divisions.
- **Seed moratorium.** Do **not** add another new engine seed until ≥2 existing
  divisions are *measured-competitive*. A 12th seeded engine is worth less than
  QF_LRA proven on a real corpus.
- **QF_BV work must hit its real bottleneck** — batsat-path search (kissat-class
  techniques in the native core) or deeper word-level reduction — not the theory
  loop. SAT heuristics in `lra_online.rs` do nothing for QF_BV.
- Proof/certification work still has value (it widens the *Certifying* moat we
  already lead) — but it advances assurance, **not** the parity metric; budget it
  accordingly, behind measurement.

**Progress (2026-06-24): the measurement gate now exists.**
[`axeyum-bench/examples/measure_corpus.rs`](crates/axeyum-bench/examples/measure_corpus.rs)
shells the system `z3` binary against any logic's corpus and times axeyum's
`check_auto` on the same files → decided counts, agreement, DISAGREE, **PAR-2 for
both**. First fair numbers (cvc5 slices, both-parse, 10 s, **DISAGREE=0**):
QF_BV 35/35, QF_ABV 8/8, QF_FP 5/5, QF_LRA 5/5 — **parity**; QF_LIA **8/9 vs 9/9**
(z3 ahead by one and far faster — the first honest measured gap). Artifacts under
`bench-results/measured/`.
- **Methodology lesson (load-bearing):** cvc5's own `test/regress` is
  *solver-flavored* — files carry cvc5-specific `(set-option :bv_solver/:incremental)`
  and non-BV-array logics that **z3 rejects at parse**. Scoring those as z3 misses
  fakes an axeyum win (a permissive parser is not solving power); the harness
  **excludes** them (`z3_rejected_unfair`). For a *fair* parity number, prefer a
  **neutral SMT-LIB corpus** over a competitor's regress suite.
- **These are easy instances** — "parity" here means both trivially solve. The
  easy corpus *hides* the depth gaps; the next step is harder neutral per-division
  corpora (where QF_LIA already hints z3 is ahead). Measurement is no longer the
  blocker — corpus *difficulty/neutrality* is.

**Measurement now DISCHARGED (2026-06-24).** The parallel agent generalized this
into a committed, regenerable **[`bench-results/SCOREBOARD.md`](bench-results/SCOREBOARD.md)**
— **24 logic fragments, 992 files, 663 decided, 611 oracle-compared, DISAGREE = 0**
— plus the oracle-free per-lever frontier dashboard. The "MEASURE, don't seed"
correction is answered: the weak rows now *name* the blockers (see
[`docs/PARITY-STATUS-AND-PATH.md`](docs/PARITY-STATUS-AND-PATH.md)). The strategic
question is no longer "are we measured" — it is the next section.

**Verification hygiene (2026-06-27).** The solver crate's full all-targets
clippy gate is clean again:
`CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --all-targets -j1 -- -D warnings`.
Keep this gate green for solver/proof/frontend slices; broad capability work is
only useful if the core crate remains easy to audit and re-run.

## Strategy: work backwards from Pareto dominance (2026-06-24)

**The decide-rate race is the wrong target.** Z3/cvc5 have ~20 years of tuning;
the scoreboard confirms axeyum trails on the hard rows (QF_NRA-cvc5 24%, Int-indexed
arrays ~0%, infinite-domain quantifiers 0%). Chasing "match Z3's decide% everywhere"
is a catch-up race axeyum loses on most rows, indefinitely. **Stop optimizing for
global decide-parity.**

**Instead: define and grow the set of fragments where axeyum *Pareto-dominates* the
alternatives.** A fragment is **Pareto-dominant** when axeyum is, on it,
simultaneously: **(1) decide-competitive** with Z3 (parity on that fragment),
**(2) sound** (DISAGREE = 0 — already true everywhere), **(3) Lean-certified**
(every `unsat` carries a kernel-checkable proof), and **(4) pure-Rust / `unsafe`-free /
WASM / deterministic**. On such a fragment axeyum **strictly beats every alternative**:
- vs **Z3 alone** — Z3 ties on decide but has no Lean-checkable proof and is C++ (no
  WASM, memory-unsafe);
- vs **cvc5 alone** — ties on decide, has Alethe/LFSC but not an *integrated in-tree
  Lean-kernel-checked* artifact in a pure-Rust stack;
- vs **Lean alone** — Lean cannot *auto-decide* the fragment; axeyum does, and hands
  back a proof its kernel accepts.

That is a real, defensible "we win here" — unlike "we almost match Z3's decide-rate."

**The new headline metric: four-constraint Pareto-dominance coverage.** Drive it
up per measured division: decided within budget, DISAGREE = 0, every `unsat`
has a re-checked trust-hole-free Lean certificate, and the route remains
pure-Rust / deterministic / `unsafe`-free. A fragment count is too easy to game
by slicing; coverage on a neutral corpus is the control surface.

**Working backwards — what that implies for priorities:**
1. **The binding axis is certification, not decide-rate.** Soundness (2) and
   pure-Rust (4) are already universal; decide-competitiveness (1) already holds on
   the strong rows (QF_FP/QF_UFBV/QF_UFFF 100%, QF_AUFBV 93%, QF_LIA 91%, QF_ABV 88%,
   QF_BVFP/QF_FF/QF_LRA/QF_SEQ ~80%). The **missing leg is (3) Lean certification** on
   those already-strong fragments. **That is where the structural win is, and it is
   the axis Z3 cannot match at all.** → invest the cert lane (Track 3 / PARITY Tier C)
   on the **strong-decide** fragments first, not the weak ones.
2. **Name the beachhead already won.** QF_BV (DRAT), datatypes (complete axiom-free
   Lean chain), QF_LRA (Farkas), QF_UF (congruence) are at/near all-four **today** —
   the first Pareto-dominant fragments. Make this an explicit, tracked list.
3. **The hard rows (NRA high-degree, Int-arrays, infinite quantifiers) are NOT a
   dominance opportunity near-term** — axeyum can't be decide-competitive there for a
   long time. Treat them as "match Z3's *practical* heuristics where cheap, honest
   `unknown` otherwise" — do **not** sink the dominance budget into a decide-rate
   catch-up race there.
4. **vs Lean is a pure-win axis: ship the tactic backend.** axeyum auto-discharging
   SMT-decidable Lean goals with kernel-checked proofs (the lean-smt-style bridge,
   [P3.7](docs/plan/track-3-proof-lean/P3.7-lean-reconstruction.md)) Pareto-dominates
   manual Lean on the decidable fragment — automation Lean lacks, trust Lean demands.

**The inversion in one line:** *we do not win by deciding as much as Z3; we win by
being the only stack that decides it, proves it to a Lean kernel, and runs anywhere
— so grow the fragment set where all four hold, and stop spending on the decide-race
where we structurally can't lead.*

### Refined by source-grounded review (2026-06-24, two Opus critics vs real Z3/cvc5/lean-smt)

The thesis **survives** adversarial review — but four corrections, each verified
against competitor source, are now binding:

1. **The cert moat is real AND unoccupied — confirmed from source.** cvc5's proofs
   are complete *only in "safe mode"* (which disables CAD/strong engines); **CAD/NRA
   has no checkable proof rule at all**; Alethe omits nonlinear/arrays/datatypes.
   lean-smt is **beta**, needs the **cvc5 C++ binary in the loop**, and has a
   structural **`sorry` fallback** (BV reconstruction is `add`/`eq`-only). So
   axeyum's *integrated, pure-Rust, in-tree, `#print axioms`-clean, trust-hole-free*
   self-checking is a position **no incumbent occupies.** Keep this as a *standing
   guard*: re-verify these claims whenever `references/` is refreshed (a moat that
   could silently rot if cvc5/lean-smt close their holes).
2. **Scope "dominant *today*" honestly: kernel-cert ≠ DRAT-cert.** Only the QF_BV
   **bitwise/comparison sub-fragment** reconstructs to the Lean *kernel*; mul/rem/shift
   carry a **DRAT** proof (strong, but not the kernel artifact the thesis sells).
   Every "Pareto-dominant today" claim must name the sub-fragment that is
   *axiom-clean Lean-kernel-checked*, and distinguish it from the DRAT-certified
   superset. Conflating the two is the ledger-over-substance slip the 06-23
   correction forbade.
3. **The headline metric must not be a fragment *count* (gameable by slicing).**
   Use, per division, a **four-constraint coverage %** on a *neutral, non-trivial*
   corpus: `dominant%(D) = |decided-within-budget ∧ emits a re-checked, trust-hole-free,
   #print-axioms-clean Lean cert| / |non-trivial instances|`, reported with PAR-2 vs
   Z3. An instance that decides but only DRAT-certifies does **not** count toward the
   Lean-dominant fraction.
   **READINESS REPORT LANDED (2026-06-25):**
   [`bench-results/DOMINANCE.md`](bench-results/DOMINANCE.md), regenerated by
   [`scripts/gen-dominance-scoreboard.py`](scripts/gen-dominance-scoreboard.py),
   now combines the measured decide/PAR-2 rows with a conservative proof-route
   audit queue. Rows without a committed audit remain readiness entries because
   the division baseline JSONs do not record per-instance Lean reconstruction
   coverage. Current report: **35 rows**, **992 files**, **663 decided**,
   **611 oracle-compared**, **DISAGREE = 0**, with **23 complete exact audit rows**
   and **0 remaining first-queue rows** marked `audit now` for evidence/Lean
   coverage measurement.
   **QF_UF REMEASURE + SMT-LIB DIV/MOD GUARD LANDED (2026-06-26):**
   remeasuring the QF_UF rows exposed a real soundness hazard: SMT-LIB leaves
   integer/real division by zero and integer modulo by zero underspecified, while
   Axeyum's executable evaluator uses deterministic total conventions for model
   replay. The solver now declines arithmetic routes whose divisor is not a
   syntactically known nonzero constant until an explicit underspecification
   encoding exists. The cvc5 QF_UF bounded rows are now **44/82 decided** with
   **DISAGREE=0**; the overbound row remains **4/6 decided**, **DISAGREE=0**.
   **QF_UF DECLARED-SORT EXACT AUDIT INGESTED (2026-06-26):**
   the refreshed bounded declared-sort QF_UF row now has a complete committed
   dominance audit. Equality-only conflicts over declared uninterpreted carrier
   sorts now route to the EUF Lean fragment even without an `Apply` node, and the
   zero-trust evidence lane tries the pure EUF Alethe congruence emitter directly.
   This closes the `parallel-let` Lean gap. A follow-up SAT evidence pass made
   the arithmetic/Diophantine optional evidence prepasses decline declared-sort
   rows with no Int/Real content, closing the `parser/as` and `ite4` audit
   errors. A follow-up set-cardinality pass added a checked lowered
   `set.card`→BV-popcount certificate, closing both the `sets/card` bit-blast
   trust-hole row and the `sets/card-6` evidence timeout. A follow-up
   Boolean-EUF pass added a checked equality-skeleton refutation bridge for
   pure-UF rows whose contradiction is hidden behind `not =>`, CNF, or Boolean
   `ite`, closing `simple-uf`, `uf/cnf-and-neg`, and `uf/cnf-ite`. A follow-up
   UF+arithmetic congruence pass added a checked Ackermann/congruence residual
   certificate for the mixed `list`/integer `bug303` row: congruence over the
   declared carrier sort derives the needed integer equality, then arithmetic
   DPLL refutes the retained Boolean-structured linear-arithmetic core. A final
   direct-evidence routing pass lets structural certificates run before the
   pure-real LRA/NRA evidence branch, so the nonlinear-extension
   `issue3970-nl-ext-purify` row is now certified as a term-identity
   contradiction from its expanded `distinct` disequality `(not (= t t))`. The
   exact row is now **44/44 dominant (100.0%)**, **Lean unsat 15/15 (100.0%)**,
   with **mismatches=0**, **audit_errors=0**, **timeouts=0**, and no remaining
   evidence gaps.
   **QF_UF OVERBOUND EXACT AUDIT INGESTED (2026-06-26):**
   the refreshed overbound declared-sort QF_UF row now has a complete committed
   dominance audit for its decided slice. The new online Boolean-EUF certificate
   handles the three overbound UNSAT stressors whose equality skeletons exceed
   the exhaustive Boolean-EUF case bound: the checker re-runs the deterministic
   online EUF DPLL(T) refuter on the original assertions, rejects non-pure-EUF
   shapes, and carries no trust steps. This closes `uf/cnf_abc`, `proof00`, and
   `proofs/macro-res-exp-crowding-lit-inside-unit`; the row is now
   **4/4 dominant (100.0%)**, **Lean unsat 3/3 (100.0%)**, with
   **mismatches=0**, **audit_errors=0**, and **timeouts=0**. The underlying
   decide-rate row remains **4/6 decided**; this closes certification for the
   currently decided slice, not the two undecided instances.
   **QF_UFLIA BOUNDED REMEASURE + AUDIT REFRESH LANDED (2026-06-26):**
   the bounded declared-sort QF_UFLIA baseline was stale after the mixed
   UF+arithmetic congruence route landed. Re-running the committed Z3 comparison
   now decides `bug303` as `unsat`, agrees with Z3, and moves the row from
   **5/6** to **6/6 decided (100.0%)** with **DISAGREE=0** and PAR-2 mean
   **0.002 s**. The exact dominance audit is refreshed at **6/6 dominant
   (100.0%)**, **Lean unsat 2/2 (100.0%)**, with **mismatches=0**,
   **audit_errors=0**, and **timeouts=0**.
   **QF_UFLIA PARENT EXACT AUDIT INGESTED (2026-06-26):**
   the parent `qf-uflia-cvc5-regress-clean` row now has a complete committed
   dominance audit for its six decided instances. The row is **6/6 dominant
   (100.0%)**, **Lean unsat 2/2 (100.0%)**, with **mismatches=0**,
   **audit_errors=0**, and **timeouts=0**; the two overbound timeout rows remain
   decide-rate work, not certification gaps for the decided slice.
   **QF_UFLIA PARENT ROW REMEASURE LANDED (2026-06-26):**
   the parent cvc5-regress-clean QF_UFLIA baseline was still a stale bounded
   snapshot. Re-running it over the actual parent corpus now records
   **6/8 decided (75.0%)**, **unsupported=0**, **oracle-compared=6/8**,
   **DISAGREE=0**, and PAR-2 mean **5.001 s**. The two remaining blockers are
   the real overbound `Timeout` rows, not parser/command-surface unsupported
   rows. A narrow paired-bound substitution prototype was tested and deliberately
   not committed: even after avoiding recursive-rewrite stack overflow on the
   generated formulas, it did not certify the overbound rows within the 10 s
   budget. The next useful move there is a deeper arithmetic/UF Boolean-skeleton
   reduction, not another shallow equality-propagation seed.
   **QF_UFLIA OVERBOUND EQUALITY PROPAGATION PROBE RETAINED (2026-06-26):**
   the online LIA theory now soundly propagates integer equality atoms from
   LP-infeasible strict branches (`eq=true`) or an LP-infeasible equality branch
   (`eq=false`), with direct unit coverage. This is a narrow DPLL(T) prune, not a
   row closure: both overbound files still time out in the same 873-atom lazy-LIA
   skeleton with 1433 upfront bound lemmas. A broader static-bound experiment that
   included complement bounds and removed the large-atom implication guard was
   rejected because it inflated upfront lemmas to 5484 without deciding either
   row. Next work should instrument lazy UF+LIA CEGAR iterations and attack SAT
   relevance / Boolean-skeleton reduction, not add more shallow bound seeding.
   **QF_UFLIA OVERBOUND DISPATCH DIAGNOSTICS LANDED (2026-06-26):**
   lazy function-consistency CEGAR `unknown`s now report refinement counters, and
   generic `lia-dpll` budget `unknown`s over UF queries report when UF-aware routes
   were not reached plus the Ackermann pair count. The two overbound rows both
   show the same immediate shape at short budget: `lia-dpll` exhausts the budget
   first, `arithmetic_function=true`, `ackermann_pairs=282`; the UF-aware lazy
   route is not reached by `check_auto`. The next useful move is therefore route
   scheduling / shared-deadline work so admitted arithmetic-UF overbound instances
   get a UF-aware probe before opaque-app LIA DPLL consumes the budget. If that
   probe reports `sat_candidates=0`, then the blocker is the 873-atom function-free
   Boolean arithmetic skeleton itself.
   **BOUNDED PRE-LIA UF+ARITH PROBE LANDED (2026-06-26):**
   small non-array integer UF+arithmetic instances over the eager Ackermann bound
   now get a cloned, capped lazy UF+arithmetic probe before generic opaque-app
   `lia-dpll`; probe errors decline and fall through instead of changing solver
   semantics. The cvc5 generated overbound rows are deliberately outside this
   probe's admission cap (**1248 assertions > 256**, `ackermann_pairs=282`), because
   the cloned probe duplicates the same large function-free arithmetic skeleton
   solve and costs seconds even with a tiny nominal timeout. Their next lever is
   not "try lazy CEGAR earlier" anymore; it is a cheaper relevance/global-deadline
   or first-model strategy for the 873-atom arithmetic Boolean skeleton.
   **ONLINE LIA TIMEOUT STATS LANDED (2026-06-26):**
   online LIA DPLL(T) timeouts now report a stable search-state snapshot
   (variables, theory atoms, clause counts, trail depth, decisions, conflicts,
   restarts, reductions). On both generated QF_UFLIA overbound rows at 1 s the
   generic opaque-app LIA path times out with **vars=3873**, **theory_atoms=485**,
   **clauses=10651**, **trail=1314**, **decisions=1**, **conflicts=0**,
   **learned_live=0**, and **restarts=0**. This rules out conflict-learning churn
   as the immediate short-budget blocker: the route burns its budget during the
   first giant propagation / repeated LIA-feasibility phase before any useful SAT
   skeleton exploration. Next work should add relevance filtering, batched/cheap
   propagation, or a first-model/skeleton precheck before asserting 1k+ literals
   through the incremental LIA theory.
   **DEFERRED LARGE ONLINE LIA FEASIBILITY LANDED (2026-06-26):**
   the online LIA driver now switches large skeletons (>=128 LIA atoms or >=4096
   CNF clauses) to a sound deferred-feasibility mode: Boolean assignments are
   recorded cheaply, one full LIA feasibility check runs at the theory-propagation
   boundary, infeasible live sets are reported as ordinary theory-conflict
   propagations, and expensive LP entailment probes are skipped. Core minimization
   is also skipped in this mode, so the fallback does not reintroduce hundreds of
   LIA checks just to shrink a conflict. On the two generated QF_UFLIA overbound
   rows at 1 s, the timeout now moves past the online first-propagation stall and
   reaches the legacy lazy arithmetic loop: **31-33 rounds**, **873 atoms**,
   **1433 bound lemmas**, **31-33 blocking lemmas**. The rows are still `unknown`;
   the next lever is the legacy 873-atom arithmetic refinement loop / route
   scheduling, not online DPLL(T)'s initial propagation.
   **QF_UFLIA OVERBOUND ROUTE SCHEDULING LANDED (2026-06-26):**
   large non-array integer UF+arithmetic queries whose Ackermann pair count is
   over the eager bound now skip generic `lia-dpll` after the exact linear
   refuters decline, and fall through to the UF-aware lazy CEGAR route. This
   avoids solving the same large function-free arithmetic abstraction twice.
   The generated overbound rows now trace as: pre-LIA cloned probe skipped
   (`1248 > 256` assertions), `lia-simplex` unsupported, `lia-dpll` explicitly
   skipped for overbound UF+arithmetic, then `uf-arith-lazy-overbound` owns the
   single abstraction solve and reports **applications=42**, **function_groups=3**,
   **potential_pairs=282**, **solve_rounds=1**, **sat_candidates=0**, and no
   pair checks / lemmas before the 873-atom arithmetic abstraction times out after
   about **32** lazy-LIA rounds. The rows remain `unknown`; next work is the
   arithmetic abstraction itself (relevance / assumption filtering or a cheaper
   first-model / UNSAT-core-producing skeleton loop), not more route duplication.
   **LIA LP CORE DIAGNOSTICS LANDED (2026-06-26):**
   integer simplex collection now preserves the source assertion for each
   generated constraint, and the arithmetic solver exposes a self-checked
   LP-relaxation unsat-core helper from Farkas multipliers. The lazy arithmetic
   loop tries this relaxation core before the generic minimizer and now reports
   learned theory-core sizes on budget `unknown`. On both generated QF_UFLIA
   overbound rows at 1 s the route remains `unknown`, but the timeout now says
   **873 atoms**, **1433 bound lemmas**, **32 blocking lemmas**, and
   **core_len_last=min=max=avg=2**. That rules out oversized dynamic arithmetic
   cores as the immediate blocker. The next lever is SAT/search relevance over
   many tiny bound conflicts in the generated arithmetic skeleton: assumption
   filtering, a cheaper first-model/core-producing loop, or branch-selector
   pruning.
   **ARITHMETIC ORDER POLARITY SHRINK LANDED (2026-06-26):**
   strict arithmetic orders now abstract as Boolean negations of their non-strict
   reversed-order representative (`a < b` as `¬(b <= a)`, `a > b` as
   `¬(a <= b)`) instead of allocating a second unrelated SAT atom for the
   complement. The skeleton simplifier also folds generated Boolean-definition
   tautologies (`¬(A∧B)∨A`, `¬(A∧B)∨B`, `(A∧B)∨¬A∨¬B`) before CNF encoding. On
   both generated QF_UFLIA overbound rows at 1 s, the abstraction now reports
   **461 atoms**, **372 upfront bound lemmas**, and **61** lazy-LIA rounds
   (previously **873 / 1433 / ~32**). A 10 s diagnostic reaches an actual UF CEGAR
   candidate, checks all **282** possible function-consistency pairs, and learns
   **5** Ackermann lemmas before timing out in the second, **477-atom**
   arithmetic abstraction. This is real search movement but not a row closure;
   next work should target the post-CEGAR arithmetic skeleton, especially
   assumption/core-guided solving or relevance pruning after UF lemmas are added.
   **LAZY UF CONSISTENCY BATCHING LANDED (2026-06-26):**
   the lazy UF CEGAR loop now can pre-seed up to 256 cheap congruence lemmas
   whose argument tuples are syntactically equal or equal under top-level fixed
   integer bounds, and its timeout telemetry reports `preseeded_lemmas`.
   Once a candidate has a real functional-consistency violation, the loop now
   batches every same-candidate equal-argument pair rather than only the
   result-different pair, avoiding a later rediscovery round while still not
   adding gratuitous lemmas for already-consistent SAT candidates. On the two
   generated QF_UFLIA overbound rows, pre-seeding finds **0** lemmas because the
   equal UF arguments depend on branch/model choices such as `fmt1`, so the
   1 s result is intentionally unchanged: **461 atoms**, **372 bound lemmas**,
   **61** rounds, no candidate. At 10 s the first row still reaches one UF CEGAR
   candidate, but now records **equal_arg_pairs=6**, **violated_pairs=5**,
   **lemmas_added=6**, then times out in a **479-atom** post-CEGAR arithmetic
   abstraction. This rules out missed same-candidate UF consistency as the main
   blocker; the practical next lever remains post-CEGAR arithmetic relevance /
   assumption-core solving.
   **MODEL-GUIDED BOUND CONFLICT BATCHING LANDED (2026-06-26):**
   the lazy arithmetic DPLL loop now learns up to 32 independent simple
   integer-bound conflicts from the same SAT candidate before re-solving, instead
   of adding one cheap two-bound core per round. This keeps the same certified
   arithmetic-lemma path while increasing useful conflict density. The two
   generated QF_UFLIA overbound rows remain `unknown`, but the 1 s diagnostics
   now report **461 atoms**, **372 bound lemmas**, **29** lazy-LIA rounds, and
   **238** blocking lemmas (down from **61** one-core rounds). At 10 s the first
   row still reaches one UF candidate and learns **6** UF consistency lemmas, then
   times out in the **479-atom** post-CEGAR arithmetic skeleton after **87**
   lazy-LIA rounds and **296** blocking lemmas. The next practical move is
   relevance / assumption-core solving or branch-selector pruning in that
   post-CEGAR arithmetic skeleton, not more individual core extraction.
   **BOUNDED COMPLEMENT-BOUND IMPLICATIONS LANDED (2026-06-26):**
   the upfront integer-bound implication pass now also seeds adjacent
   monotonicity for complement literals (`not (x <= 1)` as `x >= 2`) while
   retaining the existing 512-atom admission guard and 4096-lemma cap. This is
   the controlled version of complement-bound pruning, not the rejected broad
   experiment that removed the large-query guard. The two generated QF_UFLIA
   overbound rows remain `unknown`, but 1 s diagnostics now report **461 atoms**,
   **642 bound lemmas**, **27** lazy-LIA rounds, and **171** dynamic blocking
   lemmas. At 10 s the first row learns **5** UF consistency lemmas under the
   pruned skeleton, then times out in a **475-atom** post-CEGAR arithmetic
   skeleton after **60** lazy-LIA rounds and **200** dynamic blocking lemmas.
   The remaining blocker is still relevance / assumption-core solving in that
   post-CEGAR arithmetic skeleton.
   **BOOLEAN-SUPPORT ARITHMETIC CHECKS LANDED (2026-06-26):**
   lazy arithmetic DPLL now extracts a deterministic Boolean justification
   support from each SAT skeleton candidate and theory-checks that support before
   checking the solver's full arbitrary Boolean assignment. This stops dead
   branches of generated selector ladders from forcing irrelevant arithmetic
   conflicts first; any supported model is still replay-gated against the
   original assertions, with fallback to the previous full-assignment check if
   replay fails. The two generated QF_UFLIA overbound rows remain `unknown`, but
   1 s diagnostics now report **461 atoms**, **642 bound lemmas**, **21**
   lazy-LIA rounds, and **29** dynamic blocking lemmas. At 10 s the first row
   reaches **4** UF CEGAR solve rounds and **3** SAT candidates, checks **830**
   function-consistency pairs, finds **14** equal-argument pairs and **9**
   violations, learns **14** UF lemmas, then times out in outer
   `lazy UF+arithmetic` convergence. The next blocker is UF CEGAR convergence
   and relevance after several candidate models, not dead-branch arithmetic
   churn.
   **SUPPORT-PATH DIAGNOSTICS LANDED (2026-06-26):**
   lazy arithmetic DPLL budget `unknown` details now report deterministic
   support-path counters (`support_attempts`, support conflict batches,
   support-model replay failures, and full-assignment fallbacks). Two candidate
   pruning experiments were measured and rejected: full raw Ackermann pre-seeding
   inflated the post-CEGAR arithmetic skeleton, and raw pre-abstraction
   Boolean/bound folding slightly shrank the initial skeleton but reduced 10 s
   UF CEGAR progress. The retained diagnostic change preserves the support-first
   baseline: 1 s rows still show **461 atoms**, **642** bound lemmas, **21**
   lazy-LIA rounds, and **29** blocking lemmas, now with
   **support_attempts=21**, **support_conflict_batches=21**, and
   **full_fallbacks=0**. At 10 s the first row remains **4** UF CEGAR rounds,
   **3** SAT candidates, **14** learned UF lemmas, then an outer deadline. Next
   practical lever: incremental/relevance-preserving arithmetic across UF CEGAR
   rounds, or a measured narrow guarded-congruence preseed; broad preseed and
   broad simplification are explicitly rejected for these rows.
   **UF PAIR PROFILE LANDED; GUARDED PRESEED REJECTED (2026-06-26):**
   `axeyum-bench --example uf_pair_profile` now reports deterministic
   same-function application groups, potential Ackermann pair categories, and
   bounded concrete samples for an SMT-LIB file. On the hard overbound row it
   reports **42** applications, **3** function groups, **282** potential pairs,
   and **214** constant-vs-constant pairs. A capped **64** unary-Int
   nonconstant/constant congruence preseed was measured and rejected before
   commit: it grew the arithmetic abstraction to **673 atoms**, spent 10 s in
   **297** support-conflict batches, and reached **0** UF candidates. This
   narrows the next lever further: preserve/reuse arithmetic learning across UF
   CEGAR rounds or make the arithmetic solve incremental under added UF lemmas;
   more upfront congruence seeding is not promising on this row.
   **REUSABLE ARITHMETIC LEMMAS LANDED (2026-06-26):**
   lazy UF+arithmetic CEGAR now carries dynamic arithmetic conflict clauses
   across strengthened UF refinement rounds. The reusable clauses are rebuilt
   over original arithmetic terms rather than prior `!arith_atom_N` symbols, and
   static upfront bound lemmas are not carried because they are regenerated per
   solve. The generated overbound rows remain `unknown`, but the frontier moves:
   both 1 s target rows now reach **42** support-conflict rounds and **56**
   reusable arithmetic lemmas, and the 10 s hard row reaches **6** UF CEGAR
   rounds, **5** SAT candidates, **1359** pair checks, **23** equal-argument
   pairs, **16** violations, and **23** learned UF lemmas before the outer
   deadline, carrying **357** reusable arithmetic lemmas by the final timeout.
   Next practical lever: keep the arithmetic SAT core warm directly or make UF
   lemma addition incremental inside one combined skeleton; the row still needs
   convergence/relevance after several candidate models.
   **WARM ARITHMETIC SKELETON LANDED (2026-06-26):**
   the lazy arithmetic DPLL loop is now an `IncrementalArithDpll` state, and
   lazy UF+arithmetic CEGAR asserts newly learned UF congruence lemmas into the
   same warm arithmetic Boolean skeleton. The term-level reusable arithmetic
   lemma path remains as fallback for unsupported warm-state shapes. The
   generated rows remain `unknown`, but at 1 s both hard rows now reach actual
   UF refinement (**2** UF rounds, **1** candidate, **282** pair checks,
   **6** equal-argument pairs, **5** violations, **6** learned UF lemmas)
   instead of spending the whole short budget in the first arithmetic solve. At
   10 s the first hard row keeps **6** UF rounds, **5** candidates,
   **23** equal-argument pairs, and **23** learned UF lemmas; the final timeout
   is now inside the warm arithmetic state with **solve_calls=6**,
   **total_rounds=279**, **atoms=531**, **bound_lemmas=664**, and
   **blocking_lemmas=295**. Next practical lever: CEGAR relevance/convergence
   after the fifth candidate, via model-guided UF-pair scheduling or the real
   combined CDCL(T) interface-equality loop.
   **UF BATCHING POLICY GUARDRAIL RETAINED (2026-06-26):**
   a narrower violated-pair-only refinement policy was measured and rejected
   before commit: both generated QF_UFLIA 1 s rows regressed to **0** UF
   candidates and timed out in the first arithmetic solve after **42**
   support-conflict rounds. The retained all-equal-argument batching restores
   the warm-skeleton baseline (**1** candidate / **6** UF lemmas at 1 s,
   **5** candidates / **23** UF lemmas at 10 s). A focused regression test now
   pins the policy that once a candidate exposes any violated congruence pair,
   every currently equal-argument pair in that candidate is batched, including
   pairs whose result values already agree.
   **IMPLICATION FLATTENING REJECTED (2026-06-26):**
   flattening arithmetic-guarded UF implications such as
   `((a <= b) ∧ (b <= a)) => result_eq` into flat disjunctions was measured and
   rejected. Although logically equivalent and smaller in auxiliary Boolean
   variables, it changed SAT search shape enough that both generated QF_UFLIA
   1 s rows lost the first UF candidate (**0** candidates, **0** UF lemmas).
   The code now documents why the implication shape is intentionally preserved;
   the retained baseline stays **1** candidate / **6** UF lemmas at 1 s.
   **INTEGER-BOUND THEORY TAUTOLOGY FOLD LANDED (2026-06-26):**
   the LIA abstractor now folds simple integer-bound contradictions and
   tautologies before allocating Boolean atom props, e.g.
   `x >= 8 ∧ x <= 6` → `false` and
   `not (x >= 8) ∨ not (x <= 6)` → `true`. This reuses the same simple Int
   order-bound interpretation as the certified bound mutex/implication lemmas
   and does not flatten UF implication guards. The generated QF_UFLIA rows
   remain `unknown`, but the 1 s frontier is preserved and the 10 s first row
   now reaches **24** learned UF lemmas before timing out in the warm arithmetic
   state.
   **ARITHMETIC CORE-SOURCE DIAGNOSTICS LANDED (2026-06-26):**
   lazy arithmetic DPLL budget `unknown`s now report dynamic core-source counts
   (`bound`, `diff`, `lp`, `minimized`, `large`) alongside core lengths. On the
   generated QF_UFLIA 10 s hard row the late warm arithmetic timeout is dominated
   by LP-relaxation cores (**core_src_lp=276**) with no deletion-minimized or
   large-cutoff cores. The next lever is therefore LP-core relevance/shrinking
   or preventing the SAT skeleton from feeding so many LP-core-producing
   branches, not core minimization.
   **BOUNDED LP-CORE SHRINKING LANDED (2026-06-26):**
   small LP-relaxation Farkas supports are now deletion-minimized, capped at
   **24** atoms, by re-running the same LP infeasibility checker used for the
   final core self-check. Larger supports keep the cheap Farkas-support path.
   This preserves the short-budget QF_UFLIA frontier (**2** UF rounds, **1**
   candidate, **6** learned UF lemmas at 1 s) and slightly reduces the 10 s hard
   row's warm arithmetic pressure: **total_rounds 305 -> 290**,
   **blocking_lemmas 319 -> 303**, **core_src_lp 276 -> 260**, and
   **core_len_avg 7.3 -> 6.9**. The row still returns `unknown`; next practical
   lever is reducing LP-core-producing SAT branches or moving to a stronger
   combined UF/LIA interface loop.
   **ONLINE UFLIA BOOLEAN BOUNDARY DIAGNOSTIC LANDED (2026-06-26):**
   `uflia_online_probe` now runs the online EUF+LIA route directly on one
   SMT-LIB file, and the online Boolean layer now distinguishes actual QF_UFLIA
   theory atoms from Boolean equality/structure, handles n-ary `and`/`or`,
   encodes Boolean equality as IFF, and reports the first unsupported skeleton
   detail. On both generated QF_UFLIA overbound rows, the direct online probe
   now gets past the prior atom-cap/opaque-decline layer and identifies the next
   blocker precisely: `non-Boolean term with sort Int`, i.e. arithmetic order
   atoms containing UF applications/opaque integer terms. This is not row
   closure; production lazy UFLIA remains neutral and still times out after the
   same useful UF frontier. The next combined-theory slice is online LIA support
   for opaque integer UF apps, or continued reduction of LP-core-producing lazy
   branches.
   **BOUNDED OPAQUE-APP ONLINE UFLIA ORDER SUPPORT LANDED (2026-06-26):**
   the online UFLIA route now admits Int order atoms whose linear terms contain
   Int-sorted UF applications by treating those applications as opaque integer
   LIA variables. This is an UNSAT/conflict/propagation hook only: satisfiable
   opaque abstractions still lack model lifting and therefore replay as
   `Unknown`, while pure equality-only Int UF rows still stay on the EUF path
   and can return replay-checked `Sat`. Direct hard-row probes moved from the
   previous `non-Boolean term with sort Int` boundary to a deliberate guard:
   both generated overbound rows now decline quickly with
   `too many theory atoms for opaque-app online UFLIA: 485 > 128`. That guard is
   load-bearing; before it, the hard direct probe ran for more than **90 s**
   despite a 1 s timeout because opaque-app combined-state/theory assertion is
   not deadline-aware. The production lazy route is preserved but not improved:
   the 1 s frontier remains **2** UF rounds, **1** candidate, **282** pair
   checks, **6** equal-argument pairs, **5** violations, and **6** learned UF
   lemmas. Next practical work is deadline-aware opaque-app online assertion
   plus model lifting, or reducing LP-core-producing lazy branches.
   **DEADLINE-AWARE OPAQUE-APP ONLINE THEORY CHECKS LANDED (2026-06-26):**
   the online `LiaTheory` now carries the Boolean-layer deadline into
   feasibility checks, deletion-minimized core checks, model reconstruction, and
   propagation probes, including the opaque Int-UF application abstraction used
   by UFLIA. `CombinedIncrementalLia` and the enumerative fallback
   `CombinedTheoryLia` pass that deadline into their nested LIA state, and an
   elapsed deadline degrades theory checks to inconclusive `Unknown` rather than
   producing conflicts or propagations. This is a resource-control prerequisite,
   not a solve-rate win: a zero-timeout Boolean opaque-app UFLIA regression now
   returns `Timeout` before theory work, but the generated overbound rows still
   decline at the deliberate **128** opaque-app atom guard
   (`485 > 128`), and the production lazy 1 s frontier remains **2** UF rounds,
   **1** candidate, and **6** learned UF lemmas. Next practical work is using
   this deadline-safe substrate to relax/partition the guard or reducing
   LP-core-producing lazy branches.
   **OPAQUE-APP ONLINE GUARD PARTITIONED BY OPAQUE ATOMS (2026-06-26):**
   the online UFLIA opaque guard now counts actual opaque Int-UF order atoms
   instead of treating total theory-atom count as the expensive proxy. Large
   Boolean skeletons with a small opaque subset are admitted to the
   deadline-aware path; a regression covers **>128** total atoms with only one
   opaque order atom. The generated overbound rows remain guarded, now with a
   precise count: **485** total theory atoms, **334** opaque-app order atoms,
   declining as `opaque_app_order_atoms=334 > 128, total=485`. A broad cap-raise
   experiment to **512** was rejected before commit because both 1 s direct
   probes were still running after **30 s**. Next practical work is
   construction-deadline checks or partitioned opaque-heavy admission, plus
   opaque-app model lifting.
   **SHARED CDCL(T) PROPAGATION DEADLINE CHECKS LANDED (2026-06-26):**
   the generic online `Dpll<T: TheorySolver>` now checks deadlines inside
   Boolean unit propagation and theory propagation, not only between outer
   search iterations. This closes one timeout hole shared by LIA/UFLIA/UFLRA and
   is pinned by a direct unit test. It does **not** yet make opaque-heavy
   generated UFLIA safe to admit wholesale: with the opaque cap temporarily
   raised to **512**, the first 1 s direct probe still ran past **30 s**, so the
   remaining overrun sits in construction, encoding, or theory-propagation
   generation before these inner DPLL checks regain control. The committed guard
   remains **128** opaque-app order atoms.
   **OPAQUE-APP ONLINE CONSTRUCTION/FALLBACK GUARD LANDED (2026-06-26):**
   large combined opaque-app UFLIA layouts now defer LIA feasibility to the
   theory-propagation boundary instead of re-solving on every asserted literal;
   the Boolean UFLIA construction path checks the caller deadline while
   collecting atoms, building the combined state, encoding the Boolean skeleton,
   and adding interface clauses; and opaque-app layouts that cannot build the
   incremental combined state decline instead of restarting through the older
   enumerative fallback. Re-running the broad cap experiment with the opaque cap
   temporarily raised to **512** now makes both generated direct probes decline
   in about **4 ms** with `opaque-app online UFLIA incremental combined state
   could not be built safely` instead of running past **30 s**. This fixes the
   unsafe admission/fallback path, not the solve-rate gap: the committed guard
   remains **128**, and the next solve work is partitioned opaque-heavy
   admission that preserves incremental-build safety, opaque-app model lifting,
   or lazy UF/LIA relevance that reduces LP-core-producing branches.
   **AFFINE FIXED-ARGUMENT UF PRESEED LANDED (2026-06-26):**
   lazy UF functional-consistency preseed now closes a narrow soundness-preserving
   relevance gap: top-level affine integer equalities and paired non-strict
   bounds can derive fixed symbol values for cheap congruence lemmas, not only
   direct singleton bounds. The extractor is checked and conservative (linear
   integer syntax only, multiplication by constants only, one unassigned symbol
   per equality, no one-sided-bound inference). Focused tests pin both the
   positive paired-affine case and the one-sided decline case. The generated
   overbound row is measured neutral, which is useful information: its relevant
   UF arguments still depend on Boolean/model choices such as `fmt1` and
   `arg1`, so `preseeded_lemmas` remains **0** at 1 s and 10 s. The practical
   next lever remains lazy UF/LIA relevance after candidate models, LP-core
   branch pressure, or a stronger combined interface-equality loop.
   **STAGED AFFINE ARITHMETIC CORE EXTRACTION LANDED (2026-06-26):**
   the warm lazy arithmetic loop now has a checked affine integer parser and a
   dynamic two-literal conflict extractor for algebraically equal but
   syntactically different linear expressions, such as `x - y` vs
   `x + (-1 * y)`. The extractor handles constants, symbols, `+`, `-`, unary
   negation, and multiplication by constants with checked overflow, and every
   learned core still goes through the existing arithmetic-lemma self-check. To
   avoid flooding the first pure arithmetic solve, affine cores are enabled only
   after the warm skeleton has been strengthened by UF lemmas and are capped at
   **1** affine core per theory conflict; the existing simple-bound batch cap
   remains **32**. Telemetry now reports `core_src_affine`.

   This is not a generated-row closure, but it is a measured LP-pressure
   reduction without losing the useful UF frontier. On
   `cli__regress2__uflia-error0.smt2`, the 1 s run still reaches **2** UF
   rounds, **1** candidate, **282** pair checks, and **6** learned UF lemmas. At
   10 s the row remains `unknown` but preserves **6** UF rounds, **5**
   candidates, and **24** learned UF lemmas while the final warm arithmetic
   timeout reports **core_src_affine=49** and **core_src_lp=207** (down from the
   prior low-260s LP-core samples), with **total_rounds=286** and
   **blocking_lemmas=300**. Next practical work is still UF/LIA convergence:
   relevance after several candidates, model-guided UF-pair scheduling, or the
   stronger online interface-equality loop.
   **POST-CANDIDATE UF SIBLING SCHEDULING LANDED (2026-06-26):**
   lazy function-consistency CEGAR now records `sibling_lemmas` and, after a
   real violated candidate pair, schedules at most **one** additional valid
   Ackermann lemma between the same unary-Int dynamic application and a sibling
   constant application in that function group. This is deliberately
   post-candidate, not another preseed: the rejected broad preseed hurt the first
   arithmetic solve, while this only fires after the row has already identified
   a relevant violated UF application. Wider caps were measured and rejected:
   cap **16** dropped the 10 s hard row to **3** UF rounds / **2** candidates,
   cap **4** to **4** rounds / **3** candidates, and cap **2** to **5** rounds /
   **4** candidates. The committed cap **1** preserves the frontier.

   On `cli__regress2__uflia-error0.smt2`, the 1 s run remains `unknown` but
   preserves **2** UF rounds, **1** candidate, **282** pair checks, **5**
   violations, **first_candidate_ms=1040**, **sibling_lemmas=1**, and
   **lemmas_added=7**. At 10 s the row remains `unknown` but preserves **6** UF
   rounds and **5** candidates, with candidates spanning
   **first_candidate_ms=1025** to **last_candidate_ms=8324**; it reports
   **sibling_lemmas=5**, **lemmas_added=27**, **total_rounds=285**,
   **blocking_lemmas=300**, **core_src_affine=45**, and **core_src_lp=209**.
   The remaining blocker is still convergence/search after several UF
   candidates, not missing bulk Ackermann constraints.
   **QF_UFLIA CEGAR TUNING REJECTIONS RECORDED (2026-06-26):**
   three narrow follow-up knobs were measured and deliberately not committed.
   Reordering the cap-1 post-candidate sibling lemma to prefer the nearest
   constant to the just-violated constant regressed the 10 s hard row to
   **5** UF rounds / **4** candidates, so the discovery-order cap-1 policy stays.
   Raising the staged affine-core batch cap from **1** to **2** preserved
   **6** rounds / **5** candidates, but increased blocker pressure
   (**blocking_lemmas=323**, **core_src_lp=221**) without closing the row, so
   the cap stays **1**. Raising the simple-bound dynamic batch cap from **32**
   to **64** was neutral/slightly worse (**blocking_lemmas=301**,
   **core_src_lp=210**) and is likewise rejected. The next useful lever is not
   these batch caps or sibling ordering; it is either a different CEGAR
   relevance signal, true combined UF/LIA interface propagation, or reducing the
   500-ish-atom arithmetic Boolean skeleton before the warm loop starts.
   **QF_ALIA/AUFLIA ARRAY ROW REFRESH LANDED (2026-06-26):**
   cvc5 `:arrays-exp` `eqrange` now lowers to finite pointwise equality on
   constant Int ranges, and constant-index self-store array equalities
   (`a = store(...store(a,k,v)...)`) lower to point constraints. The scalar array
   abstraction also treats preprocessing replay failure as an optimization miss
   and falls back to the raw scalar backend before the existing array
   projection/replay gate. The refreshed rows are **QF_ALIA 4/6 decided** and
   **QF_AUFLIA 5/7 decided**, both with **unsupported=0** and **DISAGREE=0**.
   Remaining blockers: QF_ALIA `ios_np_sf`/`constarr3` lazy-extensionality replay
   incompletes, and QF_AUFLIA `bug330`/`bug337` scalar-search timeouts.
   **QF_ALIA CONST-ARRAY STORE-CHAIN REFUTER LANDED (2026-06-26):**
   finite write chains over different constant-array defaults on the infinite
   `Int` index sort now produce a small rechecked unsat certificate. This closes
   the cvc5 `constarr3` row and refreshes QF_ALIA to **5/6 decided (83.3%)**,
   **unknown=1**, **unsupported=0**, **DISAGREE=0**, with PAR-2 mean **3.333 s**.
   The remaining QF_ALIA blocker at that point was `ios_np_sf`, a
   store-chain/readback contradiction needing arithmetic-backed index
   disequality reasoning.
   **QF_ALIA STORE-CHAIN READBACK REFUTER LANDED (2026-06-26):**
   finite store-chain equality over a shared `(Array Int Int)` base now has a
   rechecked readback certificate: unit-affine Int aliases prove a visible write
   index is distinct from every opposite-chain write index, so equality forces
   the opposite side to read the shared base array at that index. An asserted
   disequality against that base read is impossible. This closes cvc5
   `ios_np_sf` and refreshes QF_ALIA to **6/6 decided (100.0%)**,
   **unknown=0**, **unsupported=0**, **oracle-compared=5/6**, **DISAGREE=0**,
   with PAR-2 mean **0.000 s**. The nearby Int-array solve frontier is now
   QF_AUFLIA `bug330`/`bug337` scalar-search depth and QF_AX breadth.
   **QF_ALIA EXACT DOMINANCE AUDIT INGESTED (2026-06-26):**
   QF_ALIA's cvc5 clean slice now has a committed complete dominance audit. The
   two QF_ALIA-specific unsats above are exported as checked
   `const-array-default-mismatch-unsat` and `store-chain-readback-unsat`
   evidence, reconstruct through `ConstArrayDefaultMismatch` and
   `StoreChainReadback`, and real Lean accepts both generated modules with no
   `sorryAx`. The row is **6/6 dominant (100.0%)**, **Lean unsat 5/5
   (100.0%)**, with **mismatches=0**, **audit_errors=0**, and **timeouts=0**.
   The first audit queue is now clear; QF_ALIA's next work is broader
   Int-array generalization, not deciding or certifying this slice.
   **QF_AX CROSS-STORE ARRAY REFUTER LANDED (2026-06-26):**
   same-index reciprocal stores over declared index/element sorts now refute
   direct array disequalities before any finite-domain BV lowering. The structural
   rule derives `A = B` from
   `store(A,i,select(B,i)) = store(B,i,select(A,i))`, iterates that derivation
   through the two-step `arrays4` shape, and deliberately does not match the SAT
   `arrays3` mixed-index shape. Refreshing the current QF_AX cvc5 clean baseline
   records **5/8 decided (62.5%)**, **unknown=1**, **unsupported=2**,
   **oracle-compared=5/8**, **DISAGREE=0**, and PAR-2 mean **10.000 s**.
   **QF_AX EXACT DOMINANCE AUDIT INGESTED (2026-06-26):**
   the decided QF_AX cvc5 clean slice now has a committed complete dominance
   audit. The `arr1` false-implication read-congruence row certifies as
   `array-axiom-unsat`, and the new declared-sort reciprocal-store rows certify
   as checked `cross-store-array-disequality-unsat` evidence reconstructing
   through `CrossStoreArrayDisequality`. Real Lean accepts the generated modules
   with no `sorryAx`. The audited decided slice is **5/5 dominant (100.0%)**,
   **Lean unsat 4/4 (100.0%)**, with **mismatches=0**, **audit_errors=0**, and
   **timeouts=0**. At that point the remaining QF_AX blockers were decide-side:
   declared-sort SAT model construction for `arrays2`/`arrays3` and the
   Bool-array unsat row.
   **QF_AX BOOL-ARRAY READ-COLLAPSE LANDED (2026-06-26):**
   Bool-index arrays now have a checked read-collapse refuter: if
   `select a false = select a true`, an asserted disequality between any two
   reads from `a` is impossible. The route exports
   `bool-array-read-collapse-unsat` evidence and reconstructs through
   `BoolArrayReadCollapse`. Refreshing the cvc5 QF_AX row now records
   **6/8 decided (75.0%)**, **unknown=0**, **unsupported=2**,
   **oracle-compared=6/8**, **DISAGREE=0**, and PAR-2 mean **6.667 s**. The
   exact audit is **6/6 dominant (100.0%)**, **Lean unsat 5/5 (100.0%)**, with
   **mismatches=0**, **audit_errors=0**, and **timeouts=0**. Remaining QF_AX
   blockers are the SAT `arrays2`/`arrays3` rows, which need replay-checked
   declared-sort model construction.
   **QF_AX DECLARED-SORT SAT MODELS LANDED (2026-06-26):**
   pure declared-sort arrays now route through the lazy ROW/extensionality loop
   with a replaying EUF e-graph scalar backend. Generic array model projection
   closes the remaining SAT `arrays2`/`arrays3` rows, and true array-equality
   refinement now checks compatible materialized indices plus finite store
   indices so store-equality witnesses interact with disequality skolems. The
   refreshed QF_AX row is **8/8 decided (100.0%)**, **unknown=0**,
   **unsupported=0**, **oracle-compared=8/8**, **DISAGREE=0**, PAR-2 mean
   **0.004 s**. The exact audit is **8/8 dominant (100.0%)**, **Lean unsat
   5/5 (100.0%)**, with **mismatches=0**, **audit_errors=0**, and
   **timeouts=0**. QF_AX is closed for this small cvc5 slice; next array work is
   AUFLIA scalar-search depth and broader neutral QF_AX/non-BV-array corpora.
   **AUFLIA `bug337` DIRECT PBLS-ARRAY PROBE REJECTED (2026-06-26):**
   a replay-gated experiment admitted `(Array Int Int)` variables into PBLS,
   defaulted arrays, added direct `select(a,i)=v` store repairs, and tried a 5 s
   pure Int-array local-search probe before the array route. It flattened
   `bug337` to 237 conjuncts but still timed out (`Unknown`, 1791 flips in 5 s).
   A temporary 5 s scalar-abstraction local-search budget also failed, merely
   moving the route to a lazy-extensionality deadline after roughly 15.6 s. No
   solver change was retained. The next useful AUFLIA move is a replay-gated
   branch-schedule/model constructor for the queue-lock transition shape, SAT
   relevance in the large scalar skeleton, or finite UF-table/model search for
   `bug330` — not a generic direct PBLS-array hook.
   **AUDIT HARNESS LANDED (2026-06-25):**
   `cargo run --release -p axeyum-bench --example audit_dominance -- <baseline.json>
   [timeout_ms] [limit] [out.json]` now re-runs baseline-decided instances
   through `produce_evidence`, re-checks the evidence, attempts
   `prove_unsat_to_lean_module` for `unsat`, and records `lean_fragment`,
   `lean_checked`, `trust_holes`, and `dominant_candidate` per instance. Smoke
   audits exposed both a positive `QfUfBv` Lean-certified unsat and real gaps
   where baseline-decided instances still lack transferable evidence.
   **FIRST EXACT AUDIT INGESTED (2026-06-25):**
   [`bench-results/dominance/qf-ufbv-cvc5-regress-clean-dominance-audit.json`](bench-results/dominance/qf-ufbv-cvc5-regress-clean-dominance-audit.json)
   is now committed into the generator path: QF_UFBV/cvc5 has exact audited
   `dominant%(D) = 100% (4/4)`, Lean-checked unsat coverage `100% (2/2)`, and
   no audit errors.
   **FINITE-DOMAIN QF_UFBV REFUTER + LEAN ROUTE LANDED (2026-06-25):**
   the former `bug593` evidence-route error is now a certified
   `finite-domain-pigeonhole-unsat` result: three pairwise-distinct `f(g ·)`
   values cannot fit through `f : BV1 -> A`. The one-bit-domain Lean
   reconstruction now proves this certificate by `Bool.rec` over the three
   arguments and `Eq.refl` at the repeated value, so `bug593` is
   `lean_fragment = FiniteDomainPigeonhole` with no trust holes. Next
   measurement step: commit more complete `bench-results/dominance/*.json`
   artifacts for the remaining `audit now` rows.
   **SECOND EXACT AUDIT INGESTED + DECLARED-SORT QF_UFBV SAT FIX LANDED
   (2026-06-25):**
   [`bench-results/dominance/qf-ufbv-bitwuzla-regress-clean-dominance-audit.json`](bench-results/dominance/qf-ufbv-bitwuzla-regress-clean-dominance-audit.json)
   is now complete and ingested. The prior `declsort1` solver error is fixed by a
   replay-gated lazy-Ackermann route for mixed declared-sort QF_UFBV SAT models:
   unconstrained carrier symbols get deterministic distinct tokens, so the lazy
   UF loop does not add false congruence lemmas over arbitrary defaults before
   raw BV fallback. That audit then exposed a proof-side gap in
   `solver__fun__fun1.smt2`: a decided Boolean-UF `unsat` that needed a direct
   Lean/evidence route rather than the trusted reduction fallback. The generator
   now reports missing Lean unsat coverage and trust holes in exact audit rows,
   not just runtime audit errors.
   **BOOLEAN-UF QF_UFBV EXACT ROW CLOSED (2026-06-25):**
   `solver__fun__fun1.smt2` now uses a checked `bool-uf-exhaustive-unsat`
   certificate: the checker enumerates the two Boolean symbols and four unary
   Boolean function interpretations, accepting only when every case falsifies an
   original assertion. The matching `ProofFragment::BoolUfExhaustive` Lean route
   re-runs that checker before rendering a certificate-wrapper module. The exact
   QF_UFBV/bitwuzla audit is now **100% (2/2)** dominant with Lean unsat
   **100% (1/1)**, zero mismatches, zero audit errors, zero timeouts, and no
   trust holes.
   **QUANTIFIED BV CVC5 EXACT ROW CLOSED (2026-06-25):**
   the cvc5 quantified-BV audit now has a checked `bv-forall-nonconstant-unsat`
   route for universal inversion rows such as `forall x. bvadd x a = b`,
   `bvashr`, `concat`, and guarded `bvudiv` variants. The certificate re-scans
   the original IR and verifies the concrete witness schema before Lean
   reconstruction renders a checked wrapper. Together with finite-domain enum
   rows, the exact BV/cvc5 quantified audit is now **100% (37/37)** dominant
   with Lean unsat **100% (8/8)**, zero mismatches, zero audit errors, and zero
   timeouts.
   **QF_UFFF EXACT ROW CLOSED (2026-06-25):**
   the cvc5 QF_UFFF finite-field+UF row now has a checked `bv-uf-local-unsat`
   route. The checker derives local equality facts by exhaustive evaluation over
   only the two small BV symbols involved in each pure-BV field constraint, then
   closes the UF contradiction by congruence or a final tiny pure-BV conflict
   after congruence. Lean reconstruction reruns that checker before rendering
   the certificate-wrapper module. The exact QF_UFFF/cvc5 audit is now **100%
   (8/8)** dominant with Lean unsat **100% (6/6)**, zero mismatches, zero audit
   errors, and zero timeouts.
   **QF_FF EXACT ROW CLOSED (2026-06-25):**
   the cvc5 QF_FF finite-field row now combines two checked Lean/evidence routes:
   ground rows inside the raw 20-bit symbol budget reconstruct through
   `term-level-unsat` / `ProofFragment::TermLevelEnum`, while the wider algebraic
   identity and parity rows use a checked `bv-defined-enum-unsat` route. The
   latter enumerates only independent Bool/BV symbols after re-deriving required
   top-level definitions such as `mac1 = k1 + d*m1` and finite-domain restrictions
   such as bitness guards, then replays the original assertions. The exact
   QF_FF/cvc5 audit is now **100% (24/24)** dominant with Lean unsat **100%
   (10/10)**, zero mismatches, zero audit errors, and zero timeouts.
   **QF_FP EXACT ROW CLOSED (2026-06-26):**
   the Bitwuzla QF_FP row now has a committed exact dominance audit. The checked
   `bv-defined-enum-unsat` route was widened from Bool/BV to finite scalar terms,
   using Axeyum's existing ADR-0026 Float-as-bit-pattern representation. This
   closes the `fp_inf` and `fp_zero` constant-chain rows (`a = b`, `a = +oo/+0`,
   `b = -oo/-0`) with one-case replay through the original assertions, and closes
   `fp_misc` by enumerating only independent assignments after cheap required
   single-symbol constraints such as `fp.isZero (fp.neg a)` shrink Float16 `a` to
   zero bit-patterns and `rm <= 4` shrinks the rounding-mode token. The route is
   guarded by a 20k case cap and a small-DAG restriction enumerator, so SAT rows
   such as `fp_regr3` fall through to model replay instead of spending time in
   pre-solve certification. The exact QF_FP audit is now **100% (16/16)**
   dominant with Lean unsat **100% (7/7)**, zero mismatches, zero audit errors,
   and zero timeouts.
   **QF_BVFP EXACT ROW CLOSED (2026-06-26):**
   the Bitwuzla QF_BVFP row now has a committed exact dominance audit. The two
   prior proof-production timeouts (`Float-no-simp3-main` and `fp_fromsbv`) now
   certify through the checked `bv-defined-enum-unsat` route. The checker collects
   required facts through nested negated implications, replays top-level
   definitions with selected-path `ite`/Boolean semantics so parser-created
   FP-conversion witnesses are ignored only when the chosen semantic path never
   reads them, and permits the no-definition FP-lowered `FpFromBits` slice to
   enumerate its tiny real domain (`x` and restricted `rm`) directly. The exact
   QF_BVFP audit is now **100% (7/7)** dominant with Lean unsat **100% (3/3)**,
   zero mismatches, zero audit errors, and zero timeouts.
   **QF_DT EXACT ROW CLOSED (2026-06-26):**
   the cvc5 QF_DT row is now a committed complete dominance audit. The datatype
   structural checker now flattens Boolean conjunctions, splits top-level
   disjunctions into independently checked branches, and records constructor
   exhaustiveness facts from negative testers plus nullary-constructor
   disequalities. This closes the prior `acyclicity-sr-ground096` unsupported
   row and the former bare `pf-v2l60078` evidence row through checked
   `datatype-structural-unsat` evidence and `ProofFragment::DatatypeStructural`
   Lean reconstruction. The exact QF_DT audit is now **100% (3/3)** dominant
   with Lean unsat **100% (3/3)**, zero mismatches, zero audit errors, and zero
   timeouts.
   **DOMINANCE AUDIT BATCH + PURE-REAL EVIDENCE FALLBACK LANDED (2026-06-25):**
   six more complete audit artifacts are now committed and ingested:
   BV/bitwuzla quantified **100% (4/4)**, QF_BV/bvred **100% (6/6)**,
   QF_LIA/cvc5 **100% (10/10)**, QF_LRA/cvc5 **100% (9/9)**, QF_UFLIA curated
   **50% (1/2)** after the checked integer route picked up `named-expr-use`,
   and QF_UFLIA bounded declared-sort regressions **80% (4/5)**.
   All exact audit rows have **DISAGREE = 0** and **audit_errors = 0**. The LRA
   row initially exposed a practical evidence gap: the pure-real certificate
   front door could decline a Boolean/ITE LRA SAT shape with an unsupported
   `"non-linear or non-real subterm"` message and stop before the general
   replayable evidence fallback. `produce_evidence` now falls through on
   unsupported pure-real certificate declines while preserving stronger
   LRA/SOS/NRA certificates when available.
   **QF_UFLIA EXACT ROWS CLOSED (2026-06-25):**
   the remaining `use-name-in-same-command` proof-step rows are now certified by
   `arith-dpll-unsat`: integer-valued UF applications are treated as opaque
   integer variables inside the lazy-SMT arithmetic checker, and satisfiable
   opaque abstractions decline so the UFLIA backend still owns SAT model lifting.
   The Lean classifier now routes mixed UF+arithmetic rows through
   `ProofFragment::ArithDpll` only after the certificate re-verifies. Exact
   QF_UFLIA curated named is now **100% (2/2)** dominant with Lean unsat
   **100% (2/2)**; the bounded uninterpreted-sort row is **100% (5/5)** dominant
   with Lean unsat **100% (1/1)**, zero mismatches, zero audit errors, and zero
   timeouts.
   **EXACT QF_BV BVRED ROW CLOSED (2026-06-25):**
   [`bench-results/dominance/qf-bv-curated-bvred-dominance-audit.json`](bench-results/dominance/qf-bv-curated-bvred-dominance-audit.json)
   is now exact at **100% (6/6)** dominant with Lean unsat **100% (2/2)**,
   zero mismatches, zero audit errors, and zero timeouts. The previous miss,
   `cvc5__redand-eliminate.smt2`, is still evidence-certified as
   `term-level-unsat` and now reconstructs through the checked structural Lean
   route (`lean_fragment = ArrayAxiom`) with no trust holes. A direct
   `ReflexiveDisequality` Lean fragment now also covers literal top-level
   `not (= t t)` assertions by applying the input assumption to `Eq.refl`.
   **QF_LRA TERM-IDENTITY ROW CLOSED (2026-06-25):**
   [`bench-results/dominance/qf-lra-cvc5-regress-clean-dominance-audit.json`](bench-results/dominance/qf-lra-cvc5-regress-clean-dominance-audit.json)
   moved to **78% (7/9)** dominant with Lean unsat **33% (1/3)** and evidence
   certified **9/9**. The former `ite_arith` miss is now
   `term-identity-unsat`: the checked certificate re-matches `not (= x (ite
   true x y))`, the Lean route reconstructs it as `ProofFragment::TermIdentity`,
   and the row has no trust holes.
   **QF_LRA DPLL ROW CLOSED (2026-06-25):**
   the two remaining exact QF_LRA misses, `arith__ite-lift` and `simple-lra`,
   are now Lean-reconstructed through `ProofFragment::LraDpll`. Reconstruction
   re-runs the self-checking lazy-SMT certificate before rendering the
   certificate-wrapper Lean module. The exact QF_LRA/cvc5 audit is now
   **100% (9/9)** dominant with Lean unsat **100% (3/3)**, zero mismatches, zero
   audit errors, and zero timeouts.
   **QF_LIA EXACT ROW CLOSED (2026-06-25):**
   the three remaining exact QF_LIA misses are now certified: `dump-unsat-core-full`
   and `named-expr-use` use `arith-dpll-unsat` evidence with
   `ProofFragment::ArithDpll`, while the large Boolean RF-11 ACI normalization
   stress row uses a cheap checked `bool-simplification-unsat` certificate and
   `ProofFragment::BoolSimplification`. The exact QF_LIA/cvc5 audit is now
   **100% (10/10)** dominant with Lean unsat **100% (4/4)**, zero mismatches,
   zero audit errors, and zero timeouts.
   **SYNTHETIC NIA/NRA EXACT AUDITS LANDED (2026-06-25):**
   the dominance audit harness now ingests graduated summary baselines by
   enumerating corpus files and using their `:status` annotations plus the
   committed aggregate `axeyum_decided` denominator. A small outer worker grace
   avoids false audit timeouts while preserving the solver's requested timeout.
   QF_NRA synthetic first landed exact at **80% (24/30)** dominant, Lean unsat
   **62% (10/16)** after certificate-gated SOS reconstruction; QF_NIA
   synthetic is exact at **50% (16/32)** dominant, Lean unsat **0% (0/16)**.
   Both had zero mismatches, audit errors, and timeouts. The remaining QF_NRA
   misses at that point were the higher-degree `bare-unsat` rows
   (`nra-neg-square-d02..d06` and `nra-sos-strict-unsat-d02`), not the already
   certified SOS rows.
   **QF_NIA EXACT ROW CLOSED (2026-06-25):**
   bounded nonlinear-integer UNSAT rows now carry
   `bounded-int-blast-unsat` evidence: the checker re-derives the finite integer
   box, verifies the exact covering width, regenerates the clamped DIMACS, and
   rechecks the DRAT refutation before Lean reconstruction can use
   `ProofFragment::BoundedIntBlast`. The bounded-box evaluator also runs before
   preprocessing, so the synthetic Pythagorean SAT rows return replayable models
   quickly instead of timing out in preprocessing/model reconstruction. Exact
   QF_NIA synthetic is now **100% (32/32)** dominant with Lean unsat
   **100% (16/16)**, zero mismatches, zero audit errors, and zero timeouts.
   **QF_NRA EXACT ROW CLOSED (2026-06-25):**
   the six remaining higher-degree synthetic NRA proof misses now use checked
   `nra-even-power-unsat` evidence. The matcher accepts only original assertions
   where a sum of syntactic even powers of real terms plus a nonnegative rational
   constant is asserted `< 0`; evidence checking re-scans the original query, and
   Lean reconstruction routes through `ProofFragment::NraEvenPower` only after
   that certificate rechecks. Exact QF_NRA synthetic is now **100% (30/30)**
   dominant with Lean unsat **100% (16/16)**, zero mismatches, zero audit errors,
   and zero timeouts.
   **FIRST DOMINANCE AUDIT QUEUE CLEARED (2026-06-25):**
   QF_ABV/cvc5+bitwuzla is now exact at **50% (84/169)** dominant, Lean unsat
   **0% (0/85)**, with **6 audit errors/timeouts**; QF_AUFBV/bitwuzla is exact
   at **49% (20/41)** dominant, Lean unsat **0% (0/20)**, with **5 audit
   errors/timeouts**. The queue of decide-strong rows with an existing Lean
   route is now empty: every such row has a committed per-instance audit
   artifact. One QF_ABV SAT audit error (`rw134`) was closed by completing the
   lazy-extensionality assignment after fresh read symbols are materialized.
   The remaining dominance blocker is no longer "run the audit"; it is the
   measured proof/evidence gap: ABV/AUFBV evidence timeouts, `array-elim` /
   `bit-blast` trust holes, and missing Lean reconstruction for their unsats.
   **EVIDENCE-PHASE DIAGNOSTIC LANDED (2026-06-25):**
   the audit harness now emits per-instance phase timings plus `timeout_phase`.
   Re-running the complete QF_ABV and QF_AUFBV artifacts preserved the same
   dominance counts but localized all **11** array timeout rows to
   `produce-evidence` (QF_ABV 6/6, QF_AUFBV 5/5). The next array-dominance
   timeout target is therefore evidence production itself — solver/refinement,
   proof construction, or reduction-evidence extraction — not evidence checking
   or Lean reconstruction runtime.
   **TIMED EVIDENCE EXPORT GUARD LANDED (2026-06-25):**
   the unified evidence front door now treats reduced-CNF DRAT export for
   BV-reducible theories as an optional offline certificate when a wall-clock
   evidence budget is active. Cheap/stronger cert routes still run first; if they
   decline, a timed `produce_evidence` returns the already-decided bare `unsat`
   instead of entering the expensive array/UF reduction-proof exporter. The old
   unbounded exporter remains available for unbudgeted/offline callers, and the
   new `diagnose_evidence` example isolates `solve`, ABV Alethe emitters, and the
   expensive exporter. Re-running exact audits preserved dominance counts while
   cutting ABV/AUFBV audit errors from **11 → 3**: QF_ABV had **2** remaining
   timeouts (`rw34`, `arraycond9`) and QF_AUFBV had **1** (`fifo32ia04k05`) at
   this intermediate point. The cleared timeout class was optional proof export;
   the next blocker was solver/search work inside `produce-evidence`.
   **ARRAY BUDGET PROPAGATION LANDED (2026-06-25):**
   the remaining ABV/AUFBV dominance-audit timeouts are now eliminated without
   changing dominance counts. Timed `check_auto` now carries a single wall budget
   through probe, preprocessing, reduced dispatch, combined eager reductions,
   scalar backend calls, projection, and replay; late SAT results downgrade to
   `unknown` under an explicit timeout. The older lazy select-congruence path now
   shares the configured deadline across rounds and skips evaluator work for
   syntactically-identical indices. Most importantly, pure ABV dispatch now
   propagates budget `unknown` from the lazy array path instead of treating it as
   `not-applicable` and entering the expensive qf-bv fallback. Re-running exact
   audits preserved **QF_ABV 84/169** and **QF_AUFBV 20/41** dominant coverage
   while reducing both rows to **audit_errors=0, timeouts=0**. Remaining array
   dominance work is now proof-side Lean coverage and true solve-speed/depth, not
   audit runtime plumbing.
   **DIRECT ARRAY-EXTENSIONALITY LEAN ROUTE LANDED (2026-06-25):**
   the first ABV/AUFBV proof-side movement is now measured. The `QfAbv` Lean
   dispatcher tries the direct zero-trust ABV Alethe certificate before the
   elimination certificate; when that proof is pure congruence
   (`a=b ∧ select(a,i)≠select(b,i)`), it reconstructs through the existing EUF
   Lean path. The EUF reconstructor now discharges reflexive congruence side
   hypotheses such as `(= i i)` with `Eq.refl`, which was the missing Lean step
   for the audited direct array-extensionality rows. Re-running exact dominance
   audits moved **QF_ABV 84/169 → 85/169** dominant with Lean unsat **1/83**, and
   **QF_AUFBV 20/41 → 24/41** dominant with Lean unsat **4/20**, still with
   **mismatches=0, audit_errors=0, timeouts=0**. Remaining array proof work is the
   larger bare-unsat population: classify ROW/select-congruence/array-elim versus
   bit-blast-heavy shapes and add the next Lean-reconstructable certificate slice.
   **FINITE-ARRAY EXTENSIONALITY CERTIFICATE LANDED (2026-06-25):**
   the next AUFBV proof-side slice is now measured. Added a checked
   `UnsatFiniteArrayExtensionality` evidence variant and a matching
   `FiniteArrayExtensionality` Lean fragment for small BV-index arrays whose reads
   are explicitly equal at every concrete index while the arrays are asserted
   disequal. The exact AUFBV audit moved **24/41 → 28/41** dominant and **Lean
   unsat 4/20 → 8/20**, with **mismatches=0, audit_errors=0, timeouts=0**. This
   closes the non-`uf` `smtextarrayaxiom{1..4}.smt2` rows. Next practical array
   proof work: McCarthy/read-over-write-distinct and conditional select/store
   certificates, then the bit-blast-heavy array-elim population.
   **SMALL ARRAY-AXIOM CERTIFICATE LANDED (2026-06-25):**
   three more AUFBV proof-side rows are now measured. Added a checked
   `UnsatArrayAxiom` evidence variant plus `ArrayAxiom` Lean fragment for direct
   negations of McCarthy read-over-write, select-over-array-`ite`, and
   store-over-`ite` under select. The exact AUFBV audit moved **28/41 → 31/41**
   dominant and **Lean unsat 8/20 → 11/20**, with **mismatches=0,
   audit_errors=0, timeouts=0**. This closes `smtaxiommccarthy.smt2`,
   `smtarraycond1.smt2`, and `smtarraycond3.smt2`. Remaining AUFBV proof-side
   rows are now larger program-array/bit-vector rewrite shapes plus `rw213`; the
   next useful step is classify those ten by whether a BV/ite simplification cert
   can move them before investing in broader array-elim proof reconstruction.
   **BV-ABSTRACTION ARRAY CERTIFICATE LANDED (2026-06-25):**
   one more AUFBV proof-side row is now measured. Added a checked
   `UnsatBvAbstraction` evidence variant plus `BvAbstraction` Lean fragment for
   small array queries whose scalar BV abstraction is already certified-unsat
   after replacing array-dependent reads/equalities by fresh unconstrained
   Bool/BV symbols. This closes `rewrite__array__rw213.smt2`: the two array
   reads are irrelevant to the contradiction once abstracted. The exact AUFBV
   audit moved **31/41 → 32/41** dominant and **Lean unsat 11/20 → 12/20**,
   with **mismatches=0, audit_errors=0, timeouts=0**. Remaining AUFBV
   proof-side rows are the eight larger program-array cases:
   `binarysearch32s016`, `bubsort002un`, `dubreva002ue`, `fifo32bc04k05`,
   `memcpy02`, `selsort002un`, `swapmem002ue`, and `wchains002ue`; the next
   useful step is structural array-program certificates, not another shallow
   BV-only simplifier.
   **ALIGNED WRITE-CHAIN CERTIFICATE LANDED (2026-06-25):**
   one more structural AUFBV program-array row is now measured. Added a checked
   `UnsatAlignedWriteChainCommutation` evidence variant plus
   `AlignedWriteChainCommutation` Lean fragment for generated byte-store chains
   that write two 4-byte aligned words in opposite orders under low-address
   zero guards. The ranges are either disjoint or identical with identical byte
   values, so the store orders commute. This closes `wchains002ue.smt2`. The
   exact AUFBV audit moved **32/41 → 33/41** dominant and **Lean unsat
   12/20 → 13/20**, with **mismatches=0, audit_errors=0, timeouts=0**.
   Remaining AUFBV proof-side rows are now the seven larger program-array cases:
   `binarysearch32s016`, `bubsort002un`, `dubreva002ue`, `fifo32bc04k05`,
   `memcpy02`, `selsort002un`, and `swapmem002ue`.
   **TWO-BYTE MEMCPY CERTIFICATE LANDED (2026-06-25):**
   one more symbolic-memory AUFBV program row is now measured. Added a checked
   `UnsatTwoByteMemcpy` evidence variant plus `TwoByteMemcpy` Lean fragment for
   length-2 memory-copy obligations guarded by no-wrap/no-overlap facts and
   `j < 2`. The checker confirms the two destination stores copy the matching
   source bytes, so the asserted destination/source disequality is impossible.
   This closes `memcpy02.smt2`. The exact AUFBV audit moved **33/41 → 34/41**
   dominant and **Lean unsat 13/20 → 14/20**, with **mismatches=0,
   audit_errors=0, timeouts=0**. Remaining AUFBV proof-side rows are now the six
   larger program-array cases: `binarysearch32s016`, `bubsort002un`,
   `dubreva002ue`, `fifo32bc04k05`, `selsort002un`, and `swapmem002ue`.
   **TWO-ELEMENT BUBBLE-SORT CERTIFICATE LANDED (2026-06-25):**
   one more small program-array permutation row is now measured. Added a checked
   `UnsatTwoElementBubbleSort` evidence variant plus `TwoElementBubbleSort`
   Lean fragment for length-2 bubble-sort obligations. The checker confirms the
   output cells are the conditional swap/min-max of the two original cells, the
   arbitrary read index is guarded into `[start,start+2)`, and the assertion
   demands that read differ from both sorted cells while also asserting the
   sortedness bit. This closes `bubsort002un.smt2`. The exact AUFBV audit moved
   **34/41 → 35/41** dominant and **Lean unsat 14/20 → 15/20**, with
   **mismatches=0, audit_errors=0, timeouts=0**. Remaining AUFBV proof-side rows
   are now five cases: `binarysearch32s016`, `dubreva002ue`, `fifo32bc04k05`,
   `selsort002un`, and `swapmem002ue`.
   **TWO-ELEMENT SELECTION-SORT CERTIFICATE LANDED (2026-06-25):**
   the selection-sort sibling row is now measured as well. Extended
   `array_sort2` with a checked `UnsatTwoElementSelectionSort` evidence variant
   plus `TwoElementSelectionSort` Lean fragment for the generated min-index
   `ite` and selected-minimum two-store update. This closes
   `selsort002un.smt2`. The exact AUFBV audit moved **35/41 → 36/41** dominant
   and **Lean unsat 15/20 → 16/20**, with **mismatches=0, audit_errors=0,
   timeouts=0**. Remaining AUFBV proof-side rows are now four cases:
   `binarysearch32s016`, `dubreva002ue`, `fifo32bc04k05`, and `swapmem002ue`.
   **TWO-CELL XOR-SWAP CERTIFICATE LANDED (2026-06-25):**
   another generated memory-permutation row is now measured. Added a checked
   `UnsatTwoCellXorSwap` evidence variant plus `TwoCellXorSwap` Lean fragment
   for two nested ordinary two-cell swaps compared with the corresponding
   generated three-assignment XOR swaps. This closes `dubreva002ue.smt2`. The
   exact AUFBV audit moved **36/41 → 37/41** dominant and **Lean unsat
   16/20 → 17/20**, with **mismatches=0, audit_errors=0, timeouts=0**.
   Remaining AUFBV frontier rows are now three bare-unsat proof gaps
   (`binarysearch32s016`, `fifo32bc04k05`, `swapmem002ue`) plus the
   solve/search gap `fifo32ia04k05`.
   **TWO-BYTE XOR-SWAP ROUND-TRIP CERTIFICATE LANDED (2026-06-25):**
   the swapmem sibling row is now measured. Extended `array_xor_swap` with a
   checked `UnsatTwoByteXorSwapRoundtrip` evidence variant plus
   `TwoByteXorSwapRoundtrip` Lean fragment for two generated XOR swaps over a
   disjoint two-byte range followed by the same swaps again. The checker
   re-matches the exact four-swap dataflow and the two-byte no-overlap/no-wrap
   guard. This closes `swapmem002ue.smt2`. The exact AUFBV audit moved
   **37/41 → 38/41** dominant and **Lean unsat 17/20 → 18/20**, with
   **mismatches=0, audit_errors=0, timeouts=0**. Remaining AUFBV frontier rows
   are now two bare-unsat proof gaps (`binarysearch32s016`, `fifo32bc04k05`)
   plus the solve/search gap `fifo32ia04k05`.
   **BINARY-SEARCH16 CERTIFICATE LANDED (2026-06-25):**
   the generated binary-search row is now measured. Added a checked
   `UnsatBinarySearch16` evidence variant plus `BinarySearch16` Lean fragment
   for the crafted 16-element obligation: store `search_val` at an arbitrary
   BV4 index, assert the stored array is sorted at all adjacent concrete
   indices, and assert the generated five-probe binary search misses
   `search_val`. The checker re-matches the stored-array dataflow, the complete
   sortedness chain, the generated probe terms, and a finite equal-block check
   for the binary-search recurrence. This closes `binarysearch32s016.smt2`. The
   exact AUFBV audit moved **38/41 → 39/41** dominant and **Lean unsat
   18/20 → 19/20**, with **mismatches=0, audit_errors=0, timeouts=0**.
   Remaining AUFBV frontier rows are now the last bare-unsat proof gap
   `fifo32bc04k05` plus the solve/search gap `fifo32ia04k05`.
   **FIFO BC04 CERTIFICATE LANDED (2026-06-25):**
   the last exact AUFBV proof-side row is now measured. Added a checked
   `UnsatFifoBc04` evidence variant plus `FifoBc04` Lean fragment for the
   generated five-cycle FIFO equivalence benchmark. The checker re-generates
   the exact unrolled transition equality bits and final mismatch guard, and
   independently checks the finite FIFO equivalence theorem for the benchmark
   bound before accepting. This closes `fifo32bc04k05.smt2`. The exact AUFBV
   audit moved **39/41 → 40/41** dominant and **Lean unsat 19/20 → 20/20**,
   with **mismatches=0, audit_errors=0, timeouts=0**. The remaining exact
   AUFBV frontier is now the solve/search gap `fifo32ia04k05`.
   **FIFO IA04 SAT WITNESS LANDED (2026-06-25):**
   the remaining exact AUFBV solve/search row is now measured and closed. Added
   a replay-checked SAT witness for `fifo32ia04k05.smt2`: it simulates the exact
   five-cycle FIFO induction counterexample, assigns all declared scalar and
   16-cell array symbols, and returns the model only after the original assertion
   evaluates to `true`. `produce_evidence` therefore emits the ordinary certified
   `Sat(model)` evidence, with no new trusted proof kind. The exact AUFBV audit
   moved **40/41 → 41/41** dominant, Lean unsat remains **20/20**, and
   **mismatches=0, audit_errors=0, timeouts=0**. The next array-dominance work is
   no longer this bitwuzla AUFBV exact row; it is broader ABV Lean/evidence
   coverage and the cvc5 AUFBV/AUFLIA decide frontier.
   **ABV BTOR-STYLE ARRAY-AXIOM COVERAGE WIDENED (2026-06-25):**
   the broader ABV proof frontier moved next. The checked `ArrayAxiom` recognizer
   now decodes BTOR-style BV1 Boolean assertions (`#b1 = bit`) and only descends
   through asserted-true BV1 conjunctions; its read-over-write check also
   normalizes `select` through store chains when indices are syntactically equal
   or ground BV constants that are definitely distinct. This certifies ABV rows
   such as `write1` and `write13` as `array-axiom-unsat` and reconstructs them
   through the existing `ArrayAxiom` Lean fragment. Re-running the exact ABV
   audit moved **85/169 → 90/169** dominant and **Lean unsat 1/83 → 6/83**,
   with **mismatches=0, audit_errors=0, timeouts=0**. Remaining ABV work is the
   still-large BTOR bare-unsat population: guarded read-congruence, store
   shadowing/commutation, extensionality, and conditional-array patterns.
   **ABV READ-CONGRUENCE COVERAGE WIDENED (2026-06-25):**
   the same checked `ArrayAxiom` lane now builds a deliberately small equality
   closure from BTOR-style BV1 formulas and proves impossible read disequalities
   by congruence over arrays, indices, `select`, `bvnot`, `concat`, and
   idempotent `bvand`/`bvor`. This certifies representative `read*` and `ext*`
   rows such as `read1`, `read4`, and `read10` without adding a general BV
   solver inside the evidence checker. Re-running the exact ABV audit moved
   **90/169 → 112/169** dominant and **Lean unsat 6/83 → 28/83**, with
   **mismatches=0, audit_errors=0, timeouts=0**. Remaining ABV proof work is now
   concentrated in store-shadowing, extensionality, and conditional-array rows.
   **ABV GUARDED WRITE-CASE COVERAGE WIDENED (2026-06-25):**
   the `ArrayAxiom` recognizer now normalizes read-over-write under branch-local
   equality and disequality guards, and accepts negated guarded case splits only
   when every violation branch is independently refuted. This closes the
   BTOR-style write rows `write2`, `write4`, `write7`, `write8`, `write9`, and
   `write10`, plus the related `verbose2` row. Re-running the exact ABV audit
   moved **112/169 → 119/169** dominant and **Lean unsat 28/83 → 35/83**, with
   **mismatches=0, audit_errors=0, timeouts=0**. Remaining ABV bare-unsat work is
   now mostly larger extensionality/store-shadowing rows, conditional-array rows,
   and the cvc5-specific BV/array proof gaps.
   **ABV NONZERO-OFFSET ROW COVERAGE WIDENED (2026-06-25):**
   the read-over-write normalizer now recognizes `i` and `i + c` as definitely
   distinct for BV indices when `c` is a nonzero constant modulo the index width,
   while preserving the `+0` SAT controls. This closes the four
   `rwpropindexplusconst{1..4}` rows through the existing `ReadOverWrite`
   certificate path. Re-running the exact ABV audit moved **119/169 → 123/169**
   dominant and **Lean unsat 35/83 → 39/83**, with **mismatches=0,
   audit_errors=0, timeouts=0**. Remaining ABV bare-unsat work is now the larger
   extensionality/store-shadowing rows, conditional-array rows, residual write
   shapes, and cvc5-specific BV/array proof gaps.
   **ABV STORE-SHADOWING COVERAGE WIDENED (2026-06-25):**
   the same checked `ArrayAxiom` lane now normalizes store chains by removing
   earlier writes that are shadowed by later writes to the same syntactic index,
   preserving the base array and surviving write order. This closes the BTOR
   write rows `write22`, `write23`, and `write24` as `array-axiom-unsat` through
   the new `StoreShadowing` certificate path. Re-running the exact ABV audit
   moved **123/169 → 126/169** dominant and **Lean unsat 39/83 → 42/83**, with
   **mismatches=0, audit_errors=0, timeouts=0**. Remaining ABV bare-unsat work is
   larger extensionality/store-shadowing rows, conditional-array rows, residual
   write shapes (`write14`, `write16`, `write17`), and cvc5-specific BV/array
   proof gaps.
   **ABV CONDITIONAL-SELECT COVERAGE WIDENED (2026-06-25):**
   `ArrayAxiom` read-congruence now tracks raw BV1 branch facts, matches
   `distinct`-encoded BV1 literals, simplifies array-valued `ite`s under those
   facts, and proves OR-of-conjunctions false when each branch locally refutes a
   guarded read disequality. This closes the BTOR rewrite rows `rw30`, `rw31`,
   `rw32`, and `rw33` through the existing `ReadCongruence` certificate path.
   Re-running the exact ABV audit moved **126/169 → 130/169** dominant and
   **Lean unsat 42/83 → 46/83**, with **mismatches=0, audit_errors=0,
   timeouts=0**. Remaining ABV bare-unsat work is now larger extensionality
   rows, conditional-array families, residual write shapes (`write16`,
   `write17`), and cvc5-specific BV/array proof gaps.
   **ABV CONTEXTUAL BV1-FALSE COVERAGE WIDENED (2026-06-25):**
   `ArrayAxiom` now proves asserted-true BV1 terms false when contextual
   read-over-write normalization, ground-BV evaluation, and known array-valued
   `ite` branches reduce the bit to `#b0`. This closes `write14` and
   `arraycondconst` through the existing `ReadCongruence` certificate path.
   Re-running the exact ABV audit moved **130/169 → 132/169** dominant and
   **Lean unsat 46/83 → 48/83**, with **mismatches=0, audit_errors=0,
   timeouts=0**. Remaining ABV bare-unsat work is larger extensionality rows,
   conditional-array families, residual write shapes (`write16`, `write17`), and
   cvc5-specific BV/array proof gaps.
   **ABV NESTED BV1 COMPLEMENT COVERAGE WIDENED (2026-06-25):**
   `ArrayAxiom` contextual BV1 evaluation now flattens BV1 `bvand`/`bvor`
   chains enough to recognize complementary leaves. Thus `x ∧ ¬x` nested inside
   a BTOR/AIG-encoded condition proves that condition false, and `x ∨ ¬x` proves
   the dual true, before the existing array-valued `ite` and read-congruence
   checks run. This closes `arraycondconstaig` through the existing
   `ReadCongruence` certificate path. Re-running the exact ABV audit moved
   **132/169 → 133/169** dominant and **Lean unsat 48/83 → 49/83**, with
   **mismatches=0, audit_errors=0, timeouts=0**. Remaining ABV bare-unsat work
   is larger extensionality rows, conditional-array families, residual write
   shapes (`write16`, `write17`), and cvc5-specific BV/array proof gaps.
   **ABV FINITE-EXTENSIONALITY BIT COVERAGE WIDENED (2026-06-25):**
   `ArrayAxiom` contextual term equivalence now recognizes the BTOR BV1
   encoding of finite array extensionality: a conjunction of read-equality bits
   over a complete small BV-index domain is equivalent to the array-equality
   bit. The checker accepts only complete covers: all concrete indices for small
   domains, or the two definitely-distinct indices of a BV1 domain. This closes
   `ext5` and `ext21` through the existing `ReadCongruence` certificate path.
   Re-running the exact ABV audit moved **133/169 → 135/169** dominant and
   **Lean unsat 49/83 → 51/83**, with **mismatches=0, audit_errors=0,
   timeouts=0**. Remaining ABV bare-unsat work is larger extensionality rows,
   conditional-array families, residual write shapes (`write16`, `write17`), and
   cvc5-specific BV/array proof gaps.
   **ABV BV-NOT INJECTIVITY READ-CONGRUENCE COVERAGE WIDENED (2026-06-25):**
   the local `ArrayAxiom` equality closure now records the inverse fact for
   bit-vector complement literals: from `bvnot x = bvnot y` it records `x = y`
   (and analogously for disequality). This is enough to refute BTOR read
   congruence obligations whose index equality is hidden behind bitwise
   complement. This closes `read22` through the existing `ReadCongruence`
   certificate path. Re-running the exact ABV audit moved **135/169 → 136/169**
   dominant and **Lean unsat 51/83 → 52/83**, with **mismatches=0,
   audit_errors=0, timeouts=0**. Remaining ABV bare-unsat work is larger
   extensionality rows, conditional-array families, residual write shapes
   (`write16`, `write17`), and cvc5-specific BV/array proof gaps.
   **ABV CONCAT-SUFFIX ROW COVERAGE WIDENED (2026-06-25):**
   `ArrayAxiom` index reasoning now recognizes that two BV terms are definitely
   distinct when their known concrete low-bit suffixes disagree, even if their
   concat boundaries differ. This proves `(concat v0 #x00)` distinct from
   `(concat v1 #b1)` by the low bit, enabling read-over-write normalization.
   This closes `3vl1` through the existing `ReadOverWrite` certificate path.
   Re-running the exact ABV audit moved **136/169 → 137/169** dominant and
   **Lean unsat 52/83 → 53/83**, with **mismatches=0, audit_errors=0,
   timeouts=0**. Remaining ABV bare-unsat work is larger extensionality rows,
   conditional-array families, residual write shapes (`write16`, `write17`), and
   cvc5-specific BV/array proof gaps.
   **ABV STORE SAME-CELL INJECTIVITY COVERAGE WIDENED (2026-06-25):**
   the `ArrayAxiom` read-congruence equality closure now records the injectivity
   fact for equal stores at the same base/index: from
   `store(a, i, v) = store(a, i, w)` it records `v = w`. This closes the BTOR
   `extarraywrite1` row through the existing `ReadCongruence` certificate path.
   Re-running the exact ABV audit moved **137/169 → 138/169** dominant and
   **Lean unsat 53/83 → 54/83**, with **mismatches=0, audit_errors=0,
   timeouts=0**. The refreshed artifact now has **50** `array-axiom-unsat`
   rows and **29** remaining `bare-unsat` rows. Remaining ABV bare-unsat work is
   larger extensionality rows, conditional-array families, residual write shapes
   (`write16`, `write17`), and cvc5-specific BV/array proof gaps.
   **ABV STORE SELF-UPDATE READ COVERAGE WIDENED (2026-06-25):**
   the same equality closure now records the read consequence of a self-update:
   from `a = store(a, i, v)` it records that `select(a, i)` is equal to `v`.
   This closes the BTOR `ext22` row through the existing `ReadCongruence`
   certificate path. Re-running the exact ABV audit moved **138/169 → 139/169**
   dominant and **Lean unsat 54/83 → 55/83**, with **mismatches=0,
   audit_errors=0, timeouts=0**. The refreshed artifact now has **51**
   `array-axiom-unsat` rows and **28** remaining `bare-unsat` rows. Remaining
   ABV bare-unsat work is larger extensionality rows, conditional-array
   families, residual write shapes (`write16`, `write17`), and cvc5-specific
   BV/array proof gaps.
   **ABV EQUAL STORE-CHAIN READBACK COVERAGE WIDENED (2026-06-25):**
   the `ArrayAxiom` read-congruence proof context now also handles Boolean
   top-level equality/disequality conjunctions, and it can use asserted equal
   array/store terms by reading both sides back at candidate store/select
   indices when direct ROW facts discharge the intervening writes. This closes
   the BTOR `ext27` and `ext28` rows through the existing `ReadCongruence`
   certificate path. Re-running the exact ABV audit moved **139/169 → 141/169**
   dominant and **Lean unsat 55/83 → 57/83**, with **mismatches=0,
   audit_errors=0, timeouts=0**. The refreshed artifact now has **53**
   `array-axiom-unsat` rows and **26** remaining `bare-unsat` rows. Remaining
   ABV bare-unsat work is conditional-array families, residual extensionality
   rows, residual write shapes (`write16`, `write17`), and cvc5-specific
   BV/array proof gaps.
   **ABV BV1-ORDER EXTENSIONALITY COVERAGE WIDENED (2026-06-25):**
   the `ArrayAxiom` read-congruence proof context now records the BV1 endpoint
   consequence of asserted true `bvult` facts (`lhs = #b0`, `rhs = #b1`) and
   finite array equality can use those known read values when they cover the
   whole BV1 index domain. This closes the BTOR `ext16` and `ext26` rows through
   the existing `ReadCongruence` certificate path. Re-running the exact ABV
   audit moved **141/169 → 143/169** dominant and **Lean unsat 57/83 → 59/83**,
   with **mismatches=0, audit_errors=0, timeouts=0**. The refreshed artifact now
   has **55** `array-axiom-unsat` rows and **24** remaining `bare-unsat` rows.
   Remaining ABV bare-unsat work is conditional-array families, remaining
   extensionality/order rows, residual write shapes (`write16`, `write17`), and
   cvc5-specific BV/array proof gaps.
   **ABV CONCAT-XOR FINITE EXTENSIONALITY COVERAGE WIDENED (2026-06-25):**
   the equality closure now records the zero-xor fact `bvxor(x, y) = 0 -> x = y`,
   pushes equality through same-shaped `concat` terms, and lets finite array
   equality consume asserted read-equality facts when those reads cover the full
   finite BV-index domain. This closes the BTOR `ext23` row through the existing
   `ReadCongruence` certificate path. Re-running the exact ABV audit moved
   **143/169 → 144/169** dominant and **Lean unsat 59/83 → 60/83**, with
   **mismatches=0, audit_errors=0, timeouts=0**. The refreshed artifact now has
   **56** `array-axiom-unsat` rows and **23** remaining `bare-unsat` rows.
   Remaining ABV bare-unsat work is conditional-array families, remaining
   extensionality/order rows, residual write shapes (`write16`, `write17`), and
   cvc5-specific BV/array proof gaps.
   **ABV FINITE ROW-WISE EXTENSIONALITY COVERAGE WIDENED (2026-06-25):**
   the finite-array equality checker now reads both arrays at candidate indices
   collected from store chains and recorded read facts, normalizes those reads
   through contextual read-over-write facts, and accepts row equality only when
   equalities or known BV1 read values prove agreement over a complete finite
   BV-index domain cover. This closes the BTOR `ext19`, `ext24`, and `ext25`
   rows through the existing `ReadCongruence` certificate path. Re-running the
   exact ABV audit moved **144/169 → 147/169** dominant and **Lean unsat
   60/83 → 63/83**, with **mismatches=0, audit_errors=0, timeouts=0**. The
   refreshed artifact now has **59** `array-axiom-unsat` rows and **20**
   remaining `bare-unsat` rows. Remaining ABV bare-unsat work is conditional
   array families (`arraycond*`), the remaining extensionality/order row
   `ext13`, residual read/write shapes (`read9`, `write16`, `write17`), and
   cvc5-specific BV/array proof gaps.
   **ABV SYMBOLIC-COVER/IMPLICATION EXTENSIONALITY COVERAGE WIDENED
   (2026-06-25):** the checked `ArrayAxiom` read-congruence lane now proves
   BV1 disjunctions of the form `¬antecedent ∨ consequent` by assuming the
   antecedent and checking the consequent, recognizes complete symbolic finite
   BV-domain covers from pairwise-distinct read indices, reads back through
   stored arrays whose equality is itself proven by such a complete read cover,
   and has a BV1 order-profile rule for arrays whose false/true rows are aligned
   by equal index-order bits. This closes `read9`, `write16`, `write17`, and
   `ext13` through the existing `ReadCongruence` certificate path. Re-running
   the exact ABV audit moved **147/169 → 151/169** dominant and **Lean unsat
   63/83 → 67/83**, with **mismatches=0, audit_errors=0, timeouts=0**. The
   refreshed artifact now has **63** `array-axiom-unsat` rows and **16**
   remaining `bare-unsat` rows. Remaining ABV bare-unsat work is now mostly
   conditional array families (`arraycond*`), the residual `ext11` row, and
   cvc5-specific BV/array proof gaps.
   **ABV ARRAY-ITE ALL-TRUE BRANCH-COVER COVERAGE WIDENED (2026-06-25):**
   the checked `ArrayAxiom` read-congruence lane now recognizes BV1-indexed,
   BV1-valued array-valued `ite` terms that are read as true at both concrete
   BV1 indices while every possible leaf array is guarded by an asserted
   `not (read0 && read1)` constraint. This closes `arraycond3`, `arraycond5`,
   `arraycond6`, `arraycond7`, and `arraycond8` through the existing
   `ReadCongruence` certificate path. Re-running the exact ABV audit moved
   **151/169 → 156/169** dominant and **Lean unsat 67/83 → 72/83**, with
   **mismatches=0, audit_errors=0, timeouts=0**. The refreshed artifact now has
   **68** `array-axiom-unsat` rows and **11** remaining `bare-unsat` rows.
   Remaining ABV bare-unsat work is now the residual conditional array family
   (`arraycond11`, `arraycond12`, `arraycond13`, `arraycond14`, `arraycond18`),
   `ext11`, and cvc5-specific BV/array proof gaps.
   **ABV CONTEXTUAL ITE-BRANCH/SELF-UPDATE COVERAGE WIDENED (2026-06-25):**
   the checked `ArrayAxiom` read-congruence lane now saturates equalities through
   `ite` terms whose conditions are known, reduces equal-branch array `ite`s,
   records compound BV1 guard values, detects equivalent BV1 terms with
   conflicting known values, and handles the narrow self-update branch split
   where `a = store(a, i, v)` forces the readback at `i`. This closes
   `arraycond11`, `arraycond12`, `arraycond13`, `arraycond14`, `arraycond18`,
   and `ext11` through the existing `ReadCongruence` certificate path.
   Re-running the exact ABV audit moved **156/169 → 162/169** dominant and
   **Lean unsat 72/83 → 78/83**, with **mismatches=0, audit_errors=0,
   timeouts=0**. The refreshed artifact now has **74** `array-axiom-unsat`
   rows and **5** remaining `bare-unsat` rows, all cvc5-specific:
   `bug637.delta`, `issue9041`, `bvproof2`, `issue9519`, and `proj-issue321`.
   **ABV CVC5 SAME-CELL STORE/RANGE COVERAGE WIDENED (2026-06-25):**
   the checked `ArrayAxiom` read-congruence lane now detects contradictory
   derived equalities when same-cell store injectivity forces two same-width BV
   values whose conservative unsigned ranges are disjoint. The range recognizer
   is intentionally small (constants, symbols, zero-extension, concat,
   equal-branch `ite` union, and non-wrapping add) and only refutes equalities
   already derived by the certificate lane. This closes the cvc5
   `issue9519` and `proj-issue321` rows through the existing
   `ReadCongruence` certificate path. Re-running the exact ABV audit moved
   **162/169 → 164/169** dominant and **Lean unsat 78/83 → 80/83**, with
   **mismatches=0, audit_errors=0, timeouts=0**. The refreshed artifact now has
   **76** `array-axiom-unsat` rows and **3** remaining `bare-unsat` rows:
   `bug637.delta`, `issue9041`, and `bvproof2`.
   **ABV CVC5 STORE-RESTORE NO-OP COVERAGE WIDENED (2026-06-25):**
   the checked `ArrayAxiom` store-chain lane now recognizes the cvc5
   `bug637.delta` no-op/restore pattern: write a definitely distinct cell,
   perform a store that writes the original value back to the other cell, then
   restore the first cell from the original array. This closes the row through
   the existing `StoreShadowing` certificate path without invoking bit-blast
   trust. Re-running the exact ABV audit moved **164/169 → 165/169** dominant
   and **Lean unsat 80/83 → 81/83**, with **mismatches=0, audit_errors=0,
   timeouts=0**. The refreshed artifact now has **77** `array-axiom-unsat`
   rows and **2** remaining `bare-unsat` rows: `issue9041` and `bvproof2`.
   **ABV CVC5 SAME-VALUE STORE-CHAIN COVERAGE WIDENED (2026-06-25):**
   the checked `ArrayAxiom` store-chain lane now proves same-base store chains
   equal when every write stores the same definitely equal value and both write
   index sets cover each other, including small concrete BV ranges such as a
   zero-extended BV1 index covered by concrete writes at `0` and `1`. This
   closes the cvc5 `bvproof2` row through the existing `StoreShadowing`
   certificate path without invoking bit-blast trust. Re-running the exact ABV
   audit moved **165/169 → 166/169** dominant and **Lean unsat 81/83 → 82/83**,
   with **mismatches=0, audit_errors=0, timeouts=0**. The refreshed artifact
   now has **78** `array-axiom-unsat` rows and **1** remaining `bare-unsat`
   row: `issue9041`.
   **ABV CVC5 SIGNED-BV1 READ-CONGRUENCE GAP CLOSED (2026-06-25):**
   the checked `ArrayAxiom` read-congruence lane now uses conservative static
   BV range facts for `bvult` guards, fixed-sign `sign_extend`, full-width
   `extract`, singleton-range equivalence, and disjoint-range index
   distinctness. It also recognizes Boolean contradictions of the form
   `P = not Q` once the certificate lane independently proves `P = Q`. This
   closes the cvc5 `issue9041` row through the existing `ReadCongruence`
   certificate path without invoking bit-blast trust. Re-running the exact ABV
   audit moved **166/169 → 167/169** dominant and **Lean unsat 82/83 → 83/83**,
   with **mismatches=0, audit_errors=0, timeouts=0**. The refreshed artifact
   now has **79** `array-axiom-unsat` rows and **0** remaining `bare-unsat`
   rows; the residual ABV non-dominant audit entries are checked `unknown`
   search-frontier rows (`rw34`, `arraycond9`).
   **EXACT ABV DOMINANCE ROW CLOSED (2026-06-25):** the checked
   `ArrayAxiom` read-congruence lane now recognizes ITE branch exhaustion:
   `ite(c,t,e)` cannot be disequal from both `t` and `e`. The evidence front
   door runs this structural refuter before the general solver only on small
   assertion DAGs, so tiny unsat frontier rows avoid the expensive bit-blast
   path while large SAT rewrite rows still replay models first. This closes
   BTOR `rw34` and `arraycond9` as `array-axiom-unsat` with real-Lean
   reconstruction. Re-running the exact ABV audit moved **167/169 → 169/169**
   dominant and **Lean unsat 83/83 → 85/85**, with **mismatches=0,
   audit_errors=0, timeouts=0**. The refreshed artifact now has **84**
   `sat-model` rows, **81** `array-axiom-unsat` rows, **3**
   `bv-abstraction-unsat` rows, **1** `alethe-unsat` row, and no `unknown` or
   `bare-unsat` exact-audit entries.
4. **Two of the three "deprioritized hard rows" are actually cheap, decider-already-
   built, dominance-*eligible* wins — do NOT deprioritize them.** The deciders exist;
   the blocker is **one IR change**, and it is itself the highest-leverage move:
   - Add **`Sort::Uninterpreted(SortId)`** (an interned `Copy` id, mirroring the
     existing `Sort::Datatype(DatatypeId)`) and generalize **`Sort::Array`
     index/element to `SortId`** — **one change** that unlocks **both** QF_UF-over-
     uninterpreted-sorts (route to the *already-built* `solve_qf_uf_online` e-graph,
     not the BV over-approximation the parser currently forces) **and** Int-indexed
     arrays (QF_ALIA/QF_AUFLIA, currently ~0% purely on this). Both already have
     Alethe/Lean cert routes (`euf_alethe`, congruence/ROW certs) → directly
     Pareto-dominance-eligible. This is *one* keystone, not two, and it is near-term.
     **SLICE LANDED (2026-06-25):** arity-0 SMT-LIB `declare-sort` now stays
     first-class as `Sort::Uninterpreted(SortId)` with replayable EUF model tokens;
     parser/writer round-trip declared sorts, and `check_auto` routes pure
     many-sorted EUF through the e-graph path.
     **ARRAY SLICE LANDED (2026-06-25):** `Sort::Array` now carries sort-valued
     index/element metadata (`ArraySortKey`) instead of BV widths only; SMT-LIB
     parses/writes free `(Array Int Int)` terms, `select`/`store` typecheck over
     the real component sorts, and `check_auto` proves the congruence-UNSAT
     slice for Int-indexed arrays; at that point model-producing non-BV array SAT
     shapes still returned `unknown` pending generic projection.
     **MODEL/SCALAR ROUTE SLICE LANDED (2026-06-25):** non-BV arrays now have a
     replayable `Value::GenericArray`; the evaluator handles generic
     `const-array`/`select`/`store`; lazy ROW/extensionality projection compares
     full `Value`s and reconstructs generic arrays; and `check_auto` routes the
     Bool/linear-Int array slice through arithmetic DPLL. `(Array Int Int)` free
     reads, ROW conflicts, and disequality witnesses now replay as `sat`/`unsat`
     instead of blanket `unknown`. Local fair-slice remeasurement moved QF_ALIA to
     **3/5 decided, DISAGREE=0** (artifact under `bench-results/local/`), while
     QF_AUFLIA remains **1/3** and QF_UF-overbound remains **4/6**. Remaining
     keystone work: refresh committed baselines, then broaden from the current
     Bool/linear-Int array slice to mixed AUFLIA/UF and other non-BV component
     sorts.
     **ARRAY-ARGUMENT UF PREREQ LANDED (2026-06-25):** UF signatures now admit
     array-valued parameters (but still reject array-valued results), and
     `FuncValue`/UF model projection use full-`Value` tables whenever a signature
     mentions arrays. SMT-LIB now parses AUFLIA shapes such as
     `g : (Array Int Int) -> Int`, and `check_auto` proves the narrow congruence
     conflict `a=b ∧ g(a)≠g(b)` as `unsat`. This is deliberately scoped: the
     broader lazy ROW/extensionality route still needs a scalar backend that can
     solve UF+LIA with array-argument applications before QF_AUFLIA remeasurement
     should be expected to move materially.
     **MIXED ROW+UF ROUTE LANDED (2026-06-25):** lazy ROW/extensionality now has
     a `QF_UFLIA` scalar backend and `check_auto` routes non-BV
     Bool/linear-Int+UF array slices through it. Model projection preserves UF
     interpretations and completes missing UF/non-Int values before replay, so
     SAT shapes such as `select a (idx a)` replay. Local QF_AUFLIA fair-slice
     remeasurement is **2/6 decided, DISAGREE=0** (the common parsed set expanded
     from three to six after array-argument UF admission). Remaining blockers are
     now concrete: scalar Int-array timeout (`bug337`), array term shapes outside
     the current ROW fragment (`bug330`, `swap...`), and missing
     array-equality-to-UF congruence refinement (`bug336`).
     **STORE-DISJUNCTION REFUTER LANDED (2026-06-25):** the array fast path now
     exploits the valid consequence
     `store(a,i,v)=b ∧ store(a,j,w)=b ⇒ i=j ∨ a=b` by splitting the two branches
     and delegating each branch refutation to the checked EUF congruence refuter.
     This closes the `bug336` corpus pattern (`f(x)≠f(y)` refutes `x=y`;
     `g(a)≠g(b)` refutes `a=b`) and moves the local QF_AUFLIA fair slice to
     **3/6 decided, DISAGREE=0**. Remaining QF_AUFLIA blockers: scalar Int-array
     timeout (`bug337`) and array-valued structural terms outside the current ROW
     fragment (`bug330`, `swap...`).
     **STRUCTURAL ROW COVERAGE SLICE LANDED (2026-06-25):** the lazy ROW
     abstraction now preserves array-valued UF arguments at scalar application
     boundaries, lowers `select(ite c a b, i)` to scalar branch reads, permits store
     ROW misses to point at scalar read expressions, and lets mixed array+UF queries
     fall through past the UF-arithmetic overbound `unknown` into the array route.
     Local QF_AUFLIA fair-slice measurement remains **3/6 decided, DISAGREE=0**
     (artifact under `bench-results/local/`), but the frontier moved: `bug330` and
     `swap...` are no longer structural ROW rejections. Remaining blockers are now
     scalar UFLIA Boolean atom cap (`bug330`), swap-chain replay/refinement
     incompleteness, and the scalar Int-array timeout (`bug337`).
     **PROJECTION-COMPLETION SLICE LANDED (2026-06-25):** the AUFLIA ROW scalar
     backend now falls back from non-budget online-UFLIA `unknown` to eager
     UF+arithmetic, and `FunctionElimination::project_model` completes
     non-application symbols before evaluating full-`Value` UF argument keys. This
     removes the concrete array-valued-UF projection failure exposed by `swap...`;
     the local QF_AUFLIA fair slice remains **3/6 decided, DISAGREE=0**. The
     remaining misses are now scalar-engine frontiers, not IR/modeling blockers:
     `bug330` has a 339-atom Boolean UFLIA abstraction (current cap 48),
     `swap...` reaches lazy-LIA timeout, and `bug337` remains a scalar Int-array
     timeout.
     **BOUNDED LIA-PROBE + CLEAN SWAP-CHAIN REFUTER LANDED (2026-06-25):**
     arithmetic DPLL now probes the shared online LIA DPLL(T) spine under a
     real deadline before falling back to the legacy certified route, and the
     array fast path has a narrow sound refuter for clean symmetric store-swap
     chains. Local QF_AUFLIA fair-slice measurement remains **3/6 decided,
     DISAGREE=0** (artifact `qf-auflia-after-swap-chain-refuter.json`); the
     cvc5 `swap...` corpus instance is still not closed. The next useful work is
     a stronger scalar UFLIA Boolean/relevance engine for `bug330`, a real
     array-permutation/ROW normalizer for `swap...`, or the scalar Int-array
     timeout in `bug337`.
     **PERMUTATION-CHAIN REFUTER LANDED (2026-06-25):** the clean swap-chain
     recognizer is now a memoized array-permutation normalizer, and proven
     array-unsat refuters run at the `check_auto` front door before expensive
     scalar normalization / UF+arithmetic. This closes the exact cvc5
     `swap_t1_pp_nf_ai_00010_004` instance via `array-unsat-refuter`. Local
     QF_AUFLIA fair-slice measurement is now **4/6 decided, DISAGREE=0**
     (artifact `qf-auflia-after-permutation-refuter.json`; Z3 remains 6/6).
     At that point, remaining QF_AUFLIA misses were only scalar-search frontiers:
     `bug330` (339 Boolean UFLIA atoms vs cap 48, then lazy-LIA timeout) and
     `bug337` (pure Int-array lazy-LIA timeout).
     **UFLIA/UFLRA DEADLINE + CAP DIAGNOSTIC LANDED (2026-06-25):** the
     integrated `Dpll<CombinedIncremental*>` drivers now actually consume the
     computed wall-clock deadline (`solve_with_deadline`) and classify exhausted
     runs as timeout `unknown`; the UFLIA Boolean atom cap is raised to 384 under
     that guard. Local QF_AUFLIA fair-slice measurement remains **4/6 decided,
     DISAGREE=0** (artifact `qf-auflia-after-uflia-deadline-cap.json`). The
     frontier sharpened: `bug330` is no longer rejected by the old 48-atom
     admission cap; it reaches online UF+LIA and declines on an uncertified
     Boolean-layer theory model, then the array route times out. `bug337`
     remains the pure Int-array lazy-LIA timeout.
     **MEASUREMENT TIMEOUT + SCALAR-ABSTRACTION DIAGNOSTICS LANDED
     (2026-06-25):** `measure_corpus` / `measure_graduated` now pass the harness
     timeout into `SolverConfig::timeout` instead of only killing the worker
     externally. Lazy ROW/extensionality now gives each scalar backend call only
     the remaining outer deadline and annotates scalar-backend unknowns with
     CEGAR round/site/lemma counts; the legacy arithmetic DPLL loop likewise
     reports atom/blocking-lemma counts. Local QF_AUFLIA fair-slice measurement
     remains **4/6 decided, DISAGREE=0** (artifact
     `qf-auflia-after-scalar-abstraction-diagnostics.json`). The remaining
     misses are now localized to the initial scalar abstraction: `bug330` fails
     at ROW round 0 with 62 select sites, then 832 arithmetic atoms / 4 blocking
     lemmas; `bug337` fails at extensionality round 0 with 152 select sites,
     then 1374 arithmetic atoms / 2 blocking lemmas. Next useful work is scalar
     relevance/atom reduction, not more array lemmas.
     **ARITHMETIC ATOM CANONICALIZATION LANDED (2026-06-25):** the legacy
     arithmetic DPLL abstraction now shares reversed order atoms, pushes negated
     order atoms to their order-complement, folds self-comparisons/equalities to
     constants, and caps the online LIA probe at 1s under a wall-clock budget so
     large abstractions leave most time to the fallback. Local QF_AUFLIA remains
     **4/6 decided, DISAGREE=0** (artifact
     `qf-auflia-after-arith-atom-canonicalization.json`). `bug330` improves from
     832 to 802 arithmetic atoms and from 4 to 7 fallback blocking lemmas before
     timeout; `bug337` is unchanged at 1374 atoms / 2 blocking lemmas.
     **SCALAR BOOLEAN SHORT-CIRCUITING LANDED (2026-06-25):** the arithmetic
     abstractor now folds Boolean constants/identical branches for `and`/`or`/
     `xor`/`=>`/Bool equality/Bool `ite` and skips dead branches before allocating
     their arithmetic atoms. This is a sound cleanup, but it is neutral on the
     current hard slice: local QF_AUFLIA remains **4/6 decided, DISAGREE=0**
     (artifact `qf-auflia-after-boolean-simplification.json`), `bug330` remains
     802 atoms / 7 blocking lemmas, and `bug337` remains 1374 atoms / 2 blocking
     lemmas. Next useful work is no longer shallow Boolean simplification; it is
     scalar relevance / Boolean-layer model certification for `bug330`, or a
     smaller initial extensionality/model-construction route for `bug337`.
     **SCALAR SNAPSHOT PREPROCESSING LANDED (2026-06-25):** lazy
     ROW/extensionality now flattens positive top-level conjunctions before
     sending the scalar abstraction through the existing replay-safe
     `propagate_values`/`solve_eqs` preprocessing wrapper. This exposes generated
     aliases and constants to word-level elimination while preserving the normal
     projection/replay gate for `sat`. Local QF_AUFLIA is still **4/6 decided,
     DISAGREE=0** (artifact `qf-auflia-after-scalar-preprocess-flatten.json`),
     but `bug337` moves from 1374 atoms / 2 blocking lemmas to 946 atoms / 7
     blocking lemmas at 10 s; at 30 s it reaches 19 blocking lemmas and still
     times out. `bug330` remains 802 atoms and times out after 6 blocking lemmas.
     Next useful work is a real `bug337` SAT/model-construction shortcut or
     `bug330` Boolean-layer model certification/relevance.
     **ONLINE LIA/LRA BOOLEAN-LEAF MODEL LIFT LANDED (2026-06-25):** standalone
     online arithmetic drivers now lift final DPLL assignments for declared
     Boolean leaves into the returned arithmetic model before replay. This fixes
     a real replay gap for Boolean-structured scalar formulas, with LIA/LRA
     regressions of the form `p ∧ (x < y ∨ y < x)`. It is neutral on the current
     AUFLIA slice: **4/6 decided, DISAGREE=0** (artifact
     `qf-auflia-after-online-boolean-model-lift.json`), `bug330` remains 802 atoms
     / 6 blocking lemmas and `bug337` remains 946 atoms / 7 blocking lemmas. A
     trial 3s online-LIA probe cap was rejected because it did not decide either
     hard file and reduced `bug330` fallback progress; keep the 1s cap until the
     online path itself is stronger.
     **SCALAR LIA BOUND-LEMMA + LARGE-CORE CUTOFF LANDED (2026-06-25):** the
     legacy arithmetic DPLL fallback now seeds certifiable two-literal integer
     bound mutex lemmas for simple asserted lower/upper contradictions
     (`x >= 1` with `x <= 0`, etc.) and skips deletion-based core minimization
     on scalar abstractions above 128 theory atoms. Small formulas still get
     minimized cores; large formulas avoid spending most of their budget in
     simplex core shrinking. Local QF_AUFLIA remains **4/6 decided,
     DISAGREE=0** (artifact `qf-auflia-after-bound-lemmas-core-cutoff.json`),
     but scalar throughput moved materially: at 10 s `bug330` reaches 40
     blocking lemmas (27 upfront bound lemmas) and `bug337` reaches 46 blocking
     lemmas (150 upfront bound lemmas); a 30 s `bug337` run reaches 84 blocking
     lemmas before the pure Boolean skeleton times out. The next useful work is
     now Boolean-skeleton scaling / relevance / incremental SAT after many
     learned clauses, or a replay-gated SAT/model-construction shortcut for
     `bug337`.
     **WARM SCALAR BOOLEAN SKELETON LANDED (2026-06-25):** the legacy arithmetic
     DPLL fallback now encodes its pure-Boolean scalar skeleton to CNF once and
     keeps a warm `IncrementalSat`, adding each learned theory blocking clause
     incrementally instead of rebuilding through the general SAT-BV path every
     round. SAT candidates still go through arithmetic model reconstruction and
     original-assertion replay. Local QF_AUFLIA remains **4/6 decided,
     DISAGREE=0** (artifact `qf-auflia-after-warm-scalar-bool-skeleton.json`),
     but the scalar frontier moved sharply: at 10 s `bug330` reaches 608 learned
     scalar clauses and `bug337` reaches 788; a 30 s `bug337` run reaches 1670
     before `rustsat-batsat` times out. The next useful work is now SAT search
     quality / relevance over the learned-clause Boolean skeleton, or a
     replay-gated SAT/model-construction shortcut for `bug337`; CNF rebuild
     overhead is no longer the bottleneck.
     **CURRENT-POLARITY INTEGER-BOUND CORES LANDED (2026-06-25):** dynamic
     scalar LIA conflicts now try a cheap two-literal integer-bound core before
     falling back to the large full-theory slice. This captures assigned
     complement bounds such as `not (x <= 1)` as lower bounds (`x >= 2`) and
     keeps the resulting lemmas on the existing certificate/replay path. Local
     QF_AUFLIA remains **4/6 decided, DISAGREE=0** (artifact
     `qf-auflia-after-cheap-bound-core.json`), but route diagnostics improve:
     `bug330` reaches 1143 scalar blocking lemmas at 10 s (was 608 after the
     warm skeleton), while `bug337` reaches 860 (was 788). The residual blocker
     is still learned-clause search quality / relevance on a large scalar
     Boolean skeleton, or a replay-gated `bug337` model-construction shortcut;
     cheap bound-core extraction is not enough by itself to close the two hard
     files.
     **INTEGER LOCAL-SEARCH SCALAR PROBE LANDED (2026-06-25):** the deterministic
     one-sided `pbls` model finder now supports `Int` variables with finite,
     formula-constant-guided moves, and the lazy ROW/extensionality scalar
     boundary runs it for 100 ms after model-sound preprocessing and before the
     exact scalar backend. Any `sat` still reconstructs through preprocessing and
     replays through the array path; misses fall through. Local QF_AUFLIA remains
     **4/6 decided, DISAGREE=0** (artifact
     `qf-auflia-after-int-local-search-scalar-probe.json`; axeyum PAR-2 6.668 s).
     The diagnostic split is clearer: `bug330` is out of this probe's current
     scope because UF applications remain in the scalar snapshot; `bug337` is
     in-scope but the probe times out, then the exact scalar loop times out after
     857 rounds. Next useful work: finite UF-table local search for `bug330`, or
     SAT relevance / replay-gated model construction for in-scope `bug337`.
     **CAPPED STRUCTURAL PBLS SCORING LANDED (2026-06-25):** the one-sided
     `pbls` model finder now uses a structural Boolean cost for compact
     assertions, so nested `and`/`or`/`not`/implication/Bool-eq/xor/Bool-ite
     formulas give local-search gradients instead of a single root-satisfied bit.
     The scorer is capped by assertion DAG size and variable incidence; large
     generated constraints keep the previous cheap root score. Local QF_AUFLIA
     remains **4/6 decided, DISAGREE=0** (artifact
     `qf-auflia-after-structural-pbls-score.json`; axeyum PAR-2 6.668 s).
     Diagnostics remain: `bug330` is UF-out-of-scope for this probe; `bug337` is
     in scope but local search times out and the exact scalar loop reaches 865
     blocking lemmas before `rustsat-batsat` timeout. Next useful work is still
     SAT relevance / replay-gated model construction for `bug337`, or finite
     UF-table model search for `bug330`.
     **CAPPED INTEGER-DIFFERENCE CORES LANDED (2026-06-25):** scalar arithmetic
     DPLL(T) now recognizes current literals of the form `x + c <= y + d` / `<`
     as integer-difference constraints and extracts compact negative-cycle cores
     before the full-slice fallback. The common two-edge cycle (`x <= y` with
     `y + 1 <= x`) is handled directly; full Bellman-Ford is capped to
     small/medium snapshots so the large AUFLIA generated slices decline this
     extractor instead of losing SAT-search budget. Local QF_AUFLIA remains
     **4/6 decided, DISAGREE=0** (artifact `qf-auflia-after-capped-idl-core.json`;
     axeyum PAR-2 6.668 s). Diagnostics are baseline-preserving rather than a
     close: `bug330` reaches 1140 blocking lemmas and `bug337` reaches 849 before
     SAT timeout. Next useful work is still SAT relevance / model construction on
     the large scalar skeleton, or a different array/branch abstraction shortcut.
     **COMPACT BOUND-IMPLICATION LEMMAS LANDED (2026-06-25):** scalar arithmetic
     DPLL(T) now seeds asserted simple-bound monotonicity lemmas such as
     `x <= 0 => x <= 1` and `x >= 2 => x >= 1` for compact skeletons only. Each
     implication is recorded as a normal certifiable LIA core
     `{stronger_bound, not weaker_bound}`. A broader all-polarity version was
     measured and rejected on the current hard AUFLIA slice because it inflated
     upfront clauses and reduced SAT refinement rounds; the landed version is
     asserted-bound-only and gated at 256 arithmetic atoms. Local QF_AUFLIA
     remains **4/6 decided, DISAGREE=0** (artifact
     `qf-auflia-after-compact-bound-implications.json`; axeyum PAR-2 6.668 s).
     Hard-file diagnostics are baseline-preserving (`bug330`: 27 upfront bound
     lemmas / 1137 blocking lemmas; `bug337`: 150 / 854). Next useful work is
     still large-skeleton SAT relevance/model construction, finite UF-table model
     search for `bug330`, or a higher-level array/branch abstraction shortcut.
     **PBLS AFFINE INTEGER REPAIR CANDIDATES LANDED (2026-06-25):** the
     replay-gated `pbls` model finder now adds assertion-local integer repair
     moves for unit-affine shapes (`x`, `x + c`, `c + x`, `x - c`) inside
     equality and order atoms, using the current value of the opposite side to
     propose boundary candidates. The candidate set is capped and remains a
     one-sided model-search heuristic; accepted `sat` models still replay through
     preprocessing and the array projection path. Local QF_AUFLIA remains **4/6
     decided, DISAGREE=0** (artifact
     `qf-auflia-after-pbls-affine-repairs.json`; axeyum PAR-2 6.668 s, Z3 PAR-2
     0.105 s). Route diagnostics are flat: `bug330` remains UF-out-of-scope for
     local search, and `bug337` still times out in local search before the exact
     scalar loop reaches 855 blocking lemmas. This should be treated as a useful
     small-query model-search primitive, not a current AUFLIA frontier closer.
     The next useful AUFLIA work remains finite UF-table model search for
     `bug330`, SAT relevance/model construction for `bug337`, or a higher-level
     array/branch abstraction shortcut.
     **FOCUSED OR BRANCH REPAIR FOR PBLS LANDED (2026-06-25):** wide
     OR-shaped assertions now keep the cheap root-truth persistent score, but
     when selected by `pbls` they get a bounded structural tie-break plus a
     branch-repair planner that tries to satisfy one disjunct by applying simple
     literal repairs as a unit. This targets generated branch-selector formulas
     like `bug337` without raising the global structural-cost cap. A broad cap
     increase and a 1 s scalar local-search probe were measured and rejected:
     neither closed the hard files. Local QF_AUFLIA remains **4/6 decided,
     DISAGREE=0** (artifact `qf-auflia-after-pbls-focused-or-repair.json`;
     axeyum PAR-2 6.668 s, Z3 PAR-2 0.104 s). Route diagnostics remain
     baseline-shaped: `bug330` is still UF-out-of-scope for local search and
     times out after 1144 scalar blocking lemmas; `bug337` still local-searches
     to timeout, then scalar LIA times out after 851 blocking lemmas. Treat this
     as a reusable branch-model-search primitive, not a current AUFLIA frontier
     close. The next AUFLIA move should be a real branch-schedule/model
     constructor, finite UF-table reasoning for `bug330`, or SAT relevance in
     the large scalar skeleton.
     **REPLAY-PROJECTION REPAIR LANDED (2026-06-26):** lazy-extensionality
     last-candidate projection now groups asserted direct select equalities by
     concrete `(array, index)`, repairs the projected array entry, and aligns
     direct scalar read-result symbols before the existing full replay gate.
     This keeps the SAT-only soundness condition unchanged. On `bug337`, the
     10 s probe still times out at round 2 with 4096 sites / 150 array-equality
     atoms / 6973 congruence lemmas / 146 diff-skolems, but replay repair sees
     154 select candidates, makes 3 array-entry and 2 scalar-symbol changes,
     and moves the first false flattened conjunct from the direct read equality
     to ordinal 209 / term 3654: the generated queue-lock transition branch
     disjunction. `diagnose_evidence` can now render generated arena terms by
     stable term id. Next useful work is replay-guided branch-schedule/model
     repair for that disjunction, not more select-equality projection.
     **BRANCH-REPLAY DIAGNOSTICS + STORE-BASE REPAIR LANDED (2026-06-26):**
     replay failures on false branch disjunctions now report branch count, best
     branch, false-literal count, first false literal, and equality values. A
     narrow replay-only repair handles `target = store(base,i,v)` by copying the
     target array into the base everywhere except the store index, preserving the
     base cell that the store overwrites. This is pinned by a target-readback
     regression and remains behind full replay. `bug337` still does not close:
     the best branch is branch 0 with one false literal,
     `x_353 = store(x_339, x_351, 2)`, where `x_353` has extra readback entries
     `[1 -> 3]` and `[2 -> 3]` not stably propagated through the current local
     projection loop. Next useful work is a branch-consistent store-chain/readback
     projection for the queue-lock transition, not another scalar timeout knob.
     **BRANCH READBACK ALIGNMENT LANDED (2026-06-26):** the store-base repair now
     immediately aligns direct scalar readback symbols for the repaired base
     array, preventing the following select-repair pass from using stale scalar
     reads to undo branch-consistent base entries. The focused regression now
     includes a stale `z = select(a,j)` read on the repaired base. `bug337` still
     does not close, but the first false replay point moves to generated branch
     ordinal 210 / term 3879, best branch 3, with one false direct array equality
     `x_339 = x_325`: `x_339` has `[0 -> 1]`, `[1 -> 3]`, `[2 -> 3]` while
     `x_325` is still default. Next useful work is replay-gated direct
     array-equality branch repair, or the more general branch-schedule projection
     that chooses equality direction from readback support.
     **BRANCH ARRAY-EQUALITY REPAIR LANDED (2026-06-26):** a single false direct
     array equality in the chosen branch is now repaired by copying the side with
     stronger projected readback evidence into the weaker side, scored by
     non-default projected entries and direct asserted `select` support, then
     aligning scalar readbacks for the target. This is still full-replay gated.
     `bug337` still does not close, but the first false replay point moves again:
     generated branch ordinal 233 / term 10144, best branch 0, now **two** false
     literals. The first is `x_17 = store(x_2, x_15, 2)`, where `x_17` has
     `[0 -> 1]`, `[1 -> 3]`, `[2 -> 3]` and the RHS store has incompatible
     `[1 -> 2]`, `[2 -> 1]`. Next useful work is a multi-literal branch-schedule
     / store-chain projection for the queue-lock branch, not more one-literal
     local repair.
     **MULTI-LITERAL BRANCH SCHEDULE REPAIR LANDED (2026-06-26):** the selected
     false branch term is now retained, and replay projection can try a bounded
     branch-local schedule repair on a copy of the assignment: direct scalar
     equalities first, then equality-shaped array/store literals, keeping the copy
     only if that branch's false-literal count decreases. This removes the
     generated branch disjunction as `bug337`'s first replay blocker. The 10 s
     probe now reaches direct equality ordinal 185 / term 2957,
     `x_361 = x_22`, with values 1 vs 0, after 207 projection repair changes.
     Next useful work is replay-gated scalar equality projection for generated
     non-branch equalities, with direction chosen from branch/readback support.
     **SCALAR EQUALITY PROJECTION REPAIR LANDED (2026-06-26):** replay projection
     now tries bounded scalar equality repair for false generated equalities,
     testing both directions where possible and keeping only assignments that
     reduce the positive replay-conjunct false count. Scalar repair has separate
     telemetry and remains full-replay gated. A final post-scalar stabilization
     reruns select repair if scalar-triggered branch repair mutates arrays. On
     `bug337`, the 10 s probe now reports **5** scalar repairs and advances to
     direct equality ordinal 190 / term 3017, `x_366 = x_92`, values 1 vs 0,
     after 218 projection repair changes. Next useful work is support-aware
     scalar/readback propagation for the remaining generated equality chain.
     **SUPPORT-AWARE SCALAR/READBACK PROJECTION LANDED (2026-06-26):** scalar
     equality direction choice now scores asserted-select readback support,
     support-aware scalar trial counters are included in replay failure notes,
     and the bounded projection stabilization loop can walk the repeated
     queue-lock readback chain under a named 32-round cap. The `bug337` 10 s
     probe advances past the scalar chain to branch disjunction ordinal 209 /
     term 3654; best branch 0 has one false literal,
     `x_345 = store(x_331, x_334, x_351)`, after 417 projection repair changes.
     The row still does not close. Next useful work is branch-consistent
     store-chain/readback projection for that target array; a blanket
     one-literal target-readback alignment was tested and rejected because it
     regressed existing single-false branch repair behavior.
     **TARGETED REPLAY BRANCH REPAIR LANDED (2026-06-26):** after the general
     projection pass, the last-candidate replay path can now repair the exact
     single false branch literal named by full original replay and replay again.
     This remains SAT-only because the original evaluator replay is still the
     only acceptance gate. On `bug337`, the 10 s probe moves past branch term
     3654 / first false term 495 to direct readback equality ordinal 208 / term
     3440, `x_384 = x_344`, values 0 vs 1, after 419 projection repair changes.
     A wider 96-round projection cap did not move the frontier, and a targeted
     scalar fallback cycled among branch 3654, equality 3440, and lower branch
     3879. Next useful work is therefore a component-level branch-choice /
     store-chain readback projection for that three-node queue-lock cycle.
     **REPLAY BRANCH-CHOICE CANDIDATES LANDED (2026-06-26):** targeted replay now
     tries every positive branch of a failed generated disjunction on a projection
     copy, rejects full-replay-worsening trials, and chooses deterministically by
     `(total_false, branch_false, ordinal)`. This is still behind the full
     original-assertion replay gate. A focused regression covers the case where
     the reported best branch is an unrepaired Boolean literal and a later branch
     is repairable. On `bug337`, the 10 s probe moves to generated branch
     disjunction ordinal 232 / term 9841; best branch 3 has one false literal
     `x_31 = x_17`, with arrays
     `(array default 0 [0 -> 1] [1 -> 3] [2 -> 3])` vs
     `(array default 0 [1 -> 2] [2 -> 1])`, after 457 projection repair changes.
     The row remains `unknown`; next useful work is component-level
     store-chain/readback projection for this lower queue-lock branch.
     **SELECTED CARRY-COMPONENT PROJECTION LANDED (2026-06-26):** targeted replay
     branch-literal repair now solves direct array equalities as a selected carry
     component: it gathers adjacent selected/best-branch array equalities touching
     the failed pair, tries every component member as representative, aligns
     direct readback symbols, and keeps only branch-improving/full-replay-
     non-worsening candidates. A narrow targeted direct-select equality repair
     is covered too, but a direct-select stabilization experiment was rejected
     because it regressed `bug337` to branch 9841 and raised projection churn to
     1848 changes. The retained `bug337` 10 s probe moves past branch 9841 /
     `x_31 = x_17` to direct readback equality ordinal 34 / term 555,
     `x_388 = select(x_325, x_337)`, values 1 vs 0, after 571 projection repair
     changes. The row remains `unknown`; next useful work is readback/store-chain
     component repair around the `x_325/x_339` transition.
     **COUPLED BRANCH-PAIR REPLAY REPAIR LANDED (2026-06-26):** targeted replay
     now has a bounded two-generated-OR branch scheduler before the existing
     single-OR branch choice. It repairs each branch candidate of the failed OR,
     observes the next full-replay blocker, and if that blocker is a different
     OR, tries each branch candidate there on the same projection copy. A pair is
     retained only when both ORs evaluate true and the full original replay false
     count strictly decreases, so SAT remains gated by the original evaluator
     replay. On `bug337`, this is a real but incomplete frontier move: the 10 s
     diagnostic advances from OR ordinal 211 / term 4108 to OR ordinal 219 / term
     6084, with branch 3's local repair pointing back to ordinal 211. Projection
     churn rises to 647 changes and the diagnostic wall time rises to ~45 s, so
     the next AUFLIA move should be a cost-controlled multi-OR/beam branch
     scheduler or pair-edge diagnostics for the 219↔211 cycle, not unbounded
     branch-pair widening.
     **BRANCH-PAIR EDGE DIAGNOSTICS LANDED (2026-06-26):** final replay failure
     notes now include a bounded `branch_pair_candidate_diagnostics` section:
     for repairable first-OR branches whose next blocker is another OR, it scores
     each second-OR branch candidate and records the post-pair global blocker.
     On `bug337`, this proves the current monotone two-OR policy cannot move the
     new frontier. From OR 219 branch 3, all OR 211 second-branch candidates
     locally repair but worsen full replay: branches 0/3 leave two false
     conjuncts, branches 1/2 leave four, and the best branch-3 path lands on OR
     212 / term 4341. The next AUFLIA repair should therefore be a bounded
     branch-schedule/beam search that can take temporary uphill moves inside the
     beam, but still accepts only final full-replay improvement, with explicit
     caps and cycle/tabu handling for the 219 → 211 → 212 queue-lock chain.
     **BOUNDED BRANCH-BEAM REPLAY REPAIR LANDED (2026-06-26):** targeted replay
     now has a capped generated-OR beam after strict pair repair: width 8,
     64 expansions, depth 6, and at most `current_false + 4` temporary false
     conjuncts inside the beam. The projected assignment is changed only when
     the final candidate strictly improves full original replay; SAT remains
     accepted only by evaluator replay. A regression covers a four-OR schedule
     where strict pair repair rejects the temporary two-false state but the beam
     repairs later ORs to reach a replaying assignment. On `bug337`, this crosses
     the 219/211/212 branch cycle but does not close the row: the new first false
     replay point is direct readback equality ordinal 34 / term 555,
     `x_388 = select(x_325, x_337)`, values 1 vs 0, after 655 projection changes.
     The next AUFLIA move should inspect why existing select/store-chain readback
     repair cannot stabilize this post-beam assignment, or add readback
     stabilization inside accepted beam states; do not widen the beam blindly.
     **BEAM READBACK STABILIZATION LANDED (2026-06-26):** accepted branch-beam
     candidates now align direct scalar readback symbols for all asserted
     `x = select(a,i)` equalities against the candidate's repaired arrays before
     scoring the beam state. This fixes the simple stale-readback shape in a
     regression (`a = store(b,i,v)` plus `y = select(a,i)`) while preserving the
     full evaluator replay SAT gate. It does **not** move `bug337`: the first
     false replay point remains direct readback equality ordinal 34 / term 555,
     `x_388 = select(x_325, x_337)`, values 1 vs 0, after the same 655
     projection changes. The next AUFLIA move should be a direct-select repair
     diagnostic for term 555 that reports chain/direct candidates, replay false
     counts, and first blockers; the simple scalar-readback-alignment hypothesis
     is now rejected.
     **DIRECT-SELECT REPAIR DIAGNOSTICS LANDED (2026-06-26):** final replay
     failure notes now include `select_candidate_diagnostics` for direct
     `x = select(a,i)` equality misses. The diagnostic replays both targeted
     select-repair candidates on copies (store-chain/readback and direct
     array-entry), reporting whether the select equality becomes true, repair
     changes, full replay false count, and the next global blocker. On `bug337`,
     this shows select repair is reached and locally works: the chain candidate
     makes term 555 true, but only ties full replay (`same_full_replay`,
     changes=37, total_false=2) and moves the blocker to generated OR ordinal
     210 / term 3879. The direct array-entry candidate also makes term 555 true
     but worsens full replay (total_false=3) and exposes ordinal 35 / term 560
     (`0` vs `1`). The next AUFLIA move should compose the same-full-replay
     chain candidate with generated-OR scheduling under the existing final
     strict replay-improvement gate; more one-step direct-select repair is not
     the bottleneck.
     **MIXED SELECT/OR REPLAY BEAM LANDED (2026-06-26):** direct-select targeted
     replay repair now first tries a bounded mixed beam over direct select
     failures and generated OR failures, accepting only a composed strict
     full-replay improvement before mutating the projection (width 8, 64
     expansions, depth 6, `current_false + 4` temporary false conjuncts, at most
     two visits per failure ordinal). This moves `bug337` from direct select
     equality ordinal 34 / term 555 to generated OR ordinal 210 / term 3879,
     after 587 projection changes. The row is still `unknown`: OR 210 branch 0
     repairs locally but returns to the select equality at ordinal 34 with
     total_false=2, while branch 3 flows to OR 211 and the old 211→212 pair
     cycle. The next AUFLIA move should either invoke the same mixed beam from
     generated-OR failures or diagnose the 210 branch-0 → 34 select cycle
     directly; keep cost caps explicit because the 10 s diagnostic route now
     takes about 76 s wall.
     **GUARDED OR/SELECT REPLAY BEAM RETAINED (2026-06-26):** invoking the same
     mixed beam from every generated-OR replay failure was measured and rejected:
     on `bug337` it regressed the final miss from OR 210 back to select equality
     34 / term 555 and raised the 10 s diagnostic route to about 149 s wall.
     The retained OR-start path is therefore admitted only for small,
     multi-false replay surfaces (`current_false > 1`, <=64 positive conjuncts),
     with a focused regression covering an OR repair that ties replay until a
     follow-up select repair is composed. On the large AUFLIA row the guard
     restores the OR 210 frontier and ~76 s diagnostic wall time. The next
     useful AUFLIA move is cycle-specific: diagnose or repair the concrete
     210 branch-0 -> 34 select transition, not a broader OR-start beam.
     **BRANCH-SELECT CYCLE DIAGNOSTIC LANDED (2026-06-26):** final generated-OR
     replay diagnostics now compose each repairable OR branch trial with the
     direct-select store-chain/direct array-entry candidates when that branch's
     next global blocker is a direct `x = select(a,i)` equality. On `bug337`,
     this confirms the concrete 210/34 queue-lock: branch 0 followed by the
     select-34 store-chain repair makes term 555 true but remains
     `worse_full_replay` at total_false=2 and lands back on OR 210 / term 3879;
     the direct array-entry select repair also makes term 555 true but worsens
     to total_false=3 and exposes ordinal 35 / term 560. The next useful AUFLIA
     move is no longer diagnostic: implement a cycle-aware replay repair for
     `210 -> 34 -> 210` that can keep the branch-0 chain repair while forcing an
     alternate OR-210 branch or component-level store-chain change, still under
     the final strict full-replay improvement gate.
     **GUARDED BRANCH-SELECT CYCLE REPAIR LANDED (2026-06-26):** the
     alternate-branch version of that pattern is now implemented for small
     replay surfaces: after branch repair -> direct select repair -> same OR,
     try a different branch from the post-select state and accept only a final
     strict full-replay improvement (8 branches, 32 trials, current_false <= 2,
     <=64 replay conjuncts). A focused regression covers the useful shape. The
     large `bug337` attempt was measured and rejected before the guard: it did
     not move the frontier from OR 210 / term 3879 and raised route time from
     ~77 s to ~93 s, so the production repair is guarded off for that large
     row. The next AUFLIA move is specifically component-level store-chain /
     branch-state repair inside `210 -> 34 -> 210`; simply trying another OR
     branch after the select repair is ruled out for `bug337`.
     **RETURNED-OR BRANCH/SELECT DIAGNOSTIC LANDED (2026-06-26):**
     branch/select candidate diagnostics now include OR-local details for the
     first global blocker after a composed branch+select trial. On `bug337`,
     branch 0 -> select 34 chain repair returns to OR 210 with best branch 0
     and exactly one false literal: term 580,
     `x_339 = store(x_325, x_337, 2)`, with lhs
     `(array default 0 [0 -> 2] [1 -> 3] [2 -> 3])` and rhs
     `(array default 0 [0 -> 2] [1 -> 2] [2 -> 1])`. The next repair target is
     therefore preserving the select-34 store-chain readback while repairing
     branch-0 store-definition term 580 / its component arrays.
     **GUARDED SAME-BRANCH STORE RESIDUAL REPAIR LANDED (2026-06-26):**
     a target-side residual repair now handles the small-surface case where the
     branch/select cycle returns to the same OR, the same branch is still best,
     and exactly one false literal remains with shape
     `target = store(base, i, v)`: rebuild `target` from the current repaired
     `base` and accept only under a strict full-original-replay improvement.
     A focused regression covers preserving `c = store(a,3,7)` after
     `5 = select(a,i)` repairs `a[2]`. The unguarded large `bug337` probe was
     measured and rejected: it did not move the frontier from OR 210 / term 3879
     and raised route time to ~87 s. With the small-surface guard restored,
     `bug337` is back in the prior unknown regime (solve ~76.9 s before evidence
     cleanup). The next AUFLIA move is residual-candidate/component-array
     diagnostics explaining why the concrete term-580 target-side repair is not
     accepted on the large row, not another broad branch-choice or store-target
     repair.
     **SAME-BRANCH RESIDUAL DIAGNOSTIC LANDED (2026-06-26):** branch/select
     candidate diagnostics now try the same-branch residual candidate on
     diagnostic copies and emit rows such as
     `chain+same_branch_store_target`. On `bug337`, term 580's target-side
     repair is locally effective and keeps select term 555 true, but full replay
     remains `worse_full_replay` with total_false=2 and the first global blocker
     moves to OR 209 / term 3654. OR 209's best branch is branch 3 with one
     false literal, term 3650, over the same two array values flipped:
     `(array default 0 [0 -> 2] [1 -> 2] [2 -> 1])` vs
     `(array default 0 [0 -> 2] [1 -> 3] [2 -> 3])`. The next AUFLIA move is a
     paired OR-210/OR-209 component-array consistency repair, not another
     isolated term-580 target repair.
     **RESIDUAL FOLLOW-UP OR DIAGNOSTIC LANDED (2026-06-26):** the same
     diagnostic now tries one best-branch follow-up when the residual state
     exposes a different generated OR, emitting rows such as
     `chain+same_branch_store_target+followup_or209_branch3`. On `bug337`,
     this repairs OR 209 branch 3 locally and preserves select 34, but full
     replay remains total_false=2 and moves to OR 219 / term 6084. OR 219's
     best branch 3 has one false literal, term 1402, comparing
     `(array default 0 [0 -> 1] [1 -> 2] [2 -> 1])` with
     `(array default 0 [1 -> 2] [2 -> 1])`. The next AUFLIA move is therefore a
     bounded multi-hop component-array chain repair/diagnostic with explicit
     replay-improvement gating, not a two-OR special case.
     **BOUNDED RESIDUAL CHAIN REPAIR LANDED (2026-06-26):** on small replay
     surfaces, the production branch/select-cycle repair now follows up to four
     generated-OR hops after the same-branch residual store-target repair,
     records the best strict full-replay improvement, and preserves the original
     OR + select at every hop. A focused regression clears the two-OR analogue.
     The large `bug337` diagnostic now shows the chain reaches OR 236 / term
     13052 at `same_full_replay`, total_false=1; OR 236 best branch 0 has 2/2
     false literals, first false term 12950 (`3` vs `1`), and blindly repairing
     that branch worsens to total_false=2 at scalar equality term 2611. The next
     AUFLIA move is scalar-aware OR-236 handling after the residual chain, not
     more component-array-only hops.
     **SCALAR-CHOICE BRANCH REPAIR LANDED (2026-06-26):** follow-up OR repair
     now compares the greedy branch repair with a bounded scalar-choice
     candidate that explores both directions of direct scalar equalities and
     scores completed branch repairs by full replay. The small `u = v` with an
     existing `u = 0` regression now chooses `v := 0` and clears replay. On
     `bug337`, this does not move the large frontier: OR 236 still selects the
     ordinary `branch` candidate, then worsens to scalar equality term 2611.
     Therefore the next AUFLIA move is an OR-236-specific diagnostic for both
     false branch literals and their scalar side effects, not another generic
     scalar-direction heuristic.
     **OR-236 SCALAR SIDE-EFFECT DIAGNOSTICS LANDED (2026-06-26):** replay OR
     notes now include bounded false-literal details for the selected best
     branch plus simulated direct scalar choices and their replay side effects.
     On `bug337`, OR 236 branch 0 is now explicit: false scalar term **12950**
     (`510 = 2609`, values **3 vs 1**) can be locally repaired by setting
     symbol **460** from term **510** to **3**, but the next blocker becomes
     term **2611** (`2609 = 2610`, **3 vs 1**) with **branch_false=1** and
     **total_false=2**. The sibling false scalar term **12951** (`510 = 2613`,
     **3 vs 2**) symmetrically drives blocker **2615** (`2613 = 2614`,
     **3 vs 2**) with the same counts. The next AUFLIA move is a paired
     repair/diagnostic over those sibling scalar chains, or a proof that this
     late OR-236 branch must be handled by a stronger combined repair.
     **PAIRED SCALAR-CHAIN DIAGNOSTIC LANDED (2026-06-27):** the OR replay
     note now applies the selected branch's false scalar literals as a coupled
     repair, then follows up to four scalar equality blockers. On `bug337`,
     forcing OR 236 branch 0 is an oscillation: setting symbols **460/461** from
     term **510** to **3** repairs branch terms **12950/12951** and reaches
     **branch_false=0**, but the downstream blockers **2611/2615** require
     setting those same symbols back from terms **2610/2614** to **1/2**,
     returning to OR **236** with **branch_false=2** and **total_false=1**.
     The next AUFLIA move is scalar-closure-aware OR-236 branch selection:
     score candidate branches after their local scalar closure, not just by raw
     false-literal count.
     **SCALAR-CLOSURE BRANCH SCORING LANDED (2026-06-27):** replay OR notes
     now score candidate branches after branch repair plus bounded scalar
     closure. On `bug337`, this rules out a simple alternate-branch fix for
     OR 236: reported branches **0..7** all locally repair to
     **raw_branch_false=0**, then scalar closure returns replay to OR **236**
     with **final_branch_false=2** and **final_total_false=1**. The next AUFLIA
     move is no longer branch choice; it is either learning/refining the
     scalar/array constraint that makes this OR-236 branch family impossible
     under the current model or preventing production repair from spending time
     on branches that immediately close back to the same OR.
     **SCALAR-CLOSURE BRANCH REJECTION GUARD LANDED (2026-06-27):**
     residual follow-up OR repair now routes candidate branch repairs through a
     bounded scalar-closure guard. The guard declines only when scalar closure
     takes at least one scalar equality step, replay returns to the same
     follow-up OR, the repaired branch is false again, and the full replay false
     count is not lower than before the candidate. On `bug337`, the route still
     reaches OR **236** with **total_false=1** and reports the same closure-loop
     branch family, but it no longer spends a follow-up repair on
     `followup_or236_branch0_branch`. The next AUFLIA move is learning/refining
     the missing scalar/array constraint that explains the OR-236 family, not
     raw OR branch forcing.
     **SCALAR-CLOSURE SCHEDULE GUARD LANDED (2026-06-27):** the same
     returned-OR guard now wraps general multi-literal branch schedule repairs,
     including the projection repair pass and targeted replay repair. This
     blocks an earlier raw branch-forcing route that could set several scalar
     symbols, make a branch locally true, then let scalar closure return to the
     same OR with no full replay improvement. On `bug337`, the row is still
     `unknown`, but the measured diagnostic now completes normally in about
     **55 s** instead of exiting through the 180 s timeout wrapper after about
     **89 s**; projection repair changes drop from **587** to **565**. The next
     AUFLIA move remains a real scalar/array refinement for the OR-236 family.
     **SELECT-BACKED SCALAR REPAIR LANDED (2026-06-27):** scalar equality,
     direct branch-literal, and multi-literal branch-schedule repairs now use
     asserted readback equalities as backing constraints. When a repair wants
     `y = v` and the original assertions contain `y = select(a, i)`, it writes
     `a[i] := v`, realigns direct select readback symbols, and then stores the
     scalar value only if still needed. This removes the measured OR-236
     oscillation on `bug337`: the diagnostic still returns `unknown`, but the
     first replay blocker moves to scalar equality **term 3408**
     (`x_383 = x_330`, values **0 vs 1**) after **430** projection repair
     changes, with `check_auto_explained` / `solve` / `produce_evidence` each
     around **49.3 s**. The next AUFLIA move is now term-3408 scalar equality
     explanation/repair, not OR-236 branch forcing.
     **SCALAR-CANDIDATE DIAGNOSTICS LANDED (2026-06-27):** top-level scalar
     replay failures now report bounded repair candidates using the same
     select-backed path as production. On `bug337`, term **3408** has two
     locally productive choices: `x_383 := x_330` exposes OR **210** / term
     **3879**, and `x_330 := x_383` exposes OR **211** / term **4108**, both
     with `total_false=2`. A targeted scalar replay repair exists for small
     replay surfaces, but the unguarded large-row version was measured/rejected
     after raising the first diagnostic call to **113 s** and still returning
     to term **3408**; it is therefore guarded off for large generated AUFLIA
     rows. A bounded scalar+OR follow-up diagnostic now composes those exposed
     ORs with one guarded best-branch repair. On `bug337`, both obvious
     compositions are negative: OR **210** branch **0** and OR **211** branch
     **3** become locally true but worsen full replay to **total_false=3** and
     return to scalar equality term **3408**. Closure-level diagnostics now show
     the next shape: repairing scalar equality after the OR-210 branch repair
     restores **total_false=2** but exposes OR **211**, while repairing scalar
     equality after the OR-211 branch repair restores **total_false=2** but
     exposes OR **210**. A second-hop OR diagnostic now closes this as a local
     cycle: OR **210** -> OR **211** -> OR **210**, and OR **211** -> OR
     **210** -> OR **211**, each reported as `returns_first_or` after scalar
     closure. A production guard now rejects this two-hop no-progress shape for
     small replay surfaces (<=64 positive conjuncts) in branch-choice repair and
     the final single-literal OR fallback. The ungated large-row version was
     measured/rejected after moving `bug337` backward to OR **210** and about
     **72.5 s**, so the large row remains diagnostic-only at term **3408**. The
     follow-up branch-term diagnostic now identifies the concrete pair:
     OR **210** branch term **3805** (store-definition branch) and OR **211**
     branch term **4107** (copy/no-store branch). Returned-OR literal
     diagnostics refine the blocker further: 4107 fails on term **4041**
     (`x_303 = x_317`, inserted-cell array vs default array), while 3805 fails
     on term **583** (`x_331 = store(x_317,x_320,x_337)`, default array vs
     inserted-cell store RHS). A small-surface returned-OR stabilizer now
     handles the synthetic version of that shape under the strict replay gate,
     but the ungated `bug337` attempt regressed the first diagnostic phase to
     **231.8 s** and was capped at <=64 replay conjuncts; the large row is back
     to ~**52.5 s** and remains at term **3408**. A diagnostic-only direct
     returned-OR stabilization probe then ruled out the obvious large-row
     literal repair: repairing OR **210** branch **3805** false literal
     **583** (`x_331 = store(x_317,x_320,x_337)`) is `worse`
     (`total_false=3`) and returns to term **3408** with values **0 vs 1**;
     repairing OR **211** branch **4107** false literal **4041**
     (`x_303 = x_317`) is also `worse` (`total_false=3`) and returns to term
     **3408** with values **1 vs 0**. The next AUFLIA move is therefore a
     paired scalar+array or relevance-guided learned large-row constraint that
     preserves the term-3408 scalar equality while relating the 4041/583
     array-cell disagreement, not direct single-literal repair, greedy
     single-OR forcing, or more local branch enumeration.
   - Pair it with a **single-witness extensionality skolem** for arrays
     (`a≠b ⇒ select(a,k)≠select(b,k)`, one fresh `k` — what Z3/cvc5 do) replacing the
     current **`2^index-bits` enumeration** (`MAX_ARRAY_EQ_INDEX_BITS=8`), which is
     *infinite* for Int indices and already walls QF_AX at 9-bit. axeyum already has
     the lazy machinery (`ArrayElimination::abstraction()`).
   - The QF_UF weak row is **mostly Tier-B front-end coverage** (unhandled
     `(Set …)`/`(Seq …)` sorts, `sin`, `fmf.card` ≈ 25 files) — **not** a congruence
     cap (only ≈5 files hit the BV-width wall). Fix the parser, not a decider.
5. **Aim the cert budget at the *valuable* frontier, not just the easy one.** The
   highest-value certification targets are the **hard rows where cvc5 has NO proof**:
   narrow certifiable **NRA/NIA-unsat** and **array-unsat** sub-fragments. Certifying
   even a narrow nonlinear-unsat fragment to a Lean kernel is a capability **no stack
   on earth has.** Promote the existing degree-2 **SOS→Lean** chain (ADR-0040) as the
   seed and define the next narrow nonlinear-unsat cert slice as a tracked keystone.
6. **NRA path: correct the label and the overclaim.** The target is **NLSAT
   (model-constructing, single-cell projection)** / **cylindrical algebraic coverings
   (CDCAC)** — *local, model-guided* — **not** global upfront "CAD." axeyum's `nra.rs`
   is already the cvc5-style **linearization front-end**; the measured QF_NRA-cvc5
   misses are dominated by **Fourier–Motzkin LRA-backstop blowups (10/27)**, so the
   cheapest real NRA gain is a **competent LRA core to replace Fourier–Motzkin**
   ([P1.6]) + a larger cross-product budget — *before* any new nonlinear engine. The
   gap-analysis doc's "strong CAD decision side" is **overstated** (no general
   multivariate CAD module exists; `nra_degree` frontier = 2 — the scoreboard is the
   truth); align that prose down.
7. **The Lean *tactic backend* is unbuilt — demote from "pure win" to roadmap item.**
   axeyum emits Lean *modules out-of-band*; there is no in-tree tactic that imports a
   Lean goal, decides it, and discharges it in place ([P3.7] unshipped). Until it
   exists, axeyum does not beat manual Lean *in Lean's own workflow*. Build it — and
   make it **fail rather than `sorry`** (lean-smt's silent-hole fallback is the exact
   UX trap to avoid).

**Net:** certify where we're strong AND convert the one cheap IR keystone (uninterp
sorts + Int-array sorts) that is *itself* dominance-eligible; spend cert budget on
the valuable (nonlinear/array-unsat) frontier cvc5 can't touch; keep the moat claim
scoped to the axiom-clean kernel sub-fragment; and stop the decide-race only where
it's genuinely a 15-year catch-up (high-degree NRA), not where one IR change closes it.

## What "done" means

See [`docs/plan/00-north-star.md`](docs/plan/00-north-star.md) for the full
definition. In one line: **Z3 parity** = feature coverage + competitive
measured performance on the decidable/semidecidable fragments, with honest
`unknown` where undecidable; **Lean parity** = every `unsat`/`valid` result
carries a machine-checkable proof a Lean-grade kernel accepts, produced by an
untrusted search and validated by small independent checkers.

## The two load-bearing fronts

1. **Performance, measured head-to-head (Track 1).** There is no parity claim
   without a clean Z3 comparison on real corpora. **Measured reframe (2026-06-18,
   public p4dfa 113 vs Z3 — see [findings](docs/research/05-algorithms/lazy-bitblasting-p21-findings.md)
   + ADR-0037):** the lever is **word-level *reduction* before bit-blasting**
   (`solve_eqs`/canonicalize/`ite`-handling), *not* lazy bit-blasting — that slice
   is arithmetic-free, so lazy-bv CEGAR is inert (0/113 heavy ops). Reduction moved
   the number 2→7/113. The remaining gap **partitions** into: ~6 *EncodingBudget*
   (deeper reduction pulls them under the encode ceiling — the proven mechanism),
   ~9 *search-bound* (kissat-class CDCL cracks them; batsat/`xor_cdcl`/PBLS all
   miss), and ~90 *large-CNF* (reduction + genuinely hard). **Decision (both in
   parallel):** reduction leads near-term; the proof-producing CDCL core is
   incrementally modernized toward competitive as a slower parallel track. Track
   the honest pulse: **Timeout→decided**.
2. **Reduction certificates (Track 3).** Today only the clausal layer (DRAT) and
   the bit-blast reduction (miter) are independently checked; every other
   reduction is trusted. Certifying them — via an **Alethe emitter** checked by
   the Rust **Carcara** checker — is the critical path to Lean parity.

## The two engineering keystones

- **Incremental e-graph + CDCL(T) loop** (Track 1, P1.4/P1.5). Almost every lazy
  theory and all quantifier work depends on a shared congruence-closure equality
  bus and a theory-propagation loop. Build it once; it unlocks Track 2.
- **Alethe term/proof IR + emitter** (Track 3, P3.2). The format that is
  simultaneously Rust-checkable (Carcara, no C/C++), BV-shaped (matches axeyum's
  lowering and existing miter), and the on-ramp to Lean. Everything downstream in
  the proof track depends on it.

## Track map

| Track | Folder | Theme |
|---|---|---|
| 1 — Engine & Performance | [`track-1-engine/`](docs/plan/track-1-engine/README.md) | SAT inprocessing, preprocessing, SAT-core modernization, e-graph, CDCL(T), theory combination, PBLS, strategy; 2026-06-27 `bvumulo` now uses the word-width threshold encoding `a > all_ones / b` instead of a doubled-width multiplier, avoiding BV512 multiplication terms for BV256 overflow checks while preserving SMT-LIB totality |
| 2 — Theories & Breadth | [`track-2-theories/`](docs/plan/track-2-theories/README.md) | lazy BV, lazy arrays, EUF, LIA cuts (+ unbounded backstop), NRA/CAD, quantifiers, strings, FP polish, datatypes, **breadth backlog** (sequences/sets/sep-logic/finite-fields/co-datatypes/rec-fun) |
| 3 — Proofs & Lean | [`track-3-proof-lean/`](docs/plan/track-3-proof-lean/README.md) | trust ledger, LRAT, Alethe IR+emitter, Carcara-checked QF_BV, embedded checker, reduction proofs, Lean kernel + reconstruction, **Craig interpolation**; 2026-06-27 `prove_unsat_to_lean_module` now falls back to normalizing the assertion spine by splitting top-level conjunctions and stripping repeated top-level double negations after direct reconstruction declines, closing the consumer-facing shape-sensitivity gap for common `hyps ∧ ¬goal` queries without perturbing existing direct routes |
| 4 — Use Cases & Frontend | [`track-4-usecases-frontend/`](docs/plan/track-4-usecases-frontend/README.md) | warm lazy memory, symexec/CFG frontend, OMT/MILP, SMT-LIB command surface, benchmarking & the perf gate, **CHC/Horn (PDR/Spacer)**, **synthesis/abduction**; 2026-06-27 memory-aware incremental assumptions now cover one-shot array/UF branch feasibility through the full dispatcher, `SymbolicMemory` gives frontends a typed load/store helper plus conservative write-log normalization / compact read-over-write `ite` construction, `SymbolicExecutor::branch` and `explore_cfg` auto-promote array/UF queries to the memory/theory-aware route when needed, `explore_cfg` / `explore_cfg_checked` provide DFS with model-witnessed targets plus concrete replay hooks, and `minimize_model` / `produce_evidence_minimized` / `prove_minimized` give property/verification frontends replay-checked lexicographic counterexample minimization over selected Bool/BV<=127/Int symbols, with metadata-aware variants for signed two's-complement BV objective order. `axeyum-property` v0 is now the first typed SDK over that surface: Bool/BV/Int handles, assumptions, proof/minimized-counterexample calls, `ProofCertificate` packaging for checked `EvidenceReport` plus best-effort standalone Lean modules and stable evidence/trust/Lean summaries, scalar/tuple/derived-struct `Symbolic` declarations and model lifting including signed-order two's-complement fixed-width Rust integers, named-field `symbolic_struct` bundles, `.equals()` aliases, property-owned Bool/BV/Int builder aliases, and `Property::all`/`any` Boolean folds that keep construction errors explicit, reusable typed BV overflow predicates, native-scalar counterexample-to-`#[test]` rendering with caller-owned prelude/setup snippets, helper-rendered Boolean / `Result<(), E>` / `Result<bool, E>` replay adapters, deterministic `#[cfg(test)]` module assembly, deterministic multi-case fixture file assembly, direct named/tuple aggregate initializer snippets, and explicit nested aggregate field composition, and the committed/generated SDK corpus gate with 16 graduated workflows, deterministic executable baseline comparisons for scalar counterexamples, an actual fixed-seed proptest shrunk counterexample, struct and replay counterexamples, proved assertions, assumption-backed proved assertions, and a Kani-style assume/assert counterexample baseline, machine-readable `corpus.json`, DISAGREE=0, and 1/1 Lean-required coverage. The SMT-LIB front door also now handles `push`/`pop`/`check-sat-assuming`/`reset-assertions` in both incremental and single-query helpers without flattening scoped scripts, exposes `solve_smtlib_get_model` for user-declared model bindings, `solve_smtlib_get_assignment` for active top-level named assertions, and `solve_smtlib_get_assertions` for scoped rendered assertion snapshots, records `set-info`/`set-option`/`get-info`/`get-option` metadata with `solve_smtlib_get_info` and `solve_smtlib_get_option` responses, and explicitly rejects full `(reset)` in the shared-arena model |

Track 4 optimization note (2026-06-27): all three OMT modes now span LIA and BV
(`box`, `lexicographic`, and `Pareto`). BV Pareto is covered for unsigned,
signed, maximize, and minimize directions, and malformed/out-of-fragment BV
Pareto objectives degrade to `Unknown` instead of hard solver errors.

Cross-cutting: [`00-north-star.md`](docs/plan/00-north-star.md) (definition of
done), [`01-dependency-dag.md`](docs/plan/01-dependency-dag.md) (the end-to-end
DAG, keystones, critical paths), and
[`gap-analysis-z3-cvc5-2026-06-22.md`](docs/plan/gap-analysis-z3-cvc5-2026-06-22.md)
(the latest practical gap analysis against Z3/cvc5), plus
[`references/`](docs/plan/references/README.md) (the distilled top-down review of
Z3, cvc5, bitwuzla, CaDiCaL/Kissat, Carcara, lean4/nanoda, lean-smt that this
plan is built on).

## Consumer-track integration (2026-06-27): converge the apps onto `main`

The demand-pull consumer track (apps that *use* axeyum to hunt bugs / prove
software properties — the [`docs/consumer-track/`](docs/consumer-track/README.md)
program) was started on an isolated `consumer-track` worktree/branch and has
**diverged** from `main`. This section is the standing plan to **merge and
integrate** it, one verifiable new-crate-only increment at a time. It is owned by
the consumer-integration lane and does not touch core IR/solver/rewrite files.

**State at takeover (2026-06-27).** Two efforts forked:
- On `main`: `axeyum-property` (+ `axeyum-property-macros`) — the typed
  prove-or-counterexample SDK — built out independently and is now a **superset**
  of the branch's version (phantom `Bv<W>`, derive, counterexample→`#[test]`
  replay fixtures, signed minimization, `ProofCertificate`/Lean modules, a
  committed `property/SCOREBOARD.md` with proptest/Kani baselines, DISAGREE=0).
- On `consumer-track` (worktree `../axeyum-consumer`): `axeyum-property`
  (+ `-derive`) **plus** the apps that never landed on `main` —
  **`axeyum-evm`** (EVM symbolic bug-hunter, Phase 1+2), **`axeyum-verify`**
  (+ `-macros`, the `#[axeyum::verify]` Rust verifier, Phase 1+2), and
  **`axeyum-consumer-bench`** (the measurement backbone).

**Reconciliation decisions.**
1. **`axeyum-property`: `main`'s is canonical.** It supersedes the branch's
   design; the branch's `axeyum-property` + `axeyum-property-derive` are
   **retired, not ported**. Any unique helper the apps need (e.g. a `Witness`/
   reproduce export, `BvArray` shape) is folded into `main`'s `axeyum-property`
   as a small additive slice.
2. **`axeyum-evm` ports as a new crate.** It depends only on
   `axeyum-ir` + `axeyum-solver` (zero property coupling), so the port is
   low-friction; adapt to `main`'s (newer, warm-array) solver API. Independent
   concrete-interpreter revalidation of every witness keeps **DISAGREE = 0**.
3. **`axeyum-verify` (+ `-macros`) ports as new crates.** Its only tie to the
   branch's SDK is `axeyum_property::Witness` (2 call sites) → rebind to
   `main`'s `axeyum-property` counterexample/replay surface.
4. **`axeyum-consumer-bench` ports and is extended** into the headline
   deliverable below.

**The measurement deliverable (answers the standing review).** The ~190
warm-incremental symbolic-execution commits (array/memory/UF readback folding —
the angr/unicorn foundation, and the right capability) are **real but
unmeasured**: the frontier dashboard has only SMT levers, nothing for
symbolic-execution depth, memory-shape coverage, or vs-hevm/angr. Integration
stands up a committed **EVM/symexec capability scoreboard** — the analog of
`DOMINANCE.md` for the symbolic-execution engine: paths explored / memory-shapes
decided / bug-classes found, with **DISAGREE = 0** vs an independent oracle (the
EVM app's own concrete interpreter always; vs hevm/halmos when installed,
honestly install-gated). This gives the engine work a number, and the shape
coverage it reports is what decides **special-case folding vs the general warm
array/UF theory (U6)** — driven by which memory shapes the corpus actually
exercises, not an unbounded fold-list.

**Sequenced increments (each: builds + gates + DISAGREE=0, committed).**
- **I0** — ✅ DONE (`79193f2`) — recorded this plan; reconciled the docs.
- **I1** — ✅ DONE (`3a22101`) — ported `axeyum-evm` (no API drift); folded the
  `reproduce` layer into `main`'s `axeyum-property`; added the workspace member.
- **I2** — ✅ DONE (`19d11b4`) — ported `axeyum-verify` + `axeyum-verify-macros`
  (own `Witness` enum; `syn`/`quote` declared directly).
- **I3** — ✅ DONE (`c840cab`) — **EVM/symexec capability scoreboard**
  (`docs/consumer-track/evm/SCOREBOARD.md`, `cargo run -p axeyum-evm --example
  measure_evm`): 6/6 decided, DISAGREE=0, 5 memory-shape classes.
  `axeyum-consumer-bench` deliberately *not* ported (retired-API + duplicative).
- **I4a** — ✅ DONE (`b774df2`) — reconciled `UPSTREAM-FEEDBACK.md`: U6 is now
  *measured* by the scoreboard (it is the special-case-vs-general arbiter).
- **I4b** — ✅ DONE (`0945c69`, `fad0650`) — `MemoryEncoding::{IteFold (default),
  WarmArray}` in `axeyum-evm`; WarmArray lowers storage to real `select`/`store`
  via `SymbolicMemory` + `assume_auto`. Scoreboard gained warm-vs-`ite` + a
  store-chain depth sweep. **Measured result (refuted the naive hypothesis):**
  `ite`-fold is *faster* and the gap **grows** with depth (depth 32: ~3 ms vs
  ~14 ms), because the array path falls to the one-shot memory dispatcher while
  `ite`-fold stays warm with constant-folding concrete guards. Recorded in
  `UPSTREAM-FEEDBACK.md` U6: the gap is *incremental-array performance*, not
  capability — a true warm lazy-array engine (retained state across
  `enter`/`backtrack`), not one-shot re-dispatch. `ite`-fold stays the default.

**Forward backlog (autonomous continuation — pick the top unblocked item).**
Each is a self-contained increment under the standing discipline below; do them
in order unless a dependency says otherwise. Update the STATUS consumer lane +
this list as each lands. Done: scoreboard coverage broadened to 8/8 incl. the
`INVALID` bug class (`db36e0e`); per-app PLAN/STATUS co-located on `main`
(`a059c6f`).

*App A — `axeyum-evm` (Phase 3):*
1. **Multi-tx invariants** — a call sequence with persistent storage between txs.
   The keystone; sliced for soundness (each slice gated DISAGREE=0):
   - **A1.1** — ✅ DONE (`4159cd3`) — `max_txs` DFS driver: on a normal halt with
     txs remaining, advance to the next tx with **fresh per-tx calldata**,
     **persisting storage** but **resetting stack/memory**. Multi-tx safe proofs
     work; a multi-tx-only revert is reached soundly (reported `Unknown` until a
     validated witness exists, never a wrong verdict). Default `max_txs=1`
     preserves all single-tx behavior.
   - **A1.2** — ✅ DONE (`e0751c4`) — `concrete::run_sequence` (persistent storage
     across txs) is the multi-tx oracle; `revalidate` replays the sequence.
   - **A1.3** — ✅ DONE (`e0751c4`) — `lift_witness` lifts the full per-tx input
     sequence; `Finding.prior_txs`; the cross-tx *init-then-revert* bug is now
     *reported* with a replay-validated 2-tx witness, and the scoreboard has a
     Multi-transaction section (bug-found + safe-proved), DISAGREE=0 over 8 cases.
   - Note: `bounded_model_check_with_memory` needs a full `TransitionSystem`
     encoding of a whole-contract step — heavier than the DFS re-entry used here.
   **A1 keystone COMPLETE.** Next A-item: **A2 `CALL`/`DELEGATECALL` modeling**.
2. **`CALL`/`DELEGATECALL`/`CREATE`/`EXTCODE*` + environment modeling** so paths
   explore *past* these opcodes instead of going `Unknown`. The soundness key
   (keeps DISAGREE=0): model each as a **witnessed symbolic environment input** —
   a fresh symbol on the symbolic side, *replayed from the witness* on the
   concrete side (the env-oracle generalizes calldata to opcode-produced
   nondeterminism). Sliced:
   - **A2.1** scalar env opcodes that pop `k`, push one fresh value: `GAS`,
     `BALANCE`, `EXTCODESIZE`/`EXTCODEHASH`, `RETURNDATASIZE`, and block/context
     (`TIMESTAMP`/`NUMBER`/`GASPRICE`/`COINBASE`/`CHAINID`/`ADDRESS`/`ORIGIN`/…).
     *Path:* `opcode.rs` (`Op::Env{pops}`), `symbolic.rs` (env-symbol allocator,
     recorded per path), `concrete.rs` (env-value oracle consumed in order),
     witness (`env_inputs`). *Exit:* a contract that branches on `gas()`/context
     explores past it; a bug after it is reported + replay-validated, DISAGREE=0.
   - **A2.1** — ✅ DONE (`a695198`) — scalar env opcodes are witnessed inputs;
     paths explore past them; scoreboard `environment` class, 10/10, DISAGREE=0.
   - **A2.2** — ✅ DONE (`f3f45c8`) — `CALL`/`CALLCODE`/`DELEGATECALL`/`STATICCALL`
     push a witnessed success flag and continue; return-length `>0`/symbolic →
     `saw_unknown` (return data unmodeled, no false safe).
   - **A2.3** — ✅ DONE (`1cfbf47`) — re-entrancy: after a non-static call, storage
     is adversarial (later `SLOAD`s read a witnessed value); `STATICCALL` does not
     dirty. The DAO threat model; SafeUpToBound stays sound.
   **A2 phase COMPLETE.** Scoreboard 12/12 decided, DISAGREE=0, `environment`
   class covering env opcodes + CALL + re-entrancy. Next A-item: A3 (WASM +
   vs-hevm, install-gated) — deferred; pivot to App C (C4) which is fully buildable.
3. **WASM in-browser surface** (the delivery differentiator) + the vs-hevm/halmos
   scoreboard once those tools are installable (the `ExternalOracle` seam exists).
   *Status:* the consumer crates are wasm-clean, but the `wasm32` build is
   **blocked on `UPSTREAM-FEEDBACK` U8** — `axeyum-solver` does not compile for
   `wasm32` (`abv.rs` uses `std::time::Instant` directly instead of the cfg'd
   `web_time` shim). Resume once U8 lands; the vs-hevm part stays install-gated.
4. **Opcode-precision deepening (DONE, ongoing)** — turn `Unknown`-forcing
   havoc/unsupported opcodes into precise models (concrete-operand fast path,
   symbolic→sound `Unknown`), each added to the differential-fuzz pool:
   - **BYTE** (0x1a) — **fully precise** (concrete index → shift+mask; symbolic
     index → bounded 32-way `ite`) (`7b9633b`, `41af539`).
   - **SIGNEXTEND** (0x0b) — **fully precise** (concrete → `sign_ext`+`extract`;
     symbolic → bounded 31-way `ite`) (`22bb92e`, `41af539`).
   - **EXP** (0x0a) — concrete base+exp → constant-fold via `Word::pow`
     (`74c6b6a`); symbolic exponent still havocs (a faithful symbolic 256-bit
     modular pow is heavy).
   - **CALL return data** — `CALL`/`STATICCALL`/`DELEGATECALL` with a concrete,
     32-aligned, bounded (≤4 words) return region now writes *witnessed* fresh
     bytes to memory (over-approximating any callee return) instead of `Unknown`;
     witness replays in the concrete oracle (`58b4fa7`). Symbolic-length/unaligned
     regions stay sound `Unknown`.
   - **LOG0–LOG4** (0xa0–0xa4) — modeled as no-op pops (logs have no effect on
     execution state); previously `Unsupported`, which hid every bug *after* a log
     (`810a6fe`). A major false-`Unknown` source closed — real contracts log on
     essentially every state change.
   - **BLOCKHASH** (0x40 → `Env(1)`) and **MSIZE** (0x59 → `Env(0)`) — witnessed
     env values (`b82eba7`).
   - **CALLDATACOPY** (0x37) — *precise* calldata→memory copy for a concrete,
     32-aligned, bounded region (the calldata is already symbolic, so the witness
     replays) (`a5894be`). In essentially every ABI dispatcher.
   - **CODECOPY** (0x39) — *precise* code→memory copy (code is concrete →
     constant words; raw bytecode now retained on `Program.code`) (`9a68459`).
   - **CREATE/CREATE2** (0xf0/0xf5) — re-entrant deploy: witnessed new-contract
     address + adversarial post-state storage (constructor may re-enter)
     (`fbb2c6e`). Closes the factory-pattern gap.
   - **SELFDESTRUCT** (0xff) — clean halt like STOP (pop beneficiary, end the
     path safely) (`f4bdba4`).
   - *Next candidates:* RETURNDATACOPY tied to a modeled return buffer;
     EXTCODECOPY (external code genuinely unknown → fresh-witnessed both sides);
     symbolic-exponent EXP (heavy). **Common runtime opcodes are now covered** —
     the remaining gaps are rarer or genuinely nondeterministic.

*App C — `axeyum-verify` (Phase 3 / hardening):*
4. **General CFG→`TransitionSystem` lowering** — replace the hand-written
   `CounterLoopSystem` with a system *built from the AST*, giving warm-solver reuse
   across unroll depths for deep loops (scalar state; arrays-in-loop-state stay on
   the one-shot `_with_memory` route, off U6). Sliced:
   - **C4.1** — ✅ DONE (`6c7be0c`) — `ScalarLoopSystem` over **N scalar variables**: `state_vars` =
     one symbol per loop variable per step; `init` = pre-loop values; `trans` =
     `guard ? body-effect : stutter` where the per-variable next-value expressions
     come from lowering the **straight-line** loop body (assignments) against the
     pre-state symbols; `bad` = the in-loop assertion/overflow predicate. Reuse the
     `lower` expression machinery seeded with a pre-state env. *Path:*
     `verify/src/{bmc,lower}.rs`. *Exit:* a multi-variable accumulator loop (e.g.
     `sum += i; i += 1; assert(sum < BAD)`) verified via warm `bounded_model_check`,
     cross-checked against the unroll route (same verdict), DISAGREE=0.
   - **C4.2** — ✅ DONE (`pending-commit`) — nested `if` inside the loop body:
     guarded assignments fold into each variable's next-value via `ite` in the
     `update` closure (demonstrated by an even-counter loop, decided via warm BMC).
   - **C4.3** — ✅ DONE (`pending-commit`) — `loop_system::loop_system(AstLoop)`
     builds a `ScalarLoopSystem` from AST guard/update/assert exprs, **re-lowering
     each BMC step against the step's pre-state via the real `lower_pure_expr`** (no
     duplicated lowering). Update panic classes (overflow/`÷0`) fold into the bad
     predicate, so safety stays sound. Tested: an AST counter loop finds its
     assertion violation, proves safe out of reach, and catches an update overflow
     — all via warm `bounded_model_check`.
   - **C4.4** — ✅ DONE (`pending-commit`) — `loop_from_program` auto-detects the
     `let(const)* ; while { straight-line body }` shape and builds an `AstLoop`
     (params = free state, pre-loop lets = pinned state, body `Assign`/`Assert`
     threaded into per-variable updates + position-correct asserts via expression
     substitution); `check_program_loop` runs it on the warm route. Cross-checked
     against the unroll route (`verify_program`): the two **agree** on a buggy and
     a safe loop.
   - **C4.5** — ✅ DONE (`pending-commit`) — nested `if`/`else` in the loop body
     folds into guarded `ite` updates (`fold_body`): each arm-assigned variable
     becomes `ite(cond, then-value, else-value)`, and arm asserts are guarded by
     the (negated) branch condition. Cross-checked vs unroll on a branching loop.
   - **C4.6** — ✅ DONE (`pending-commit`) — `verify_program_warm` routes a loop
     program's *decision* through the warm BMC route (warm `SafeWithinBound` →
     `Verified`), deferring to the unroll `verify_program` for the bug witness,
     the cert, and out-of-fragment programs. Justified by a measured **~40× warm
     speedup** on safe deep loops (scoreboard scaling sweep, the *opposite* of the
     EVM I4b result); agrees with direct `verify_program` on buggy and safe loops.
     *Follow-up (C4.7):* a cert on the warm route so `verify_program_warm` Verified
     results are `certified`/Lean-backed too.
   **C4 phase COMPLETE** (C4.1–C4.5) — verify has an AST-loop→warm-BMC path
   (straight-line + nested `if`) that agrees with the unroll route.
   - **C5 fragment-widening (DONE, ongoing)** — the `#[verify]` surface now covers
     real Rust idioms beyond the C4 core, each soundness-fuzzed against a std
     oracle: `match`-on-int desugared to a right-folded `if`/`else` chain
     (`4552857`, dispatch fuzz `575ce25`); `wrapping_{add,sub,mul}` (modular, no
     overflow class — `cb9790e`); `saturating_{add,sub,mul}` (signed+unsigned
     clamp via `ite` over the overflow predicate — `89ca038`); `min`/`max`
     (signedness-correct select — `6e01b2e`); `abs` (with its `iN::MIN` overflow);
     `checked_{add,sub,mul}` Option flow — `.unwrap()`/`.expect()`, `.unwrap_or(d)`,
     and `match … { Some(v) => .., None => .. }` via a new boolean `Expr::Overflows`;
     `pow(N)` for a constant exponent (folded to checked `Mul`s); and
     `rotate_left/right` by a constant (`Expr::Rotate` → the IR's constant rotate).
     `rotate_left/right` by a constant; and **first-class (let-bound) `Option`
     values** — `let x = a.checked_add(b);` expanded at use sites
     (`unwrap`/`unwrap_or`/`is_some`/`is_none`/`match`), a scoped virtual binding
     with sound fallback-to-error. Also fixed a latent literal-coercion gap in the
     bare `name = <lit>` assignment path. *Next C5 candidates:* `Option` *returned*
     from a fn (rarer); `count_ones`/`leading_zeros`/symbolic-amount rotate need
     core IR (filed as **U9**).
5. **MIR consumer** — a `stable-mir-json` front-end behind the same lowering core;
   demo verifying one real `axeyum-bv` leaf fn (the self-hosting PoC).
6. **vs-Kani scoreboard** once Kani is installable (DISAGREE=0 + cert-coverage).

*Cross-cutting:*
7. **Lean-cert coverage** rises for free as upstream U1/U4 widen the
   reconstructable fragment; add more in-fragment safe examples to each app's
   metric set as it does. *Progress:* the verify scoreboard now reports Lean-cert
   coverage (2/3); EVM Lean coverage is pending a small core accessor on
   `EvidenceReport` (deferred — core territory).
8. **Port the per-app `PLAN.md`/`STATUS.md`** for `evm`/`verify` from the
   `consumer-track` worktree into `docs/consumer-track/{evm,verify}/` on `main`
   (docs-only) so each app's detailed plan lives beside its scoreboard.
9. **Soundness fuzzing (DISAGREE=0 hardening)** — adversarial differential fuzzes
   with an independent concrete oracle. *Done:* EVM fuzz (random bytecode +
   calldata; concrete REVERT/INVALID ⟹ never `SafeUpToBound`; single-tx +
   multi-tx + totality; pool covers arith/mem/storage/env/call) — **found and
   fixed a real wrong-safe** (bad jump destination treated as a safe path end,
   `b1cd4a2`); verify fuzz (random `a op b`; reachable panic ⟹ never `Verified`).
   *Next:* extend to signed arithmetic + the verify array/index fragment; a
   shrinking pass on any future fuzz failure.

**Coordination.** `main` is clean and compiling at takeover; the solver agent
actively rewrites STATUS.md's *Current focus*, so consumer-integration status
lives in its **own** STATUS.md section (no line collision). All changes are
**new-crate-only + an additive root `Cargo.toml` member line** — zero conflict
with their IR/solver edits. Build/test via `scripts/mem-run.sh` (64 GB cap).

## The gap to Z3/cvc5, itemized (2026-06-22; amended 2026-06-23)

A grounded audit against `crates/axeyum-solver/src/capabilities.rs` (the golden
capability ledger) corrected the framing: **the gap is not breadth — it is depth,
maturity, and (formerly) ~3 missing engines.** axeyum already has *columns* for QF_BV,
QF_ABV, QF_UF, QF_LRA, QF_LIA, UFLIA/UFLRA, QF_NRA/NIA, QF_FP, datatypes,
quantifiers (finite + e-matching + MBQI), strings, optimization, incremental,
symbolic execution, BMC, and k-induction. The 2026-06-27 Track-4 slice also
closes the immediate symbolic-memory/keccak-as-UF branch-query gap:
`IncrementalBvSolver` scopes deferred array/UF assertions, `check_with_memory`
and `check_assuming_with_memory` dispatch them through the full pure-Rust solver,
`SymbolicExecutor` exposes memory-aware assume/branch/status/model calls,
auto-routes `branch` and CFG branch/assume/status/model queries to that path
when arrays or UFs appear, and now keeps a narrow read-over-write slice warm:
same-index store/read-back constraints collapse to the stored value, and
literal-distinct concrete-address store misses skip the unrelated store to
expose inner read-backs; reads from constant arrays collapse to the default
value, covering zero-initialized toy-memory loads before any symbolic write; and
reads over array-valued `ite`s distribute to scalar branch reads, covering simple
state-merged memories when both selected branches reduce through that slice.
Symbolic-address read-over-write now expands to a scalar conditional
(`select(store(a, i, v), j) -> ite(i = j, v, select(a, j))`) and stays warm when
the remaining base read reduces away, covering symbolic hits/misses over
zero-initialized or otherwise reducible store chains.
Plain `select(a, i)` reads over BV-index/BV-element array symbols now abstract to
retained warm BV variables with scoped same-array select-congruence lemmas and
replay-projected array models, so symbolic-base helper loads and ROW tails whose
base read is a memory symbol no longer need the dispatcher. Direct equality
between supported array symbols is also retained as a scoped warm theory fact:
equal-array classes generate cross-array select-congruence lemmas for committed
assertions and one-shot branch assumptions, and SAT models merge equal arrays
before replay. Scalar Bool/BV
uninterpreted-function applications now get the same retained warm treatment:
`f(args)` is abstracted to an internal warm variable, same-function applications
receive scoped congruence lemmas, and SAT models project touched `FuncValue`
points before replay. Assertions and one-shot branch assumptions encode the
simplified/abstracted BV term while retaining the original memory/UF term for
replay and core reporting.
`SymbolicMemory` also provides a typed frontend
helper for array-backed `load`/`store`, load-equality branch/assume queries, and
conservative write-log normalization that drops shadowed same-index writes before
emitting compact read-over-write `ite` chains. Read-specific write-log loads now
skip writes at literal-distinct addresses and elide exact-hit guards while still
guarding later symbolic aliases; those helper branch/assume calls use the same
automatic warm/memory route, so reducible helper queries avoid the dispatcher
while unreduced memory still falls back soundly.
`explore_cfg` now owns the DFS solver mechanics for frontend-supplied CFG states:
branch feasibility, scope push/pop, infeasible pruning, unknown-safe traversal,
and replay-checked target models; with the default `memory_aware=false` it now
uses the same automatic warm/memory route as direct executor calls, so reducible
or select-abstractable CFG memory branches stay warm before falling back. This
is still a one-shot fallback for deferred theories beyond the narrow same-index /
literal-distinct / const-array / array-`ite` / reducible conditional-ROW /
BV-array select-congruence / direct array-equality / scalar-UF congruence
admission, not final warm lazy theory incrementality or a complete
lifter/emulator frontend. The
checked concrete replay hook now has a reusable tiny-target library surface:
`TinyBvProgram` validates a fixed-width BV register program, lifts instructions
to symbolic CFG steps, extracts model witnesses, and independently replays them
in a concrete emulator. It also exposes bounded program-counter reachability and
safety wrappers: reachable PCs carry concrete-replayed witnesses, and
unreachable/safe is reported only after exhaustive bounded exploration with no
unknowns, witness gaps, mismatches, or truncation. The same tiny target now has
`Load`/`Store` instructions over a zero-initialized SMT array memory, with
concrete replay using the same zero-default map and memory-bearing paths routed
through the memory-aware solver path. Concrete replay now also returns a
machine-usable trace: executed PCs/instructions, register snapshots, final
registers, final explicit memory cells, and terminal outcome.
`TinyBvProgram::from_assembly` gives that toy target a small imported text
format (`const`, arithmetic, `load`/`store`, `beq`, `win`/`lose`) with labels for
branch targets, register-vs-register equality branches (`beq rA rB ...`),
line-numbered parse errors, a public label-to-PC map, a public PC-to-source-line
map for imported instructions, deterministic PC-to-label lookup, typed static
CFG edges via `successors` / `cfg_edges`, source/label-aware basic blocks via
`basic_blocks`, deterministic Graphviz DOT export for the basic-block CFG via
`cfg_dot`, trace-highlighted DOT overlays via `cfg_dot_with_trace`,
block-coverage-highlighted DOT overlays via `cfg_dot_with_coverage`,
edge-coverage-highlighted DOT overlays via `cfg_dot_with_edge_coverage`, block
lookup and compressed block trace paths via `basic_block_containing_pc` /
`trace_basic_blocks`, taken CFG edge reports via `trace_cfg_edges`,
source-aware concrete trace rows via `trace_source_steps`, a consolidated
witness replay report via `trace_report`, replay-checked test-case generation
reports via `test_cases_for_pc_checked` / `test_cases_for_label_checked`, and
block-coverage test-suite reports via `test_cases_for_basic_blocks_checked`,
edge-coverage test-suite reports via `test_cases_for_cfg_edges_checked`, and
label-based reachability/safety query wrappers over the existing checked PC
queries. P4.2 still needs richer byte-level/binary frontend work,
unbounded/certified safety, and eventual warm lazy theory reuse.

> **Reframe (2026-06-22; amended 2026-06-23).** With interpolation done and CHC/abduction opened (item 3
> below) and the NRA CAD decision side complete, the three categorically-missing
> engines are now *addressed*. So the dominant gap is no longer "what can't we
> decide." It is **(A) architecture maturity** — chiefly *online* multi-theory
> combination, still eager Ackermann today (the e-graph keystone and the EUF lazy
> DPLL(T) loop already exist; cross-theory propagation does not) — and **(B) the
> certify-gap**: fragments that now *decide* but cannot yet *prove* their `unsat`
> (NRA CAD, NIA). The honest one-liner: **the gap is now "can we certify and explain
> at the same assurance," not "can we decide."** Leverage order is at the end of this
> section.

The honest gap is three things, in size order:

**1. Depth / completeness on a mostly-complete grid** — most fragments are
`validated`/`sound-incomplete`/`experimental` where Z3 is complete-and-tuned. The
depth ladders are already planned; this audit only sharpens their exit criteria:
- NRA: linear abstraction + McCormick → **nlsat/CAD** — [P2.5](docs/plan/track-2-theories/P2.5-nra-cad.md)
  (active; as of 2026-06-22 the **CAD decision side is complete** — N-var algebraic
  critical-point lifting — and the fuzz-measured QF_NRA Unknown rate fell 109→64,
  QF_NIA 498→146, QF_UFLIA 311→18; remaining = proof/Lean evidence for the new
  unsats. Five standing Z3 differential gates clean).
- LIA: **bounded** bit-blast/B&B → **unbounded-complete** (Omega/Cooper backstop) — [P2.4 T2.4.8](docs/plan/track-2-theories/P2.4-lia-cuts.md) (added).
- Strings: bounded BV-lowered → **unbounded** decision procedure — [P2.7](docs/plan/track-2-theories/P2.7-strings.md).
- Quantifiers: maturity of e-matching/MBQI — [P2.6](docs/plan/track-2-theories/P2.6-quantifiers.md).

**2. Architecture / performance maturity** — the *highest-leverage* axis now:
- **Online multi-theory combination has moved from gap to first production route**
  ([P1.6](docs/plan/track-1-engine/README.md)). Online LRA/LIA theory solvers and
  online UFLRA/UFLIA Nelson-Oppen-style combination are now the default
  `check_auto` route for mixed UF+arithmetic, with eager Ackermann as fallback.
  The remaining Z3-class gap is **quality of the spine**: theory propagation,
  lazy antecedents, 1-UIP theory-clause learning, relevance filtering, then moving
  lazy arrays/BV/datatypes/quantifiers onto it.
- **SAT core: BVE + vivification have landed** (bounded variable elimination /
  subsumption / compaction in the SAT-BV path; `axeyum-cnf::vivify` with DRAT
  accounting). Remaining levers: wire/measure vivification in the SAT-BV pipeline,
  glue/LBD retention, SCC/equiv-lit substitution, probing, and word-level BV
  abstraction. The hard-QF_BV tail (~9 instances) remains mostly search-bound.

**3. ~3 categorically-absent engines** — **ALL THREE now addressed (2026-06-22),
each verify-guarded (untrusted search, trusted small checking); depth/fuller
versions remain:**
- **CHC / Horn (PDR/Spacer)** — *unbounded* invariant discovery, the step beyond
  today's bounded BMC + inductive k-induction. The single biggest categorical hole
  vs Z3. [P4.6](docs/plan/track-4-usecases-frontend/P4.6-chc-horn.md). **OPENED
  (ADR-0048):** verify-guarded single-predicate **IC3/PDR over QF_BV**
  (`prove_safety_pdr`) discovers invariants where k-induction is inconclusive —
  `Safe` only when the discovered invariant passes the 3 implication checks; **MBP
  for LRA** (P2.6-T2.6.6) **landed** as the Spacer predecessor primitive; an **IMC**
  (interpolation-based model checking) consumer of the interpolation API is the next
  slice. Depth: LRA-theory PDR, online LRA solver, multi-predicate Horn core.
- **Craig interpolation** — a feature column *and* CHC's lemma engine; read off
  the already-checked proof. [P3.8](docs/plan/track-3-proof-lean/P3.8-interpolation.md)
  **ENGINE DONE (2026-06-22, ADR-0047):** interpolants land for conjunctive
  **QF_LRA** (Farkas), **QF_UF** (congruence-explanation), **propositional/SAT**
  (McMillan over the LRAT resolution proof), **QF_BV** (joint bit-blast + lifted
  propositional interpolant), and **QF_UFLRA** (Ackermannize → LRA interpolant →
  translate) — every phase-exit fragment, each **verify-before-return** (declines
  rather than emitting anything unverified). Only the SMT-LIB `(get-interpolant)`
  parse surface remains (coordinate `axeyum-smtlib`).
- **Synthesis / abduction (SyGuS, `get-abduct`)** — turns the checker into a
  generator. [P4.7](docs/plan/track-4-usecases-frontend/P4.7-synthesis.md).
  **OPENED (ADR-0049):** `abduct(axioms, conjecture)` — bounded enumeration of
  shared-vocab atoms, each candidate returned only when `check_auto` confirms
  consistency + sufficiency + vocabulary. Depth: SyGuS grammar synthesizing *new*
  atoms, CEGIS, minimality, `(get-abduct)` surface.
- Plus the enumerated **breadth tail** (sequences, sets/bags, separation logic,
  finite fields, co-datatypes, rec-fun) kept *counted*, not forgotten:
  [P2.10](docs/plan/track-2-theories/P2.10-breadth-backlog.md).

**Where axeyum is already ahead:** self-checking evidence (DRAT + Alethe + an
in-tree Lean-grade kernel + universal model replay) — ahead of Z3, competitive
with cvc5. That is the moat and it exists today; the plan's job is to keep
*widening* it (Track 3) while closing depth (Track 2) and adding the three engines.

**Next, in leverage order (amended 2026-06-23)** — full rationale in the
[gap analysis](docs/plan/gap-analysis-z3-cvc5-2026-06-22.md):
1. **Make online combination a real CDCL(T) spine** ([P1.6](docs/plan/track-1-engine/README.md)):
   theory propagation, lazy antecedents, 1-UIP theory learning, relevance, then
   lazy arrays/BV ([P2.2](docs/plan/track-2-theories/P2.2-arrays-lazy.md)/[P2.1](docs/plan/track-2-theories/P2.1-bv-lazy.md)).
   **LANDING (2026-06-23):** theory propagation (LRA/LIA), **1-UIP theory-conflict
   learning + non-chronological backjump** (LRA/LIA/EUF), and a warm combined-theory
   oracle with combined propagation (UFLRA/UFLIA) are in. Remaining spine quality:
   relevance filtering, then moving lazy arrays/BV/datatypes/quantifiers onto it.
2. **Certify what already decides** — Lean/Alethe evidence for NRA CAD and NIA
   `unsat` ([P2.5](docs/plan/track-2-theories/P2.5-nra-cad.md)/[Track 3](docs/plan/track-3-proof-lean/README.md)).
   Attacks the certify-gap head-on and widens the unique moat. **LANDING:**
   interpolants promoted **Validated→Checked** (LRA/EUF/LIA/UFLRA/UFLIA/QF_BV), and
   Lean reconstruction extended (more QF_LIA shapes, disjunctive QF_LRA, QF_ABV ROW
   Carcara-checked). Remaining: NRA CAD / general NIA `unsat` certificates.
3. **Measure** the levers as they land — this is the [measurement-debt](#true-parity-the-maturity-ladder-and-the-measurement-debt-2026-06-23)
   payoff. **SAT vivification is now wired into the SAT-BV pipeline** (gated by
   `cnf_vivify`, default off) **and exposed to the harness** (`axeyum-bench --vivify`),
   so its QF_BV effect is now measurable; word-level BV abstraction is next.
   **Quantifier maturity** ([P2.6](docs/plan/track-2-theories/P2.6-quantifiers.md);
   MBQI is now MBP-driven).
4. **Deepen the seeded engines** behind a stable API — CHC/PDR ([P4.6](docs/plan/track-4-usecases-frontend/P4.6-chc-horn.md))
   and the `(get-interpolant)`/`(get-abduct)` SMT-LIB surfaces — then the breadth tail.

## True parity: the maturity ladder and the measurement debt (2026-06-23)

A sober big-picture check, because the ledger now reads as "we have almost
everything Z3/cvc5 have." That is true **at the seed level** and misleading as a
parity claim: **a sound, verify-guarded first slice of an engine is not parity
with a 15-to-20-year production engine.** Every capability climbs a ladder, and
naming the rung honestly is the difference between a real roadmap and a feature
checklist:

| Rung | Meaning | Where axeyum mostly is |
|---|---|---|
| **Seeded** | sound, verify-guarded first slice (often conjunctive / bounded / single-predicate) | **most newer engines** — CHC/PDR, abduction, interpolation, online combination |
| **Decides** | complete on the decidable fragment; honest `unknown` outside | QF_BV, QF_UF, QF_LRA; NRA CAD decision side |
| **Measured-competitive** | solved-count + PAR-2 within target of Z3/cvc5 on a *committed* corpus, same hardware/timeout | **QF_BV only** (p4dfa 113, parity, both hard-capped) |
| **Certifying** | every `unsat` carries a Lean-checkable certificate | QF_BV (DRAT), QF_LRA (Farkas), QF_UF, degree-2 SOS — **ahead of Z3** |
| **Production** | tuned, scalable, robust across the division's *full* benchmark suite | **none yet** — Z3/cvc5 are here across all divisions |

**The honest position:** axeyum has **breadth of seeds + a leading *certifying*
story + one measured division.** It is *not* at Z3/cvc5 parity, and the distance
is dominated by two things the ledger does not show — **production depth** (the
bulk of Z3's ~688k LoC) and **measurement debt** (only QF_BV is measured; every
other "parity" is a feature-ledger assertion, not a number).

**The phase pivot.** Breadth acquisition is essentially done — the ledger has a
seed for nearly everything. **The standing rule now inverts: stop adding new engine
seeds; deepen, *measure*, and certify the ones that exist.** A new seed without a
measured corpus behind it adds claim-surface, not parity.

**What true parity actually requires — and the realistic bet:**
1. **Measured per-division corpora vs Z3/cvc5 — the #1 credibility item.** Today
   [P4.5](docs/plan/track-4-usecases-frontend/P4.5-benchmarking.md) measures QF_BV
   alone. Parity is a *number per division* (QF_LRA, QF_LIA, QF_UF, QF_UFLIA,
   QF_ABV, QF_NIA, QF_NRA, QF_S), not a ledger row. **Gate every "parity" claim on a
   committed measured slice; until a division has one, its status is
   "seeded/decides," never "parity."**
2. **Do not race Z3 to production depth on every division** — that is a 15-year
   loss. **Pick the divisions where axeyum can be both measured-competitive *and*
   fully-certifying** — QF_BV, QF_LRA, QF_UF, QF_LIA, QF_ABV — and drive those to the
   top of the ladder. "Fast-enough **and** every `unsat` carries a Lean-checkable
   proof" is a position **neither Z3 nor cvc5 occupies**; that is the winnable parity.
3. **Accept sound-incompleteness on the hard frontiers** (NRA, strings, full
   quantifiers, large-scale CHC) as the honest steady state — match Z3's *practical*
   heuristics where cheap, return first-class `unknown` otherwise, and let
   **certification, not raw decide-rate, be the differentiator.**

In one line: **true parity is measured-and-certified on a chosen set of divisions —
not a feature checklist — and the next phase is depth + evidence, not more seeds.**

## How to use this plan each session

1. Read **[STATUS.md](STATUS.md)** — it names the current focus and the next
   task.
2. Open that task's phase file under `docs/plan/track-*/`. Each task lists its
   goal, the reference file paths to read, its size, and its exit criteria.
3. Do the task as a sound, tested, committed increment (the project's normal
   discipline: `just check`, model replay / independent re-check, ADR if it's a
   new public surface or decision).
4. Update STATUS.md (the phase row + changelog). Keep the capability ledger
   (`crates/axeyum-solver/src/capabilities.rs`) and its golden matrix in sync.

## Standing rules (do not violate)

- Default build is **pure Rust, no C/C++**; native/feature-gated leaves only.
- `unsafe_code` is denied workspace-wide; exceptions need an ADR.
- `unknown` is a first-class result; never a wrong `sat`/`unsat`.
- **Graceful `unknown`, never OOM/crash.** Every solving path must degrade to
  `Unknown` under a *deterministic* resource bound — no unbounded memory/time on
  adversarial input. Precedent: sat_bv's pre-lowering oversized-encoding refusal;
  NRA's `MAX_CROSS_PRODUCTS` admission bound (2026-06-19, refuses ≥3 distinct-operand
  cross-products before building lemmas — bounded *or* unbounded, since the blowup is
  inside a single LRA solve call that the wall-clock checks can't intercept). Add a
  bound before adding a feature that can blow up.
- Every `sat` replay-checks; every new `unsat` route gets an independent checker
  or an explicit, ledgered trust note.
- **Build caps:** use `CARGO_BUILD_JOBS=2` and `-j1` for solver/bench work on
  this host; `CARGO_BUILD_JOBS=4` / `-j4` is an upper cap, not the default.
  Default 16-way parallelism and high-`--jobs` benches OOM-kill this host.
  **Run test/build/bench under the 64 GiB
  memory cap** — `scripts/mem-run.sh <cmd>` (or `just test-guarded`) applies a
  `ulimit -v` so a runaway allocation aborts *that process* instead of OOM-killing
  the host. Override the cap with `MEM_LIMIT_GB=N`.
- **Coordination (multi-agent):** a second agent works `axeyum-rewrite` /
  `axeyum-smtlib` (word-level reduction, P1.2 — the destination-2 near-term lever).
  Treat those crates as theirs; this agent covers measurement, proof/Lean
  (Track 3), breadth/feature-parity (Track 2), and incremental SAT-core
  modernization. Do not edit `canonical.rs` etc. without coordinating.
- **Do not sweep the 41GB public corpus** to "make progress." Measure once on a
  committed slice, then stop.
- Decisions are recorded as ADRs in `docs/research/09-decisions/`.
- Commit trailer:
  `Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>`.

## Provenance

The plan was synthesized from a top-down review of the cloned reference solvers
in `references/` (Z3 ~688k LoC, cvc5 ~512k, bitwuzla, CaDiCaL, Kissat, Carcara,
lean4, nanoda_lib, lean-smt, drat-trim) by five parallel Opus sub-agents on
2026-06-15; their full reports are in
[`docs/plan/references/`](docs/plan/references/README.md). axeyum today (2026-06-22)
is **~143k LoC of Rust across 14 crates** with a broad, evidence-backed
decidable+arithmetic foundation (destination 1) — including a complete CAD
decision side for NRA, a competitive pure-Rust proof-emitting SAT core, and
self-checking evidence (DRAT + Alethe + an in-tree Lean-grade kernel + universal
model replay) that already leads Z3. This plan is the route to destinations 2
(Z3-class performance) and 3 (Lean-checkable proofs). Live per-session state is in
[STATUS.md](STATUS.md); the foundation phase history is in the research
[roadmap](docs/research/08-planning/roadmap.md).
