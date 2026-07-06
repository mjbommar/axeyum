# Archived: STATUS changelog entries through 2026-07-02

Archived from STATUS.md by the task-#27 truncation.

- **2026-07-02 (evening)** — **UF+arith model parity, QF_UFLIA at 100%, and the
  hash_sat diagnosis arc.** (`bff67679`) skeleton-only Bool symbols are now
  injected in the UFLIA/UFLRA builders too — UFLIA had been *defaulting them to
  `false`* (a wrong-witness value), UFLRA omitted them; TermId-sorted,
  replay-gated; both z3 fuzzes DISAGREE=0. (`9037baa2`) both residual QF_UFLIA
  divisions re-measured at **100% decided** (6→8/8, 0→2/2, DISAGREE=0, PAR-2
  5.0→0.57 and 20.0→2.29) — movers attributed per-instance to the `3cd6c810`
  deadline threading. (`c3ed7fe8`, `5536ccd5`) the NAS `hash_sat_*` grind was
  measured twice-over: first relocated to the offline lazy-arith loop + the
  CDCL(T) leaf re-search, then the implemented seeding fix *disproved that
  premise honestly* — the committed leaf fails replay on one nested-congruence
  literal (321/322 leaves die the same way); the real lever is
  **congruence-aware model reconstruction** (opaque-app value pinning),
  documented in P1.6 with the cap raise gated behind it. CI-runner test
  hardening en route: frontier ratchets and the dispatch budget-excused cap are
  hardware-relative and now scale/report under `CI=true` (`49534eb2`,
  `f2dbb773`); route traces structurally end in a `Declined` on any early exit
  (`8f29423c`, `570ba82d`).
- **2026-07-02** — **P1.4 reframe + the last honest `#[ignore]` flips green**
  (`86998ea8`): a read-only scoping pass found the e-graph keystone is
  **essentially already built** (hash-cons + backtrackable union-find,
  congruence cascade, proof forest with explain-to-LCA, push/pop, th_vars —
  all in `axeyum-egraph` with an independent `check_congruence` re-validator),
  and the "uninterpreted-sort `ite` SAT" blocker was a **model-assembly
  completeness gap**: skeleton-only Bool symbols (lifted `ite` conditions)
  never entered the built model, so replay failed and the route declined.
  Fixed by injecting DPLL-committed Bool values (TermId-sorted; replay-gated —
  no wrong sat possible); NEW ite/uninterpreted-sort differential fuzz: 1500
  instances, 0 unknowns, DISAGREE=0. Remaining P1.4/P1.5/P1.6 depth re-scoped
  as slices 3-6 (model-assembly parity in UF+arith builders, UFLIA CEGAR
  convergence, UF×NRA interface routing + a new combination fuzz, qinst
  e-matching depth).
- **2026-07-02** — **QF_AX lazy-ext verdicts were hash-order-dependent**
  (`d73e00f1`): `euf_egraph::build_model` assigned uninterpreted-class codes
  while iterating HashMaps (per-process random order), so the same instance
  decided `Sat` ~88% of runs and declined otherwise — the CI flake behind
  `arrays3`. TermId-sorted coding + BTreeMap tables; 200/200 identical
  verdicts; in-suite 64-run determinism guard; abv fuzz DISAGREE=0. Also:
  `lean_crosscheck` parallelized + sliced (`15365a00`, 4 h+ → 14 s default,
  full 157 modules ~16 s via `--ignored`), and the UFLIA combination loop now
  honors `config.timeout` (`3cd6c810`, bug330 >90 s at a 2 s budget → 8.5 s,
  `deadline_honored.rs` regression, uflia fuzz 2500 DISAGREE=0).
- **2026-07-02** — **Strings: 5 gate-downgraded unsats recovered**
  (`a264681a`): a step-1a pure-LIA projection in the gate (drop non-Int
  abstracted assertions on an unknown full solve — sound weakening), exact
  `s = "" ⟺ len = 0` equality facts, and an unbounded-reachability
  regex-emptiness fold (`L(R) = ∅ ⟹ in_re = false`). **Committed re-measure:
  QF_S 48→52 (PAR-2 6.68→5.56), QF_SLIA 11→12, QF_SEQ 26, DISAGREE=0**; 8 new
  regression tests (recovery + must-still-downgrade pairs); the remaining 16
  downgrades are classified per-instance as Phase-B work (regex decision
  procedure, lexicographic reasoning) in ADR-0052's follow-up section. Two
  suggested coarseness relaxations were REJECTED as unsound with written
  arguments (exact-interval `in_re`; packed-seq decode wouldn't move targets).
- **2026-07-02** — **NRA `/0` division witnesses** (`124e18aa`): `Assignment`
  carries a `real_div_zero` interpretation (numerator→quotient) the evaluator
  consults at denominator 0; `check_with_nra` builds it from the elimination
  triples (conflict ⇒ decline). Forced-div-by-zero promotes `unknown → sat`;
  the nra fuzz caught a dropped-witness wrong-sat mid-development (preprocess/
  dispatch_reduced now thread the witness — the gate earned its keep); both
  fuzzes DISAGREE=0. **Committed baseline regenerated: QF_NRA 21/38 decided
  (was 9/38)**, PAR-2 9.19→8.66; SCOREBOARD row refreshed (also absorbing the
  coprime-split + sign-refutation gains that had been route-trace-only).
- **2026-07-02** — **fifo_bc04 un-ignored** (`e67f218f`): root cause was
  `f4575ea5`'s contextual-`ite` equality saturation running at every
  read-congruence probe node (O(dag·ite²) — the FIFO row is small but
  `ite`-dense). Verdict-safe saturation-work gate (probe only declines);
  >600 s → 3.2 s; qfabv/carcara/array_elim suites confirm no certificate lost.
- **2026-07-02** — **Strings re-measured under the ADR-0052 gate**
  (`cf923084`): QF_S 59→48, QF_SLIA 15→11, QF_SEQ 26 unchanged; 23 prior
  `unsat`s now honest `unknown`s, **two on declared-`sat` instances** (real
  wrong verdicts the oracle path never compared — it skips unknowns). The
  9-hour first re-run attempt exposed an exponential per-path skeleton walk in
  the new blast (`f403991b`, memoized; divisions now measure in ~10 min).
- **2026-07-02** — **CI plumbing**: the last red job was runner **disk
  exhaustion** (`878dcffc`: drop test debuginfo + free ~30 GB of preinstalled
  toolsets); then per-ref cancel-in-progress starved every conclusion under
  the two-lane push cadence (`ed4a3f2c`→`5970e6b5`: queue-and-complete, keyed
  by sha). PBLS scope test un-rotted (`377316a8`: Int is in-scope since
  c093fa91; the decline probe moves to Real).

- **2026-07-02** — **Evidence dispatch un-rotted + zero-trust Alethe outranks
  structural certs** (`459ffc41`): hoisted the `zero_trust_alethe_certificate`
  chain above the structural pre-solve hooks (size-gated at 2000 DAG nodes) —
  three shadowed Alethe-evidence tests green again; the stale integer-route
  label updated; honest `#[ignore]`s with tracked follow-ups
  (uninterpreted-sort `ite` SAT → P1.4/P1.5 keystone; `fifo_bc04` perf
  regression). Evidence suite: 66/0/2-ignored in ~14 s.
- **2026-07-02** — **Exponential evidence walk fixed** (`0bc133c2`):
  `set_cardinality`'s `collect_bitvec_terms` walked the term DAG per-path (no
  visited set) — FP rows ground for 8+ hours in `produce_evidence` while plain
  `solve` took 2 ms; introduced 2026-06-26 with the module, it had been
  stalling every full-suite run and CI test job since. Visited-set fix; the
  qf_fp/qf_bvfp evidence tests drop to ~3 s.
- **2026-07-02** — **CI repaired after 198 consecutive red runs** (`0d10aeba`):
  MSRV 1.85→1.88 (let-chains, verified `cargo +1.88.0 check --workspace`
  clean), axeyum-ir rustdoc links + test clippy, 11 files formatted,
  `euf_egraph` generous-budget flake 60 s→600 s, cargo-deny
  `allow-wildcard-paths` (path deps flagged by newer cargo-deny).
- **2026-07-01** — **NRA coprime-split CAD projection** (`98719094`): the
  measured dominant CAD decline was a shared-factor `Res ≡ 0`, not a cap;
  McCallum-style coprime splitting at every projection level. **Curated QF_NRA
  13→20 decided by route-trace** (sat 6→9, unsat 7→11), all matching declared
  `:status` (the committed-baseline confirmation landed later with `124e18aa`:
  QF_NRA 21/38);
  `nra`+`nia` differential fuzzes DISAGREE=0.
- **2026-07-01** — **P2.7 A.2 landed: the `len`↔LIA link + bounded-string
  `unsat` gate** (`50a9fb8b`, ADR-0052): `bv2nat`-linear→BV equivalence blast
  (both directions decide, DRAT-carrying); parser-built unbounded length
  abstraction (`len(x++y)=len(x)+len(y)`, atom→`fresh_bool ∧ fact` relaxation,
  regex match-length intervals, `substr`-family facts); every front-door
  `unsat` on a bounded-string script confirmed bound-independent or downgraded
  to honest `unknown` (`solve_smtlib` family, `get-proof`, `unsat-core`, and
  the bench harness). **Gap-10 (`str.len`-unsat) decides**, and a **measured
  pre-existing wrong-unsat class vs Z3 was repaired** (`len(s)=9`/`=100`,
  pinned cross-width `prefixof`, long-forcing regex, symbolic over-bound
  `substr`, the lexicographic gap `"aaaaaaaa" < s < "aaaaaaab"`) — 10
  regression tests; `string_differential_fuzz` DISAGREE=0 over 900 instances
  with the generator extended past the bound. QF_S scoreboard re-run pending
  (verdicts changed).
- **2026-07-01** — **Finite-gradient-descent descent-bound row landed.**
  Added a source-linked checked QF_LRA/Farkas refutation for the malformed
  descent-bound slack row in
  [`artifacts/examples/math/finite-gradient-descent-v0/`](artifacts/examples/math/finite-gradient-descent-v0/).
  Exact replay computes descent slack `1/4`, while the bad row claims the same
  slack is nonpositive; the route regression now parses the new SMT-LIB
  artifact and checks `UnsatFarkas` evidence.

- **2026-07-01** — **Finite-active-set inactive-slack row landed.**
  Added a source-linked checked QF_LRA/Farkas refutation for the malformed
  inactive lower-bound slack row in
  [`artifacts/examples/math/finite-active-set-qp-v0/`](artifacts/examples/math/finite-active-set-qp-v0/).
  Exact active-face replay computes slack `0 - (-1) = 1`, while the bad row
  claims the same slack is nonpositive; the route regression now parses the new
  SMT-LIB artifact and checks `UnsatFarkas` evidence.

- **2026-07-01** — **Finite-active-set degenerate multiplier row landed.**
  Added a degenerate active-bound witness, replay row, checked
  QF_LRA/Farkas SMT-LIB artifact, validator logic, and
  `math_resource_lra_routes` regression to
  [`artifacts/examples/math/finite-active-set-qp-v0/`](artifacts/examples/math/finite-active-set-qp-v0/).
  Exact replay keeps the tight bound and zero multiplier distinct from general
  active-set degeneracy theory, while the malformed positive multiplier is now
  rejected by checked `UnsatFarkas` evidence.

- **2026-07-01** — **Dynamics query guide landed.**
  Added
  [`docs/foundational-resources/DYNAMICS-QUERIES.md`](docs/foundational-resources/DYNAMICS-QUERIES.md)
  as the focused consumer guide for finite differential-equations and
  dynamical-systems resources. It records concept-scoped and pack-scoped
  Farkas queries for finite recurrences, transition/invariant rows, explicit
  Euler rows, stochastic kernels, finite Markov chains, hitting-time equations,
  and calculus shadow prerequisites. Updated PLAN, buildout docs, consumer
  indexes, and the foundational-resource smoke check while keeping continuous
  ODE/PDE theory, flow/stability/bifurcation, chaos/ergodic theory, Euler
  convergence, stochastic-process limits, continuous-time Markov processes,
  numerical stability, and floating-point claims in the horizon lanes.

- **2026-07-01** — **Measure-theory query guide landed.**
  Added
  [`docs/foundational-resources/MEASURE-THEORY-QUERIES.md`](docs/foundational-resources/MEASURE-THEORY-QUERIES.md)
  as the focused consumer guide for finite measure resources. It records
  concept-scoped Farkas queries for finite measure additivity,
  product/integration, pushforward, conditional expectation, stochastic
  kernels, and tail/concentration rows, plus pack-scoped drills for finite
  measure, monotonicity/subadditivity, product measures, simple integration,
  martingales, hitting times, kernels, and concentration examples. Updated
  PLAN, buildout docs, consumer indexes, and the foundational-resource smoke
  check.

- **2026-07-01** — **Foundations/discrete query guide landed.**
  Added
  [`docs/foundational-resources/FOUNDATIONS-DISCRETE-QUERIES.md`](docs/foundational-resources/FOUNDATIONS-DISCRETE-QUERIES.md)
  as the focused consumer guide for logic/proof, set-theory/foundations, and
  discrete-math resources. It records Boolean queries for proof/CNF and
  refutation rows, Alethe queries for finite quantifier, partition, quotient,
  and relation/function rows, Diophantine/LIA queries for finite counting and
  bounded induction rows, plus checked finite cardinality and Boolean-algebra
  drills. Updated PLAN, buildout docs, consumer indexes, and the
  foundational-resource smoke check.

- **2026-07-01** — **Analysis/numerical query guide landed.**
  Added
  [`docs/foundational-resources/ANALYSIS-NUMERICAL-QUERIES.md`](docs/foundational-resources/ANALYSIS-NUMERICAL-QUERIES.md)
  as the focused consumer guide for real-analysis, numerical-analysis, and
  complex-analysis resources. It records concept-scoped Farkas queries for
  metric balls, bounded epsilon-delta rows, finite dynamics/Euler rows,
  residual rows, exact-vs-floating rows, and complex real-pair transforms,
  plus pack-scoped drills for algebraic derivative, integral, root-finding,
  sequence, Euler, and complex examples. Updated PLAN, buildout docs, consumer
  indexes, and the foundational-resource smoke check.

- **2026-07-01** — **Functional/operator query guide landed.**
  Added
  [`docs/foundational-resources/FUNCTIONAL-OPERATOR-QUERIES.md`](docs/foundational-resources/FUNCTIONAL-OPERATOR-QUERIES.md)
  as the focused consumer guide for finite functional-analysis/operator
  resources. It records concept-scoped Farkas queries for operator/Chebyshev,
  eigenpair/Rayleigh, and inner-product/projection rows, plus Alethe queries
  for finite dual/tensor equality rows and pack-scoped drills for the current
  functional/operator examples. Updated PLAN, buildout docs, consumer indexes,
  and the foundational-resource smoke check.

- **2026-07-01** — **Optimization/convexity query guide landed.**
  Added
  [`docs/foundational-resources/OPTIMIZATION-CONVEXITY-QUERIES.md`](docs/foundational-resources/OPTIMIZATION-CONVEXITY-QUERIES.md)
  as the focused consumer guide for finite optimization resources. It records
  concept-scoped Farkas queries for LP objectives, rational convexity shadows,
  projection/residual rows, and exact-vs-floating boundaries, plus pack-scoped
  drills for KKT, active-set QP, SDP, gradient descent, Armijo/Wolfe line
  search, projected gradient, and proximal gradient rows. Updated PLAN,
  buildout docs, consumer indexes, and the foundational-resource smoke check.

- **2026-06-30** — **Math curriculum detailed build ledger landed.**
  Added
  [`docs/foundational-resources/MATH-CURRICULUM-DETAILED-BUILD-PLAN.md`](docs/foundational-resources/MATH-CURRICULUM-DETAILED-BUILD-PLAN.md)
  as the execution-grade plan for the current math-resource surface. It records
  the then-current 84-pack baseline, R0-R6 gates, build waves, the
  unclassified solver-reuse queue, field and curriculum-node ledgers, validation commands,
  and the first next increment: source-linked `PHP(3,2)` CNF/DRAT/LRAT
  promotions for `proof-methods-refutation-v0` and `counting-v0`.

- **2026-06-30** — **Solver-reuse disposition audit landed.**
  Added
  [`docs/foundational-resources/generated/solver-reuse-disposition-audit.md`](docs/foundational-resources/generated/solver-reuse-disposition-audit.md)
  from pack metadata, wired it into `check-foundational-resources`, and updated
  the curriculum buildout docs. The audit reports 84 promoted solver-reuse
  packs, 0 non-benchmark-horizon packs, and 0 unclassified packs.

- **2026-06-30** — **Probability/statistics bridge concepts landed.**
  Added generated bridge-concept rows for finite probability mass tables,
  pushforward distributions, stochastic kernels, conditional expectation, and
  tail/count obstructions. Regenerated the ontology and field dashboard; the
  foundational concept atlas then validated at 70 rows: 23 curriculum rows,
  18 field rows, 27 bridge rows, and 2 example-family rows.

- **2026-06-30** — **Proof/logic bridge concepts landed.**
  Added generated bridge-concept rows for refutation-as-query, finite
  proof-pattern replay, finite quantifier expansion, and bounded induction
  obligations. Regenerated the ontology and field dashboard; the foundational
  concept atlas then validated at 74 rows: 23 curriculum rows, 18 field rows,
  31 bridge rows, and 2 example-family rows.

- **2026-06-30** — **Proof-object anatomy bridge concepts landed.**
  Added generated bridge-concept rows for Boolean CNF DRAT/LRAT anatomy,
  QF_LRA Farkas certificate anatomy, QF_UF Alethe certificate anatomy, and
  QF_BV bit-blast certificate anatomy. Regenerated the ontology and dashboards;
  the foundational concept atlas now validates at 78 rows: 23 curriculum rows,
  18 field rows, 35 bridge rows, and 2 example-family rows.

- **2026-06-30** — **Set/foundations bridge concepts landed.**
  Added generated bridge-concept rows for finite Boolean algebra, finite
  partition/relation roundtrips, finite image/preimage/inverse tables, finite
  bijection/cardinality, and cardinality theorem horizons. Regenerated the
  ontology and dashboards; the foundational concept atlas now validates at
  83 rows: 23 curriculum rows, 18 field rows, 40 bridge rows, and 2
  example-family rows.

- **2026-06-30** — **Standalone finite topology and finite measure lessons landed.**
  Added
  [`finite-topology-end-to-end.md`](docs/learn/math/finite-topology-end-to-end.md)
  and
  [`finite-measure-end-to-end.md`](docs/learn/math/finite-measure-end-to-end.md)
  as focused first-principles learner pages for `finite-topology-v0` and
  `finite-measure-v0`. Updated the learner index and topology/probability
  cluster pages so the existing combined topology/measure page is a bridge
  rather than the only entry point.

- **2026-06-30** — **Standalone linear optimization lesson landed.**
  Added
  [`linear-optimization-end-to-end.md`](docs/learn/math/linear-optimization-end-to-end.md)
  as the focused first-principles learner page for `linear-optimization-v0`.
  Updated the learner index plus rational/real and linear-algebra cluster pages
  so the combined linear-system/LP page is a bridge rather than the only LP
  entry point.

- **2026-06-30** — **Standalone finite probability mass-table lesson landed.**
  Added
  [`finite-probability-mass-tables-end-to-end.md`](docs/learn/math/finite-probability-mass-tables-end-to-end.md)
  as the focused first-principles learner page for `finite-probability-v0`.
  Updated the learner index and probability/statistics cluster page so the
  broad finite-probability process page is a bridge rather than the only
  probability entry point.

- **2026-06-30** — **Curriculum field-readiness consumer query landed.**
  Extended
  [`query-foundational-resources.py`](scripts/query-foundational-resources.py)
  with a `fields` command that summarizes pack counts, check counts,
  proof-status counts, proof-cookbook route counts, solver-reuse statuses,
  sample packs, and Lean-horizon packs per math field from the committed JSON
  contract. Updated
  [`CONSUMER-QUERIES.md`](docs/foundational-resources/CONSUMER-QUERIES.md) and
  the foundational-resource smoke check so consumer examples now cover
  field-level curriculum readiness as well as pack/check/concept mining.

- **2026-06-30** — **Dynamics field-readiness consumer query landed.**
  Added a
  `differential_equations_and_dynamical_systems` plus Farkas field-readiness
  example and checked-row drill-down to
  [`CONSUMER-QUERIES.md`](docs/foundational-resources/CONSUMER-QUERIES.md).
  The foundational-resource smoke check now covers this dynamics/Farkas lane
  alongside the probability/Farkas field summary, making the recent
  bounded-dynamics, finite-Euler, stochastic-kernel, and hitting-time resources
  visible through the public JSON consumer boundary.

- **2026-06-30** — **Measure-theory bridge concepts landed.**
  Extended
  [`gen-foundational-concepts.py`](scripts/gen-foundational-concepts.py) with
  `bridge_finite_measure_additivity` and
  `bridge_finite_product_integration`. The generated atlas now validates 92
  concept rows: 23 curriculum rows, 18 field rows, 46 bridge rows, and 5
  example-family rows. Measure-theory field queries now expose finite
  event-algebra/additivity, complement, product-table, marginal,
  finite Fubini-style sum, and simple-function integral replay slices while
  keeping Lebesgue, convergence-theorem, product-measure existence, and
  almost-everywhere claims in the Lean-horizon lane.

- **2026-06-30** — **Measure-theory field-readiness consumer query landed.**
  Added measure/Farkas field readiness, measure bridge concept lookup, and
  checked measure-theory Farkas row drill-down examples to
  [`CONSUMER-QUERIES.md`](docs/foundational-resources/CONSUMER-QUERIES.md).
  The foundational-resource smoke check now runs those queries alongside the
  probability/Farkas and dynamics/Farkas examples, making finite measure,
  product-measure, integration, random-variable, conditional-expectation,
  martingale, kernel, hitting-time, and concentration resources visible through
  the public JSON consumer boundary.

- **2026-06-30** — **Optimization/convexity bridge concepts landed.**
  Extended
  [`gen-foundational-concepts.py`](scripts/gen-foundational-concepts.py) with
  `bridge_lp_objective_farkas` and
  `bridge_rational_convexity_shadow`. The generated atlas now validates 94
  concept rows: 23 curriculum rows, 18 field rows, 48 bridge rows, and 5
  example-family rows. Optimization/convexity field queries now expose exact LP
  feasibility, objective-threshold Farkas replay, finite midpoint/Jensen
  shadows, affine monotonicity, gradient replay, Hessian-minor witnesses, and
  least-squares normal-equation replay, with finite KKT
  stationarity/complementarity replay now added while KKT sufficiency, duality,
  SDP, and convergence claims stay in the Lean-horizon lane.

- **2026-06-30** — **Optimization/convexity field-readiness consumer query landed.**
  Added optimization/Farkas field readiness, LP-objective and convexity bridge
  concept lookup, and checked optimization/convexity Farkas row drill-down
  examples to
  [`CONSUMER-QUERIES.md`](docs/foundational-resources/CONSUMER-QUERIES.md).
  The foundational-resource smoke check now runs those queries alongside the
  probability/Farkas, dynamics/Farkas, and measure/Farkas examples, making exact
  LP thresholds, finite convexity shadows, least-squares normal equations,
  gradient/Hessian replay, residual bounds, eigenpair, and related matrix
  witnesses visible through the public JSON consumer boundary.

- **2026-06-30** — **Finite recurrence prefix resource landed.**
  Added
  [`finite-recurrence-prefix-v0`](artifacts/examples/math/finite-recurrence-prefix-v0/README.md)
  and
  [`finite-recurrence-prefix-end-to-end.md`](docs/learn/math/finite-recurrence-prefix-end-to-end.md)
  as the next sequences/discrete/linear-algebra bridge. The pack validates
  Fibonacci prefix replay, affine recurrence replay, companion-matrix state
  replay, a source-linked checked QF_LRA/Farkas rejection for a false
  Fibonacci value, and a recurrence-theory Lean-horizon row. At that point, the
  math resource surface had 89 promoted non-template packs, 447 checks, 209
  checked rows, 186 replay-only rows, and 52 Lean-horizon rows.

- **2026-06-30** — **Bounded monotone sequence resource landed.**
  Added
  [`bounded-monotone-sequence-v0`](artifacts/examples/math/bounded-monotone-sequence-v0/README.md)
  and
  [`bounded-monotone-sequence-end-to-end.md`](docs/learn/math/bounded-monotone-sequence-end-to-end.md)
  as the next sequences-and-limits bridge. The pack validates exact rational
  monotone-prefix replay, finite prefix supremum replay, finite tail-gap
  replay, a source-linked checked QF_LRA/Farkas rejection for a false
  upper-bound claim, and a monotone-convergence Lean-horizon row. The math
  resource surface now has 88 promoted non-template packs, 442 checks, 208
  checked rows, 183 replay-only rows, and 51 Lean-horizon rows.

- **2026-06-30** — **Finite measure monotonicity resource landed.**
  Added
  [`finite-measure-monotonicity-v0`](artifacts/examples/math/finite-measure-monotonicity-v0/README.md)
  and
  [`finite-measure-monotonicity-end-to-end.md`](docs/learn/math/finite-measure-monotonicity-end-to-end.md)
  as the next finite measure-theory bridge. The pack validates normalized
  finite measure-table replay, subset monotonicity, finite union
  subadditivity, a source-linked checked QF_LRA/Farkas rejection for a false
  subset-measure claim, and a convergence/countable-measure Lean-horizon row.
  The math resource surface then had 87 promoted non-template packs, 437 checks,
  207 checked rows, 180 replay-only rows, and 50 Lean-horizon rows.

- **2026-06-30** — **Rigid configuration geometry resource landed.**
  Added
  [`rigid-configuration-geometry-v0`](artifacts/examples/math/rigid-configuration-geometry-v0/README.md)
  and
  [`rigid-configuration-geometry-end-to-end.md`](docs/learn/math/rigid-configuration-geometry-end-to-end.md)
  as the next exact geometry bridge. The pack validates triangle
  distance-table replay, translation isometry replay, congruent-triangle
  distance replay, a source-linked checked QF_LRA/Farkas rejection for a false
  distance-table claim, and a graph-rigidity/rigid-motion-classification Lean-horizon
  row. The math resource surface then had 86 promoted non-template packs and the
  geometry field has five focused learner-linked packs.

- **2026-06-30** — **Incidence geometry resource landed.**
  Added
  [`incidence-geometry-v0`](artifacts/examples/math/incidence-geometry-v0/README.md)
  and
  [`incidence-geometry-end-to-end.md`](docs/learn/math/incidence-geometry-end-to-end.md)
  as the next exact geometry bridge. The pack validates line-equation replay,
  non-parallel line intersection, point-on-line replay, a source-linked checked
  QF_LRA/Farkas rejection for false intersection-coordinate and incidence
  claims, and a
  projective/synthetic geometry Lean-horizon row. It establishes the
  line-incidence bridge that later finite-geometry resources build on.

- **2026-06-30** — **Geometry and complex bridge concepts landed.**
  Extended
  [`gen-foundational-concepts.py`](scripts/gen-foundational-concepts.py) with
  `bridge_coordinate_orientation_geometry` and
  `bridge_complex_real_pair_transform`. The generated atlas now validates 88
  concept rows: 23 curriculum rows, 18 field rows, 42 bridge rows, and 5
  example-family rows. Geometry and complex-analysis field queries now expose
  the finite coordinate/affine/oriented-area and complex real-pair transform
  replay slices while keeping synthetic, differential, global, and analytic
  theorem claims in the Lean-horizon lane.

- **2026-06-30** — **Functional-analysis bridge concepts landed.**
  Extended
  [`gen-foundational-concepts.py`](scripts/gen-foundational-concepts.py) with
  `bridge_inner_product_projection` and
  `bridge_finite_operator_chebyshev`. That increment raised the generated
  atlas to 90 concept rows: 23 curriculum rows, 18 field rows, 44 bridge rows,
  and 5 example-family rows. Functional-analysis field queries now expose finite
  Gram/projection, operator-bound, Chebyshev recurrence, interpolation, and
  alternating-residual replay slices while keeping Banach, Hilbert,
  compact-operator, minimax, and infinite-dimensional approximation theorem
  claims in the Lean-horizon lane.

- **2026-06-30** — **Authorization-policy rules/law pack landed.**
  Added
  [`authorization-policy-v0`](docs/rules-as-code/examples/authorization-policy-v0/README.md)
  as the second rules-as-code resource pack, with cited source policy, bounded
  model, expected-result JSON, replayed version-delta witnesses, and checked
  Bool/QF_LIA fixtures for tenant isolation, explicit deny precedence, admin
  tenant guarding, and bounded implementation equivalence. Generalized
  [`validate-rules-as-code.py`](scripts/validate-rules-as-code.py) to discover
  multiple packs and validate pack-specific finite replay. Extended
  [`rules_as_code_examples`](crates/axeyum-solver/tests/rules_as_code_examples.rs)
  with the four authorization proof-route regressions.

- **2026-06-30** — **Boolean CNF/LRAT example-family row landed.**
  Added generated `family_boolean_cnf_lrat` atlas row grouping recurring finite
  Boolean refutations across logic, proof-method, counting, finite-set,
  finite-cardinality, graph, finite-predicate, and finite-topology packs. The
  family is backed by the shared
  `cargo test -p axeyum-cnf --test math_resource_boolean_routes` regression and
  raises the atlas to 84 rows: 23 curriculum rows, 18 field rows, 40 bridge
  rows, and 3 example-family rows.

- **2026-06-30** — **Integer Diophantine example-family row landed.**
  Added generated `family_integer_diophantine` atlas row grouping recurring
  integer equalities, count contradictions, coefficient obstructions, bounded
  arithmetic claims, and checked arithmetic-evidence rows. The family is backed by
  `cargo test -p axeyum-solver --test math_resource_lia_routes` across modular
  arithmetic, gcd/Bezout, integer/natural arithmetic, induction, cardinality,
  generating functions, polynomial identities, statistics, finite homology,
  and graph-search runtime packs, raising the atlas to 85 rows: 23 curriculum
  rows, 18 field rows, 40 bridge rows, and 4 example-family rows.

- **2026-06-30** — **Fixed-width QF_BV/DRAT example-family row landed.**
  Added generated `family_fixed_width_bv_drat` atlas row grouping fixed-width
  finite algebra, residue, and one-bit graph contradictions. The family is
  backed by `cargo test -p axeyum-solver --test math_resource_bv_routes`
  across finite fields, finite rings, graph coloring, and bounded
  number-theory residue packs, raising the atlas to 86 rows: 23 curriculum
  rows, 18 field rows, 40 bridge rows, and 5 example-family rows.

- **2026-06-30** — **Finite-operator end-to-end lesson landed.**
  Added
  [`finite-operator-end-to-end.md`](docs/learn/math/finite-operator-end-to-end.md)
  to split exact finite-dimensional norm replay, row-sum operator-bound replay,
  finite Chebyshev recurrence replay, checked QF_LRA/Farkas bad-bound
  evidence, and the Banach/Hilbert/compact-operator Lean horizon out of the
  broad bounded-dynamics/operator bridge.

- **2026-06-30** — **Bounded-dynamics end-to-end lesson landed.**
  Added
  [`bounded-dynamics-end-to-end.md`](docs/learn/math/bounded-dynamics-end-to-end.md)
  to split exact recurrence trace replay, finite invariant checking, threshold
  reachability, checked QF_LRA/Farkas bad invariant-bound evidence, and the
  continuous-dynamics/ODE Lean horizon out of the combined finite
  dynamics/Euler bridge.

- **2026-06-30** — **Finite-Euler-method end-to-end lesson landed.**
  Added
  [`finite-euler-method-end-to-end.md`](docs/learn/math/finite-euler-method-end-to-end.md)
  to split exact explicit-Euler transition replay, finite polynomial-solution
  error tables, monotone invariant checking, checked QF_LRA/Farkas bad
  max-error plus bad-step evidence, and the ODE/numerical-analysis Lean horizon out of the combined
  finite dynamics/Euler bridge.

- **2026-06-30** — **PHP Bool/CNF resource promotion landed.**
  Added source-level DIMACS artifacts for
  `proof-methods-refutation-v0` and `counting-v0` `PHP(3,2)` rows and wired
  both into `crates/axeyum-cnf/tests/math_resource_boolean_routes.rs`. The
  route regression now emits DRAT, elaborates LRAT, and independently checks
  both certificates for the two PHP artifacts. The packs now carry promoted
  `solver_reuse` metadata, and generated dashboards report 66 promoted
  solver-reuse packs with 18 still unclassified.

- **2026-06-30** — **Replay-only solver-reuse classification batch landed.**
  Marked `bounded-dynamics-v0`, `complex-algebraic-v0`,
  `coordinate-geometry-v0`, `finite-measure-v0`, `finite-operator-v0`, and
  `finite-topology-v0` as explicit `non-benchmark-horizon` solver-reuse packs.
  At that point these rows remained learner-facing finite replay examples
  until they gained negative, certificate-bearing source artifacts; generated
  dashboards reported 66 promoted, 6 non-benchmark-horizon, and 12
  unclassified packs.

- **2026-06-30** — **Generating-functions QF_LIA promotion landed.**
  Added
  `artifacts/examples/math/generating-functions-v0/smt2/bad-cauchy-product-diophantine-conflict.smt2`
  for the bad finite Cauchy-product coefficient row and wired it into
  `math_resource_lia_routes`. The pack metadata now marks `solver_reuse.status`
  as `promoted`, the expected row records the checked `UnsatDiophantine`
  certificate path, and generated dashboards report 67 promoted,
  6 non-benchmark-horizon, and 11 unclassified packs.

- **2026-06-30** — **Polynomial-identities QF_LIA promotion landed.**
  Added
  `artifacts/examples/math/polynomial-identities-v0/smt2/false-rational-root-diophantine-conflict.smt2`
  for the false rational-root row and wired it into `math_resource_lia_routes`.
  The pack metadata now marks `solver_reuse.status` as `promoted`, the expected
  row records the checked `UnsatDiophantine` certificate path, and generated
  dashboards report 68 promoted, 6 non-benchmark-horizon, and 10 unclassified
  packs.

- **2026-06-30** — **Finite-predicate Bool/CNF promotion landed.**
  Added
  `artifacts/examples/math/finite-predicate-v0/cnf/forall-implies-exists.cnf`
  for the finite quantifier-expansion no-counterexample row and wired it into
  `math_resource_boolean_routes`. The pack metadata now marks
  `solver_reuse.status` as `promoted`, the expected row records the checked
  DRAT/LRAT certificate path, and generated dashboards report 69 promoted,
  6 non-benchmark-horizon, and 9 unclassified packs.

- **2026-06-30** — **Calculus Riemann-sum QF_LRA promotion landed.**
  Added
  `artifacts/examples/math/calculus-riemann-sum-v0/smt2/false-integral-farkas-conflict.smt2`
  for the false exact-integral row and wired it into `math_resource_lra_routes`.
  The pack metadata now marks `solver_reuse.status` as `promoted`, the expected
  row records the checked `UnsatFarkas` certificate path, and generated
  dashboards report 70 promoted, 6 non-benchmark-horizon, and 8 unclassified
  packs.

- **2026-06-30** — **Sequence-limit QF_LRA promotion landed.**
  Added
  `artifacts/examples/math/sequence-limit-shadow-v0/smt2/bounded-cauchy-tail-farkas-conflict.smt2`
  for the bounded Cauchy-tail no-counterexample row and wired it into
  `math_resource_lra_routes`. The pack metadata now marks
  `solver_reuse.status` as `promoted`, the expected row records the checked
  `UnsatFarkas` certificate path, and generated dashboards report 71 promoted,
  6 non-benchmark-horizon, and 7 unclassified packs.

- **2026-06-30** — **Multivariable-calculus QF_LRA promotion landed.**
  Added
  `artifacts/examples/math/multivariable-calculus-rational-v0/smt2/bad-gradient-farkas-conflict.smt2`
  for the bad-gradient row and wired it into `math_resource_lra_routes`. The
  pack metadata now marks `solver_reuse.status` as `promoted`, the expected row
  records the checked `UnsatFarkas` certificate path, and generated dashboards
  report 72 promoted, 6 non-benchmark-horizon, and 6 unclassified packs.

- **2026-06-30** — **Calculus-algebraic QF_LRA promotion landed.**
  Added
  `artifacts/examples/math/calculus-algebraic-shadow-v0/smt2/false-derivative-farkas-conflict.smt2`
  for the false derivative-value row and wired it into
  `math_resource_lra_routes`. The pack metadata now marks
  `solver_reuse.status` as `promoted`, the expected row records the checked
  `UnsatFarkas` certificate path, and generated dashboards report 73 promoted,
  6 non-benchmark-horizon, and 5 unclassified packs.

- **2026-06-30** — **Complex-plane QF_LRA promotion landed.**
  Added
  `artifacts/examples/math/complex-plane-transforms-v0/smt2/bad-unit-square-real-part-farkas-conflict.smt2`
  for the bad unit-square real-part row and wired it into
  `math_resource_lra_routes`. The pack metadata now marks
  `solver_reuse.status` as `promoted`, the expected row records the checked
  `UnsatFarkas` certificate path, and generated dashboards report 74 promoted,
  6 non-benchmark-horizon, and 4 unclassified packs.

- **2026-06-30** — **Induction-obligations QF_LIA promotion landed.**
  Added
  `artifacts/examples/math/induction-obligations-v0/smt2/bounded-step-counterexample-count-lia-conflict.smt2`
  for the bounded bad-step count row and wired it into
  `math_resource_lia_routes`. The pack metadata now marks
  `solver_reuse.status` as `promoted`, the expected row records the checked
  arithmetic-evidence path, and generated dashboards report 75
  promoted, 6 non-benchmark-horizon, and 3 unclassified packs.

- **2026-06-30** — **Cardinality-principles QF_LIA promotion landed.**
  Added
  `artifacts/examples/math/cardinality-principles-v0/smt2/overlap-additivity-diophantine-conflict.smt2`
  for the overlapping-set false additivity count row and wired it into
  `math_resource_lia_routes`. The pack metadata now marks
  `solver_reuse.status` as `promoted`, the expected row records the checked
  `UnsatDiophantine` certificate path, and generated dashboards report 76
  promoted, 6 non-benchmark-horizon, and 2 unclassified packs.

- **2026-06-30** — **Polynomial-factorization QF_LRA promotion landed.**
  Added
  `artifacts/examples/math/polynomial-factorization-rational-v0/smt2/irreducible-quadratic-discriminant-farkas-conflict.smt2`
  for the fixed irreducible-quadratic discriminant row and wired it into
  `math_resource_lra_routes`. The pack metadata now marks
  `solver_reuse.status` as `promoted`, the expected row records the checked
  `UnsatFarkas` certificate path, and generated dashboards report 77 promoted,
  6 non-benchmark-horizon, and 1 unclassified pack.

- **2026-06-30** — **Real-algebra RCF-shadow QF_LRA promotion landed.**
  Added
  `artifacts/examples/math/reals-rcf-shadow-v0/smt2/negative-discriminant-farkas-conflict.smt2`
  for the fixed negative-discriminant no-real-root row and wired it into
  `math_resource_lra_routes`. The pack metadata now marks
  `solver_reuse.status` as `promoted`, the expected row records the checked
  `UnsatFarkas` certificate path, and generated dashboards report 78 promoted,
  6 non-benchmark-horizon, and 0 unclassified packs.

- **2026-06-30** — **Finite-measure QF_LRA promotion landed.** Added
  `artifacts/examples/math/finite-measure-v0/smt2/bad-complement-measure-farkas-conflict.smt2`
  for the bad complement-measure row and wired it into `math_resource_lra_routes`.
  The pack metadata now marks `solver_reuse.status` as `promoted`, the expected
  row records the checked `UnsatFarkas` certificate path, and generated
  dashboards then reported 79 promoted, 5 non-benchmark-horizon, and 0 unclassified
  packs.

- **2026-06-30** — **Finite-topology Bool/CNF promotion landed.** Added
  `artifacts/examples/math/finite-topology-v0/cnf/bad-empty-open-rejected.cnf`
  for the bad empty-open row and wired it into `math_resource_boolean_routes`.
  The pack metadata now marks `solver_reuse.status` as `promoted`, the expected
  row records the checked DRAT/LRAT certificate path, and generated dashboards
  then reported 80 promoted, 4 non-benchmark-horizon, and 0 unclassified packs.

- **2026-06-30** — **Coordinate-geometry QF_LRA promotion landed.** Added
  `artifacts/examples/math/coordinate-geometry-v0/smt2/bad-distance-squared-farkas-conflict.smt2`
  for the bad squared-distance row and wired it into `math_resource_lra_routes`.
  The pack metadata now marks `solver_reuse.status` as `promoted`, the expected
  row records the checked `UnsatFarkas` certificate path, and generated
  dashboards then reported 81 promoted, 2 non-benchmark-horizon, and 0 unclassified
  packs.

- **2026-06-30** — **Finite-operator QF_LRA promotion landed.** Added
  `artifacts/examples/math/finite-operator-v0/smt2/bad-operator-bound-farkas-conflict.smt2`
  for the bad operator-bound row and wired it into `math_resource_lra_routes`.
  The pack metadata now marks `solver_reuse.status` as `promoted`, the expected
  row records the checked `UnsatFarkas` certificate path, and generated
  dashboards then reported 82 promoted, 2 non-benchmark-horizon, and 0 unclassified
  packs.

- **2026-06-30** — **Complex-algebraic QF_LRA promotion landed.** Added
  `artifacts/examples/math/complex-algebraic-v0/smt2/bad-norm-squared-farkas-conflict.smt2`
  for the bad norm-squared row and wired it into `math_resource_lra_routes`.
  The pack metadata now marks `solver_reuse.status` as `promoted`, the expected
  row records the checked `UnsatFarkas` certificate path, and generated
  dashboards report 83 promoted, 1 non-benchmark-horizon, and 0 unclassified
  packs.

- **2026-06-29** — **Proof-cookbook math-example route sections landed.**
  Added `Math Examples Using This Route` sections to the six active proof
  recipes for Boolean CNF/LRAT, QF_BV bit-blast, QF_LIA/Diophantine,
  QF_LRA/Farkas, QF_UF/Alethe, and Lean horizons. Each section now points to
  concrete foundational math packs and the relevant route regression, so the
  cookbook links proof mechanics back to curriculum resources without
  overclaiming theorem-level coverage.

- **2026-06-29** — **Algebra-map bridge concepts landed.**
  Added generated bridge-concept rows for
  `bridge_homomorphism_preservation`, `bridge_kernel_image`,
  `bridge_quotient_map`, `bridge_ideal_closure`, `bridge_module_action`,
  `bridge_tensor_bilinearity`, and `bridge_group_action`. The foundational
  concept atlas now validates at 65 rows: 23 curriculum rows, 18 field rows,
  22 bridge rows, and 2 example-family rows. The generated field dashboard now
  exposes the added abstract-algebra, set-theory, linear-algebra, number-theory,
  discrete-math, and functional-analysis bridge coverage, and the roadmap queue
  advances to proof-cookbook route examples.

- **2026-06-29** — **Linear-algebra computation bridge concepts landed.**
  Added generated bridge-concept rows for `bridge_lu_replay`,
  `bridge_rank_nullity`, `bridge_residual_bound`, `bridge_eigenpair`,
  `bridge_characteristic_polynomial`, and
  `bridge_random_matrix_finite_moment`. The foundational concept atlas now
  validates at 58 rows: 23 curriculum rows, 18 field rows, 15 bridge rows, and
  2 example-family rows. The generated field dashboard now exposes the added
  linear-algebra, numerical-analysis, optimization, probability/statistics, and
  operator-theory bridge coverage, and the roadmap queue advances to algebra
  map bridge rows.

- **2026-06-29** — **Analysis/topology bridge concepts landed.**
  Added generated bridge-concept rows for `bridge_metric_ball`,
  `bridge_bounded_epsilon_delta_shadow`, `bridge_compactness_shadow`,
  `bridge_connectedness_shadow`, and `bridge_continuity_preimage`. The
  foundational concept atlas now validates at 52 rows: 23 curriculum rows,
  18 field rows, 9 bridge rows, and 2 example-family rows. The generated field
  dashboard now exposes the added real-analysis, topology, and set-theory
  bridge coverage, and the roadmap queue advances to linear-algebra
  computation concept rows.

- **2026-06-29** — **Curriculum pressure fragment dashboard landed.**
  Added the generated
  [`curriculum-pressure-by-fragment.md`](docs/foundational-resources/generated/curriculum-pressure-by-fragment.md)
  planning view and wired it into the foundational-resource freshness gate. It
  groups the then-current 86 non-template math packs into overlapping
  Bool/CNF, QF_BV, QF_LIA, QF_LRA, QF_UF, NRA/RCF, finite-replay, and
  Lean-horizon buckets, making solver/proof demand visible from committed
  metadata instead of manual scans.

- **2026-06-29** — **Function composition pack landed.**
  Added
  [`artifacts/examples/math/function-composition-v0/`](artifacts/examples/math/function-composition-v0/)
  with finite composition, image/preimage replay, bijection inverse tables,
  composition associativity, checked non-injective inverse counterexample
  evidence, and a general function-law Lean-horizon row. Extended
  [`validate-foundational-example-pack.py`](scripts/validate-foundational-example-pack.py)
  to check the pack by exact finite function-graph replay.

- **2026-06-29** — **Calculus Riemann-sum pack landed.**
  Added
  [`artifacts/examples/math/calculus-riemann-sum-v0/`](artifacts/examples/math/calculus-riemann-sum-v0/)
  with exact finite left/right/trapezoid Riemann sums, midpoint replay,
  polynomial antiderivative endpoint replay, monotone lower/upper sums,
  checked false-integral counterexample evidence, and a fundamental-theorem
  Lean-horizon row. Extended
  [`validate-foundational-example-pack.py`](scripts/validate-foundational-example-pack.py)
  to check the pack by exact rational partition and polynomial-integral replay.

- **2026-06-29** — **Cardinality principles pack landed.**
  Added
  [`artifacts/examples/math/cardinality-principles-v0/`](artifacts/examples/math/cardinality-principles-v0/)
  with finite inclusion-exclusion, disjoint-union additivity, bipartite-edge
  double counting, powerset enumeration, checked false-additivity
  counterexample evidence, and a Cantor-Schroeder-Bernstein Lean-horizon row.
  Extended
  [`validate-foundational-example-pack.py`](scripts/validate-foundational-example-pack.py)
  to check the pack by exact finite set, subset, degree, and powerset replay.

- **2026-06-29** — **Induction patterns pack landed.**
  Added
  [`artifacts/examples/math/induction-patterns-v0/`](artifacts/examples/math/induction-patterns-v0/)
  with finite weak-induction evenness checks, Fibonacci strong-induction
  bounds, prefix-sum loop-invariant replay, checked bad-step counterexample
  evidence, and a full induction-schema Lean-horizon row. Extended
  [`validate-foundational-example-pack.py`](scripts/validate-foundational-example-pack.py)
  to check the pack by exact integer-table replay and bounded step validation.

- **2026-06-29** — **Proof-method patterns pack landed.**
  Added
  [`artifacts/examples/math/proof-methods-patterns-v0/`](artifacts/examples/math/proof-methods-patterns-v0/)
  with finite direct proof/modus ponens replay, contrapositive equivalence,
  proof-by-cases checking, contradiction refutation, checked invalid-converse
  counterexample evidence, and a natural-deduction Lean-horizon row. Extended
  [`validate-foundational-example-pack.py`](scripts/validate-foundational-example-pack.py)
  to check these proof patterns by exact Boolean assignment replay and
  deterministic truth-table enumeration.

- **2026-06-29** — **Equivalence-class pack landed.**
  Added
  [`artifacts/examples/math/equivalence-classes-v0/`](artifacts/examples/math/equivalence-classes-v0/)
  with finite equivalence relation replay, quotient-map fiber checks,
  partition-to-relation round trips, checked rejection of a non-transitive
  relation, and a checked QF_UF/Alethe quotient-map congruence row. Extended
  [`validate-foundational-example-pack.py`](scripts/validate-foundational-example-pack.py)
  to check finite equivalence classes, quotient-map fibers, induced
  partition relations, representatives, transitivity counterexamples, and the
  linked proof artifact/regression.

- **2026-06-29** — **Convexity rational pack landed.**
  Added
  [`artifacts/examples/math/convexity-rational-v0/`](artifacts/examples/math/convexity-rational-v0/)
  with exact rational midpoint Jensen replay, finite-grid second differences,
  affine threshold monotonicity, checked bad midpoint-convexity and
  affine-threshold rejections, and a general convex-analysis Lean-horizon row.
  Extended
  [`validate-foundational-example-pack.py`](scripts/validate-foundational-example-pack.py)
  to check exact rational convexity grids, midpoint averages, affine threshold
  samples, and finite convexity counterexamples.

- **2026-06-29** — **Real-analysis rational pack landed.**
  Added
  [`artifacts/examples/math/real-analysis-rational-v0/`](artifacts/examples/math/real-analysis-rational-v0/)
  with exact rational interval/ball inclusion, bounded linear epsilon-delta
  replay, squeeze-style polynomial side conditions, checked bad-delta
  rejection, and a general real-analysis Lean-horizon row. Extended
  [`validate-foundational-example-pack.py`](scripts/validate-foundational-example-pack.py)
  to check exact rational intervals, open balls, linear finite samples,
  polynomial bounds, and false-delta counterexamples.

- **2026-06-29** — **Graph search runtime pack landed.**
  Added
  [`artifacts/examples/math/graph-search-runtime-v0/`](artifacts/examples/math/graph-search-runtime-v0/)
  with finite BFS/DFS target-discovery cost counters, shortcut-tail family
  replay, checked rejection of a false DFS cost bound, and an asymptotic
  graph-search Lean-horizon row. Extended
  [`validate-foundational-example-pack.py`](scripts/validate-foundational-example-pack.py)
  to recompute BFS pop order, DFS preorder, generated shortcut-tail graphs,
  and visited-count counters from raw finite graph data.

- **2026-06-29** — **Finite Chebyshev-system pack landed.**
  Added
  [`artifacts/examples/math/finite-chebyshev-systems-v0/`](artifacts/examples/math/finite-chebyshev-systems-v0/)
  with exact finite Vandermonde unisolvence, interpolation replay,
  alternation-style residual signs, duplicate-node rejection, and a
  Chebyshev-system Lean-horizon row. Extended
  [`validate-foundational-example-pack.py`](scripts/validate-foundational-example-pack.py)
  with exact determinant, polynomial-basis matrix, sign, interpolation, and
  null-vector checks.

- **2026-06-29** — **Finite concentration pack landed.**
  Added
  [`artifacts/examples/math/finite-concentration-v0/`](artifacts/examples/math/finite-concentration-v0/)
  with exact finite Markov, Chebyshev, and union-bound replay over rational
  atom tables. Extended
  [`validate-foundational-example-pack.py`](scripts/validate-foundational-example-pack.py)
  to recompute expectations, variances, tail probabilities, union
  probabilities, and bad-bound refutations without claiming general
  concentration or limit theorems.

- **2026-06-29** — **Rationals LRA pack landed.**
  Added
  [`artifacts/examples/math/rationals-lra-v0/`](artifacts/examples/math/rationals-lra-v0/)
  with exact rational replay for density, additive inverse, trichotomy, and
  order transitivity. Extended
  [`validate-foundational-example-pack.py`](scripts/validate-foundational-example-pack.py)
  to parse fraction strings with exact arithmetic, keeping this pack free of
  floating-point tolerance claims.

- **2026-06-29** — **Modular arithmetic pack landed.**
  Added
  [`artifacts/examples/math/modular-arithmetic-v0/`](artifacts/examples/math/modular-arithmetic-v0/)
  with replayed CRT and modular-inverse witnesses plus exhaustive finite checks
  for a composite non-unit and a Fermat-style prime-modulus property. Extended
  [`validate-foundational-example-pack.py`](scripts/validate-foundational-example-pack.py)
  with pack-specific arithmetic replay so this is a checked resource artifact,
  not only a structural metadata row.

- **2026-06-29** — **First substantive math example pack landed.**
  Added
  [`artifacts/examples/math/proof-methods-refutation-v0/`](artifacts/examples/math/proof-methods-refutation-v0/)
  as the first curriculum-backed math pack. It models proof by refutation using
  the finite pigeonhole principle, includes a `PHP(2,2)` SAT witness control
  case, records `PHP(3,2)` as the UNSAT teaching target, and keeps checked
  CNF/LRAT evidence as an explicit proof gap. The generated concept atlas now
  marks existing referenced pack metadata as `validated`.

- **2026-06-29** — **Foundational example-pack scaffold landed.**
  Added the example-pack schema, validator, and validating template pack:
  [`foundational-example-pack.schema.json`](artifacts/ontology/foundational-example-pack.schema.json),
  [`validate-foundational-example-pack.py`](scripts/validate-foundational-example-pack.py),
  and [`artifacts/examples/math/template-v0/`](artifacts/examples/math/template-v0/).
  This completes the structural M2 scaffold; the next resource increment is the
  first substantive math pack, starting with `proof-methods-refutation-v0`.

- **2026-06-29** — **Foundational Concept Atlas seed landed.**
  Added the first machine-readable concept atlas:
  [`foundational-concepts.schema.json`](artifacts/ontology/foundational-concepts.schema.json),
  [`foundational-concepts.json`](artifacts/ontology/foundational-concepts.json),
  [`gen-foundational-concepts.py`](scripts/gen-foundational-concepts.py), and
  [`validate-foundational-concepts.py`](scripts/validate-foundational-concepts.py).
  The validator checks all 23 curriculum nodes, all 18 math fields, curriculum
  prerequisite/unlock alignment, field IDs, local source links, and planned
  pack/proof metadata. Added generated coverage/proof-gap dashboards under
  [`docs/foundational-resources/generated/`](docs/foundational-resources/generated/).

- **2026-06-29** — **Math curriculum resource buildout planned.**
  Added
  [`docs/foundational-resources/MATH-CURRICULUM-BUILDOUT.md`](docs/foundational-resources/MATH-CURRICULUM-BUILDOUT.md)
  with a detailed plan to build resources from the existing math curriculum:
  concept-atlas schema/data, example-pack schema, math packs, education pages,
  proof/certificate links, generated dashboards, CI hooks, and future library
  boundaries. Linked it from the foundational resources README, roadmap,
  mdBook summary, and `PLAN.md`.

- **2026-06-29** — **Foundational math field taxonomy added.**
  [`docs/foundational-resources/MATH-FIELDS.md`](docs/foundational-resources/MATH-FIELDS.md)
  now grounds the Foundational Concept Atlas math lane in 18 undergraduate and
  graduate fields, maps them to Axeyum slices/proof horizons, and names the
  first example packs. The roadmap, source ledger, docs hub, mdBook summary,
  sibling notes, and `PLAN.md` now link the taxonomy.

- **2026-06-29** — **Foundational resource expansion researched and planned.**
  Added [`docs/foundational-resources/`](docs/foundational-resources/) with a
  web/GitHub/clone-backed source ledger and a comprehensive roadmap for
  foundational mathematics, computer science, logic, and statistics resources.
  The roadmap defines a planned concept atlas, math deepening, CS foundations,
  logic/proof resources, statistics/probability packs, validation requirements,
  phases, backlog, and graduation criteria.

- **2026-06-28** — **Rules-as-Code first pack landed.**
  Added the toy
  [`Benefit Eligibility V0`](docs/rules-as-code/examples/benefit-eligibility-v0/README.md)
  rule pack with metadata, cited source clauses, model notes, expected checks,
  replayed witnesses, and explicit proof gaps. Added
  [`rules-core.schema.json`](artifacts/ontology/rules-core.schema.json) and
  [`validate-rules-as-code.py`](scripts/validate-rules-as-code.py) so the pack
  has a concrete validation command before solver-proof integration.

- **2026-06-28** — **Proof Certificate Cookbook first recipes landed.**
  Added initial route recipes for QF_BV bit-blast/DRAT evidence, QF_UF
  congruence/Alethe evidence, QF_LRA Farkas evidence, and array read-over-write
  axiom evidence under [`docs/proof-cookbook/recipes/`](docs/proof-cookbook/recipes/).
  The recipes include tiny formulas, current checker/test links, trust
  boundaries, Lean status, and capability/trust references.

- **2026-06-28** — **SMT Fragment Atlas first artifact landed.**
  Added the machine-readable atlas MVP:
  [`artifacts/ontology/smt-fragments.json`](artifacts/ontology/smt-fragments.json),
  [`artifacts/ontology/smt-fragments.schema.json`](artifacts/ontology/smt-fragments.schema.json),
  and [`scripts/validate-smt-fragment-atlas.py`](scripts/validate-smt-fragment-atlas.py).
  The initial ten rows link parser/IR/solver/model/proof/benchmark/dominance
  state back to local evidence and keep frontier rows explicitly partial.
  Validation passed with `python3 scripts/validate-smt-fragment-atlas.py`.

- **2026-06-28** — **Sibling incubator roadmaps drafted.**
  Added structured folders and detailed roadmaps for
  [`SMT Fragment Atlas`](docs/atlas/ROADMAP.md),
  [`Proof Certificate Cookbook`](docs/proof-cookbook/ROADMAP.md), and
  [`Rules-as-Code Verification Lab`](docs/rules-as-code/ROADMAP.md). The plans
  define audience, schemas/content structures, example slices, validation
  checks, Axeyum capability links, and graduation criteria. Updated
  [`docs/sibling-projects.md`](docs/sibling-projects.md), the docs hub, mdBook
  summary, and PLAN pointer to reference the new detailed plans.

- **2026-06-27** — **Sibling project notes documented.**
  Added `docs/sibling-projects.md` as the incubation note for educational
  content, taxonomy/ontology artifacts, complementary libraries, downstream
  verification apps, and law/rules reasoning projects. The note ranks the top
  30 ideas, groups them into families, records inside-vs-separate-repo guidance,
  calls out rules-as-code/legal-policy reasoning tasks, and recommends the first
  three incubators: SMT Fragment Atlas, Proof Certificate Cookbook, and
  Rules-as-Code Verification Lab. Linked it from `PLAN.md`, `docs/README.md`,
  and `docs/SUMMARY.md`.

- **2026-06-27** — **Multi-agent worktree protocol documented.**
  Added `docs/contributor-guide/multi-agent-worktrees.md` with the recommended
  hub-and-spoke collaboration model: one worktree per agent/task, topic
  branches, one `main` integration owner, explicit high-conflict file ownership,
  safe push rules when a branch already contains someone else's unpushed
  commits, conflict handling, and cleanup commands. Linked it from `PLAN.md`,
  `docs/README.md`, `docs/contributor-guide/README.md`, and `docs/SUMMARY.md`.

- **2026-06-27** — **Consumer-track integration lane opened.** Took over the
  diverged consumer track. Recorded the merge plan in
  [PLAN.md § Consumer-track integration](PLAN.md#consumer-track-integration-2026-06-27-converge-the-apps-onto-main)
  and a dedicated STATUS lane: `main`'s `axeyum-property` is canonical (branch
  duplicate + `-derive` retired); `axeyum-evm` / `axeyum-verify` (+`-macros`) /
  `axeyum-consumer-bench` port from `../axeyum-consumer` as new crates; and the
  ~190-commit warm-symexec engine gets a committed **EVM/symexec capability
  scoreboard** (DISAGREE=0) to end its measurement vacuum. New-crate-only,
  no core edits.
- **2026-06-27** — **Warm direct array-equality admission.**
  Direct equality between supported BV-indexed Bool/BV array symbols is now a
  retained warm theory fact. The incremental solver generates scoped
  cross-array select-congruence lemmas from equal-array classes for committed
  assertions and one-shot assumptions, projects SAT models by merging equal
  arrays before replay, and keeps user-facing cores/replay terms on the
  original array assertions. Focused regressions cover asserted equal-array
  conflicts, SAT equal-array model projection, and non-persisting one-shot
  equal-array assumptions. General array extensionality, arbitrary array terms,
  surviving store equalities, non-Bool/BV array components, and full retained
  lazy array/UF clauses remain P4.1/U6 work. Verification passed:
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test symbolic_execution warm_array_equality -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test symbolic_execution -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test incremental -j1 -- --nocapture`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --all-targets -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 RUSTDOCFLAGS="-D warnings" cargo doc -p axeyum-solver --no-deps -j1`;
  `./scripts/check-links.sh`.

- **2026-06-27** — **Warm BV div/rem readback cleanup.**
  The warm scalar simplifier now folds exact BV division/remainder wrappers
  after memory rewrites. It handles unsigned division by literal zero to
  all-ones, unsigned/signed division by literal one, zero divided by a
  syntactically nonzero divisor, remainder/modulo by literal zero or one, and
  self-remainder/self-modulo. Focused regression covers direct simplification,
  warm assertion encoding, original-term replay for a division-by-one readback
  equality, and an UNSAT self-remainder readback path. Signed division by zero
  and nontrivial variable divisors remain ordinary BV terms; full lazy
  arrays/UFs, retained theory clauses, extensionality, and arbitrary array
  terms remain P4.1/U6 work. Verification passed:
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test symbolic_execution warm_bv_readback_div_rem_identities_drop_wrappers -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test symbolic_execution -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test incremental -j1 -- --nocapture`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --all-targets -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 RUSTDOCFLAGS="-D warnings" cargo doc -p axeyum-solver --no-deps -j1`;
  `./scripts/check-links.sh`.

- **2026-06-27** — **Warm BV shift readback cleanup.**
  The warm scalar simplifier now folds exact BV shift identity wrappers after
  memory rewrites. Shift-by-zero wrappers around BV readbacks collapse for
  `bvshl`, `bvlshr`, and `bvashr`; zero shifted by any amount collapses to
  zero; and all-ones arithmetic-right-shifted by any amount stays all ones.
  Focused regression covers direct simplification, warm assertion encoding,
  original-term replay for a zero-shift readback equality, and an UNSAT
  zero-shift/readback disequality path. Nonzero variable shifts and over-shift
  rewrites remain ordinary BV terms; full lazy arrays/UFs, retained theory
  clauses, extensionality, and arbitrary array terms remain P4.1/U6 work.
  Verification passed:
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test symbolic_execution warm_bv_readback_shift_identities_drop_wrappers -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test symbolic_execution -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test incremental -j1 -- --nocapture`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --all-targets -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 RUSTDOCFLAGS="-D warnings" cargo doc -p axeyum-solver --no-deps -j1`;
  `./scripts/check-links.sh`.

- **2026-06-27** — **Warm BV slice/extension readback cleanup.**
  The warm scalar simplifier now folds BV structural identity wrappers after
  memory rewrites: whole-width extracts and zero-bit `zero_extend` /
  `sign_extend` around BV readbacks collapse before CNF encoding. Focused
  regression covers direct simplification, warm assertion encoding,
  original-term replay for a whole-extract readback equality, and an UNSAT
  whole-extract/readback disequality path. Partial extracts and positive-width
  extensions remain ordinary BV terms; full lazy arrays/UFs, retained theory
  clauses, extensionality, and arbitrary array terms remain P4.1/U6 work.
  Verification passed:
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test symbolic_execution warm_bv_readback_slice_extension_identities_drop_wrappers -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test symbolic_execution -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test incremental -j1 -- --nocapture`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --all-targets -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 RUSTDOCFLAGS="-D warnings" cargo doc -p axeyum-solver --no-deps -j1`;
  `./scripts/check-links.sh`.

- **2026-06-27** — **Warm BV comparison readback cleanup.**
  The warm scalar simplifier now folds BV comparison wrappers after memory
  rewrites. Reflexive unsigned/signed comparisons collapse to constants, and
  unsigned endpoint facts such as `load <u 0`, `0 <=u load`,
  `load <=u all_ones`, `load >u all_ones`, `load >=u 0`, and
  `all_ones >=u load` disappear before CNF encoding. Focused regression covers
  direct simplification, warm assertion encoding, original-term replay for a
  tautological range guard, and an UNSAT impossible lower-bound path. Full lazy
  arrays/UFs, retained theory clauses, extensionality, and arbitrary array terms
  remain P4.1/U6 work. Verification passed:
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test symbolic_execution warm_bv_readback_comparison_identities_drop_constant_wrappers -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test symbolic_execution -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test incremental -j1 -- --nocapture`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --all-targets -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 RUSTDOCFLAGS="-D warnings" cargo doc -p axeyum-solver --no-deps -j1`;
  `./scripts/check-links.sh`.

- **2026-06-27** — **Warm BV arithmetic readback cleanup.**
  The warm scalar simplifier now folds exact modular BV arithmetic wrappers
  after memory rewrites. BV readbacks such as
  `select(store(mem, i, v), i) + #x00` collapse to `v`, multiply-by-zero/one
  wrappers collapse, double `bvneg` collapses, and self-subtraction or
  additive-inverse readbacks collapse to zero before CNF encoding. Focused
  regression covers direct simplification, warm assertion encoding,
  original-term replay, and an UNSAT self-subtraction readback path. Division
  and remainder identities remain out of scope until SMT-LIB zero-divisor
  guards are explicit; full lazy arrays/UFs, retained theory clauses,
  extensionality, and arbitrary array terms remain P4.1/U6 work.
  Verification passed:
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test symbolic_execution warm_bv_readback_arithmetic_identities_drop_constant_wrappers -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test symbolic_execution -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --test incremental -j1 -- --nocapture`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --all-targets -j1 -- -D warnings`;
  `CARGO_BUILD_JOBS=2 RUSTDOCFLAGS="-D warnings" cargo doc -p axeyum-solver --no-deps -j1`;
  `./scripts/check-links.sh`.

- **2026-06-27** — **Warm BV bitwise readback cleanup.**
  The warm scalar simplifier now folds bitwise BV identity wrappers after memory
  rewrites. BV readbacks such as `select(store(mem, i, v), i) & #xff` collapse
  to `v`, zero/all-ones annihilators collapse to constants, double `bvnot`
  collapses, and self-xor readbacks collapse to zero before CNF encoding.
  Focused regression covers direct simplification, warm assertion encoding,
  original-term replay, and an UNSAT self-xor readback path. Full lazy
  arrays/UFs, retained theory clauses, extensionality, and arbitrary array terms
  remain P4.1/U6 work.

- **2026-06-27** — **Warm Bool xor/implication cleanup.**
  The warm scalar simplifier now folds Boolean `xor` and implication after
  memory rewrites. Predicate-like readbacks such as
  `true => select(store(mem, i, p), i)` collapse to `p`,
  `select(store(mem, i, p), i) => false` collapses to `not p`, and self-xor /
  complement-xor readbacks collapse to `false` / `true` before CNF encoding.
  Focused regression covers warm assertion encoding, original-term replay, and
  an UNSAT self-xor readback path. Full lazy arrays/UFs, retained theory
  clauses, extensionality, and arbitrary array terms remain P4.1/U6 work.

- **2026-06-27** — **Warm Bool connective cleanup.**
  The warm scalar simplifier now folds binary Boolean `and`/`or` after memory
  rewrites: constants, idempotent operands, and obvious complements collapse
  before CNF encoding. Predicate-like memory readbacks such as
  `select(store(mem, i, p), i) and true` now simplify to `p`, while
  `select(store(mem, i, p), i) and not(select(store(mem, i, p), i))`
  simplifies to `false`. Focused regression covers warm assertion encoding,
  original-term replay, and the UNSAT contradictory readback path. Full lazy
  arrays/UFs, retained theory clauses, extensionality, and arbitrary array terms
  remain P4.1/U6 work.

- **2026-06-27** — **Warm Bool readback equality cleanup.**
  The warm scalar simplifier now folds Boolean equality against constants and
  removes double negation. Symbolic Bool memory readbacks that reduce through
  ROW no longer keep residual equality wrappers: `select(store(mem, i, p), i) =
  true` simplifies to `p`, and `not(select(store(mem, i, p), i) = false)` also
  simplifies to `p`. Focused regression covers Bool-array memory replay, SAT
  projection, and an UNSAT branch under the negated stored value. Full lazy
  arrays/UFs, retained theory clauses, extensionality, and arbitrary array terms
  remain P4.1/U6 work.

- **2026-06-27** — **Warm scalar ITE equality cleanup.**
  `IncrementalBvSolver::simplify_memory_for_warm_assertion` now distributes
  equality over Bool/BV-valued `ite`s, folds literal-distinct constant
  equalities to `false`, and collapses Boolean identity ITEs. Conditional
  read/write-index memory rewrites that previously encoded `ite(flag, 1, 0) =
  1` now simplify to the path predicate itself before warm encoding. This trims
  residual CNF while keeping SAT replay on the original memory assertion. Full
  lazy arrays/UFs, retained theory clauses, extensionality, and arbitrary array
  terms remain P4.1/U6 work.

- **2026-06-27** — **Warm conditional-write-index read splitting.**
  `IncrementalBvSolver::simplify_memory_for_warm_assertion` now splits reads
  over stores whose write index is an `ite` before the generic symbolic ROW
  equality:
  `select(store(a, ite(c, i, j), v), k) -> ite(c, select(store(a, i, v), k), select(store(a, j, v), k))`.
  The resulting branch-local store/read terms reuse the existing same-index,
  literal-distinct, constant-array, shadowed-ROW, and trivial-scalar cleanup
  rules. Focused regression covers a replay-checked warm assertion where only
  the true conditional-write branch updates the selected cell. Full lazy
  arrays/UFs, retained theory clauses, extensionality, and arbitrary array terms
  remain P4.1/U6 work.

- **2026-06-27** — **Warm conditional-index read splitting.**
  `IncrementalBvSolver::simplify_memory_for_warm_assertion` now distributes
  reads over index-valued `ite`s before read-over-write handling:
  `select(a, ite(c, i, j)) -> ite(c, select(a, i), select(a, j))`. Conditional
  symbolic addresses can therefore split into scalar branch reads and reuse the
  existing same-index, literal-distinct, constant-array, shadowed-ROW, and
  trivial-scalar cleanup rules. Focused regression covers a replay-checked warm
  assertion where only the true conditional-address branch reads the stored
  value. Full lazy arrays/UFs, retained theory clauses, extensionality, and
  arbitrary array terms remain P4.1/U6 work.

- **2026-06-27** — **Warm reflexive memory tautology pruning.**
  The warm memory simplifier now folds `t = t` to `true` and Boolean negation
  over constants after memory rewrites expose them. Same-readback array-ITE/ROW
  conditions now collapse to warm tautologies or contradictions instead of
  leaving residual equality CNF, while SAT replay still checks the original
  memory term.

- **2026-06-27** — **Warm array-ITE same-readback guard pruning.**
  The warm memory simplifier now collapses trivial scalar `ite`s exposed by
  memory rewrites, including same-branch results after select-over-array-ITE and
  ROW read-back. Branch-merged memory states whose selected branches both read
  the same stored value now avoid bit-blasting an irrelevant merge guard while
  still replaying the original memory assertion.

- **2026-06-27** — **Warm ROW same-index shadow pruning.**
  The warm memory simplifier now drops earlier stores at the same syntactic
  index when a later store shadows them before symbolic ROW expansion. This
  keeps simple write-log shapes from bit-blasting dead old values and duplicate
  equality guards while preserving original-term replay and retained
  BV-indexed Bool/BV select abstraction for the remaining base read. Full
  retained lazy array/UF clauses remain P4.1/U6 work.

- **2026-06-27** — **Warm wide-BV scalar UF projection.**
  Extended retained warm scalar-UF abstraction from compact Bool/BV function
  applications to wide/BV256 argument and result values. Warm UF projection now
  stores touched wide function points through full-value `FuncValue` entries
  with canonical `Value::WideBv`s, branch preflight keeps BV256 keccak-style UF
  fork conditions on one-shot warm assumptions, and the IR function-model
  storage selector treats wide BV signatures as full-value interpretations.

- **2026-06-27** — **Warm wide-BV array select projection.**
  Extended the retained warm array-select projection path from compact BV arrays
  to wide/BV256 storage-style reads: BV-indexed Bool/BV array symbols whose
  index or element width exceeds 128 bits now project touched entries through
  `GenericArrayValue` with canonical `Value::WideBv` indices/elements before
  original-term replay. The IR evaluator now keeps array operations out of the
  wide-BV arithmetic dispatcher and well-founded defaults use wide/generic array
  values when a BV component is wider than 128 bits.

- **2026-06-27** — **Warm Bool-array select-congruence admission.**
  Extended retained warm array-select abstraction from BV-valued arrays to
  BV-indexed Bool-valued arrays. Bool reads now become internal warm Bool
  variables, same-array congruence lemmas remain scoped, and replay projection
  writes touched entries through `GenericArrayValue`, keeping predicate/set-like
  symbolic-base reads warm for committed assertions and one-shot branches.

- **2026-06-27** — **Warm branch routing recognizes retained select/UF slices.**
  `SymbolicExecutor::branch` now preflights simplified fork conditions against
  the retained select/UF abstraction coverage before falling back to the memory
  dispatcher. One-shot fork queries over plain BV-indexed Bool/BV array-symbol
  reads and scalar Bool/BV UF apps now encode warm assumptions, scoped
  congruence lemmas, and replay projections instead of conservatively rebuilding
  through `check_with_memory`.

- **2026-06-27** — **Warm scalar UF congruence admission.**
  Added retained warm abstraction for scalar Bool/BV UF applications in the
  incremental memory path: `f(args)` becomes an internal warm variable,
  same-function application pairs get scoped congruence lemmas, and SAT models
  project touched `FuncValue` entries before original-term replay. This keeps
  keccak-style scalar UF branch constraints warm for committed assertions and
  one-shot assumptions; full lazy arrays/UF remain U6/P4.1 work.

- **2026-06-27** — **Warm BV-valued array select-congruence admission.**
  Added a first retained warm array-read abstraction for the incremental memory
  path: BV-indexed, BV-valued array-symbol reads become internal BV variables,
  same-array select pairs get scoped congruence lemmas, and SAT models are
  projected back to array entries before original-term replay. Symbolic-base
  helper loads and reducible ROW tails can now stay warm; full lazy arrays/UF
  remain U6/P4.1 work.

- **2026-06-27** — **BV Pareto robustness and signed mixed-direction coverage.**
  Hardened `optimize_bv_pareto` so malformed/out-of-fragment objective values
  return `ParetoOutcome::Unknown` instead of a hard solver error, and added a
  signed mixed max/min Pareto-front regression. Updated P4.3 status to stop
  listing BV Pareto as remaining work.

- **2026-06-27** — **Read-specific write-log guards shrink frontend memory formulas.**
  Updated `SymbolicMemory::load_with_write_log` so concrete/literal writes known
  distinct from the read do not emit guards, exact read hits are unguarded, and
  only later symbolic aliases retain guards. Concrete read-log hits can collapse
  to pure warm BV conditions while preserving last-writer-wins aliasing.

- **2026-06-27** — **CFG exploration uses warm auto route by default.**
  Updated `explore_cfg` so default branch/assume/status/model checks use
  `branch`, `assume_auto`, `status_auto`, and `model_auto` instead of
  pre-classifying raw array terms and forcing the memory dispatcher. Reducible
  CFG memory conditions now stay warm; `memory_aware=true` remains the explicit
  force-dispatch mode.

- **2026-06-27** — **SymbolicMemory helpers use warm auto route.**
  Routed `SymbolicMemory` load-equality branch/assume helpers, including compact
  write-log helpers, through `assume_auto` / `branch`. Reducible helper calls
  now stay on ordinary warm `status` / `model`; unreduced symbolic-base loads
  still fall back through the memory route and remain pruning-safe as `Unknown`
  on the warm-only status path.

- **2026-06-27** — **Warm symbolic ROW conditional admission.**
  Extended the warm-safe memory simplifier to expand undecided
  read-over-write into a scalar conditional
  `ite(write_index = read_index, value, select(base, read_index))`, then
  recursively simplify the base read. This keeps symbolic-address hits/misses
  over zero-initialized or otherwise reducible store chains on the warm
  assertion/assumption/branch path with original-term replay. Symbolic base
  arrays, unreduced ROW tails, extensionality, and UF lemmas remain deferred to
  the memory dispatcher.

- **2026-06-27** — **Warm array-ITE read admission.**
  Extended the warm-safe memory simplifier to distribute reads over array-valued
  `ite`s before warm classification, then recursively simplify the resulting
  scalar branch reads. This keeps simple branch-merged memory states on the warm
  assertion/assumption/branch path when their selected branches reduce through
  the existing same-index, literal-distinct, or constant-array rules. General
  array state, symbolic distinct-index ROW, extensionality, and UF lemmas remain
  deferred to the memory dispatcher.

- **2026-06-27** — **Warm constant-array read admission.**
  Extended the warm-safe memory simplifier to collapse
  `select((as const Array) v, i)` to `v` before warm classification. This keeps
  zero-initialized constant-array reads and concrete miss chains over them on the
  warm assertion/assumption/branch path while preserving original-term replay
  and core reporting. Symbolic array state, symbolic distinct-index ROW,
  extensionality, and UF lemmas remain deferred to the memory dispatcher.

- **2026-06-27** — **Warm literal ROW chain admission.**
  Extended the warm-safe ROW simplifier beyond same-index hits: if a store's
  literal index is provably different from the read's literal index, the warm
  simplifier skips that store and continues simplifying the read. This keeps
  concrete-address store-chain misses on the warm assertion/assumption/branch
  path while preserving original-term replay/core reporting. Symbolic
  distinct-index ROW remains deferred to the memory dispatcher.

- **2026-06-27** — **Warm same-index ROW assumptions and branches.**
  Extended the narrow warm-safe same-index ROW simplifier from committed
  assertions to one-shot assumptions and symbolic-execution branch fork queries.
  `check_assuming_simplifying_memory` and
  `check_assuming_core_simplifying_memory` encode the simplified BV term but
  replay and report cores against the original memory assumptions; `branch` uses
  that route before falling back to the memory dispatcher. General array/UF
  constraints remain deferred to `check_with_memory`.

- **2026-06-27** — **Property SDK Kani-style assume/assert baseline.**
  Added a bounded Kani-style assume/assert counterexample row to the property
  corpus: an independent Rust scan of the `kani::assume(debit <= 10)` plus
  `assert(balance.wrapping_sub(debit) <= balance)` analogue finds
  `(balance = 0, debit = 1)`, matching Axeyum's minimized SDK witness.
  Regenerated artifacts at 16 cases, 5 proved, 11 disproved, 0 unknown,
  DISAGREE=0, and 1/1 Lean-required coverage.

- **2026-06-27** — **Solver clippy gate restored.**
  Cleared the existing `axeyum-solver --all-targets -D warnings` lint debt with
  behavior-neutral test allowances, local test renames, and small mechanical
  cleanups in `auto.rs`. The solver library unit suite also passes at 609 tests.

- **2026-06-27** — **SymbolicMemory write-log normalization.**
  Added public `SymbolicMemoryWrite` plus conservative write-log normalization
  and compact read-over-write helpers on `SymbolicMemory`. Frontends can drop
  same-index shadowed writes, emit read-specific `ite` guards only for writes
  that may alias, and branch/assume on the resulting load equality through the
  memory-aware route. Focused tests cover concrete shadow dropping and symbolic
  last-writer-wins aliasing.

- **2026-06-27** — **Property SDK proptest baseline comparison.**
  Added an actual proptest-backed baseline row to the property corpus: a
  fixed-seed `TestRunner` shrinks the wrapping-add monotonicity failure to
  `(x = 1, y = 255)`, matching both the exhaustive Rust baseline and Axeyum's
  minimized counterexample. Regenerated artifacts at 15 cases, 5 proved,
  10 disproved, 0 unknown, DISAGREE=0, and 1/1 Lean-required coverage.

- **2026-06-27** — **Property SDK replay baseline comparison.**
  Added a replay-oriented baseline row to the property corpus: Axeyum's
  minimized transfer counterexample matches the first bounded Rust struct
  failure, and the generated Rust regression test replays that witness through a
  caller-owned failure predicate. Regenerated artifacts at 14 cases, 5 proved,
  9 disproved, 0 unknown, DISAGREE=0, and 1/1 Lean-required coverage.

- **2026-06-27** — **Property SDK assumption baseline comparison.**
  Added a bounded precondition/assertion baseline row to the property corpus:
  Axeyum proves `x <= 10 => x + 1 <= 11` over `u8` with checked evidence,
  while an independent bounded Rust scan finds no precondition-respecting
  failure. Regenerated artifacts at 13 cases, 5 proved, 8 disproved, 0 unknown,
  DISAGREE=0, and 1/1 Lean-required coverage.

- **2026-06-27** — **Property SDK struct baseline comparison.**
  Added a derived-struct executable baseline row to the property corpus:
  Axeyum's minimized `TransferInput` counterexample is checked against the
  first failing struct found by an independent bounded Rust predicate scan.
  Regenerated artifacts at 12 cases, 4 proved, 8 disproved, 0 unknown,
  DISAGREE=0, and 1/1 Lean-required coverage.

- **2026-06-27** — **Consumer upstream feedback log restored.**
  Restored `docs/consumer-track/UPSTREAM-FEEDBACK.md` on `main`, reconciled its
  old branch-only U1-U7 entries against current evidence, and linked it from the
  consumer-track README. The log now separates resolved consumer-facing asks
  from the still-open warm lazy-array/UF and broader Lean reconstruction
  frontiers.

- **2026-06-27** — **Property SDK expression builder aliases.**
  Added fallible `Property`-owned Bool/BV/Int expression builder aliases over
  the existing typed handles and a generated corpus row proving a mixed
  Bool/BV/Int identity with checked evidence. Regenerated artifacts at 11
  cases, 4 proved, 7 disproved, 0 unknown, DISAGREE=0, and 1/1 Lean-required
  coverage.

- **2026-06-27** — **Property SDK proved baseline comparison.**
  Added a second deterministic executable baseline row to the property corpus:
  Axeyum proves `u8` wrapping-add commutativity with checked evidence, while an
  independent bounded Rust predicate scan confirms there is no concrete
  failure. Regenerated artifacts at 10 cases, 3 proved, 7 disproved, 0 unknown,
  DISAGREE=0, and 1/1 Lean-required coverage.

- **2026-06-27** — **Property SDK baseline comparison first slice.**
  Added a deterministic proptest-style executable baseline row to the property
  corpus: Axeyum's minimized `u8` wrapping-add counterexample is checked
  against the first failing pair found by an independent bounded Rust predicate
  scan. Regenerated the corpus artifacts at 9 cases, 2 proved, 7 disproved,
  0 unknown, DISAGREE=0, and 1/1 Lean-required coverage.

- **2026-06-27** — **Property SDK fixture file assembly.**
  Added `Counterexample::render_rust_test_file` so frontends can assemble
  caller-owned top-level prelude blocks plus multiple generated modules or test
  items into deterministic multi-case fixture files; refreshed the nested
  aggregate corpus row to check a complete fixture file with the replay module,
  smoke module, and helper-rendered `Result<bool, _>` replay assertion.

- **2026-06-27** — **Property SDK test module assembly.**
  Added `Counterexample::render_rust_test_module` so frontends can wrap
  caller-owned imports/helpers and generated `#[test]` items in deterministic
  sanitized `#[cfg(test)]` modules; refreshed the nested aggregate corpus row
  to check module-level imports plus the helper-rendered `Result<bool, _>`
  replay assertion.

- **2026-06-27** — **Property SDK Result replay adapters.**
  Added `Counterexample::render_rust_replay_call`,
  `render_rust_replay_expect_ok`, `render_rust_replay_expect_ok_assertion`,
  `render_rust_test_with_replay_expect_ok`, and
  `render_rust_test_with_replay_expect_ok_assertion` so generated
  counterexample tests can cover `Result<(), E>` and `Result<bool, E>` replay
  functions while keeping replay semantics caller-owned; refreshed the nested
  aggregate corpus row to check the `Result<bool, _>` replay assertion.

- **2026-06-27** — **Property SDK replay assertion helper.**
  Added `Counterexample::render_rust_replay_assertion` and
  `render_rust_test_with_replay_assertion` so generated counterexample tests can
  share the common `assert!(replay_fn(args...));` body while the replay function
  and argument expressions remain caller-owned; refreshed the nested aggregate
  corpus row to check the helper-rendered assertion.

- **2026-06-27** — **Property SDK prelude-aware replay tests.**
  Added `Counterexample::render_rust_test_with_prelude` so generated Rust
  counterexample tests can include caller-owned imports/module prelude plus
  aggregate/domain setup snippets before the replay assertion; refreshed the
  nested aggregate corpus row to check the complete generated `#[test]`.

- **2026-06-27** — **Property SDK explicit nested aggregate replay.**
  Added `render_rust_named_struct_let_with_fields` for caller-owned nested
  aggregate replay composition, kept implicit nested inference rejected by the
  direct helper, and regenerated the property corpus artifacts at 8 cases, 2
  proved, 6 disproved, DISAGREE=0, with 1/1 Lean-required coverage.

- **2026-06-27** — **Property SDK corpus broadened.**
  Added generated corpus rows for unsigned-add overflow helper witnesses and
  derived `Symbolic` struct counterexample lifting; regenerated
  `corpus.json`/`SCOREBOARD.md`; totals are 7 cases, 2 proved, 5 disproved, 0
  unknown, DISAGREE=0, and 1/1 Lean-required coverage.

- **2026-06-27** — **Property SDK generated corpus artifacts.**
  Refactored the committed property corpus into a shared support module, added
  the `property_corpus_scoreboard` generator example, committed
  `docs/consumer-track/property/corpus.json`, and made the corpus integration
  test compare the executed results against both JSON and Markdown snapshots.

- **2026-06-27** — **Property SDK corpus scoreboard first slice.**
  Added `crates/axeyum-property/tests/corpus.rs` and
  `docs/consumer-track/property/SCOREBOARD.md` as the first committed PROP.6
  measurement gate: five graduated SDK workflows, 2 proved, 3 disproved, 0
  unknown, DISAGREE=0, and 1/1 Lean-required coverage. External proptest/Kani
  baselines remain open.

- **2026-06-27** — **Property certificate summaries.**
  Added stable `Evidence::kind_label()` strings and
  `ProofCertificate::summary()` so frontend reports can show outcome,
  evidence route/provenance, trust-step certification bits, and Lean
  reconstruction status without inspecting raw solver artifacts.

- **2026-06-27** — **Property Lean certificate surface first slice.**
  Added `ProofCertificate` / `LeanModule`, re-exported the relevant solver
  evidence and reconstruction types, and added `prove_with_certificate` plus
  `prove_minimized_with_certificate` so proved property queries can carry the
  checked Axeyum `EvidenceReport` and a best-effort standalone Lean module.

- **2026-06-27** — **Property expression ergonomics first slice.**
  Added Bool/BV/Int `.equals()` aliases plus `Property::all` and
  `Property::any` Boolean folds, preserving the SDK's explicit fallible builder
  contract while removing common equality/fold boilerplate.

- **2026-06-27** — **Property structured Rust counterexample snippets.**
  Added `Counterexample::render_rust_named_struct_let` and
  `render_rust_tuple_struct_let` for direct symbolic input bundles. The helpers
  reuse scalar replay bindings and reject nested aggregate inference until a
  frontend supplies the domain shape.

- **2026-06-27** — **Signed-order counterexample minimization metadata.**
  Added metadata-aware model minimization objectives, proof/evidence facade
  variants, and a solver facade method so signed BV symbols can minimize in
  two's-complement order. `axeyum-property::Property::prove_minimized` now uses
  that path for signed `Symbolic` inputs while raw BV inputs remain unsigned.

- **2026-06-27** — **Property SDK signed fixed-width `Symbolic` inputs.**
  Added `Symbolic` implementations for `i8`/`i16`/`i32`/`i64` as
  two's-complement BV terms, with signed model lifting and signed Rust
  counterexample literal rendering for SDK-declared signed BV symbols.

- **2026-06-27** — **Property SDK `Symbolic` derive macro.**
  Added the `axeyum-property-macros` proc-macro crate and re-exported
  `#[derive(axeyum_property::Symbolic)]`. The derive supports named, tuple, and
  unit structs over the existing `Symbolic` / `symbolic_struct` surface and
  lifts concrete Rust values from replay-checked models.

- **2026-06-27** — **Property SDK named-field symbolic bundles.**
  Added `Property::symbolic_struct` and `SymbolicStruct::{field,struct_field}`
  so frontends can build struct-shaped symbolic input bundles with deterministic
  dotted Axeyum names and stable sanitized counterexample identifiers.

- **2026-06-27** — **Property SDK scalar/tuple `Symbolic` trait.**
  Added `Symbolic` plus `Property::symbolic` / `Property::concrete` for Bool,
  unsigned Rust-integer BV inputs, signed fixed-width Rust-integer BV inputs,
  Int-backed `i128`, unit, and 2-/3-tuples with deterministic field naming and
  model lifting.

- **2026-06-27** — **Property counterexample-to-test rendering.**
  Added `Counterexample` / `InputBinding` in `axeyum-property`, with
  deterministic extraction from replay-checked models and Rust let-binding /
  `#[test]` skeleton rendering for native Bool/Int/BV<=128 inputs.

- **2026-06-27** — **`axeyum-property` typed proof SDK v0.**
  Added the first bounded-property SDK crate with typed `Bool`, `Bv<W>`, and
  `Int` handles over `TermArena`, proof/minimized-counterexample calls delegated
  to the existing evidence APIs, scalar model lifting, and typed unsigned BV
  overflow helpers for EVM/Rust verifier consumers.

- **2026-06-27** — **Lean proof input-shape normalization.**
  Added a shared Lean-reconstruction fallback normalizer that splits only
  top-level assertion-spine conjunctions and strips repeated top-level double
  negations after direct reconstruction declines. `prove_unsat_to_lean_module`
  and `reconstruct_sos_to_lean_module` both use it. Focused real-Lean
  regressions cover normalized QF_UFBV/finite-BV+UF and array read-over-write
  refutations.

- **2026-06-27** — **SMT-LIB get-assertions helper.**
  Added `ScriptCommand::GetAssertions` and exported
  `solve_smtlib_get_assertions`, returning requested scoped assertion-stack
  snapshots as deterministic rendered terms. The helper honors
  `assert`/`push`/`pop`/`reset-assertions`, ignores one-shot
  `check-sat-assuming` literals, and returns `None` when a script has no
  `(get-assertions)` requests. Focused parser and solver tests cover scoped
  snapshots, assumption exclusion, and the no-request case.

- **2026-06-27** — **SMT-LIB get-model helper.**
  Added parser-side model declaration tracking for user-declared constants and
  uninterpreted functions, plus exported `SmtLibModel` /
  `solve_smtlib_get_model`. The helper returns declaration-ordered model
  constants as `Value`s and available function interpretations as `FuncValue`s
  for sat scripts that requested `(get-model)`, and returns `None` when no model
  was requested or the query is not sat.

- **2026-06-27** — **SMT-LIB get-option helper.**
  Added parser recording for `get-option` requests and exported
  `solve_smtlib_get_option`, returning requested option values in script order.
  Explicit `set-option` values are returned verbatim; common SMT-LIB defaults
  are reported when unset; unknown options return `unsupported`. The support
  matrix wording now distinguishes commands ignored by the single-result facade
  from commands served by explicit helper APIs.

- **2026-06-27** — **SMT-LIB get-info metadata helper.**
  The parser now records `set-info`, `set-option`, and requested `get-info`
  commands. Added `solve_smtlib_get_info`, which returns recorded metadata in
  request order with defaults for `:name`/`:version`, computed
  `:reason-unknown`, and an explicit `unsupported` marker for unknown info keys.
  Focused parser and solver tests cover metadata capture, defaults, and
  unsupported-key behavior.

- **2026-06-27** — **SMT-LIB get-assignment helper.**
  Added `solve_smtlib_get_assignment`, evaluating active top-level `:named`
  assertions under the sat model and returning `(name, bool)` pairs in scoped
  active assertion order. The helper shares the single-query command replay, so
  popped assertions and assertions cleared by `reset-assertions` are not
  reported. Focused tests cover named assignment values, scoped name filtering,
  and the no-model case.

- **2026-06-27** — **SMT-LIB scoped single-query front door.**
  Added a shared scoped-command replay helper for the single-result SMT-LIB
  APIs. `solve_smtlib`, OMT helpers, `get-value`, `get-unsat-core`, and
  `get-proof` now honor `push`/`pop`, `check-sat-assuming`, and
  `reset-assertions` for zero-or-one-query scripts instead of using the flat
  assertion list; multi-query scripts return a clear `Unsupported` pointing to
  `solve_smtlib_incremental`. Focused tests cover push/pop, reset-assertions,
  multi-query rejection, and scoped unsat-core labels.

- **2026-06-27** — **Tiny BV edge coverage DOT overlays.**
  Added `TinyBvProgram::cfg_dot_with_edge_coverage`, rendering replay-checked
  edge suites over the deterministic basic-block CFG DOT. Covered,
  bounded-unreachable, and unknown incident blocks get distinct node styles, and
  rendered block-to-block edges exercised by edge tests are highlighted while
  intra-block instruction fallthroughs remain implicit. Focused tests pin exact
  edge-coverage DOT for the imported memory program.

- **2026-06-27** — **Tiny BV edge coverage suites.**
  Added `TinyBvEdgeTestGenerationReport`, `TinyBvEdgeCoverageReport`, and
  `TinyBvProgram::{test_cases_for_cfg_edge_checked,test_cases_for_cfg_edges_checked}`.
  Edge targeting uses a private edge-aware symbolic state and concrete replay
  must contain the targeted edge before a test case is reported. Focused tests
  assert all five imported memory-program edges are covered and distinguish the
  true and false branch witnesses.

- **2026-06-27** — **Tiny BV coverage DOT overlays.**
  Added `TinyBvProgram::cfg_dot_with_coverage`, rendering generated coverage
  suites over the deterministic basic-block CFG DOT. Covered, bounded-
  unreachable, and unknown targets get distinct node styles, and edges exercised
  by generated tests are highlighted. Focused tests pin exact coverage DOT for
  the imported memory program and preserve the prior static/trace DOT contracts.

- **2026-06-27** — **Tiny BV block coverage suites.**
  Added `TinyBvCoverageReport` and
  `TinyBvProgram::test_cases_for_basic_blocks_checked`, aggregating
  replay-checked per-block-entry test generation over the deterministic
  `basic_blocks()` order. The report exposes target, covered, generated,
  unreachable, unknown, and completeness counts while preserving each target's
  reachability diagnostics. Focused tests assert the imported memory program
  covers entry/win/lose blocks and keeps the false-edge witness for the lose
  block.

- **2026-06-27** — **Tiny BV generated test cases.**
  Added `TinyBvTestCase`, `TinyBvTestGenerationReport`, and
  `TinyBvProgram::{test_cases_for_pc_checked,test_cases_for_label_checked}`.
  The helper runs checked reachability, keeps reachability diagnostics, and
  packages each verified witness as a canonical trace report with target
  PC/label metadata. Focused tests assert generated test cases for an imported
  memory program reach the target and retain the expected branch witness.

- **2026-06-27** — **Tiny BV trace DOT overlays.**
  Added `TinyBvProgram::cfg_dot_with_trace`, rendering concrete replay paths
  over the deterministic basic-block CFG DOT. Visited blocks are filled and
  taken rendered block edges are highlighted; intra-block transitions remain
  implicit. Focused tests pin exact winning and losing path overlays for an
  imported memory program.

- **2026-06-27** — **Tiny BV CFG DOT export.**
  Added `TinyBvProgram::cfg_dot`, a deterministic Graphviz DOT export for the
  toy BV basic-block CFG. The export renders source/label-aware blocks and
  labelled terminator edges from the existing typed CFG, giving frontend tools a
  stable visualization artifact without rebuilding the graph. Focused tests pin
  the exact DOT for an imported memory program.

- **2026-06-27** — **Tiny BV trace reports.**
  Added `TinyBvTraceReport` and `TinyBvProgram::trace_report`, packaging a
  concrete witness, canonical replay trace, source rows, block visits, and taken
  CFG edges into one coherent path report. Focused tests assert that report
  fields match the separately-derived source/block/edge views for both winning
  and losing imported assembly witnesses.

- **2026-06-27** — **Tiny BV taken CFG edges.**
  Added `TinyBvTraceEdgeStep` and `TinyBvProgram::trace_cfg_edges`, producing
  source-aware taken-edge reports from concrete replay traces. Focused tests
  assert fallthrough edges plus branch-true and branch-false classification for
  winning and losing imported assembly witnesses.

- **2026-06-27** — **Tiny BV block trace paths.**
  Added `TinyBvTraceBlockStep`,
  `TinyBvProgram::basic_block_containing_pc`, and
  `TinyBvProgram::trace_basic_blocks`, mapping concrete replay traces back to
  compressed block visits. Focused tests assert PC-to-block lookup and
  block-path grouping for solver-found imported memory and register-equality
  branch witnesses.

- **2026-06-27** — **Tiny BV basic blocks.**
  Added `TinyBvBasicBlock` and `TinyBvProgram::basic_blocks`, grouping the tiny
  BV instruction CFG into deterministic source/label-aware blocks. Block
  leaders include entry, assembly labels, branch targets, and instructions after
  branches or terminal blocks; blocks carry source-line lists and outgoing
  terminator edges. Focused tests assert exact block partitions for imported
  memory and register-equality branch programs.

- **2026-06-27** — **Tiny BV static CFG edges.**
  Added `TinyBvCfgEdgeKind`, `TinyBvCfgEdge`,
  `TinyBvProgram::successors`, and `TinyBvProgram::cfg_edges`, exposing a
  deterministic static CFG graph for the toy BV frontend. Focused tests pin
  fallthrough edges, branch true/false ordering, terminal-block edge absence,
  whole-program edge order, and invalid source-PC diagnostics for imported
  assembly programs.

- **2026-06-27** — **Tiny BV source-aware traces.**
  Added `TinyBvTraceSourceStep`, `TinyBvProgram::labels_at_pc`, and
  `TinyBvProgram::trace_source_steps`, giving imported assembly programs a
  deterministic source-aware view of concrete replay traces. The derived rows
  preserve each executed PC/instruction/register snapshot and attach imported
  source line plus labels, while leaving `TinyBvConcreteTrace` as the canonical
  replay artifact. Focused tests assert source-line and label annotations for
  solver-found memory and register-equality branch witnesses.

- **2026-06-27** — **Tiny BV assembly source locations.**
  Added `TinyBvProgram::from_assembly`, a deliberately small text importer for
  the toy BV frontend. The importer parses `rN` register operands, decimal/hex
  constants and branch targets, comments, labels, and the existing instruction
  set, then validates through `TinyBvProgram::new` and retains labels in a
  public deterministic map. Added `labels`, `label_pc`,
  `reach_label_checked`, and `check_label_safety_checked`; dangling labels are
  rejected before import. Added `TinyBvInsn::BranchRegEq` and assembly
  `beq rA rB THEN ELSE`, with symbolic lifting and concrete replay over two
  register terms/values. Imported programs now retain deterministic
  PC-to-source-line metadata through `source_lines()` / `source_line()`. Focused
  tests cover an imported label-bearing memory program through label-based
  checked reachability/safety, source-line mapping for concrete trace PCs, a
  register equality branch through checked reachability/concrete replay, and
  line-numbered parse errors, duplicate/missing/dangling label errors, missing
  label-query errors, plus shared register-validation errors.

- **2026-06-27** — **Tiny BV concrete traces.**
  Added `TinyBvConcreteStep`, `TinyBvConcreteTrace`, and
  `TinyBvProgram::concrete_trace`. Concrete trace replay is now the single
  implementation behind `concrete_run` and `concrete_reaches_pc`, and records
  executed PCs/instructions, pre-step registers, final PC, final registers,
  sorted explicit memory cells, and terminal outcome. Focused tests assert both
  control-flow traces and final memory/register state for solver-found witnesses.

- **2026-06-27** — **Tiny BV memory instructions.**
  Added `TinyBvInsn::Load` and `TinyBvInsn::Store`, `TinyBvState::memory`, and
  zero-initialized symbolic memory for memory-bearing tiny BV programs. The
  frontend automatically enables the memory-aware CFG checker when memory
  instructions are present, and concrete replay uses a deterministic
  zero-default memory map to match `const_array(width, 0)`. Focused tests cover
  store/load reachability and read-over-write safety.

- **2026-06-27** — **Tiny BV bounded reachability/safety.**
  Added `TinyBvReachabilityReport`, `TinyBvReachabilityStatus`,
  `TinyBvSafetyReport`, and `TinyBvSafetyStatus`, plus
  `TinyBvProgram::reach_pc_checked`, `check_pc_safety_checked`, and
  `concrete_reaches_pc`. The wrappers answer bounded PC reachability/safety
  through the checked CFG harness: reachable/unsafe returns concrete-replayed
  witnesses; unreachable/safe is reported only after diagnostic-clean exhaustive
  bounded search. Focused tests cover both reachable and unreachable target PCs.

- **2026-06-27** — **Tiny BV frontend library.**
  Added public `TinyBvProgram`, `TinyBvInsn`, `TinyBvState`,
  `TinyBvWitness`, `TinyBvConcreteOutcome`, and `TinyBvExploreOutcome`.
  The tiny target validates register/program references, declares symbolic
  inputs, lifts instructions to `CfgStep`s, explores through the checked CFG
  harness, extracts concrete input words from models, and independently replays
  witnesses in a concrete emulator. A focused integration test now exercises the
  public library frontend end to end.

- **2026-06-27** — **Checked CFG concrete replay hook.**
  Added public `CfgCheckedReached`, `CfgConcreteMismatch`,
  `CfgCheckedOutcome`, and `SymbolicExecutor::explore_cfg_checked`. The checked
  harness turns model-witnessed CFG targets into concrete-verified targets only
  after frontend-supplied witness extraction and concrete replay accept them,
  while missing witnesses and mismatches stay visible diagnostics. The tiny VM
  test now uses this checked path for its winning-input replay.

- **2026-06-27** — **CFG explorer harness.**
  Added public `CfgStep`, `CfgExploreConfig`, `CfgExploreOutcome`,
  `CfgReached`, and `SymbolicExecutor::explore_cfg`. The harness lets frontends
  supply CFG states and branch terms while the executor manages scopes,
  feasibility pruning, unknown-safe traversal, and replay-checked target models.
  The tiny VM integration now exercises the public harness and concrete-replays
  the resulting winning input.

- **2026-06-27** — **SymbolicMemory frontend helper.**
  Added public `SymbolicMemory` on the symbolic-execution surface: a typed
  array-backed memory state with declaration helpers, `load`/`store` builders,
  and load-equality branch/assume adapters that use `SymbolicExecutor`'s
  memory-aware solver path. This starts the P4.2 frontend memory model while
  preserving the honest P4.1 boundary: true warm lazy arrays/UF remain future
  work.

- **2026-06-27** — **Memory-aware incremental assumptions.**
  `IncrementalBvSolver` now defers scoped array/UF assertions to the full
  dispatcher and adds `check_assuming_with_memory` plus a coarse sound
  assumption-core variant. `SymbolicExecutor` gained memory-aware
  assume/branch/status/model/enumerate methods, closing the branch-query part of
  the symbolic-memory/keccak-as-UF consumer gap while leaving true warm lazy
  theory incrementality as P4.1 follow-up.

- **2026-06-27** — **AUFLIA returned-OR stabilization probe.**
  Scalar-candidate diagnostics now try the direct returned-OR array/store
  literal repair on a diagnostic clone and `diagnose_evidence` renders the
  terms. On `bug337`, repairing term **583** in OR **210** or term **4041** in
  OR **211** is `worse`, raises replay to **total_false=3**, and returns to
  term **3408**. This rules out direct 4041/583 repair as the large-row learned
  constraint.

- **2026-06-27** — **AUFLIA small-surface returned-OR stabilization.**
  Supported scalar readback repair now tries a capped returned-OR
  array/store-literal stabilization on small replay surfaces and keeps it only
  on strict replay improvement. The ungated `bug337` attempt regressed the
  first diagnostic phase to **231811.473 ms** and was guarded off; the capped
  large-row run is back near **52.5 s** and still unknown at term **3408**.

- **2026-06-27** — **AUFLIA returned-OR literal diagnostics.**
  Scalar follow-up diagnostics now include raw/closure returned-OR branch and
  first-false literal details, and `diagnose_evidence` renders those terms. On
  `bug337`, the 3805/4107 toggle is now grounded in array/store coherence:
  term **4041** (`x_303 = x_317`) and term **583**
  (`x_331 = store(x_317,x_320,x_337)`) disagree by one inserted array cell.

- **2026-06-27** — **AUFLIA follow-up branch-term diagnostics.**
  Replay notes now include best-branch term IDs for failed ORs and scalar
  follow-up OR hops, and `diagnose_evidence` can render them with
  `AXEYUM_DIAGNOSE_RENDER_LIMIT`. On `bug337`, the large toggle is now grounded
  as OR210 branch **3805** (store-definition branch) paired with OR211 branch
  **4107** (copy/no-store branch).

- **2026-06-27** — **AUFLIA small-surface two-OR cycle guard.**
  Branch-choice repair and the final single-literal OR fallback now decline a
  small-surface scalar+OR two-hop cycle when the next OR repair returns to the
  original OR at no replay-false improvement. The follow-up guard is capped at
  **64** positive conjuncts: the ungated large-row version regressed `bug337`
  to OR **210** and ~**72.5 s**, while the capped version keeps the term
  **3408** frontier and **52.3 s** solve/evidence band.

- **2026-06-27** — **AUFLIA scalar+OR two-step cycle diagnostics.**
  Replay notes now take one bounded second OR hop after scalar+OR closure
  exposes another failed OR. On `bug337`, the second hop reports
  `returns_first_or` in both directions: OR **210** -> OR **211** -> OR **210**
  and OR **211** -> OR **210** -> OR **211**, each at **total_false=2** after
  closure.

- **2026-06-27** — **AUFLIA scalar+OR closure diagnostics.**
  Follow-up OR diagnostics now report scalar-closure step details and closure
  replay state separately from the raw branch repair. On `bug337`, candidate
  **0** closes OR **210** only to expose OR **211** after scalar closure, while
  candidate **1** closes OR **211** only to expose OR **210**. Both stay at
  **total_false=2** after closure, identifying a two-OR toggle rather than a
  hidden improvement.

- **2026-06-27** — **AUFLIA scalar+OR follow-up diagnostics.**
  Scalar-candidate replay notes now compose an exposed OR with one bounded
  best-branch repair and scalar-closure simulation. On `bug337`, both term-3408
  scalar directions are negative evidence: OR **210** branch **0** and OR **211**
  branch **3** become locally true but worsen full replay to **total_false=3**
  and return to term **3408**. The path stays diagnostic-only; the next useful
  repair must preserve the scalar equality while reducing full replay.

- **2026-06-27** — **AUFLIA scalar-candidate diagnostics.**
  Replay notes now report top-level scalar equality repair candidates using
  the select-backed repair path. On `bug337`, term **3408** has two locally
  productive directions: `x_383 := x_330` exposes OR **210** / term **3879**,
  while `x_330 := x_383` exposes OR **211** / term **4108**. Unguarded targeted
  scalar replay repair was measured and rejected on the large row; the retained
  production repair is guarded to small replay surfaces only.

- **2026-06-27** — **AUFLIA select-backed scalar repair.**
  Scalar equality, branch-literal, and branch-schedule projection repairs now
  use asserted direct-select readbacks as backing constraints: forcing
  `y = v` with `y = select(a, i)` writes `a[i] := v` before aligning readback
  symbols. This moves `bug337` past the OR-236 scalar-closure loop to equality
  term **3408** (`x_383 = x_330`), still `unknown`, with projection repair
  changes at the new blocker down to **430**.

- **2026-06-27** — **AUFLIA scalar-closure schedule guard.**
  General multi-literal branch scheduling now uses the same returned-OR scalar
  closure guard as residual follow-up OR repair. On `bug337`, this does not
  close the row but reduces replay repair churn and brings the diagnostic/solve
  path down to about **55 s** while keeping the frontier at OR **210** / nested
  OR **236**.

- **2026-06-27** — **AUFLIA scalar-closure branch rejection guard.**
  Residual follow-up OR repair now rejects branch candidates whose bounded
  scalar closure returns to the same OR with the branch false again and no full
  replay improvement. On `bug337`, this stops the production/diagnostic repair
  chain before `followup_or236_branch0_branch`; the row remains `unknown`, but
  the route no longer spends a repair hop on the measured OR-236 closure loop.

- **2026-06-27** — **AUFLIA scalar-closure branch scoring.**
  Replay OR notes now score branch candidates after bounded scalar closure. On
  `bug337`, this rules out a simple alternate OR-236 branch choice: reported
  branches **0..7** all repair locally, then scalar closure returns replay to
  OR **236** with **final_branch_false=2** and **final_total_false=1**. The next
  lever is a missing scalar/array refinement or a production closure-aware
  rejection guard for this branch family.

- **2026-06-27** — **AUFLIA paired scalar-chain diagnostic.**
  Replay OR notes now include a paired scalar-chain trace for the selected best
  branch. On `bug337`, OR 236 branch 0 is no longer just two sibling blockers:
  repairing branch terms **12950/12951** drives scalar blockers **2611/2615**,
  and repairing those sends replay back to OR **236** with **branch_false=2**.
  Next work is scalar-closure-aware branch selection for OR 236.

- **2026-06-26** — **AUFLIA OR-236 scalar side-effect diagnostics.**
  Replay OR notes now include bounded false-literal details for the selected
  branch and simulated direct scalar-choice side effects. On `bug337`, OR 236
  branch 0 is now explicit: term **12950** can be locally repaired only by
  driving the next blocker to **2611**, while term **12951** drives the sibling
  blocker to **2615**; both leave **branch_false=1** and **total_false=2**.
  Next work should solve or explain those sibling scalar chains together.

- **2026-06-26** — **AUFLIA scalar-choice branch repair.**
  Follow-up OR repair now compares greedy branch repair with a scalar-choice
  branch candidate that explores both directions of scalar equalities and scores
  completed branch repairs by full replay. The small `u = v` / `u = 0`
  direction regression now clears. On `bug337`, the scalar-choice candidate does
  not beat the greedy OR-236 branch repair; the frontier remains term **2611**.
  Next work is an OR-236 diagnostic for both false literals and their side
  effects.

- **2026-06-26** — **AUFLIA bounded residual chain repair.**
  The small-surface branch/select-cycle repair now follows up to four generated
  OR hops after the same-branch residual store-target repair, recording the best
  strict full-replay improvement while preserving the original OR and select.
  A focused regression clears a residual follow-up OR array equality to
  **total_false=0**. The large `bug337` diagnostic now reaches OR **236** at
  **total_false=1** before a blind OR-236 branch repair worsens to scalar
  equality **term 2611**; next work is scalar-aware OR-236 handling.

- **2026-06-26** — **AUFLIA residual follow-up OR diagnostics.**
  Same-branch residual diagnostics now try one follow-up generated-OR branch
  after the residual state and emit rows such as
  `chain+same_branch_store_target+followup_or209_branch3`. A focused regression
  covers the small analogue where the follow-up OR repair clears replay. On
  `bug337`, the OR-209 branch repair preserves select **34** but keeps
  **total_false=2** and moves the blocker to OR **219** / term **6084**. Next
  work is a bounded multi-hop component-array chain, not a two-OR special case.

- **2026-06-26** — **AUFLIA same-branch residual diagnostics.**
  Branch/select candidate diagnostics now add post-select same-branch residual
  rows when a composed branch+select trial returns to the same generated OR with
  one remaining false literal. The row `chain+same_branch_store_target` captures
  the target-side store repair result without enabling that repair on large
  rows. On `bug337`, term **580**'s target-side repair keeps select **34** true
  but remains **total_false=2** and exposes OR **209** / term **3654**, with a
  branch-3 false literal term **3650** over the same array values flipped. Next
  work is paired OR-210/OR-209 component-array repair.

- **2026-06-26** — **AUFLIA guarded same-branch store residual repair.**
  Added a small-surface target-side residual repair for branch/select cycles:
  after branch repair plus store-chain select repair returns to the same OR, if
  the same branch has exactly one remaining false literal of the shape
  `target = store(base,i,v)`, rebuild `target` from the current repaired `base`
  and accept only if full-original replay strictly improves. A focused
  regression covers preserving `c = store(a,3,7)` after `5 = select(a,i)`
  repairs the base array. The unguarded `bug337` probe was measured and rejected:
  no movement from OR **210** / term **3879**, and route time grew to about
  **87 s**. Next work is residual-candidate/component-array diagnostics for the
  concrete term **580** blocker, not a broader same-branch store repair.

- **2026-06-26** — **AUFLIA returned-OR branch/select diagnostics.**
  Branch/select diagnostics now carry returned-OR details for the first global
  blocker after each composed branch+select trial. On `bug337`, this shows that
  after branch **0** -> select **34** chain repair, OR **210**'s best branch is
  still branch **0** with exactly **1/8** false literals: **term 580**,
  `x_339 = store(x_325, x_337, 2)`, with incompatible array values. Next work
  is preserving the select-34 readback while repairing branch-0 store-definition
  term **580** / component arrays.

- **2026-06-26** — **AUFLIA guarded branch/select cycle repair.**
  Added a bounded repair for small branch/select cycles: after one OR branch
  repair exposes a direct select blocker and the select repair returns to the
  same OR, try a different branch from the post-select state and accept only a
  strict full-replay improvement. The repair is capped at **8** branches,
  **32** second-branch trials, **current_false <= 2**, and **<=64** replay
  conjuncts; a focused regression covers the intended array-copy/select-break/
  alternate-branch shape. The large `bug337` unguarded attempt was measured and
  rejected: no movement from OR **210** / term **3879**, and route time rose
  from about **77 s** to about **93 s**. With the guard, `bug337` returns to the
  prior OR-210 frontier. Next work is component-level store-chain / branch-state
  repair inside **210 -> 34 -> 210**, not just selecting another OR branch.

- **2026-06-26** — **AUFLIA branch/select cycle diagnostics.**
  Final generated-OR replay failures now report bounded branch-select candidate
  rows: after a repairable OR branch, if the next global blocker is a direct
  select equality, diagnostics try the store-chain and direct array-entry
  select repairs on that branch trial and record full-replay status plus the
  next blocker. A focused regression pins the shape. On `bug337`, the target
  cycle is now explicit: branch **0** -> select **34** chain repair makes term
  **555** true but remains **worse_full_replay**, **total_false=2**, and lands
  back on OR **210** / term **3879**; the direct select repair worsens to
  **total_false=3** and exposes ordinal **35** / term **560**. Next work is a
  cycle-aware repair for **210 -> 34 -> 210**, not broader OR-start beam search
  or another one-step select repair.

- **2026-06-26** — **AUFLIA guarded OR/select replay beam.**
  Generated-OR replay failures now invoke the mixed select/OR replay beam only
  when the replay surface is small and genuinely multi-false
  (**current_false > 1**, **<=64** positive conjuncts). A focused regression
  pins the useful retained case where OR repair ties full replay by breaking a
  direct select readback and the composed select repair then strictly improves
  the full replay count. The unguarded large-row policy was measured and
  rejected: `bug337` regressed from OR **210** back to select equality **34** /
  term **555** and the diagnostic wall time rose to about **149 s**. With the
  guard, `bug337` returns to OR **210** / term **3879** at about **76 s** wall.
  Next work should target the concrete **210 branch-0 -> 34 select** cycle, not
  broaden OR-start beam search.

- **2026-06-26** — **AUFLIA mixed select/OR replay beam.**
  Direct-select targeted replay repair now starts with a bounded mixed beam over
  direct select failures and generated OR failures, accepting only a composed
  strict full-replay improvement before mutating the projection. The beam is
  capped at width **8**, **64** expansions, depth **6**, `current_false + 4`
  temporary false conjuncts, and two visits per failure ordinal. A focused
  regression pins the intended same-count select repair plus follow-up OR repair
  shape. On `bug337`, this moves the final replay miss from direct select
  equality **34** / term **555** to generated OR **210** / term **3879**, with
  **projection_repair_changes=587**. OR 210's best branch **0** locally repairs
  but returns to select equality **34** at **total_false=2**; branch **3** lands
  on OR **211**, and the branch-3 pair path reaches OR **212**. The next AUFLIA
  move should either invoke the mixed beam from generated-OR failures too or
  diagnose the **210 branch-0 → 34 select** cycle directly, while tightening cost
  controls because the 10 s diagnostic route now takes about **76 s** wall.

- **2026-06-26** — **AUFLIA direct-select repair diagnostics.**
  Final lazy-extensionality replay failures for direct `x = select(a,i)`
  equalities now report `select_candidate_diagnostics`: store-chain/readback and
  direct array-entry candidates are tried on projection copies and annotated
  with target truth, repair changes, full replay false count, and the first
  global blocker. The focused regression covers the case where both candidates
  repair the select equality but leave a later assertion false. On `bug337`, the
  first replay miss is still ordinal **34**, term **555**,
  `x_388 = select(x_325, x_337)`, values **1** vs **0**. The new diagnostic is
  actionable: the `chain` candidate makes term 555 true but is
  **same_full_replay** (**changes=37**, **total_false=2**) and lands on generated
  OR **210** / term **3879**; the `direct` candidate also makes term 555 true
  but is **worse_full_replay** (**changes=1**, **total_false=3**) and lands on
  ordinal **35** / term **560** (`0` vs `1`). The next AUFLIA move should
  compose the same-full-replay chain candidate with generated-OR repair under a
  final strict replay-improvement gate, not add another one-step select repair.

- **2026-06-26** — **AUFLIA selected carry-component projection.**
  Targeted lazy-extensionality replay now repairs direct array equality branch
  literals by solving the selected carry component, not just one equality edge:
  it gathers adjacent selected/best-branch array equalities touching the failed
  pair, tries every component member as the representative value, aligns
  readback symbols, and keeps only branch-improving/full-replay-non-worsening
  trials. A narrow targeted direct-select repair is also covered for cases where
  the failed replay conjunct is exactly `x = select(a,i)`. On `bug337`, the
  10 s diagnostic moves past generated branch **9841** / `x_31 = x_17` to direct
  readback equality ordinal **34**, term **555**, `x_388 = select(x_325,
  x_337)`, values **1** vs **0**, with **571** projection repair changes. The
  row remains `unknown`; a targeted select-stabilization trial was rejected
  because it regressed to branch **9841** and raised projection churn.

- **2026-06-26** — **AUFLIA replay branch-choice candidates.**
  Last-candidate lazy-extensionality replay now evaluates all positive branches
  of a failed generated disjunction on projection copies and keeps only
  replay-non-worsening repairs, choosing deterministically by total false
  conjuncts, branch false literals, and branch ordinal. A focused regression
  covers the case where the reported best branch is an unrepaired Boolean
  literal and a later branch is repairable. On `bug337`, the 10 s diagnostic
  moves from the prior branch/equality/lower-branch cycle to generated branch
  ordinal **232**, term **9841**; best branch **3** has one false literal
  **2520**, `x_31 = x_17`, with arrays
  `(array default 0 [0 -> 1] [1 -> 3] [2 -> 3])` vs
  `(array default 0 [1 -> 2] [2 -> 1])`. The row remains `unknown`; the next
  target is component-level store-chain/readback projection for this lower
  queue-lock branch.

- **2026-06-26** — **AUFLIA targeted replay branch repair.**
  Last-candidate lazy-extensionality replay now performs a bounded targeted
  repair for the exact single false branch literal reported by full original
  replay, then immediately replays again. A focused regression pins the
  `b = store(a,i,v)` branch-literal case. On `bug337`, this moves the 10 s
  diagnostic past branch term **3654** / first false term **495** to direct
  readback equality ordinal **208**, term **3440**, `x_384 = x_344`, values
  **0** vs **1**, with **419** projection repair changes. The row remains
  `unknown`; measured rejected probes show the next unit of work is the
  component-level branch-choice/readback cycle across branch **3654**, equality
  **3440**, and lower branch **3879**.

- **2026-06-26** — **AUFLIA support-aware scalar/readback projection.**
  Lazy-extensionality replay projection now scores scalar equality directions by
  asserted-select readback support, widens bounded projection stabilization to
  32 rounds, and reports support-aware scalar trial counters in replay failure
  notes. The new focused regression covers read-supported scalar propagation
  through an equality chain. On `bug337`, the 10 s diagnostic advances past
  `x_366 = x_92` to branch ordinal **209** / term **3654**; best branch **0**
  has one false literal, `x_345 = store(x_331, x_334, x_351)`, after **417**
  projection repair changes. The row remains `unknown`; the next target is a
  branch-consistent store-chain/readback projection for that queue-lock step.

- **2026-06-26** — **Replay-gated lazy-extensionality candidates.**
  Lazy extensionality now preserves the latest scalar `sat` candidate and tries
  one final projection/original replay before returning timeout/scalar-unknown/
  max-round `unknown`. A candidate can only become `sat` if every original
  assertion evaluates true under the reconstructed model; otherwise the unknown
  path is preserved and annotated. On `bug337`, the candidate does not replay:
  the 10 s detail now ends with
  `last_candidate_replay=false(assertion_ordinal=0, term=13053, failed_conjunct_ordinal=30, failed_conjunct_term=465)`,
  so the row remains open but the next target is the failed branch/support, not
  a blind CEGAR cap.

- **2026-06-26** — **AUFLIA lazy-extensionality diagnostics.**
  Lazy extensionality deadline/scalar/max-round `unknown` details now carry
  refinement counters (`round`, `sites`, `array_eq_atoms`, ROW/congruence lemmas,
  diff-skolems, and working assertions). A zero-timeout regression pins the
  format. The 10 s `bug337` diagnostic now reports **round=2**, **sites=4096**,
  **array_eq_atoms=150**, **row_lemmas=42**, **cong_lemmas=6973**,
  **diff_skolems=146**, and **working_assertions=7127**, so the next AUFLIA
  move should be site/relevance control or replay-gated queue-lock model
  construction.

- **2026-06-26** — **UFLIA CEGAR tuning guardrails.**
  Measured and rejected three tempting generated-row tweaks: nearest-constant
  cap-1 UF sibling ordering (**5** UF rounds / **4** candidates at 10 s),
  staged affine-core cap **2** (**blocking_lemmas=323**, **core_src_lp=221**),
  and simple-bound batch cap **64** (**blocking_lemmas=301**,
  **core_src_lp=210**). No code from those experiments was retained; the
  baseline remains sibling cap **1**, affine cap **1**, and bound cap **32**.

- **2026-06-26** — **Lazy UF CEGAR timing telemetry.**
  Lazy function-consistency `unknown` details now report `elapsed_ms`,
  `first_candidate_ms`, and `last_candidate_ms` in addition to the refinement
  counters. The cap-2 sibling experiment was measured and rejected
  (**5** UF rounds / **4** candidates at 10 s), so the committed cap remains
  **1**. On the hard generated QF_UFLIA row, cap 1 still preserves **6** UF
  rounds / **5** candidates at 10 s, with candidate timing now visible
  (**first_candidate_ms=1025**, **last_candidate_ms=8324**).

- **2026-06-26** — **Post-candidate unary-Int UF sibling scheduling.**
  Lazy UF CEGAR now reports `sibling_lemmas` and adds at most one sibling
  dynamic-vs-constant Ackermann lemma after a real unary-Int UF violation. Wider
  caps were measured and rejected because they reduced 10 s candidate progress.
  The committed cap preserves the hard row's **6** UF rounds / **5** candidates
  while adding **5** sibling lemmas and slightly lowering warm arithmetic
  pressure (**total_rounds=280**, **blocking_lemmas=295**,
  **core_src_lp=204**).

- **2026-06-26** — **Staged affine arithmetic core extraction.**
  Lazy arithmetic now recognizes dynamic two-literal conflicts between checked
  affine integer bounds even when the equivalent linear expressions have
  different syntax. The extractor is disabled on the first warm arithmetic
  solve and then capped to one affine core per theory conflict after UF lemmas
  strengthen the skeleton. The generated QF_UFLIA hard row remains `unknown`,
  but the useful 1 s UF frontier is preserved (**2** rounds, **1** candidate,
  **6** learned UF lemmas), and the 10 s hard row preserves **6** UF rounds /
  **5** candidates / **24** learned UF lemmas while shifting **49** cores to
  `core_src_affine` and reducing LP cores to **207**.

- **2026-06-26** — **Opaque-app online UFLIA construction is bounded.**
  Large combined opaque-app UFLIA states now use deferred LIA feasibility at
  the theory-propagation boundary, Boolean UFLIA construction has deadline
  checkpoints, and opaque-app layouts that cannot build the incremental
  combined state decline instead of falling into the unsafe enumerative
  fallback. With the opaque cap temporarily raised to **512**, both generated
  direct probes now decline in about **4 ms** with the incremental-build-safety
  diagnostic instead of running past **30 s**. The committed cap remains
  **128** because this is safe decline, not convergence.

- **2026-06-26** — **Shared CDCL(T) propagation honors deadlines.**
  The generic online `Dpll<T: TheorySolver>` now checks deadlines inside
  Boolean unit propagation and theory propagation. Timeout returns through the
  existing `solve_with_deadline = None` path; conflicts still use the existing
  1-UIP analysis. A focused unit test covers expired-deadline unit
  propagation. Re-running the broad opaque cap experiment still exceeded
  **30 s**, so remaining opaque-heavy admission work is construction/encoding or
  theory-propagation generation, not this loop boundary.

- **2026-06-26** — **Opaque-app online guard partitioned by opaque atom count.**
  The online UFLIA opaque-app guard now counts actual opaque Int-UF order atoms
  instead of rejecting by total theory atoms whenever any opaque app appears.
  Large mixed skeletons with a small opaque subset are admitted; a new
  regression covers **>128** total atoms with one opaque order atom. The
  generated overbound rows remain guarded with a sharper diagnostic:
  **334** opaque-app order atoms out of **485** total. A broad cap raise to
  **512** was measured and rejected because 1 s direct probes still ran past
  **30 s**.

- **2026-06-26** — **Opaque-app online UFLIA theory checks now inherit deadlines.**
  `LiaTheory` carries the online DPLL(T) deadline into feasibility, core
  minimization, model reconstruction, and propagation probes, including the
  opaque Int-UF app abstraction. `CombinedIncrementalLia` and the enumerative
  `CombinedTheoryLia` fallback forward that deadline to nested LIA state. A
  zero-timeout Boolean opaque-app UFLIA regression now returns `Timeout` before
  theory work. The generated overbound probes still stop at the **128** atom
  guard (`485 > 128`), and the production lazy 1 s frontier remains **2** UF
  rounds, **1** candidate, and **6** learned UF lemmas.

- **2026-06-26** — **Bounded opaque-app online UFLIA order support.**
  Online UFLIA now treats Int-sorted UF applications in Int order atoms as
  opaque LIA variables for UNSAT/conflict/propagation checks, reusing the
  existing opaque-app arithmetic abstraction. Pure Int UF equality-only SAT
  remains on the EUF replay path. Large opaque-app online skeletons now decline
  above **128** theory atoms; the generated overbound probes moved from
  `non-Boolean term with sort Int` to
  `too many theory atoms for opaque-app online UFLIA: 485 > 128`. The guard
  prevents the pre-guard behavior where the direct online probe ran for more
  than **90 s** despite a 1 s timeout. The production lazy 1 s frontier remains
  **2** UF rounds, **1** candidate, and **6** learned UF lemmas.

- **2026-06-26** — **Online UFLIA Boolean boundary diagnosed.**
  Added `uflia_online_probe`; the online UFLIA Boolean encoder now handles
  n-ary `and`/`or`, Boolean equality/IFF, precise theory-atom collection, and
  first unsupported-shape details. Direct hard-row probes now decline with
  `non-Boolean term with sort Int`, identifying opaque UF applications inside
  Int arithmetic atoms as the next online-combination gap. The production lazy
  route is preserved but not improved: the 10 s hard row remains `unknown` with
  **6** UF rounds, **24** learned UF lemmas, and LP-core-dominated arithmetic
  timeout telemetry.

- **2026-06-26** — **Bounded LP-relaxation core shrinking retained.**
  Small LP-relaxation Farkas supports are now deletion-minimized through the
  same LP infeasibility checker used for self-checking, capped at **24** atoms.
  The QF_UFLIA 10 s hard row remains `unknown`, but warm arithmetic pressure
  improves from **305** rounds / **319** blocking lemmas /
  **core_src_lp=276** / **core_len_avg=7.3** to **290** rounds /
  **303** blocking lemmas / **core_src_lp=260** / **core_len_avg=6.9** while
  preserving the 1 s UF frontier.

- **2026-06-26** — **Arithmetic core-source diagnostics expose LP-core bottleneck.**
  Lazy arithmetic DPLL timeout details now include dynamic core-source counts.
  The QF_UFLIA 10 s hard row is dominated by LP-relaxation cores
  (**core_src_lp=276**) with no minimized or large fallback cores, narrowing the
  next lever to LP-core relevance/shrinking rather than deletion minimization.

- **2026-06-26** — **Integer-bound theory tautologies folded before LIA abstraction.**
  Simple Int-bound contradictions/tautologies now fold before Boolean atom
  allocation. The QF_UFLIA overbound rows remain `unknown`, but the retained
  frontier is preserved; the 10 s first row now learns **24** UF lemmas before
  timeout.

- **2026-06-26** — **Implication flattening rejected for UFLIA search shape.**
  Flattening arithmetic-guarded UF implications into disjunctions was measured
  and rejected: both generated QF_UFLIA 1 s rows lost the first UF candidate.
  The implication-preserving path is now documented in code; retained
  diagnostics stay at **1** candidate and **6** UF lemmas at 1 s.

- **2026-06-26** — **UF batching policy guardrail retained.**
  A violated-pair-only lazy UF refinement experiment was measured and rejected:
  both generated QF_UFLIA 1 s rows regressed to **0** candidates. Added a
  focused test pinning the retained policy that once any violation appears in a
  candidate, all currently equal-argument pairs are batched. The warm-skeleton
  hard-row diagnostics remain at **1** candidate / **6** UF lemmas at 1 s and
  **5** candidates / **23** UF lemmas at 10 s.

- **2026-06-26** — **Warm arithmetic skeleton for lazy UFLIA CEGAR.**
  Lazy UF+arithmetic now keeps one `IncrementalArithDpll` state across
  monotone UF congruence refinements and asserts only the newly learned UF
  lemmas into that warm arithmetic skeleton. The generated rows remain
  `unknown`, but at 1 s both rows now reach actual UF refinement
  (**2** rounds, **1** candidate, **6** UF lemmas); at 10 s the hard row keeps
  **6** rounds, **5** candidates, and **23** UF lemmas with warm-state
  diagnostics (**solve_calls=6**, **total_rounds=279**, **blocking_lemmas=295**).

- **2026-06-26** — **Reusable arithmetic lemmas advance UFLIA CEGAR.**
  Lazy UF+arithmetic CEGAR now reuses dynamic arithmetic conflict clauses across
  UF refinement rounds by rebuilding them over original arithmetic terms. Static
  upfront bound lemmas are not carried. The generated rows remain `unknown`, but
  1 s diagnostics move to **42** support-conflict rounds and **56** reusable
  lemmas; the 10 s hard row moves to **6** UF rounds, **5** candidates, and
  **23** learned UF lemmas, carrying **357** reusable arithmetic lemmas by the
  final timeout.

- **2026-06-26** — **UF pair profile rules out guarded preseed.**
  Added `axeyum-bench --example uf_pair_profile` to profile lazy UF
  same-function application groups and potential Ackermann pair categories from
  an SMT-LIB file. The hard QF_UFLIA overbound row has **42** applications,
  **3** function groups, and **282** potential pairs, of which **214** are
  constant-vs-constant. A capped **64** unary-Int nonconstant/constant preseed
  experiment was rejected: it grew the arithmetic abstraction to **673 atoms**
  and reached **0** UF candidates at 10 s.

- **2026-06-26** — **Support-path diagnostics expose UFLIA CEGAR blocker.**
  Lazy arithmetic DPLL `unknown` details now report support attempts,
  unavailable supports, support conflict batches, support-model attempts, replay
  failures, and full-assignment fallbacks. The generated QF_UFLIA overbound
  1 s rows preserve the support-first baseline and now show
  **support_attempts=21**, **support_conflict_batches=21**, and
  **full_fallbacks=0**; the 10 s row remains **4** UF CEGAR rounds,
  **3** candidates, and **14** learned UF lemmas before the outer deadline.
  Full Ackermann preseed and broad pre-abstraction folding were measured and
  rejected for these rows.

- **2026-06-26** — **Boolean-support arithmetic checks cut dead-branch churn.**
  Lazy arithmetic DPLL now extracts a deterministic Boolean justification support
  for each SAT skeleton candidate and checks/replays that support before the full
  arbitrary SAT assignment. The target QF_UFLIA rows remain `unknown`, but 1 s
  diagnostics move to **21** lazy-LIA rounds and **29** dynamic blockers; the
  10 s row now reaches **3** UF candidates and learns **14** UF lemmas before
  timing out in outer UF+arithmetic CEGAR convergence.

- **2026-06-26** — **Bounded complement-bound implications prune UFLIA ladders.**
  The upfront LIA implication pass now seeds adjacent monotonicity for complement
  bounds under the existing atom/lemma caps. The target QF_UFLIA rows remain
  `unknown`, but 1 s diagnostics move to **642 bound lemmas / 27 rounds / 171**
  dynamic blockers, and the 10 s post-CEGAR row improves to **475 atoms / 60
  rounds / 200** dynamic blockers.

- **2026-06-26** — **Lazy LIA batches model-guided bound conflicts.**
  The lazy arithmetic DPLL loop now learns up to 32 independent simple
  integer-bound conflicts from one SAT candidate before re-solving. The target
  QF_UFLIA overbound rows remain `unknown`, but the 1 s rows move from **61**
  one-core rounds to **29** batched rounds with **238** blocking lemmas; the 10 s
  post-CEGAR row times out after **87** rounds and **296** blocking lemmas.

- **2026-06-26** — **Lazy UF consistency batches same-candidate lemmas.**
  The lazy UF CEGAR loop now pre-seeds cheap fixed-bound congruence lemmas and,
  after any real candidate violation, batches all same-candidate equal-argument
  lemmas. The generated QF_UFLIA overbound rows still return `unknown`: pre-seed
  finds 0 target lemmas, and the 10 s row now adds 6 lemmas before timing out in
  the 479-atom post-CEGAR arithmetic skeleton.

- **2026-06-26** — **Arithmetic order polarity abstraction shrank UFLIA.**
  Strict arithmetic orders now abstract as Boolean negations of non-strict
  reversed-order representatives, and generated Boolean definition tautologies
  are folded before SAT encoding. The QF_UFLIA overbound rows still return
  `unknown`, but their 1 s abstraction shrank from 873 to 461 atoms and now
  reaches roughly 61 lazy-LIA rounds; at 10 s it reaches a UF CEGAR candidate and
  adds Ackermann lemmas before timing out in the post-CEGAR arithmetic skeleton.
  Full `axeyum-solver` library tests pass again after aligning two proof-route
  priority assertions with the current dispatcher.

- **2026-06-26** — **LIA LP core diagnostics added.**
  Integer simplex collection now preserves assertion origins and exposes a
  self-checked LP-relaxation unsat-core helper. The lazy arithmetic loop tries
  that core and reports learned core sizes. The QF_UFLIA overbound rows still
  return `unknown`, but now show every dynamic core is length 2, shifting next
  work from core minimization to SAT/search relevance in the 873-atom skeleton.

- **2026-06-26** — **QF_UFLIA overbound route duplication removed.**
  Overbound non-array integer UF+arithmetic now skips generic `lia-dpll` after
  exact linear refuters decline and routes the single large abstraction through
  UF-aware lazy CEGAR. The target rows no longer spend two timeout windows on the
  same 873-atom arithmetic skeleton; they still remain `unknown` with
  `sat_candidates=0`, pointing next at arithmetic-skeleton relevance/core work.

- **2026-06-26** — **Large online LIA feasibility deferred.**
  Large online LIA skeletons now defer full feasibility checks to the
  theory-propagation boundary and skip LP entailment/core minimization in that
  mode. The generated QF_UFLIA overbound rows now get past the online
  first-propagation stall and reach the legacy lazy arithmetic fallback at 1 s
  (31-33 rounds over 873 atoms), leaving the fallback refinement loop as the next
  blocker.

- **2026-06-26** — **Online LIA timeout stats added.**
  Online LIA DPLL(T) timeouts now include search-state counters. The generated
  QF_UFLIA overbound rows time out at 1 s with one decision, zero conflicts, no
  learned clauses, and a 1314-literal trail, pointing next work at relevance /
  propagation cost rather than conflict-learning churn.

- **2026-06-26** — **Bounded pre-LIA UF+arithmetic probe added.**
  Over-eager-bound non-array integer UF+arithmetic queries now get a cloned,
  capped lazy UF+arithmetic probe before generic opaque-app `lia-dpll`. Small
  overbound congruence conflicts can decide there; generated QF_UFLIA overbound
  rows skip the probe quickly because their 1248 assertions would duplicate the
  large function-free arithmetic skeleton solve.

- **2026-06-26** — **QF_UFLIA overbound dispatch starvation diagnosed.**
  Added `unknown` diagnostics for lazy function-consistency CEGAR stats and for
  generic LIA DPLL budget exhaustion before UF-aware routes. Both QF_UFLIA
  overbound rows now report that UF-aware solving is not reached from
  `check_auto` because opaque-app LIA DPLL consumes the budget first
  (`ackermann_pairs=282`), sharpening the next task to route scheduling /
  deadline sharing rather than more shallow bound seeding.

- **2026-06-26** — **QF_UFLIA overbound equality propagation retained.**
  Added conservative online LIA propagation for integer equality atoms:
  equality-true needs both strict disequality branches LP-infeasible, and
  equality-false needs the equality branch LP-infeasible. The two QF_UFLIA
  overbound rows remain `unknown` at 10 s, so this is recorded as pruning, not a
  decide-rate win. The broader upfront complement-bound lemma widening was
  tested and rejected because it inflated initial lemmas without closing either
  row.

- **2026-06-26** — **QF_UFLIA parent dominance audit ingested.**
  Committed the exact dominance audit for the parent
  `qf-uflia-cvc5-regress-clean` row. The six decided instances are now **6/6
  dominant**, Lean unsat **2/2**, with **mismatches=0**, **audit_errors=0**,
  and **timeouts=0**. Regenerated `bench-results/DOMINANCE.md`; it now reports
  **23 complete exact audit rows**.

- **2026-06-26** — **QF_AX declared-sort SAT rows closed.**
  Added a declared-sort EUF scalar backend for lazy QF_AX ROW/extensionality and
  refined true array equalities over compatible materialized/store indices. This
  closes `arrays2` and `arrays3` with replay-checked generic-array SAT models.
  QF_AX is now **8/8 decided**, **unsupported=0**, **DISAGREE=0**, and the exact
  audit is **8/8 dominant**, Lean unsat **5/5**. Scoreboards now report
  **663 decided** and **611 oracle-compared** overall.

- **2026-06-26** — **QF_AX Bool-array read-collapse row closed.**
  Added a checked Bool-index array read-collapse refuter with evidence and Lean
  reconstruction. It closes cvc5 QF_AX `bool-array.smt2` as UNSAT and refreshes
  QF_AX to **6/8 decided**, **unknown=0**, **unsupported=2**,
  **DISAGREE=0**. The exact audit is now **6/6 dominant**, Lean unsat **5/5**,
  with no mismatches, audit errors, or timeouts. Scoreboards now report
  **661 decided** and **609 oracle-compared** overall.

- **2026-06-26** — **Exact QF_AX dominance row closed.**
  Added checked evidence and Lean reconstruction for QF_AX declared-sort
  read-congruence and cross-store disequality refutations. The committed QF_AX
  dominance audit is now **5/5 dominant**, Lean unsat **4/4**,
  **mismatches=0**, **audit_errors=0**, and **timeouts=0**. Regenerated the
  dominance scoreboard; it now reports **22 complete exact audit rows**.

- **2026-06-26** — **QF_AX declared-sort cross-store rows closed.**
  Added a structural reciprocal-store refuter for same-index array swaps over
  arbitrary component sorts. It closes QF_AX `arrays0` and `arrays4` as UNSAT,
  does not match SAT `arrays3`, and refreshes QF_AX to **5/8 decided** with
  **DISAGREE=0**. Scoreboards now report **660 decided** and **608
  oracle-compared** overall.

- **2026-06-26** — **Exact QF_ALIA dominance row closed.**
  Added checked evidence and Lean reconstruction routes for the QF_ALIA
  constant-default mismatch and store-chain/readback refuters. The cvc5 QF_ALIA
  audit is now **6/6 dominant**, Lean unsat **5/5**, **mismatches=0**,
  **audit_errors=0**, and **timeouts=0**. Regenerated the dominance scoreboard;
  it now reports **21 complete exact audit rows** and an empty first audit queue.

- **2026-06-26** — **QF_ALIA `ios_np_sf` closed.**
  Added a checked finite store-chain/readback refuter for shared-base
  `(Array Int Int)` equalities with unit-affine index disequality reasoning.
  QF_ALIA is now **6/6 decided**, **unknown=0**, **unsupported=0**,
  **DISAGREE=0**; scoreboards now report **658 decided** and
  **606 oracle-compared** overall.

- **2026-06-26** — **QF_ALIA `constarr3` closed.**
  Added a checked finite-write/constant-default mismatch refuter for Int-indexed
  arrays. QF_ALIA is now **5/6 decided**, **unsupported=0**, **DISAGREE=0**;
  scoreboards now report **657 decided** and **605 oracle-compared** overall.

- **2026-06-26** — **QF_ALIA/AUFLIA array baselines refreshed.**
  Added finite cvc5 `eqrange` lowering plus constant-index self-store equality
  normalization, and made scalar-array preprocessing replay failures fall back
  to the raw scalar backend. QF_ALIA is now **4/6 decided**, QF_AUFLIA is now
  **5/7 decided**, both with **unsupported=0** and **DISAGREE=0**. Regenerated
  scoreboards now report **656 decided** and **604 oracle-compared** overall.

- **2026-06-26** — **QF_UFLIA parent row refreshed.**
  Re-ran the parent cvc5-regress-clean QF_UFLIA baseline over the actual parent
  corpus. It moves from the stale bounded snapshot **4/8 decided, unsupported=4**
  to **6/8 decided, unknown=2, unsupported=0**, with **DISAGREE=0**. Regenerated
  scoreboards now report **651 decided** and **600 oracle-compared** overall.

- **2026-06-26** — **QF_UFLIA bounded row remeasured to full dominance.**
  Refreshed the bounded declared-sort QF_UFLIA baseline and exact dominance
  audit after the current mixed UF+arithmetic route already decides `bug303`.
  The row is now **6/6 decided**, **DISAGREE=0**, **6/6 dominant**, and Lean
  unsat **2/2**. Regenerated scoreboards then reported **649 decided** and
  **598 oracle-compared** overall.

- **2026-06-26** — **Exact QF_UF overbound dominance row closed.**
  Added a checked online Boolean-EUF certificate and Lean route for large
  pure-EUF Boolean skeletons that are too large for exhaustive assignment
  enumeration. The overbound QF_UF audit now certifies all four baseline-decided
  instances: **4/4 dominant**, Lean unsat **3/3**, **mismatches=0**,
  **audit_errors=0**, and **timeouts=0**. Regenerated the dominance scoreboard;
  at that point it reached its **20th complete exact audit row**.

- **2026-06-26** — **Exact QF_UF bounded declared-sort dominance row closed.**
  Moved the direct structural evidence pre-solve ahead of the pure-real
  LRA/NRA evidence branch, so `issue3970-nl-ext-purify` no longer returns
  checked `unknown`; its expanded `distinct` contains a reflexive disequality
  and now certifies as `term-identity-unsat` with Lean fragment
  `TermIdentity`. Regenerated the exact QF_UF dominance audit and dominance
  scoreboard: **44/44 dominant**, Lean unsat **15/15**, **mismatches=0**,
  **audit_errors=0**, and **timeouts=0**.

- **2026-06-26** — **QF_UF div/mod underspecification guard and remeasurement.**
  Fixed a QF_UF soundness hazard where SMT-LIB integer `mod` by zero was being
  concretized through the evaluator convention during an UNSAT route. Arithmetic
  routes now decline div/mod/real-div terms whose divisor is not a syntactically
  known nonzero constant, and the lazy arithmetic DPLL abstractor validates atoms
  before they enter the Boolean skeleton. Refreshed QF_UF baselines:
  overbound **4/6 decided**, bounded **44/82 decided** on both current rows,
  all with **DISAGREE=0**. Regenerated scoreboards: **648 decided**,
  **597 oracle-compared**, **18 complete exact audit rows**.
  Verification:
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib mod_by -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --lib abstractor_rejects_unsupported_integer_mod_atom -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-bounded/cli__regress1__sygus__proj-issue165.smt2 10000`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --features z3 -- corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-bounded --timeout-ms 10000 --backend solver --compare-z3 --jobs 4 --out bench-results/baselines/qf-uf-cvc5-regress-clean-bounded-solver-vs-z3-10s.json`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --features z3 -- corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-bounded --timeout-ms 10000 --backend solver --compare-z3 --jobs 4 --out bench-results/baselines/qf-uf-cvc5-regress-clean-bounded-uninterp-sorts-solver-vs-z3-10s.json`;
  `CARGO_BUILD_JOBS=2 cargo run -q -p axeyum-bench --features z3 -- corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-overbound --timeout-ms 10000 --backend solver --compare-z3 --jobs 4 --out bench-results/baselines/qf-uf-cvc5-regress-clean-overbound-uninterp-sorts-solver-vs-z3-10s.json`;
  `python3 scripts/gen-scoreboard.py`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `CARGO_BUILD_JOBS=2 cargo check -p axeyum-solver --lib -j1`;
  `CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --lib --all-features -j1 -- -D warnings`;
  `python3 -m py_compile scripts/gen-scoreboard.py scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **Exact QF_NRA synthetic dominance row closed.**
  Added first-class `UnsatNraEvenPower` evidence and
  `ProofFragment::NraEvenPower` reconstruction for the remaining higher-degree
  synthetic NRA proof misses (`nra-neg-square-d02..d06` and
  `nra-sos-strict-unsat-d02`). The certificate checker re-scans the original
  assertions and accepts only strict-negative sums of syntactic even powers plus
  a nonnegative rational constant; Lean reconstruction reuses the same checked
  route before rendering. Re-ran the exact QF_NRA synthetic audit and
  regenerated `bench-results/DOMINANCE.md`: QF_NRA synthetic is now **30/30
  dominant** with Lean unsat **16/16**, with zero mismatches, audit errors, and
  timeouts.
  Verification:
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-solver --lib -j1`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --test evidence qf_nra_even_power_rows_use_checked_evidence -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --test lean_crosscheck qf_nra_even_power_audit_rows_check_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-nra-synthetic-graduated-vs-z3.json 30000 30 bench-results/dominance/qf-nra-synthetic-graduated-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **Exact QF_NIA synthetic dominance row closed.**
  Added first-class `UnsatBoundedIntBlast` evidence and
  `ProofFragment::BoundedIntBlast` reconstruction for bounded nonlinear-integer
  UNSAT rows. The bounded-int-blast certificate recheck now re-derives the
  finite box, verifies the covering width, regenerates the clamped DIMACS from
  the original query, and rechecks DRAT before the evidence or Lean wrapper is
  accepted. Also added a pre-preprocessing bounded-box evaluator, which keeps
  bounded NIA SAT rows such as the synthetic Pythagorean family on the fast,
  replay-checkable model path. Re-ran the exact QF_NIA synthetic audit and
  regenerated `bench-results/DOMINANCE.md`: QF_NIA synthetic is now **32/32
  dominant** with Lean unsat **16/16**, with zero mismatches, audit errors, and
  timeouts.
  Verification:
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-solver --lib -j1`;
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --test evidence qf_nia_bounded_unsat_rows_use_bounded_int_blast_evidence -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --test lean_crosscheck qf_nia_bounded_int_blast_audit_rows_check_in_real_lean -j1 -- --nocapture`;
  `AXEYUM_DIAGNOSE_ONLY_EVIDENCE=1 CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/synthetic/QF_NIA/graduated/nia-pythagorean-m08.smt2 30000`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-nia-synthetic-graduated-vs-z3.json 30000 32 bench-results/dominance/qf-nia-synthetic-graduated-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **Exact QF_UFLIA dominance rows closed.**
  Added an unsat-oriented opaque-UF mode for the integer simplex and wired
  ArithDPLL to verify integer theory lemmas with it. The dispatcher treats a
  satisfiable opaque arithmetic abstraction as a decline for mixed UF+Int rows,
  preserving replay-checked UFLIA SAT model lifting. Lean reconstruction now
  routes mixed UF+arithmetic rows to `ProofFragment::ArithDpll` only after the
  widened certificate re-verifies. Re-ran the exact QF_UFLIA audits and
  regenerated `bench-results/DOMINANCE.md`: curated named is now **2/2
  dominant** with Lean unsat **2/2**, and bounded uninterpreted-sort
  regressions are **5/5 dominant** with Lean unsat **1/1**, with zero
  mismatches, audit errors, and timeouts.
  Verification:
  `cargo test -p axeyum-solver --test evidence congruence_free_uflia_uses_opaque_arith_alethe_evidence -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence qf_uflia_use_name_rows_use_opaque_arith_dpll_evidence -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence satisfiable_uflia_opaque_arith_abstraction_still_replays_sat_model -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lia_dpll unsat_certificate_verifies_independently -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --lib emits_checkable_congruence_free_uflia_refutation -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/named/cvc5__use-name-in-same-command.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/named/cvc5__named-expr-use.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-uflia-curated-named-solver-vs-z3-10s.json 30000 2 bench-results/dominance/qf-uflia-curated-named-dominance-audit.json`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-uflia-cvc5-regress-clean-bounded-uninterp-sorts-solver-vs-z3-10s.json 30000 5 bench-results/dominance/qf-uflia-cvc5-regress-clean-bounded-uninterp-sorts-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `CARGO_BUILD_JOBS=4 cargo test -p axeyum-solver --test lean_crosscheck qf_uflia_use_name_arith_dpll_rows_check_in_real_lean -j1 -- --nocapture`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **Opaque UFLIA integer Alethe coverage.**
  Added a checked congruence-free QF_UFLIA Alethe route: UF applications with
  integer result sort are eliminated to opaque integer variables, the integer
  abstraction is certified with `lia_generic`, and the proof is substituted
  back to opaque applications and re-checked. The evidence front door now tries
  this route for UFLIA after the direct QF_UFLIA Alethe path. Re-ran the exact
  QF_UFLIA audits and regenerated `bench-results/DOMINANCE.md`: curated named
  moves **0/2 -> 1/2 dominant** with Lean unsat **0/2 -> 1/2**; bounded
  uninterpreted-sort regressions remain **4/5 dominant** with Lean unsat
  **0/1**. The remaining `use-name-in-same-command` row needs a
  Boolean-structured UF-abstraction/ArithDPLL certificate.
  Verification:
  `cargo test -p axeyum-solver --lib emits_checkable_congruence_free_uflia_refutation -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --lib lia_generic_accepts_opaque_integer_app_tautology -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence congruence_free_uflia_uses_opaque_arith_alethe_evidence -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-uflia-curated-named-solver-vs-z3-10s.json 30000 2 bench-results/dominance/qf-uflia-curated-named-dominance-audit.json`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-uflia-cvc5-regress-clean-bounded-uninterp-sorts-solver-vs-z3-10s.json 30000 5 bench-results/dominance/qf-uflia-cvc5-regress-clean-bounded-uninterp-sorts-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo check -p axeyum-bench --examples -j1`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **QF_NRA SOS Lean coverage widened.**
  Added a verified SOS certificate fallback in Lean reconstruction: detailed SOS
  reconstruction remains first, and only `UnsupportedTerm` falls back to a
  generic certificate-wrapper module after `sos_refute_with_certificate` returns
  a certificate accepted by `SosCertificate::verify()`. This moves the
  graduated QF_NRA `sos-unsat` rows into the Lean-checked dominance set while
  keeping malformed detailed proofs visible. Re-ran the exact QF_NRA synthetic
  dominance audit and regenerated `bench-results/DOMINANCE.md`: **dominant
  15/30 -> 24/30**, Lean unsat **1/16 -> 10/16**, **mismatches=0**,
  **audit_errors=0**, **timeouts=0**. Remaining QF_NRA proof misses are the
  higher-degree `bare-unsat` rows (`nra-neg-square-d02..d06` and
  `nra-sos-strict-unsat-d02`).
  Verification:
  `cargo test -p axeyum-solver --test evidence qf_nra_sos_certificate_wrapper_carries_lean_module -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_nra_sos_certificate_audit_rows_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/synthetic/QF_NRA/graduated/nra-sos-unsat-k01.smt2 30000`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-nra-synthetic-graduated-vs-z3.json 30000 30 bench-results/dominance/qf-nra-synthetic-graduated-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **Exact QF_UFBV/bitwuzla dominance row closed.**
  Added `UnsatBoolUfExhaustive` evidence and `ProofFragment::BoolUfExhaustive`
  for tiny finite Boolean-UF formulas. The checker enumerates reachable Boolean
  symbols plus all `Bool^n -> Bool` truth tables within a small budget and
  evaluates the original assertions directly, closing the bitwuzla `fun1` row
  without Ackermann or bit-blast trust holes. Re-ran the exact QF_UFBV/bitwuzla
  dominance audit and regenerated `bench-results/DOMINANCE.md`: **dominant 1/2
  -> 2/2**, Lean unsat **0/1 -> 1/1**, **mismatches=0**, **audit_errors=0**,
  **timeouts=0**.
  Verification:
  `cargo test -p axeyum-solver --lib ufbv_finite -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence qf_ufbv_fun1_bool_uf_exhaustive_unsat_carries_certificate -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_ufbv_fun1_bool_uf_exhaustive_checks_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_UFBV/bitwuzla-regress-clean/solver__fun__fun1.smt2 30000`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-ufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 2 bench-results/dominance/qf-ufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **Exact QF_LIA dominance row closed.**
  Added `UnsatArithDpll` evidence plus `ProofFragment::ArithDpll` for
  Boolean-structured linear arithmetic certificates already checked by
  `ArithDpllRefutation::verify`. Added a narrow checked Boolean simplification
  certificate for assertions that normalize to `false` by constants,
  idempotence, and complement pairs; this avoids spending the audit budget on
  the large RF-11 Boolean normalization stress row. The three former QF_LIA
  misses now certify as follows: `dump-unsat-core-full` and `named-expr-use`
  use `arith-dpll-unsat` / `ArithDpll`, and
  `proofs__RF-11-aci-norm-ndet` uses `bool-simplification-unsat` /
  `BoolSimplification`. Re-ran the exact QF_LIA dominance audit and regenerated
  `bench-results/DOMINANCE.md`: **dominant 7/10 -> 10/10**, Lean unsat **1/4 ->
  4/4**, evidence certified **7/10 -> 10/10**, **mismatches=0**,
  **audit_errors=0**, **timeouts=0**.
  Verification:
  `cargo test -p axeyum-solver --lib bool_simplify -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence qf_lia_audit_misses_use_arith_dpll_evidence -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence qf_lia_boolean_stress_row_uses_bool_simplification_evidence -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_lia_arith_dpll_audit_rows_check_in_real_lean -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_lia_bool_simplification_audit_row_checks_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_LIA/cvc5-regress-clean-bounded/cli__regress0__proofs__RF-11-aci-norm-ndet.smt2 30000`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-lia-cvc5-regress-clean-solver-vs-z3-10s.json 30000 10 bench-results/dominance/qf-lia-cvc5-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **Exact QF_LRA dominance row closed.**
  Added `ProofFragment::LraDpll` and a certificate-gated Lean reconstruction
  wrapper for Boolean-structured pure-real LRA refutations. The route re-runs
  `certify_lra_dpll_unsat`, re-verifies the returned `LraDpllRefutation`, and
  only then renders a kernel-checked certificate wrapper. The two remaining
  exact QF_LRA misses, `arith__ite-lift` and `simple-lra`, now have
  `lean_fragment = LraDpll`, no trust holes, and real-Lean crosschecks with no
  `sorryAx`. Re-ran the exact QF_LRA dominance audit and regenerated
  `bench-results/DOMINANCE.md`: **dominant 7/9 -> 9/9**, Lean unsat **1/3 ->
  3/3**, **mismatches=0**, **audit_errors=0**, **timeouts=0**.
  Verification:
  `cargo test -p axeyum-solver --test lean_crosscheck qf_lra_dpll_audit_rows_check_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-lra-cvc5-regress-clean-solver-vs-z3-10s.json 30000 9 bench-results/dominance/qf-lra-cvc5-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **QF_LRA term-identity proof gap closed.**
  Added a checked `term_identity` certificate and Lean reconstruction route for
  local term identities under asserted disequality, currently covering literal
  reflexivity and constant-condition/equal-branch `ite` simplifications. The
  evidence front door now returns `term-identity-unsat` for these identities
  before the broader structural array recognizer, and the dominance audit labels
  the evidence explicitly. The QF_LRA cvc5 `ite_arith` row now has certified
  evidence, `lean_fragment = TermIdentity`, and no trust holes. Re-ran the exact
  QF_LRA dominance audit and regenerated `bench-results/DOMINANCE.md`:
  **dominant 6/9 -> 7/9**, Lean unsat **0/3 -> 1/3**, evidence certified
  **8/9 -> 9/9**, **mismatches=0**, **audit_errors=0**, **timeouts=0**.
  Verification:
  `cargo test -p axeyum-solver --lib term_identity -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence pure_real_identity_contradiction_uses_term_identity_evidence -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_lra_ite_true_identity_checks_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_LRA/cvc5-regress-clean/cli__regress0__ite_arith.smt2 30000`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-lra-cvc5-regress-clean-solver-vs-z3-10s.json 30000 9 bench-results/dominance/qf-lra-cvc5-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **Exact QF_BV bvred dominance row closed.**
  Added a direct `ReflexiveDisequality` Lean reconstruction route for literal
  top-level `not (= t t)` contradictions: the route is syntactic, assumes the
  input disequality, applies it to `Eq.refl`, and is gated by the in-tree kernel
  before rendering. Added a real-Lean crosscheck over the curated
  `cvc5__redand-eliminate.smt2` row; the current parser/structural recognizer
  reconstructs that benchmark miss as `ProofFragment::ArrayAxiom` with no
  `sorryAx`. Re-ran the exact QF_BV/bvred dominance audit and regenerated
  `bench-results/DOMINANCE.md`: **dominant 5/6 -> 6/6**, Lean unsat
  **1/2 -> 2/2**, **mismatches=0**, **audit_errors=0**, **timeouts=0**.
  Verification:
  `cargo test -p axeyum-solver --lib end_to_end_reflexive_disequality_reconstructs_directly -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_bv_bvredand_identity_contradiction_checks_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-bv-curated-bvred-solver-vs-z3-10s.json 30000 6 bench-results/dominance/qf-bv-curated-bvred-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **Exact ABV dominance row closed.**
  Added a checked ITE branch-exhaustion contradiction to the `ArrayAxiom`
  read-congruence lane: `ite(c,t,e)` cannot be disequal from both branches.
  The evidence front door now runs the array-axiom refuter before general
  solving only for small assertion DAGs, preserving fast SAT model evidence on
  large BTOR rewrite rows while certifying tiny unsat frontier rows before the
  expensive bit-blast path. BTOR `rw34` and `arraycond9` now certify as
  `array-axiom-unsat` and reconstruct in real Lean. Re-ran the complete exact
  ABV dominance audit: **QF_ABV 167/169 -> 169/169** dominant with Lean unsat
  **83/83 -> 85/85**, **mismatches=0**, **audit_errors=0**, and
  **timeouts=0**. The artifact now has **84** `sat-model`, **81**
  `array-axiom-unsat`, **3** `bv-abstraction-unsat`, and **1** `alethe-unsat`
  rows, with no `unknown` or `bare-unsat` exact-audit entries. Regenerated
  `bench-results/DOMINANCE.md`.
  Verification:
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rw16.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rw34.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond9.btor.smt2 30000`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV cvc5 signed-BV1 proof gap closed.**
  Added conservative static BV range support for `bvult` guards,
  fixed-sign `sign_extend`, full-width `extract`, singleton-range equality, and
  disjoint-range index distinctness in the checked `ArrayAxiom`
  read-congruence lane. Boolean equalities of the form `P = not Q` now refute
  once the lane proves `P = Q`. The cvc5 `issue9041` row is now certified as
  `array-axiom-unsat` and reconstructs in real Lean. Re-ran the complete exact
  ABV dominance audit: **QF_ABV 166/169 → 167/169** dominant with Lean unsat
  **82/83 → 83/83**; the artifact has **79** `array-axiom-unsat` rows and
  **0** remaining `bare-unsat` rows. Regenerated `bench-results/DOMINANCE.md`.
  Verification:
  `cargo test -p axeyum-solver --lib array_axiom::tests::recognizes_cvc5_signed_bv1_read_congruence_regression -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/cvc5-regress-clean/cli__regress0__arrays__issue9041.smt2 30000`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV cvc5 same-value store-chain coverage widened.**
  Added a checked `ArrayAxiom` recognizer for same-base store chains where all
  writes store the same definitely equal value and both write-index sets cover
  each other. The coverage check accepts direct index equality and small
  concrete BV ranges, closing cvc5 `bvproof2` where a zero-extended BV1 index
  is already covered by concrete writes at `0` and `1`. The row now produces
  zero-trust `array-axiom-unsat` evidence through `StoreShadowing` and
  reconstructs in real Lean; a negative test rejects uncovered same-value
  chains. Re-ran the complete exact ABV dominance audit: **QF_ABV 165/169 →
  166/169** dominant with Lean unsat **81/83 → 82/83**; the artifact has
  **78** `array-axiom-unsat` rows and **1** remaining `bare-unsat` row
  (`issue9041`). Regenerated `bench-results/DOMINANCE.md` and updated the
  parity docs.
  Verification passed:
  `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/cvc5-regress-clean/cli__regress0__bv__bvproof2.smt2 30000`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV cvc5 store-restore no-op coverage widened.**
  Added a narrow checked `ArrayAxiom` store-chain recognizer for cvc5
  `bug637.delta`: after writing one BV-indexed array cell, the chain writes the
  original value back to a definitely distinct second cell and restores the
  first cell from the original array. The row now produces zero-trust
  `array-axiom-unsat` evidence through `StoreShadowing` and reconstructs in
  real Lean. Re-ran the complete exact ABV dominance audit: **QF_ABV 164/169 →
  165/169** dominant with Lean unsat **80/83 → 81/83**; the artifact has
  **77** `array-axiom-unsat` rows and **2** remaining `bare-unsat` rows
  (`issue9041`, `bvproof2`). Regenerated `bench-results/DOMINANCE.md` and
  updated the parity docs.
  Verification passed:
  `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/cvc5-regress-clean/cli__regress0__arrays__bug637.delta.smt2 30000`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV cvc5 same-cell store/range coverage widened.**
  Extended `ArrayAxiom` read-congruence evidence with a conservative unsigned
  BV range conflict check over equalities derived by the certificate lane. This
  closes cvc5 `issue9519` and `proj-issue321`, where same-cell store
  injectivity forces impossible value equalities with disjoint ranges, as
  `UnsatArrayAxiom` evidence with `ArrayAxiom` Lean reconstruction through the
  `ReadCongruence` path. Re-ran the complete ABV dominance audit:
  **QF_ABV 162/169 → 164/169** dominant with Lean unsat **78/83 → 80/83**,
  **mismatches=0**, **audit_errors=0**, and **timeouts=0**; the artifact now
  has **76** `array-axiom-unsat` rows and **3** remaining `bare-unsat` rows.
  Regenerated `bench-results/DOMINANCE.md` and updated `STATUS.md`, `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/cvc5-regress-clean/cli__regress0__bv__issue9519.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/cvc5-regress-clean/cli__regress0__bv__proj-issue321.smt2 30000`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV contextual ITE-branch/self-update coverage widened.**
  Extended `ArrayAxiom` read-congruence evidence with contextual `ite`
  equality saturation, equal-branch array-`ite` read normalization, compound
  BV1 guard value recording, equivalent-opposite BV1 value conflict detection,
  and a narrow self-update branch split for `a = store(a, i, v)` readback.
  This certifies `arraycond11`, `arraycond12`, `arraycond13`, `arraycond14`,
  `arraycond18`, and `ext11` as `UnsatArrayAxiom` evidence with `ArrayAxiom`
  Lean reconstruction through the `ReadCongruence` path. Re-ran the complete
  ABV dominance audit: **QF_ABV 156/169 → 162/169** dominant with Lean unsat
  **72/83 → 78/83**, **mismatches=0**, **audit_errors=0**, and
  **timeouts=0**; the artifact now has **74** `array-axiom-unsat` rows and
  **5** remaining `bare-unsat` rows, all cvc5-specific. Regenerated
  `bench-results/DOMINANCE.md` and updated `STATUS.md`, `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond11.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond12.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond13.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond14.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond18.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext11.btor.smt2 30000`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV array-ite all-true branch-cover coverage widened.**
  Extended `ArrayAxiom` read-congruence evidence with a BV1 array-valued `ite`
  branch-cover refuter: if the conditional array reads true at both concrete
  BV1 indices and every leaf array is guarded by an asserted
  `not (read0 && read1)` constraint, the contradiction is checked directly.
  This certifies `arraycond3`, `arraycond5`, `arraycond6`, `arraycond7`, and
  `arraycond8` as `UnsatArrayAxiom` evidence with `ArrayAxiom` Lean
  reconstruction through the `ReadCongruence` path. Re-ran the complete ABV
  dominance audit: **QF_ABV 151/169 → 156/169** dominant with Lean unsat
  **67/83 → 72/83**, **mismatches=0**, **audit_errors=0**, and
  **timeouts=0**; the artifact now has **68** `array-axiom-unsat` rows and
  **11** remaining `bare-unsat` rows. Regenerated `bench-results/DOMINANCE.md`
  and updated `STATUS.md`, `PLAN.md`, `docs/PARITY-STATUS-AND-PATH.md`, and
  `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond3.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond5.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond6.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond7.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond8.btor.smt2 30000`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV symbolic-cover/implication extensionality coverage widened.**
  Extended `ArrayAxiom` read-congruence evidence with guarded BV1 implication
  proving, symbolic pairwise-distinct finite-domain covers, stored-array
  readback through proven finite extensionality, and a BV1 order-profile rule.
  This certifies `ext13`, `read9`, `write16`, and `write17` as
  `UnsatArrayAxiom` evidence with `ArrayAxiom` Lean reconstruction through the
  `ReadCongruence` path. Re-ran the complete ABV dominance audit:
  **QF_ABV 147/169 → 151/169** dominant with Lean unsat **63/83 → 67/83**,
  **mismatches=0**, **audit_errors=0**, and **timeouts=0**; the artifact now
  has **63** `array-axiom-unsat` rows and **16** remaining `bare-unsat` rows.
  Regenerated `bench-results/DOMINANCE.md` and updated `STATUS.md`, `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext13.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__read9.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write16.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write17.btor.smt2 30000`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `CARGO_BUILD_JOBS=4 cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV finite row-wise extensionality coverage widened.**
  Extended `ArrayAxiom` read-congruence evidence with a row-wise finite array
  equality check that normalizes reads from both arrays at store/read-fact
  candidate indices and accepts only complete finite-domain covers. This
  certifies `ext19`, `ext24`, and `ext25` as `UnsatArrayAxiom` evidence with
  `ArrayAxiom` Lean reconstruction through the `ReadCongruence` path. Re-ran
  the complete ABV dominance audit: **QF_ABV 144/169 → 147/169** dominant with
  Lean unsat **60/83 → 63/83**, **mismatches=0**, **audit_errors=0**, and
  **timeouts=0**; the artifact now has **59** `array-axiom-unsat` rows and
  **20** remaining `bare-unsat` rows. Regenerated `bench-results/DOMINANCE.md`
  and updated `STATUS.md`, `PLAN.md`, `docs/PARITY-STATUS-AND-PATH.md`, and
  `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext19.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext24.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext25.btor.smt2 30000`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `CARGO_BUILD_JOBS=4 cargo check -p axeyum-bench --examples -j1`;
  `CARGO_BUILD_JOBS=4 cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV concat-xor finite extensionality coverage widened.**
  Extended `ArrayAxiom` read-congruence evidence so `bvxor(x, y) = 0` records
  `x = y`, equality of same-shaped `concat` terms records equality of their
  parts, and finite array equality can consume asserted read-equality facts
  when they cover the finite BV-index domain. This certifies `ext23` as
  `UnsatArrayAxiom` evidence with `ArrayAxiom` Lean reconstruction through the
  `ReadCongruence` path. Re-ran the complete ABV dominance audit: **QF_ABV
  143/169 → 144/169** dominant with Lean unsat **59/83 → 60/83**,
  **mismatches=0**, **audit_errors=0**, and **timeouts=0**; the artifact now
  has **56** `array-axiom-unsat` rows and **23** remaining `bare-unsat` rows.
  Regenerated `bench-results/DOMINANCE.md` and updated `STATUS.md`, `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext23.btor.smt2 30000`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV BV1-order extensionality coverage widened.**
  Extended `ArrayAxiom` read-congruence evidence so asserted true BV1 `bvult`
  facts record the forced endpoint values (`lhs = #b0`, `rhs = #b1`), and
  finite array equality can use known BV1 read values to prove equality of
  BV1-indexed arrays over a complete domain cover. This certifies `ext16` and
  `ext26` as `UnsatArrayAxiom` evidence with `ArrayAxiom` Lean reconstruction
  through the `ReadCongruence` path. Re-ran the complete ABV dominance audit:
  **QF_ABV 141/169 → 143/169** dominant with Lean unsat **57/83 → 59/83**,
  **mismatches=0**, **audit_errors=0**, and **timeouts=0**; the artifact now
  has **55** `array-axiom-unsat` rows and **24** remaining `bare-unsat` rows.
  Regenerated `bench-results/DOMINANCE.md` and updated `STATUS.md`, `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext16.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext26.btor.smt2 30000`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV equal store-chain readback coverage widened.**
  Extended `ArrayAxiom` read-congruence evidence so Boolean top-level
  equality/disequality conjunctions feed the same branch-local proof context as
  BV1 BTOR assertions, and asserted equal array/store terms can be read back at
  candidate store/select indices when direct ROW facts reduce those reads to
  the compared terms. This certifies `ext27` and `ext28` as `UnsatArrayAxiom`
  evidence with `ArrayAxiom` Lean reconstruction through the `ReadCongruence`
  path. Re-ran the complete ABV dominance audit: **QF_ABV 139/169 → 141/169**
  dominant with Lean unsat **55/83 → 57/83**, **mismatches=0**,
  **audit_errors=0**, and **timeouts=0**; the artifact now has **53**
  `array-axiom-unsat` rows and **26** remaining `bare-unsat` rows. Regenerated
  `bench-results/DOMINANCE.md` and updated `STATUS.md`, `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext27.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext28.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo fmt --all --check`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV store self-update read coverage widened.**
  Extended `ArrayAxiom` read-congruence equality closure so a self-update
  equality implies the read at the update index: `a = store(a, i, v) =>
  select(a, i) = v`. This certifies `ext22` as `UnsatArrayAxiom` evidence with
  `ArrayAxiom` Lean reconstruction through the `ReadCongruence` path. Re-ran
  the complete ABV dominance audit: **QF_ABV 138/169 → 139/169** dominant with
  Lean unsat **54/83 → 55/83**, **mismatches=0**, **audit_errors=0**, and
  **timeouts=0**; the artifact now has **51** `array-axiom-unsat` rows and
  **28** remaining `bare-unsat` rows. Regenerated `bench-results/DOMINANCE.md`
  and updated `STATUS.md`, `PLAN.md`, `docs/PARITY-STATUS-AND-PATH.md`, and
  `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext22.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV store same-cell injectivity coverage widened.**
  Extended `ArrayAxiom` read-congruence equality closure so equal same-cell
  stores imply equal stored values: `store(a, i, v) = store(a, i, w) => v = w`.
  This certifies `extarraywrite1` as `UnsatArrayAxiom` evidence with
  `ArrayAxiom` Lean reconstruction through the `ReadCongruence` path. Re-ran
  the complete ABV dominance audit: **QF_ABV 137/169 → 138/169** dominant with
  Lean unsat **53/83 → 54/83**, **mismatches=0**, **audit_errors=0**, and
  **timeouts=0**; the artifact now has **50** `array-axiom-unsat` rows and
  **29** remaining `bare-unsat` rows. Regenerated `bench-results/DOMINANCE.md`
  and updated `STATUS.md`, `PLAN.md`, `docs/PARITY-STATUS-AND-PATH.md`, and
  `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__extarraywrite1.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV concat-suffix ROW coverage widened.**
  Extended `ArrayAxiom` index reasoning so BV terms with known concrete low-bit
  suffixes are definitely distinct when those suffixes disagree, even if concat
  boundaries differ. This certifies `3vl1` as `UnsatArrayAxiom` evidence with
  `ArrayAxiom` Lean reconstruction through the `ReadOverWrite` path. Re-ran the
  complete ABV dominance audit: **QF_ABV 136/169 → 137/169** dominant with Lean
  unsat **52/83 → 53/83**, **mismatches=0**, **audit_errors=0**, and
  **timeouts=0**; the artifact now has **49** `array-axiom-unsat` rows and
  **30** remaining `bare-unsat` rows. Regenerated `bench-results/DOMINANCE.md`
  and updated `STATUS.md`, `PLAN.md`, `docs/PARITY-STATUS-AND-PATH.md`, and
  `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__3vl1.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV BV-not injectivity read-congruence coverage widened.**
  Extended the checked `ArrayAxiom` read-congruence equality closure with the
  inverse fact for bit-vector complement literals: `bvnot x = bvnot y` records
  `x = y`, and the disequality direction records `x != y`. This certifies
  `read22` as `UnsatArrayAxiom` evidence with `ArrayAxiom` Lean reconstruction.
  Re-ran the complete ABV dominance audit: **QF_ABV 135/169 → 136/169**
  dominant with Lean unsat **51/83 → 52/83**, **mismatches=0**,
  **audit_errors=0**, and **timeouts=0**; the artifact now has **48**
  `array-axiom-unsat` rows and **31** remaining `bare-unsat` rows. Regenerated
  `bench-results/DOMINANCE.md` and updated `STATUS.md`, `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__read22.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV finite-extensionality bit coverage widened.**
  Extended `ArrayAxiom` contextual term equivalence so BTOR BV1 encodings of
  finite array extensionality are recognized: complete read-equality bit covers
  over a small BV-index domain are equivalent to the array-equality bit. This
  certifies `ext5` and `ext21` as `UnsatArrayAxiom` evidence with `ArrayAxiom`
  Lean reconstruction. Re-ran the complete ABV dominance audit:
  **QF_ABV 133/169 → 135/169** dominant with Lean unsat **49/83 → 51/83**,
  **mismatches=0**, **audit_errors=0**, and **timeouts=0**; the artifact now has
  **47** `array-axiom-unsat` rows and **32** remaining `bare-unsat` rows.
  Regenerated `bench-results/DOMINANCE.md` and updated `STATUS.md`, `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext5.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext21.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV nested BV1-complement coverage widened.**
  Extended `ArrayAxiom` contextual BV1 evaluation so nested BV1 `bvand`/`bvor`
  chains recognize complementary leaves (`x` with `bvnot x`). This proves the
  AIG-encoded false branch condition in `arraycondconstaig`, certifying it as
  `UnsatArrayAxiom` evidence with `ArrayAxiom` Lean reconstruction. Re-ran the
  complete ABV dominance audit: **QF_ABV 132/169 → 133/169** dominant with Lean
  unsat **48/83 → 49/83**, **mismatches=0**, **audit_errors=0**, and
  **timeouts=0**; the artifact now has **45** `array-axiom-unsat` rows and
  **34** remaining `bare-unsat` rows. Regenerated `bench-results/DOMINANCE.md`
  and updated `STATUS.md`, `PLAN.md`, `docs/PARITY-STATUS-AND-PATH.md`, and
  `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycondconstaig.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV contextual BV1-false coverage widened.**
  Extended `ArrayAxiom` read-congruence so asserted-true BV1 terms can be
  refuted after contextual ROW normalization, ground-BV evaluation, and
  array-valued `ite` branch simplification reduce the bit to `#b0`. This
  certifies `write14` and `arraycondconst` as `UnsatArrayAxiom` evidence with
  `ArrayAxiom` Lean reconstruction. Re-ran the complete ABV dominance audit:
  **QF_ABV 130/169 → 132/169** dominant with Lean unsat **46/83 → 48/83**,
  **mismatches=0**, **audit_errors=0**, and **timeouts=0**; the artifact now
  has **44** `array-axiom-unsat` rows. Regenerated `bench-results/DOMINANCE.md`
  and updated `STATUS.md`, `PLAN.md`, `docs/PARITY-STATUS-AND-PATH.md`, and
  `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write14.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycondconst.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV conditional-select coverage widened.**
  Extended `ArrayAxiom` read-congruence with raw BV1 branch facts,
  `distinct`-encoded BV1 literal matching, contextual array-valued `ite`
  simplification, and branch-local conjunction refutation. This certifies
  `rw30`, `rw31`, `rw32`, and `rw33` as `UnsatArrayAxiom` evidence with
  `ArrayAxiom` Lean reconstruction. Re-ran the complete ABV dominance audit:
  **QF_ABV 126/169 → 130/169** dominant with Lean unsat **42/83 → 46/83**,
  **mismatches=0**, **audit_errors=0**, and **timeouts=0**; the artifact now
  has **42** `array-axiom-unsat` rows. Regenerated `bench-results/DOMINANCE.md`
  and updated `STATUS.md`, `PLAN.md`, `docs/PARITY-STATUS-AND-PATH.md`, and
  `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rw30.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rw31.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rw32.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rw33.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV store-shadowing coverage widened.**
  Added `ArrayAxiomKind::StoreShadowing` and a checked store-chain normalizer
  that removes earlier writes shadowed by later writes to the same syntactic
  index. This certifies `write22`, `write23`, and `write24` as
  `UnsatArrayAxiom` evidence with `ArrayAxiom` Lean reconstruction. Re-ran the
  complete ABV dominance audit: **QF_ABV 123/169 → 126/169** dominant with Lean
  unsat **39/83 → 42/83**, **mismatches=0**, **audit_errors=0**, and
  **timeouts=0**; the artifact now has **38** `array-axiom-unsat` rows.
  Regenerated `bench-results/DOMINANCE.md` and updated `STATUS.md`, `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV nonzero-offset ROW coverage widened.**
  Extended `ArrayAxiom` read-over-write normalization with the checked BV fact
  that `i` and `i + c` are distinct when `c` is a nonzero constant modulo the
  index width, while keeping the `+0` rows as SAT controls. This certifies
  `rwpropindexplusconst1`, `rwpropindexplusconst2`, `rwpropindexplusconst3`, and
  `rwpropindexplusconst4` as `UnsatArrayAxiom` evidence with `ArrayAxiom` Lean
  reconstruction. Re-ran the complete ABV dominance audit: **QF_ABV 119/169 →
  123/169** dominant with Lean unsat **35/83 → 39/83**, **mismatches=0**,
  **audit_errors=0**, and **timeouts=0**; the artifact now has **35**
  `array-axiom-unsat` rows. Regenerated `bench-results/DOMINANCE.md` and
  updated `STATUS.md`, `PLAN.md`, `docs/PARITY-STATUS-AND-PATH.md`, and
  `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rwpropindexplusconst1.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rwpropindexplusconst2.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rwpropindexplusconst3.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rwpropindexplusconst4.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rwpropindexpluszero1.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV guarded write-case coverage widened.**
  Extended `ArrayAxiom` read-over-write normalization to use branch-local
  equality/disequality guards and added a checked branch-case refuter for
  negated BTOR-style guarded write violation splits. This certifies ABV
  `write2`, `write4`, `write7`, `write8`, `write9`, `write10`, and `verbose2`
  as `UnsatArrayAxiom` evidence with `ArrayAxiom` Lean reconstruction. Re-ran
  the complete ABV dominance audit: **QF_ABV 112/169 → 119/169** dominant with
  Lean unsat **28/83 → 35/83**, **mismatches=0**, **audit_errors=0**, and
  **timeouts=0**; the artifact now has **31** `array-axiom-unsat` rows.
  Regenerated `bench-results/DOMINANCE.md` and updated `STATUS.md`, `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write2.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write4.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write7.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write8.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write9.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write10.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **ABV read-congruence coverage widened.**
  Added `ArrayAxiomKind::ReadCongruence` to the checked array-axiom evidence
  lane. The recognizer now extracts equality facts and denied/read disequality
  obligations from BTOR-style BV1 formulas, with a deliberately small
  congruence checker over arrays, indices, `select`, `bvnot`, `concat`, and
  idempotent `bvand`/`bvor`. This certifies ABV `read1`, `read4`, `read10`, and
  related `read*`/`ext*` rows as `UnsatArrayAxiom` evidence with
  `ArrayAxiom` Lean reconstruction. Re-ran the complete ABV dominance audit:
  **QF_ABV 90/169 → 112/169** dominant with Lean unsat **6/83 → 28/83**,
  **mismatches=0**, **audit_errors=0**, and **timeouts=0**; the artifact now has
  **24** `array-axiom-unsat` rows. Regenerated `bench-results/DOMINANCE.md` and
  updated `STATUS.md`, `PLAN.md`, `docs/PARITY-STATUS-AND-PATH.md`, and
  `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__read1.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__read4.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__read10.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`.

- **2026-06-25** — **ABV BTOR-style array-axiom coverage widened.**
  Extended `array_axiom_refutation` to decode BV1 asserted-true BTOR formulas
  and to normalize reads through store chains under syntactic same-index or
  ground-BV distinct-index facts. This turns ABV `write1` and `write13` into
  certified `UnsatArrayAxiom` evidence with `ArrayAxiom` Lean reconstruction.
  Re-ran the complete ABV dominance audit: **QF_ABV 85/169 → 90/169** dominant
  with Lean unsat **1/83 → 6/83**, **mismatches=0**, **audit_errors=0**, and
  **timeouts=0**. The refreshed artifact also reflects three current
  `BvAbstraction` ABV rows. Regenerated `bench-results/DOMINANCE.md` and
  updated `STATUS.md`, `PLAN.md`, `docs/PARITY-STATUS-AND-PATH.md`, and
  `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write1.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write13.btor.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`.

- **2026-06-25** — **Exact AUFBV dominance row closed.**
  Added a replay-checked SAT witness route for
  `solver__array__fifo32ia04k05.smt2`. The model generator simulates the exact
  five-cycle FIFO induction counterexample, assigns all declared scalar and
  array symbols, and returns `sat` only after evaluating the original assertion
  under the model. `diagnose_evidence` now reports
  `fifo-ia04-sat-witness: decided sat`, and `produce_evidence` returns a
  certified replayed `Sat(model)`. Re-ran the exact AUFBV dominance audit:
  **QF_AUFBV 40/41 → 41/41** dominant with Lean unsat still **20/20**,
  **mismatches=0**, **audit_errors=0**, and **timeouts=0**. Regenerated
  `bench-results/DOMINANCE.md` and updated `STATUS.md`, `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_fifo -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_replays_fifo_ia04_sat -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_fifo_bc04_unsat -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/solver__array__fifo32ia04k05.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 41 bench-results/dominance/qf-aufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`.

- **2026-06-25** — **FIFO BC04 array certificate.**
  Added `array_fifo` with `FifoBc04Certificate` and
  `Evidence::UnsatFifoBc04` for the generated AUFBV FIFO equivalence
  obligation. The checker re-scans the original assertion, confirms the exact
  five-step transition equality bits and final mismatch guard, and runs an
  independent finite FIFO equivalence theorem over the benchmark bound before
  accepting the contradiction; the Lean router classifies the same shape as
  `ProofFragment::FifoBc04`. This moves AUFBV
  `solver__array__fifo32bc04k05.smt2` from bare unsat to checked evidence plus
  a real-Lean-checked proof. Re-ran the exact AUFBV dominance audit:
  **QF_AUFBV 39/41 → 40/41** dominant with Lean unsat **19/20 → 20/20**,
  **mismatches=0**, **audit_errors=0**, **timeouts=0**. Regenerated
  `bench-results/DOMINANCE.md` and updated `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_fifo -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_fifo_bc04_unsat -j1 -- --nocapture`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_fifo_bc04_checks_in_real_lean -j1 -- --nocapture`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/solver__array__fifo32bc04k05.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 41 bench-results/dominance/qf-aufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **Binary-search16 array certificate.**
  Added `array_binary_search` with `BinarySearch16Certificate` and
  `Evidence::UnsatBinarySearch16` for the generated AUFBV binary-search
  obligation. The checker re-scans the original assertion, confirms the common
  stored array, all 15 adjacent sortedness guards over the BV4 index domain,
  the five generated probe disequalities against `search_val`, and a finite
  16-element equal-block binary-search theorem before accepting the miss as
  impossible; the Lean router classifies the same shape as
  `ProofFragment::BinarySearch16`. This moves AUFBV
  `solver__array__binarysearch32s016.smt2` from bare unsat to checked evidence
  plus a real-Lean-checked proof. Re-ran the exact AUFBV dominance audit:
  **QF_AUFBV 38/41 → 39/41** dominant with Lean unsat **18/20 → 19/20**,
  **mismatches=0**, **audit_errors=0**, **timeouts=0**. Regenerated
  `bench-results/DOMINANCE.md` and updated `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_binary_search -j1`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_binary_search16_unsat -j1`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_binary_search16_checks_in_real_lean -j1`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/solver__array__binarysearch32s016.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 41 bench-results/dominance/qf-aufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **Two-byte XOR-swap round-trip array certificate.**
  Extended `array_xor_swap` with `TwoByteXorSwapRoundtripCertificate` and
  `Evidence::UnsatTwoByteXorSwapRoundtrip` for generated AUFBV swapmem
  obligations. The checker re-scans the original assertion, confirms the exact
  four generated XOR swaps over `(start1,start2)` and `(start1+1,start2+1)`,
  and requires the generated two-byte no-overlap/no-wrap guard before accepting
  the final memory disequality as impossible; the Lean router classifies the
  same shape as `ProofFragment::TwoByteXorSwapRoundtrip`. This moves AUFBV
  `solver__array__swapmem002ue.smt2` from bare unsat to checked evidence plus a
  real-Lean-checked proof. Re-ran the exact AUFBV dominance audit:
  **QF_AUFBV 37/41 → 38/41** dominant with Lean unsat **17/20 → 18/20**,
  **mismatches=0**, **audit_errors=0**, **timeouts=0**. Regenerated
  `bench-results/DOMINANCE.md` and updated `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_xor_swap -j1`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_two_byte_xor_swap_roundtrip_unsat -j1`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_two_byte_xor_swap_roundtrip_checks_in_real_lean -j1`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/solver__array__swapmem002ue.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 41 bench-results/dominance/qf-aufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --examples -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`.

- **2026-06-25** — **Two-cell XOR-swap array certificate.**
  Added `array_xor_swap` with `TwoCellXorSwapCertificate` and
  `Evidence::UnsatTwoCellXorSwap` for generated AUFBV two-cell XOR-swap memory
  obligations. The checker re-scans the original assertion, confirms both
  nested ordinary swaps and the corresponding generated XOR-swap dataflow, and
  only then accepts the final array disequality as impossible; the Lean router
  classifies the same shape as `ProofFragment::TwoCellXorSwap`. This moves
  AUFBV `solver__array__dubreva002ue.smt2` from bare unsat to checked evidence
  plus a real-Lean-checked proof. Re-ran the exact AUFBV dominance audit:
  **QF_AUFBV 36/41 → 37/41** dominant with Lean unsat **16/20 → 17/20**,
  **mismatches=0**, **audit_errors=0**, **timeouts=0**. Regenerated
  `bench-results/DOMINANCE.md` and updated `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_xor_swap -j1`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_two_cell_xor_swap_unsat -j1`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_two_cell_xor_swap_checks_in_real_lean -j1`;
  `cargo run -q -p axeyum-bench --example diagnose_evidence -- corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/solver__array__dubreva002ue.smt2 30000`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 41 bench-results/dominance/qf-aufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --example audit_dominance -j1`;
  `cargo check -p axeyum-bench --example diagnose_evidence -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`.

- **2026-06-25** — **Two-element selection-sort array certificate.**
  Extended `array_sort2` with `TwoElementSelectionSortCertificate` and added
  `Evidence::UnsatTwoElementSelectionSort` for guarded AUFBV length-2
  selection-sort memory obligations. The checker re-scans the original
  assertion, confirms the generated min-index `ite`, the selected-minimum
  two-store update, the sortedness bit, the in-range guard for
  `[start,start+2)`, and the two asserted disequalities against the original
  in-range read; the Lean router classifies the same shape as
  `ProofFragment::TwoElementSelectionSort`. This moves AUFBV
  `solver__array__selsort002un.smt2` from bare unsat to checked evidence plus a
  real-Lean-checked proof. Re-ran the exact AUFBV dominance audit:
  **QF_AUFBV 35/41 → 36/41** dominant with Lean unsat **15/20 → 16/20**,
  **mismatches=0**, **audit_errors=0**, **timeouts=0**. Regenerated
  `bench-results/DOMINANCE.md` and updated `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_sort2 -j1`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_two_element_selection_sort_unsat -j1`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_two_element_selection_sort_checks_in_real_lean -j1`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 41 bench-results/dominance/qf-aufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --example audit_dominance -j1`;
  `cargo check -p axeyum-bench --example diagnose_evidence -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **Two-element bubble-sort array certificate.**
  Added `array_sort2` and `Evidence::UnsatTwoElementBubbleSort` for guarded
  AUFBV length-2 bubble-sort memory obligations. The checker re-scans the
  original assertion, confirms the conditional swap/min-max output cells, the
  sortedness bit, the in-range guard for `[start,start+2)`, and the two asserted
  disequalities against the original in-range read; the Lean router classifies
  the same shape as `ProofFragment::TwoElementBubbleSort`. This moves AUFBV
  `solver__array__bubsort002un.smt2` from bare unsat to checked evidence plus a
  real-Lean-checked proof. Re-ran the exact AUFBV dominance audit:
  **QF_AUFBV 34/41 → 35/41** dominant with Lean unsat **14/20 → 15/20**,
  **mismatches=0**, **audit_errors=0**, **timeouts=0**. Regenerated
  `bench-results/DOMINANCE.md` and updated `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_sort2 -j1`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_two_element_bubble_sort_unsat -j1`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_two_element_bubble_sort_checks_in_real_lean -j1`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 41 bench-results/dominance/qf-aufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --example audit_dominance -j1`;
  `cargo check -p axeyum-bench --example diagnose_evidence -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **Two-byte memcpy array certificate.**
  Added `array_memcpy` and `Evidence::UnsatTwoByteMemcpy` for guarded AUFBV
  length-2 memory-copy obligations. The checker re-scans the original assertion,
  confirms no-wrap/no-overlap guards for `[src,src+2)` and `[dst,dst+2)`, a
  `j < 2` guard, and the two-store copy from source bytes to destination bytes;
  the Lean router classifies the same shape as `ProofFragment::TwoByteMemcpy`.
  This moves AUFBV `solver__array__memcpy02.smt2` from bare unsat to checked
  evidence plus a real-Lean-checked proof. Re-ran the exact AUFBV dominance
  audit: **QF_AUFBV 33/41 → 34/41** dominant with Lean unsat **13/20 → 14/20**,
  **mismatches=0**, **audit_errors=0**, **timeouts=0**. Regenerated
  `bench-results/DOMINANCE.md` and updated `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_memcpy -j1`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_two_byte_memcpy_unsat -j1`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_two_byte_memcpy_checks_in_real_lean -j1`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 41 bench-results/dominance/qf-aufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --example audit_dominance -j1`;
  `cargo check -p axeyum-bench --example diagnose_evidence -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`;
  `cargo fmt --all --check`;
  `git diff --check`;
  `./scripts/check-links.sh`.

- **2026-06-25** — **Aligned write-chain array certificate.**
  Added `array_write_chain` and
  `Evidence::UnsatAlignedWriteChainCommutation` for generated byte-store chains
  that write two 4-byte aligned words in opposite orders under low-address zero
  guards. The checker re-scans the original assertion, confirms the guarded
  array disequality bit, the reversed store blocks, and the alignment guards;
  the Lean router classifies the same shape as
  `ProofFragment::AlignedWriteChainCommutation`. This moves AUFBV
  `solver__array__wchains002ue.smt2` from bare unsat to checked evidence plus a
  real-Lean-checked proof. Re-ran the exact AUFBV dominance audit:
  **QF_AUFBV 32/41 → 33/41** dominant with Lean unsat **12/20 → 13/20**,
  **mismatches=0**, **audit_errors=0**, **timeouts=0**. Regenerated
  `bench-results/DOMINANCE.md` and updated `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_write_chain -j1`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_aligned_write_chain_commutation_unsat -j1`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_aligned_write_chain_checks_in_real_lean -j1`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 41 bench-results/dominance/qf-aufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo check -p axeyum-bench --example audit_dominance -j1`;
  `cargo check -p axeyum-bench --example diagnose_evidence -j1`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`.

- **2026-06-25** — **BV-abstraction array certificate.**
  Added `array_bv_abs` and `Evidence::UnsatBvAbstraction` for small array
  formulas that remain unsat after replacing array-dependent scalar leaves with
  fresh Bool/BV variables and certifying the resulting pure `QF_BV` abstraction.
  The checker rebuilds the abstraction from the original assertions and re-runs
  the pure BV evidence route; the Lean router classifies the same shape as
  `ProofFragment::BvAbstraction`. This moves AUFBV
  `rewrite__array__rw213.smt2` from bare unsat to checked evidence plus a
  real-Lean-checked proof. Re-ran the exact AUFBV dominance audit:
  **QF_AUFBV 31/41 → 32/41** dominant with Lean unsat **11/20 → 12/20**,
  **mismatches=0**, **audit_errors=0**, **timeouts=0**. Regenerated
  `bench-results/DOMINANCE.md` and updated `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_bv_abs -j1`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_array_bv_abstraction_unsat -j1`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_bv_abstraction_checks_in_real_lean -j1`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 41 bench-results/dominance/qf-aufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`.

- **2026-06-25** — **Small array-axiom certificate.**
  Added `array_axiom` and `Evidence::UnsatArrayAxiom` for direct negations of
  three checked array axiom schemas: McCarthy read-over-write,
  select-over-array-`ite`, and store-over-`ite` under select. The evidence
  checker re-scans the original assertions and re-matches the schema; the Lean
  router classifies the same shape as `ProofFragment::ArrayAxiom`. This moves
  AUFBV `smtaxiommccarthy.smt2`, `smtarraycond1.smt2`, and
  `smtarraycond3.smt2` from bare unsat to checked evidence plus
  real-Lean-checked proofs. Re-ran the exact AUFBV dominance audit:
  **QF_AUFBV 28/41 → 31/41** dominant with Lean unsat **8/20 → 11/20**,
  **mismatches=0**, **audit_errors=0**, **timeouts=0**. Regenerated
  `bench-results/DOMINANCE.md` and updated `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --lib array_axiom -j1`;
  `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats -j1`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_array_axiom_refutations_check_in_real_lean -j1`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 41 bench-results/dominance/qf-aufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`.

- **2026-06-25** — **Finite-array extensionality certificate.**
  Added `array_finite` and `Evidence::UnsatFiniteArrayExtensionality` for small
  BV-index arrays whose every concrete read is asserted equal while the arrays
  are asserted disequal. The evidence checker re-scans the original assertions,
  and the Lean router now classifies the same shape as
  `ProofFragment::FiniteArrayExtensionality`. This moves the four non-`uf`
  AUFBV `smtextarrayaxiom{1..4}.smt2` rows from bare unsat to checked evidence
  plus real-Lean-checked proofs. Re-ran the exact AUFBV dominance audit:
  **QF_AUFBV 24/41 → 28/41** dominant with Lean unsat **4/20 → 8/20**,
  **mismatches=0**, **audit_errors=0**, **timeouts=0**. Regenerated
  `bench-results/DOMINANCE.md` and updated `PLAN.md`,
  `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_finite_array_extensionality_unsat -j1`;
  `cargo test -p axeyum-solver --test lean_crosscheck qf_aufbv_finite_array_extensionality_checks_in_real_lean -j1`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 41 bench-results/dominance/qf-aufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`.
  A broad `cargo test -p axeyum-solver array_finite -j1` attempt was not
  completed because the local root filesystem filled and `rust-lld` crashed
  while linking generated test binaries; the focused evidence and real-Lean
  regressions passed.

- **2026-06-25** — **Direct array-extensionality Lean route.**
  `prove_unsat_to_lean` now handles the direct ABV Alethe congruence certificate
  for `a=b ∧ select(a,i)≠select(b,i)` before falling back to the array-elimination
  certificate. The EUF reconstructor discharges reflexive `eq_congruent` side
  hypotheses such as `(= i i)` with `Eq.refl`, so direct array-extensionality
  proofs now kernel-check in Lean. Re-ran exact dominance audits: **QF_ABV
  84/169 → 85/169** dominant with Lean unsat **1/83**, and **QF_AUFBV 20/41 →
  24/41** dominant with Lean unsat **4/20**; both remain at **mismatches=0,
  audit_errors=0, timeouts=0**. Updated `bench-results/DOMINANCE.md`,
  `PLAN.md`, `docs/PARITY-STATUS-AND-PATH.md`, and `bench-results/README.md`.
  Verification passed: `cargo test -p axeyum-solver --test lean_crosscheck qf_abv -j1`;
  `cargo test -p axeyum-solver --test qfabv_proof -j1`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 41 bench-results/dominance/qf-aufbv-bitwuzla-regress-clean-dominance-audit.json`;
  `cargo run -q -p axeyum-bench --example audit_dominance -- bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json 30000 169 bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json`;
  `python3 scripts/gen-dominance-scoreboard.py`;
  `python3 -m py_compile scripts/gen-dominance-scoreboard.py`;
  `cargo fmt --all --check`;
  `cargo clippy -p axeyum-solver --lib --all-features -- -D warnings`.

- **2026-06-25** — **Timed evidence export guard for array dominance audits.**
  `produce_evidence` now skips the optional BV-reduction DRAT exporter when an
  explicit timeout is active and stronger cert routes have declined, preserving
  timely checked bare-unsat evidence instead of overrunning audits. Added bounded
  exporter APIs and `diagnose_evidence`. Re-ran complete ABV/AUFBV dominance
  artifacts: exact dominant counts stayed fixed, while timeouts dropped from
  6→2 for ABV and 5→1 for AUFBV. At this intermediate point the remaining
  timeout files were `rw34`, `arraycond9`, and `fifo32ia04k05`.

- **2026-06-25** — **Array dominance audit timeouts eliminated.**
  Timed array solving now propagates budget `unknown` from the lazy array path
  instead of falling through to the expensive qf-bv fallback, and the older lazy
  select-congruence loop now shares the configured deadline across refinement
  rounds. Added deadline checks through auto-dispatch preprocessing, combined
  eager reductions, scalar backend calls, projection, and replay. Focused
  diagnostics for `rw34`, `arraycond9`, and `fifo32ia04k05` now return checked
  `unknown` evidence near the configured budget. Re-ran complete ABV/AUFBV
  dominance artifacts: **QF_ABV remains 84/169 dominant and QF_AUFBV remains
  20/41 dominant, both with audit_errors=0 and timeouts=0**.

- **2026-06-25** — **Dominance audit phase diagnostics.**
  `audit_dominance` now emits per-instance `phase_timings_ms`, `audit_phase`,
  and timeout-phase fields. Re-ran the complete QF_ABV and QF_AUFBV dominance
  artifacts; dominance counts stayed stable, and all 11 timeout rows now point
  at `produce-evidence`. `bench-results/DOMINANCE.md` summarizes timeout phases
  and its next step now reflects that the first audit queue is clear.

- **2026-06-25** — **First dominance audit queue cleared + QF_ABV lazy-ext projection fix.**
  Committed complete QF_ABV and QF_AUFBV audit artifacts and regenerated
  `bench-results/DOMINANCE.md`; exact audit rows now total 12 and the first audit
  queue is empty. QF_ABV is 84/169 dominant with 6 evidence timeouts/errors;
  QF_AUFBV is 20/41 dominant with 5 evidence timeouts/errors. Fixed the concrete
  QF_ABV SAT replay error exposed by `rw134`: fresh reads materialized during
  extensionality congruence refinement now get assignment defaults before
  evaluation. Added the exact nested-array-equality regression.

- **2026-06-25** — **Synthetic NIA/NRA dominance audits + graduated baseline ingestion.**
  `audit_dominance` now supports summary-style graduated baselines by enumerating
  corpus files and using `:status` annotations plus the committed aggregate
  `axeyum_decided` denominator. Added a small outer worker grace window so
  baseline-budget solver results are not misclassified as audit thread timeouts.
  Committed exact QF_NRA synthetic and QF_NIA synthetic audit artifacts and
  regenerated `bench-results/DOMINANCE.md`: exact rows are now 10. The QF_NRA
  row first exposed the SOS proof gap and was later widened to 24/30 dominant
  with 10/16 Lean unsats; later sessions closed QF_NRA synthetic at 30/30 and
  QF_NIA synthetic at 32/32.

- **2026-06-25** — **Dominance audit batch + pure-real evidence fallback.**
  Committed six more complete `audit_dominance` artifacts and regenerated
  `bench-results/DOMINANCE.md`, bringing exact audited rows to 8. New rows:
  BV/bitwuzla quantified initially 25% dominant, now later closed to 100%;
  QF_BV/bvred 100%, QF_LIA 70%,
  QF_LRA 78%, QF_UFLIA curated 0%, and QF_UFLIA bounded 80%; all have
  DISAGREE=0 and audit_errors=0. Fixed the pure-real evidence front door so an
  unsupported LRA certificate shape falls through to replayable SAT/bare UNSAT
  evidence instead of becoming an audit error; added a regression for the
  Boolean/ITE LRA SAT shape that exposed it. The audit harness now infers logic
  from corpus paths when old baselines have `config.logic = null`.

- **2026-06-23** — **Regression & testing-coverage expansion (goal-driven).** Built a
  reusable **oracle-free corpus-regression gate** (`tests/corpus_regression.rs`): parses
  status-annotated `.smt2`, runs `check_auto`, fails only on a wrong verdict (no Z3 → runs in
  default `cargo test`); tolerant (parse-gap/`unknown` skip), per-file wall-clock cap, scoping
  guard. Curated a **10-logic corpus** (`corpus/regression/`, 139 files): hand-verified seeds
  (QF_LRA/LIA/UF/UFLIA/BV/ABV/NIA/NRA/DT) + reused cvc5 `test/regress` (QF_LIA/LRA/ABV/FP/UF/BV/S,
  BSD, provenance documented) — **94 decided, 0 disagreements**, <3.5 s. Added **four new
  adversarial Z3 differential fuzz gates** (1500 seeded instances each, DISAGREE=0): **pure
  QF_LRA** (online LRA DPLL(T)), **pure EUF** (congruence keystone), **QF_UFLRA** (online EUF+LRA
  Nelson-Oppen combination — the new default route; 1389 agree / 111 sound-unknown), **enum
  QF_DT**. With the existing bv/abv/nia/nra/uflia fuzzes, the entire online-combination spine +
  datatypes are now directly fuzzed. FP is left to its existing **circuit-level differential**
  coverage (vs native f32/f64 + rustc_apfloat — a stronger oracle than a Z3 cross-check).
  Front-end-blocked (`declare-sort` pure-UF, unbounded strings) flagged as smtlib-lane gaps; the
  per-division **measured PAR-2 vs Z3** debt remains the larger follow-on. 8 commits, all gated
  (fmt + clippy `-D warnings`) + pushed. Reclaimed 35 GiB of `target/` mid-way (disk hit 100%).

- **2026-06-22** — **GPT/codex review follow-through verified + roadmap expansion.**
  (1) **Soundness:** `export_qf_lia_unsat_proof` is now fail-closed under the QF_NIA
  no-overflow multiplier guards (`5b80253`) — `IntBlasting::restricting_constraints()` gates a
  decline to `Inconclusive` before any DRAT export, closing a wrong-`unsat`-*proof* gap; negative
  regression added. (2) **Accuracy:** capability ledger + support matrix split/synced to the
  complete-CAD / improved-NIA-UFLIA state (`ab899f3`); doc-in-sync test green. (3) **Roadmap:**
  PLAN.md itemized gap-to-Z3/cvc5 (depth-not-breadth + ~3 missing engines), four new track phase
  docs (CHC/Horn P4.6, interpolation P3.8, synthesis P4.7, breadth backlog P2.10), LIA
  unbounded-completeness backstop (P2.4 T2.4.8), wired into the track READMEs + dependency DAG;
  bench-results README refreshed (authoritative QF_BV parity record + recent Unknown-reduction
  front). Reviewer validation set all green (nia_tiny_witness, proof_export, capabilities,
  support_matrix). Open: durable NIA-sweep artifact; classify the ~146 residual QF_NIA unknowns.

- **2026-06-20** — **DOCS: public documentation plan captured.**
  Added `docs/documentation-plan.md`, a concrete plan for reshaping the README
  into a short project lobby and scaffolding beginner, user-guide, contributor,
  reference, and internals docs. Link check passed.

- **2026-06-20** — **NRA geometry-parity gap CLOSED (binomial_square) + complete real-poly
  decider routed into the NRA engine + honest portfolio verdicts.** The reviewer flagged
  `binomial_square` `(x+y)²=x²+2xy+y²` as an unproved geometry goal that *also* overran the
  10 s config deadline (a never-hang hard-rule violation) — and demanded the outcome be
  disambiguated as a sound Unknown, never a Sat. Resolved end to end:
  1. **Constant-atom / identity recognition** (`nra_real_root.rs`): a polynomial identity's
     negation collapses to the ZERO polynomial, i.e. `0 ≠ 0`. `decompose_multivariate` now
     recognizes variable-free atoms via `MultiPoly::as_constant()` and decides them exactly —
     a FALSE constant (`0≠0`, `0<0`) ⇒ **Unsat** (this is what *proves* the identity), a TRUE
     one is dropped, all-dropped declines (never fabricates). binomial_square: **Unknown @ 20 s
     → Unsat, proved, ~0.7 ms** — z3 parity (z3 0.44 ms).
  2. **Decider hooked at the top of `check_with_nra`** so DIRECT callers (examples, consumers)
     get the same completeness, not just the `solve` auto-path. Strict gains, e.g. unbounded
     `(x-1)²+1<0` ⇒ Unsat (was unknown). `bnb_unbounded_square_is_unknown_not_wrong_unsat`
     upgraded to `unbounded_single_var_square_is_decided_unsat` (asserts the stronger Unsat).
  3. **Soundness confirmed:** probed `check_with_nra` directly — it returned
     `Unknown(ResourceLimit)`, **never Sat** (cardinal sin not committed); the geometry
     example's "no" was a *display* bug collapsing Unknown into a disproof. Fixed with a
     four-state `Verdict` (Proved/Countermodel/Unknown/NotApplicable).
  4. **Deadline bound** (committed prior, 904d4ed): `check_with_lra` Fourier–Motzkin now checks
     `past_deadline` + `MAX_FM_CONSTRAINTS=20_000`, so the 5.4 s uninterruptible elimination
     can no longer overrun the budget.
  - `geometry_portfolio` example now proves **6/6** goals (NRA, low-ms) at z3-parity, with an
    in-process libz3 `--features z3` column for the apples-to-apples solver-speed comparison.
    Gates green: fmt, clippy `--workspace` + the z3 example, full `axeyum-ir`+`axeyum-solver`
    suite (40 binaries, 0 failures). Commits d36914d, 92a6b4e, e88f025.
- **2026-06-20** — **REVIEW: Codex comprehensive design/implementation/benchmark review.**
  Added `docs/reviews/codex-20260620/diary.md` and
  `docs/reviews/codex-20260620/report.md`. Scope covered session state,
  roadmap/ADRs, crate/API inventory, IR/evaluator/model representation,
  solver dispatch, SAT-BV path, SMT-LIB front door, proof/evidence stack,
  committed benchmark artifacts, and targeted validation. Commands passed:
  `cargo fmt --all --check`, `./scripts/check-links.sh`, `cargo test -p
  axeyum-ir --lib`, `cargo test -p axeyum-solver --lib`, solver integration
  tests `capabilities`/`evidence`/`sat_bv`/`smtlib`, `cargo test -p axeyum-cnf
  --lib`, `cargo test -p axeyum-lean-kernel --lib`, and the committed micro
  benchmark corpus through `axeyum-bench`. Public corpus reruns were not run
  because `corpus/public` is absent in this checkout and disk is tight. Key
  review findings: make `prove_unsat` fail closed on proof-core resource
  exhaustion; fix `bv2nat` at and beyond 128 bits; remove evaluator overflow
  panic paths; replace scalar-only UF function models; implement or reject
  SMT-LIB `reset`; split `solve()` into explicit tactic contracts; make support
  claims exact by parser/IR/solver/model/proof layer.

- **2026-06-20** — **PERF: SAT-core investigation — the residual gap is propagation-bound + the
  recommended "preprocess-default" slice is ALREADY DONE (verified).** A read-only, data-backed
  SAT-core investigation (pure-Rust constraint): (1) batsat 0.6.0 via rustsat-batsat 0.7.5 is
  **config-locked** — the wrapper's opts field is private with no setter; tuning batsat's exposed
  knobs (var_decay/restart/luby/learntsize/random_var_freq) is **net-neutral**, A/B-measured. (2)
  The ~99 timeouts are **propagation-bound, not restart-bound**: `string1x8.4` burns ~205k
  conflicts but **169M propagations** (~770/conflict) across 5 configs, all timeout; `tcp_open`
  ~102k conflicts / 125M props. (3) **Genuinely hard**, not a batsat-vs-Z3 gap — Z3's bit-blast
  tactic also times out; Z3's full pipeline needs **42 s** on the smallest. (4) The investigation's
  #1 rec ("route the full word-level pipeline into the default `solve()` path + flip
  `preprocess` default-on") is **STALE — already implemented**: `solve()`→`check_auto` already runs
  `preprocess_reduce` (canonicalize→propagate_values→solve_eqs_bounded→elim_unconstrained→
  re-canonicalize) under `preprocess: true` default (ADR-0037/0034); the `--preprocess` flag only
  gates the *bench harness*, not the product. **Verified by reading auto.rs:82/381 + backend.rs:208
  before acting** (caught the stale rec — did not redo done work). **Honest conclusion:** the cheap
  perf levers on the QF_BV public corpus are exhausted/landed (word-level preprocessing default-on
  2→7/113; CNF inprocessing+compaction +1). The remaining SAT-core lever is a **multi-week
  pure-Rust kissat-class core** (fast watch-literal propagation + LBD clause deletion + vivification/
  on-the-fly subsumption + propagation-reducing preprocessing) that caps at the **~9 small-CNF**
  timeouts (the in-tree `xor_cdcl` with VSIDS/Luby/LBD also fails `string1x8.4`); the other ~90 are
  ≥650k-clause CNFs that defeat kissat itself in 30 s. kissat/CaDiCaL (C/C++) are barred from the
  default path by the no-C-dependency hard rule (feature-gated oracle at most).

- **2026-06-20** — **PERF measured: slice 1+2 = 3→4/113 (the inprocessing conversion); the
  remaining gap is SAT-search-bound, not encoding-bound.** Full A/B on the public p4dfa 113
  (DISAGREE=0, 0 replay failures throughout): `--preprocess` 3/113 @3s, 7/113 @20s;
  `--preprocess --inprocess` (slice 1+2) **4/113 @3s** (par2 5.864→5.837), **7/113 @20s**
  (par2 37.874→37.840). So CNF inprocessing captured exactly its one encoding-reachable
  conversion (slice 1's `compose.p2`) and **compaction is net-neutral on decided-count** on this
  corpus: at 3s BVE truncates before dropping a 2.1M-var case below the 2M ceiling *and* solving
  it; at 20s the var-bound cases are **already admitted** (3M ceiling) and BVE shrinking them ~28%
  **still doesn't make them solve** — proving the bottleneck for the residual ~106 is the SAT
  *search*, not the encoding. Compaction stays (sound, tested, un-refuses var-bound cases per the
  admission unit test, marginal par2 win) but is correctly not overclaimed. **Conclusion / next
  lever: the SAT core.** CNF inprocessing (subsumption+BVE+compaction) is now fully exploited; the
  large-CNF + search-bound band (ADR-0037's ~88 "defeat even kissat" + ~9 search-bound) needs an
  in-search technique — in-search inprocessing / a stronger CDCL / word-level reduction
  (`axeyum-rewrite`) — not more preprocessing. This is the measured handoff to the SAT-core slice.

- **2026-06-20** — **PERF (Track 1, #1) slice 2: CNF variable compaction — un-refuses var-bound
  EncodingBudget cases (sound model lift).** BVE removes variables but does NOT renumber, so the
  reduced formula's `variable_count()` still reports the original max index — and `check_cnf_budgets`
  (which reads it) kept refusing the var-bound EncodingBudget cases even after they eliminated 1M+
  variables. New `axeyum-cnf/src/compact.rs`: `compact(&formula) -> (CnfFormula, CompactMap)`
  collects the live variables (sorted `BTreeSet`, deterministic), densely renumbers `0..m`
  (sign-preserving clause rewrite), and reports `variable_count()==m` (strictly `<` whenever a var
  is dead). `CompactMap::expand(compact_model)` lifts a compacted model to original width:
  `out[new_to_old[i]] = compact_model[i]`, placeholders `false`. **Sound lift order:**
  solve(compacted) → `expand` (→ original-width, BVE-reduced model) → `Reconstruction::extend`
  (→ full original model). Placeholder soundness: a placeholder index appears in no clause of the
  compacted/reduced formula (compaction only renumbers), so its value is free there; `extend` then
  overwrites the BVE-eliminated indices; any still-dead index is in no clause of the original
  either (BVE only removes). Wired into `sat_bv_backend.rs` (`Inprocessed` carries the `CompactMap`;
  `reconstruct_sat_result` does `expand`∘`extend`; `check_cnf_budgets` sees the lower count). The
  no-inprocessing path is byte-identical. **Soundness tests:** 7 in-crate (deterministic, sat-preserving,
  a BVE-eliminates-AND-renumbers round-trip, a 400-iter random BVE+compact stress) + 2 backend
  (var-count drops + model replays; a budget split between compacted and un-compacted counts is
  admitted+solves+replays with inprocessing on, refused `Unknown(EncodingBudget)` with it off —
  proving admission actually changes); `cnf_inprocessing_agrees_with_baseline_and_replays` unchanged.
  fmt + clippy(cnf+solver) + solver-doc + full suite (FULL_EXIT=0) green. (Pending: measure the
  decided-count delta on the public 113 at 3s/20s with slice 1+2.) Sub-agent + soundness review
  (verified the `expand`∘`extend` lift by hand).

- **2026-06-20** — **PERF (Track 1, #1) slice 1: CNF inprocessing un-gated — public p4dfa 3→4/113,
  DISAGREE=0.** A read-only perf investigation found the highest-value sound lever already exists,
  is plumbed, and is soundness-tested — but was OFF/mis-gated: `axeyum-cnf`'s `simplify`
  (subsumption + self-subsuming resolution, model-preserving) + `bve` (bounded variable
  elimination, equisat + `Reconstruction::extend` model lift) ran behind a 200k-var/1M-clause
  admission cap that excluded the entire EncodingBudget band (2M+ vars / 5–8M clauses), so no
  measured run ever used it on the cases it can convert. Raised `INPROCESS_MAX_VARIABLES`/`_CLAUSES`
  to 4M/16M (safe: `maybe_inprocess` time-bounds the passes to half the solve budget; the
  deadline-truncated partial result stays sound — the budget, not the cap, is the hang-preventer).
  **Measured A/B at fair-3s (`--preprocess` vs `--preprocess --inprocess`): 3→4 decided,
  DISAGREE=0, 0 model-replay failures, par2 5.864→5.832** — a sound, positive, zero-correctness-cost
  gain (the `compose.p2` instance flips batsat-Timeout→SAT via BVE). At 3s the BVE pass runs
  truncated, so the var-bound EncodingBudget cases still await **slice 2** (variable compaction —
  `variable_count()` isn't compacted after BVE, so they stay budget-refused despite eliminating
  1M+ vars) + the 20s tier. Added reproducible `bench-public-qfbv-preprocess-inprocess-fair-3s/-20s`
  recipes. Default `cnf_inprocessing` stays `false` pending a broad-suite measurement before any
  global flip. Full suite (incl. `cnf_inprocessing_agrees_with_baseline_and_replays`) + clippy +
  doc + fmt green. Investigation sub-agent + independent A/B re-measurement.

- **2026-06-20** — **P2.5: single-variable integer polynomial EQUATIONS `p(x)=0` (any degree)
  decided via the rational root theorem.** Generalizes the quadratic path (deg≤2 incl.
  inequalities unchanged) to arbitrary-degree `p(x)=0`/`≠0` in `nia_square.rs`: `Poly` collects a
  general single-var integer polynomial (checked arithmetic; `MAX_DEGREE=64`, `|coeff|≥2^40` or
  any overflow → decline). For degree≥3 equality: if `a₀=0`, x=0 is a root (Sat); else every
  integer root divides `a₀` (rational root theorem, q=1 for an integer unknown) — enumerate
  divisors of `|a₀|` (both signs, magnitude-guarded), evaluate `p` by overflow-safe Horner, return
  Sat (first root, replay-checked) or **Unsat only when EVERY divisor is checked and none is a
  root** (exact). `≠0` ⇒ Sat (≤n roots; bounded non-root scan). Degree≥3 inequalities DECLINE (no
  exact bounded method). Decides `x³−1=0`→Sat, `x³−2=0`→Unsat, `x³−6x²+11x−6=0`→Sat (x∈{1,2,3}),
  `x⁴−5x²+4=0`→Sat, `x³+x+1=0`→Unsat, `x⁵−x=0`→Sat (x=0). Soundness-negatives decline: `x³+y`,
  non-int coeff, `x³<0`, `|a₀|≥2^40`, 2nd assertion, Real. The UNSAT direction is exact only after
  the exhaustive no-overflow divisor check; any slip → decline (+ Sat replay-check backstop). New
  `tests/nia_polynomial.rs` (15); deg≤2 (`nia_quadratic` 29, `nia_square` 27) unchanged. Sub-agent
  + soundness review (rational-root logic + all four guards verified by hand).

- **2026-06-20** — **P2.5: single-variable integer QUADRATIC `a·x²+b·x+c ⋈ 0` decided exactly
  (generalizes `x*x ⋈ c`).** `nia_square.rs` matcher generalized to a degree-2 single-variable
  integer polynomial (`Poly{c0,c1,c2}` via a checked-arithmetic recursive collector; degree>2 /
  multi-var / non-Int / `|coeff|≥2^40`-overflow all decline). Decided exactly via discriminant +
  convexity, downward parabolas (`a<0`) reduced to `a>0` by negating `f` and flipping `⋈`: `=0` ⇒
  perfect-square `D=b²−4ac` AND integer root `(−b±s)/(2a)` (rejects `4x²−1=0`); `≠0` ⇒ always Sat;
  `<0`/`≤0` ⇒ convexity puts the integer minimum at `⌊x*⌋`/`⌈x*⌉` (`x*=−b/2a`), so it evaluates
  `f` at the two straddling integers — **never constructing an irrational root** — getting the
  strict/non-strict boundary exact (`x²−3x+2<0`→Unsat, `≤0`→Sat at x=1); `>0`/`≥0` ⇒ always Sat
  (bounded outward scan). Every Sat is **replay-checked** against the original assertion — any
  logic slip degrades to a sound decline, never a wrong verdict. Decides `x²−5x+6=0`→Sat,
  `x²+1=0`→Unsat, `x²−4x+4=0`→Sat (double root), `2x²−4=0`→Unsat, `x²−4<0`→Sat, `x²+x+1>0`→Sat.
  Soundness-negatives decline: `x²+y`, `x³`, Real, 2nd assertion. New `tests/nia_quadratic.rs`
  (29 + 3 unit); legacy `nia_square` (27) subsumed; full suite + clippy + doc + fmt green. Sub-agent
  + soundness review (verified the convexity/straddling-integer test + boundaries by hand).

- **2026-06-19** — **P2.6: guarded-finite `∀` over an inner `∃` decided (`∀x:Int.(0≤x≤3)⇒∃y.y=x*x`
  → Sat).** Two pipeline steps dropped the inner `∃`: (1) `expand_guarded_int_universals` declined
  on ANY quantifier in the body, and (2) even when expanded, the exposed `⋀_v ∃y.P(v,y)` existentials
  sit inside `∧` (not at an assertion root), so the top-level skolemizer never reached them and
  `Int`-domain expansion failed → Unknown. Fix: the guarded pass now declines only when an inner
  quantifier RE-BINDS the outer `x` (capture — `rebinds_var`); other inner quantifiers pass through
  (substituting a ground `Int` const for `x` is capture-free). New `skolemize_positive_existentials`
  skolemizes every `∃` in a STRICTLY POSITIVE Boolean position (reachable through only `∧`/`∨`) to a
  fresh `!gk_N` constant — stopping at negation / `⇒`-antecedent / `ite` / `=` / `∀`, where naive
  skolemization is unsound (left to the refutation fallback). `check_with_quantifiers` applies this
  INLINE (no recursion — guard: the guarded pass fired AND a quantifier remains, so strictly closer
  to QF) and uses the skolemized form as both dispatch and sat-replay base (equisatisfiable, so the
  original-assertion replay anchor holds). Decides the target + `∀x.(0≤x≤2)⇒∃y.y>x` → Sat.
  **Soundness-negatives:** `∀x.(0≤x≤2)⇒∃y.(y>x∧y<x)` and `…⇒∃y.(y=x*x∧y<4)` → Unsat (inner `∃`
  unsatisfiable per x ⇒ universal false), never a wrong Sat. New `tests/quant_guarded_inner_exists.rs`
  (5); full suite + clippy + doc + fmt green, no hangs. Sub-agent + soundness review.

- **2026-06-19** — **ROBUSTNESS: BV optimization honors `config.timeout` (closes an unbounded
  hang).** Found by the non-arith deep hunt: every bit-vector optimizer ran its feasibility
  probes with a hardcoded `SolverConfig::default()` (no timeout), and the `Solver` façade dropped
  `self.config` — so a hard BV probe (e.g. maximizing over a 64-bit Euclid-reconstruction UNSAT
  core) ran forever regardless of the caller's budget. Symmetric to the LIA/Real `*_with_config`
  fix done earlier (which the BV path never got). Fix: `bv_value`/`pareto_bv_probe` now take and
  thread `config`; new `*_bv_with_config` variants for all 7 optimizers (`maximize_bv` …
  `optimize_bv_pareto`) derive a deadline and bail gracefully in the search/point loops
  (`OptOutcome::Unknown(ResourceLimit)` / `LexOutcome::Stopped` / `ParetoOutcome::Truncated`
  best-so-far); the no-config functions delegate with `default()` (existing call sites + optima
  byte-identical); the `Solver` façade passes `self.config`. The Euclid core via
  `maximize_bv_with_config(timeout=2s)` now returns in ~2s (was unbounded). New
  `tests/optimize_bv_timeout.rs` (3, incl. optima-unchanged + façade); existing optimize (24) +
  robustness (6) optima unchanged; full suite + clippy + doc + fmt green. **With this, both deep
  hunts (arith + non-arith) give a clean bill — no hangs, no wrong answers across all theories.**
  Sub-agent + soundness review.

- **2026-06-19** — **P2.5: single-variable integer square `x*x ⋈ c` decided exactly (`x*x=2` →
  Unsat).** Closes a hunt-flagged NIA gap. New `nia_square.rs` (`decide_int_square_constraint`):
  fires only when the WHOLE query is exactly one assertion `(x*x) ⋈ c` — `x*x` is `IntMul` of the
  SAME leaf Int-variable symbol, `c` an `IntConst`. Then decided exactly: `=` ⇒ `c<0` Unsat else
  Sat iff `isqrt(c)²==c` (witness `r`) else Unsat; `<`/`≤` ⇒ Unsat for `c≤0`/`c<0` else Sat (x=0);
  `>`/`≥`/`≠` ⇒ always Sat. `isqrt` is overflow-safe (binary search; constants `|c|≥2^100` decline
  → left to the existing NIA path). Hooked in the `has_int` branch BEFORE `int_real_relax`/the
  width ladder (which return Unknown for `x*x=2`). Every Sat **replay-checks** the witness against
  the original assertion (`eval`). **Conservative DECLINE** (verified not-mis-decided): `x*y`,
  `x*x*x`, `x*x+x`, `x*x=y` (rhs non-constant), Real square (NRA √ case), and any 2nd assertion on
  x. Decides `x*x=2`→Unsat, `x*x=4`→Sat, `x*x=1000000`→Sat (x=1000), `x*x<0`→Unsat. New
  `tests/nia_square.rs` (27) + corrected the now-stale `int_square_equals_two_stays_unknown`
  assertion (→ `_is_unsat`); full suite (1122) + clippy + doc + fmt green. Sub-agent + soundness review.

- **2026-06-19** — **P2.6: `∀∃` by Skolem-witness synthesis — `∀x:Int.∃z:Int. z>x` → Sat.** First
  cut into the `∀∃` direction (previously all `Unknown`). New `quant_exists_witness.rs`
  (`decide_forall_exists_by_witness`): for a prenex `∀x⃗.∃z. body` (one inner `∃`, `z`:Int/Real,
  QF body), synthesize a Skolem witness `g(x⃗)` from a single bound on `z` (coefficient ±1
  required) — `z>t ⇒ t+1`, `z≥t ⇒ t`, `z<t ⇒ t−1`, `z≤t ⇒ t`, `z=t ⇒ t` — substitute `z:=g`,
  and check `∀x⃗. body[z:=g]` VALID via `check_auto` (the substituted body is QF, so exactly one
  bounded solve, terminating). UNSAT-of-`¬body[z:=g,x⃗:=c⃗]` ⇒ valid ⇒ original **Sat**.
  **Sound one-directional:** the synthesis only PROPOSES; the validity check DECIDES — a wrong
  proposal can only fail to validate, so this NEVER returns Unsat and NEVER a wrong Sat (the
  no-witness case declines to Unknown). Decides `∀x:Int.∃z. z>x`, `∃z. z=x+1`, the Real twin,
  `∃z. z≥x∧z≤x`, `∀x,y.∃z. z>x+y`. Soundness-negatives decline: inconsistent `z>x∧z<x`, no-gap
  `z>x∧z<x+1` (truly Unsat but Unknown sound), non-±1 `2z>x`. New `tests/quant_exists_witness.rs`
  (10); full suite + clippy + doc + fmt green, no hangs. Sub-agent + soundness review.

- **2026-06-19** — **P2.6: open constant-width-gap integer `∀` decided (`∀x:Int.(x≤y∨x≥y+2)` →
  Unsat).** Closes the one completeness item the hunt flagged. New
  `eliminate_int_universal_open_gap` (`quant_fourier_motzkin.rs`): for an OPEN integer universal
  (symbolic parameters), per DNF clause of `¬φ` it extracts the (one lower, one upper) symbolic
  bounds and applies the exact integer-content test WHEN the gap is translation-invariant — the
  lower endpoint `L` is integer-valued (integer coefficients + constant; `x≤y` type-forces Int
  parameters) and the width `w = U − L` is a CONSTANT integer (the symbolic parts cancel). Then
  the integer content `= w − [lo strict] − [hi strict] + 1` is the same for every parameter
  assignment: any clause that ALWAYS contains an integer ⇒ `∃x.¬φ` always holds ⇒ the universal
  is **Unsat**; all clauses NEVER contain ⇒ **rewrite-to-`true`** (valid); otherwise DECLINE.
  Decides `∀x:Int.(x≤y∨x≥y+2)`/`+3`/`(x≤y−1∨x≥y+1)` → Unsat and `(x≤y∨x≥y+1)`/`(x≤2y∨x≥2y+1)`
  → Sat. **Soundness-negatives verified:** distinct-param `(x≤y∨x≥z+2)` (symbolic width `z−y+2`)
  declines (not-Unsat AND not-Sat); width-1 multiple-coefficient `(2y,2y+1)` → Sat (never wrongly
  Unsat); non-linear `x*x≥0` declines. Hooked after the closed/real/valid FM paths; strictly
  additive. New `tests/quant_int_open_gap.rs` (9); full suite + clippy + doc + fmt green.
  Sub-agent + soundness review (verified the content formula + the disjunction logic by hand).

- **2026-06-19** — **P2.x COMPLETENESS: gcd-aware integer tightening + a hang/wrong-answer hunt
  (clean bill).** Refined the strict-inequality tightening to be gcd-exact: `L + c0 < 0` (L a
  multiple of `g = gcd(aᵢ)`) ⟺ `L ≤ g·⌊(-c0-1)/g⌋`, so `2x < 2y` ⟹ `2x-2y ≤ -2` (not the loose
  `≤ -1`). Now `2x<2y ∧ 2y<2x+2`, `3x>3y ∧ 3x<3y+3`, `1000x<1000y ∧ 1000y<1000x+1000` all decide
  UNSAT immediately (`g=1` reduces to the prior `c0+1`; magnitude-guarded by `TIGHTEN_COEFF_LIMIT`
  to avoid i128 overflow — out-of-range coefficients left strict, sound). A read-only **hunt over
  ~30 arithmetic + quantifier queries found NO hangs and NO wrong answers** (independently
  confirming the LIA fix + the coefficient cases); all remaining gaps are graceful `Unknown` on
  harder fragments (NIA `x*x=2`, NRA √2, ∀∃-witness synthesis). New gcd-coefficient tests; full
  suite green. **Queued actionable item:** `∀x:Int.(x≤y ∨ x≥y+2)` → should be UNSAT (the k≥2
  sibling of the now-Sat k=1 valid case — `∃x` in the open width-k interval `(y,y+k)` exists for
  all y when k≥2; the instantiation fallback misses the uniform witness `x=y+1`).

- **2026-06-19** — **P2.x COMPLETENESS: integer strict-inequality tightening — `c>y ∧ c<y+1`
  decides UNSAT instantly (and the open-`∀` decides Sat).** The follow-up to the LIA-hang
  deadline below: rather than merely *not hang*, the LIA solver now *decides* these. A strict
  constraint `expr < 0` over an integer-valued `expr` (all coefficients integral; vars integer)
  is equivalent to `expr ≤ -1` ≡ `expr + 1 ≤ 0`; `lia_simplex_within` tightens every such
  constraint to non-strict before branch-and-bound, making the LP relaxation EXACT. So
  `c > y ∧ c < y+1` ⇒ `c−y ≥ 1 ∧ c−y ≤ 0` is immediately LP-infeasible → instant UNSAT (no
  grind, no deadline needed), and therefore `∀x:Int.(x≤y ∨ x≥y+1)` (valid — no integer between
  consecutive integers) now decides **Sat** via the valid-universal pass, fast. Only applied
  when `expr` is provably integer-valued (else left strict — sound). Equisatisfiable, so no
  existing LIA verdict changes (lia_simplex + full suite green). Tests:
  `qf_strict_between_consecutive_is_unsat_fast` (→ Unsat) and
  `open_disjunctive_universal_is_valid_and_fast` (→ Sat), both in 0.00s.

- **2026-06-19** — **ROBUSTNESS: QF-LIA branch-and-bound honors `config.timeout` (root of the
  open-`∀` hang).** The real root: a QF-LIA query `c > y ∧ c < y+1` (real-feasible at c=y+0.5,
  integer-infeasible — no integer strictly between consecutive integers) sent
  `lia_branch_and_bound` (`lra.rs`) grinding toward its 50 000-node budget — each node a simplex
  over an ever-deeper constraint stack as it kept finding shifted fractional points — with **no
  wall-clock check**, ~minutes ignoring the budget. (Triggered pre-existingly by
  `eliminate_valid_universals` testing `∀x:Int.(x≤y ∨ x≥y+1)` for validity via `¬body[x:=c]`
  UNSAT.) Fix: `lia_branch_and_bound` takes an `Option<Instant>` deadline checked per node
  (alongside the node budget); new `check_with_lia_simplex_within(arena, assertions, deadline)`
  threads it (`check_with_lia_simplex` = the `None` case, signature unchanged so the
  function-pointer callbacks in `dpll_lia` are untouched); the two `auto.rs` integer-dispatch
  sites derive the deadline from `config.timeout`. Now `∀x:Int.(x≤y ∨ x≥y+1)` returns in ~2 s at
  a 2 s budget (was ~600 s). Belt-and-suspenders from the same investigation: `prove_unsat_by_mbqi`
  (`MAX_MBQI_INSTANCES=4096` + deadline) and `prove_quantified_unsat_via_egraph`
  (`MAX_GROUND_TERMS=8192` + deadline) also bail gracefully. Sound — only `Unknown` (the budget
  case) is added; no verdict changes. New `tests/quant_open_disjunctive_no_hang.rs` (OS-timeout
  guarded, never a wrong `Unsat`). Diagnosed by marker + panic bisection down to the QF subquery. `∀x:Int.(x≤y ∨ x≥y+1)` (open, symbolic `y`) is declined
  by the FM int-closed pass and reaches the instantiation search, which generates ever-deeper
  ground terms (`y, y+1, y+2, …`); the per-round `check_auto` grew without a `config.timeout`
  check, so the query tarpitted ~600s ignoring the budget. Both loops now bail to a graceful
  `Unknown(ResourceLimit)`: `prove_quantified_unsat_via_egraph` (a `config.timeout` deadline +
  `MAX_GROUND_TERMS=8192` cap, checked at the top of each round) and `prove_unsat_by_mbqi`
  (deadline + `MAX_MBQI_INSTANCES=4096`). Sound — both only ever returned `Unsat` from a ground
  refutation, so degrading the non-refuting path to `Unknown` changes no verdict. New
  `tests/quant_open_disjunctive_no_hang.rs` (2 s budget returns, never a wrong `Unsat`),
  OS-timeout-guarded. Same posture as the NIA-hang fix. Found via the int-closed work.

- **2026-06-19** — **P1.2 PERF: word-level preprocessing now runs to a FIXPOINT (the proven
  reduction lever, not AIG node-count).** `check_with_preprocessing` ran the model-sound passes
  (`canonicalize` → `propagate_values` → `solve_eqs_bounded` → `elim_unconstrained` →
  re-`canonicalize`) exactly ONCE. But one pass is not enough: `elim_unconstrained` can expose a
  fresh constant that `propagate_values`/`solve_eqs` then eliminate, and the re-canonicalization
  AC-normalizes substituted product trees that reveal further folds. Now it iterates the passes to
  a fixpoint (a round eliminating nothing stops; `MAX_PREPROCESS_ROUNDS=8` guards oscillation),
  composing each round's `ModelReconstructionTrail` in pass/round order. Removes more variables
  before bit-blasting → relieves the encode budget (the mechanism PLAN.md credits for public p4dfa
  2→7/113). **Sound by construction:** every pass is model-sound (equisatisfiable, so `unsat`
  transfers), and the `sat` model is still replayed against the ORIGINAL assertions — any trail/round
  composition bug surfaces there as an `Err`, never a wrong `sat`. New
  `fixpoint_resolves_a_deep_definition_chain` test (deep `w=2 → x1 → x2 → x3=5` chain: sat replays,
  contradicted-chain unsat agrees with no-preprocess); existing `preprocess_on_off_agree_on_a_battery`
  + suite green. Validated by measured DISAGREE=0, NOT node count (per the AIG finding above).

- **2026-06-19** — **P2.6: integer-Omega exactness for CLOSED universals — decides the
  inter-integer-gap cases.** `∀x:Int.(x≤0∨x≥1)` is integer-VALID but real-INVALID (x=0.5), so the
  real-validity relaxation declines it; the new `eliminate_int_universal_closed` decides it EXACTLY.
  For a CLOSED universal (φ mentions only x — every FM bound is a concrete `Rational`), `∀x:Int. φ
  ⟺ ¬∃x:Int. ¬φ`; each DNF clause of `¬φ` is a concrete real interval, and `clause_has_integer`
  runs the exact integer-emptiness test: lower L admits `ceil(L)` (non-strict) / `floor(L)+1`
  (strict), upper U admits `floor(U)` / `ceil(U)-1`, clause has an integer iff `lo_int ≤ hi_int`
  (unbounded side ⇒ trivially yes); `floor` via `div_euclid`, ±1 saturating at i128 extremes. Any
  clause with an integer ⇒ Unsat; none ⇒ rewrite to `true` (Sat). Any non-constant residual ⇒
  DECLINE (open universal — left to the real-validity path / front door). Hooked after the real
  path + the closed path, before `eliminate_int_universal_valid`. Decides `∀x:Int.(x≤0∨x≥1)`→Sat,
  `∀x:Int.(x≤0∨x≥2)`→Unsat (hole `(0,2)`∋1), `∀x:Int.(x<0∨x>0)`→Unsat. Soundness-negatives: open
  universals decline (unit-tested `is_none`), non-linear declines. New `tests/quant_int_fm_closed.rs`
  (11) + 5 in-source unit tests; full suite (1071) + clippy + doc + fmt green. (Flagged: an open
  disjunctive universal, once declined, tarpits the downstream MBQI/e-matching ~600s — pre-existing
  "never hang" item, now in the work queue.) Sub-agent + soundness review (verified the ceil/floor
  strictness by hand).

- **2026-06-19** — **P2.6: sound integer `∀`-elimination via real-validity (one-directional).**
  Extends the FM pass to decide `∀x:Int. φ` using ONLY the sound direction: integers ⊆ reals, so
  `∀x:Real. φ` valid ⇒ `∀x:Int. φ` valid (the converse is FALSE — e.g. `∀x:Int.(x≤0∨x≥1)` is
  integer-valid but real-invalid, x=0.5). `eliminate_real_universal`'s body was factored into
  `eliminate_core(…, relax_int)` returning a `Verdict` enum (`Valid` / `Unsat` / `Rewrite(χ)`) —
  cleanly isolating the "valid" verdict. New `eliminate_int_universal_valid` runs the core with
  `relax_int=true` (admitting `IntLt/Le/Gt/Ge` + Int `Eq`) and returns a `true`-rewrite **iff and
  only iff** the verdict is `Valid`; `Unsat` and any `Rewrite(_)` ⇒ DECLINE (concluding unsat
  would be unsound — the integer universal may hold in the inter-integer gaps; rewriting to the
  stronger real-χ would under-approximate). The Int path can therefore NEVER emit `Unsat` or a
  non-`true` rewrite. Hooked after the real path (`.or_else`), and after `unsat_universal` (so
  `∀x:Int. x>0` still → Unsat there). Decides `∀x:Int.(x≤0∨x>0)`, `∀x:Int.(x<5∨x≥5)` → Sat.
  **Soundness-negatives verified:** `∀x:Int.(x≤0∨x≥1)` (int-valid, real-invalid) declines → NOT
  mis-decided unsat; `∀x:Int.(x≥0∧x≤10)` (int-false) declines → does NOT become Sat (stays Unsat
  via other passes). Real path byte-identical (15 FM tests unchanged). New
  `tests/quant_int_fm_valid.rs` (7); full suite + clippy + doc + fmt green. Strictly additive +
  conservative. The full integer-Omega (deciding the inter-gap cases) remains the keystone.
  Sub-agent + careful soundness review.

- **2026-06-19** — **P2.6: single-variable real Fourier-Motzkin `∀`-elimination — first true
  quantifier elimination (keystone slice).** Decides multi-atom `∀x:Real. φ` universals the
  single-atom/vacuous passes decline, via exact real QE. New `quant_fourier_motzkin.rs`
  (`eliminate_real_universal`), hooked in `solve` after the vacuous + unsat-single-atom passes.
  Method: `∀x. φ ⟺ ¬∃x. ¬φ`; `¬φ` → DNF (De Morgan + `⇒`-desugar, capped at 64
  clauses/literals); `∃x` distributes, each conjunctive clause FM-eliminated — collect lower
  (`a<0`) / upper (`a>0`) bounds `-r/a` from `a·x+r ⋈ 0` (equality = both; x-free pass through),
  join `Lᵢ ⋈ Uⱼ` with **`<` iff either bound strict** else `≤` (the subtle correctness point:
  `∀x.(x≤0 ∨ x>0)` is valid — join `0<0` false — while `∀x.(x<0 ∨ x>0)` is unsat — join `0≤0`
  true at x=0); unbounded side ⇒ vacuously satisfiable. A clause eliminating to `true` ⇒ the
  universal is **Unsat**; else negate the residual disjunction → an x-free `χ` and **rewrite**
  the assertion to it (then re-dispatch). Real FM is EXACT, so in-scope verdicts are exact.
  **Conservative declines (sound — leave byte-identical):** Int universals (real FM isn't exact
  over ℤ — the load-bearing guard), nested quantifiers, non-linear x (`x·x`/`div`/`abs`/x-in-UF/
  array → opaque affine), non-real atoms, x-disequalities (single-point hole), over-cap DNF.
  Decides `∀x.(x≥0∧x≤10)`→Unsat, `∀x.(x≤0∨x>0)`→Sat, `∃y.∀x.(x≤y∨x≥y)`→Sat,
  `∀x.(x<0∨x≥y)`→`y≤0`. Soundness-negatives verified (non-linear `x·x` and Int both declined,
  no real universal mis-decided). New `tests/quant_fourier_motzkin.rs` (15); full suite (1047) +
  clippy + doc + fmt green. Strictly additive. The harder integer-Omega + general-boolean cases
  remain the keystone core. Sub-agent + careful soundness review.

- **2026-06-19** — **P2.6: unsatisfiable-`∀` detection — another sound `∃∀` slice.** A top-level
  `∀x. body` where `x:Int`/`Real`, `body` is a SINGLE arithmetic atom that normalizes to
  `c·x ⋈ t` with `c≠0` (x genuinely appears), `t` x-free, and `⋈∈{<,≤,>,≥,=}` is
  **unconditionally UNSAT** (a linear function of an unbounded x can't satisfy a one-sided
  constraint for all x). New `quant_unsat_universal.rs` (`detect_unsatisfiable_universal`),
  hooked in `solve` AFTER `eliminate_vacuous_universals` (which owns the `c=0` case — no overlap)
  and before `check_with_quantifiers`, returning `CheckResult::Unsat` on a match. Reuses the
  vacuous pass's `Affine`-over-`Rational` collector (so `c≠0` ⇒ the residual is exactly `c·x ⋈ t`,
  t x-free; `affine` returns `None` on any non-linear/UF/array/`bv2nat` x-occurrence ⇒ decline).
  Decides `∀x:Int. x>0`, `∀x:Int. 2x=5`, `∀x:Real. x≤y`, and (with the existing `∃`-skolemization)
  `∃y:Int.∀x:Int. x≤y` — all → Unsat (were Unknown). **Soundness-negatives verified:** `∀x. 2x≠5`
  (true; `≠` is `not(eq)` = `BoolNot`, declined structurally → not Unsat), `∀x. x+y≥x` (c=0 →
  vacuous pass, not this one), `∀x.(x>0 ∨ x≤0)` (valid disjunction, multi-atom → declined),
  guarded `∀x.(0≤x≤2)⇒x≥5` (implication → declined, still Unsat via the guarded path). New
  `tests/quant_unsat_universal.rs` (9); the quant sibling suites all green. Strictly additive.
  Sub-agent + soundness review.

- **2026-06-19** — **P3.3: quantifier certs made assume-independent (closes the main
  emitter-trust gap).** The finite-`∀` cert re-check (`check_alethe_lra_guarded_inst`) verified
  the `forall_inst_guarded` instantiation + rule structure but **accepted the proof's
  ground-fact and abstraction-definition `assume`s as given** — so a proof could `assume` a fact
  not in the query and still pass. New `check_alethe_lra_guarded_inst_against(universal, proof,
  arena, assertions)` (threaded from `Evidence::check`, which already has `assertions`) now
  classifies every `assume` and REJECTS (`Ok(false)`) anything that is not: (1) the carried
  universal, (2) an original assertion (rendered via the same `term_to_alethe_uf` the emitter
  uses — exact key match), (3) a genuinely-fresh Ackermann definition `(= !fn_app_N (f t))`
  (the introduced const must not occur in the rendered query — the load-bearing freshness
  guard), or (4) an abstracted original assertion bridged through a class-3 definition. Both
  emitters self-validate through the strengthened checker so emission and consumer re-check
  agree. **Soundness-negative tests** (`assume_independent_check_rejects_fabricated_premise`
  LIA/UF, `..._rejects_non_fresh_definition`) assert the OLD checker returns `Ok(true)` on a
  fabricated `(= a 5)` / non-fresh `(= x (g x))` assume while the new check + `Evidence::check`
  reject it — proving the gap is closed. All genuine LIA/UF/pure-LIA-`∀`/UFLIA certs + existing
  tamper tests still pass (no false negatives; class 4 was required to keep UF certs green).
  One residual remains (the carried universal isn't yet cross-verified ∈ `assertions` — see
  frontier). fmt + clippy + doc + full suite + Carcara (54) green. Sub-agent + soundness review
  (I traced and recorded the residual).

- **2026-06-19** — **P3.3: finite-`∀`-over-UF `unsat` certified (quantifier proof extended to
  a UF+arith tail).** The finite-`∀` cert only handled a pure-LIA ground tail, so
  `∀x:Int.(0≤x≤1) ⇒ f(x)=0` with `f(0)=1` (a finite-`∀` whose body uses an uninterpreted `f`,
  unsat by EUF on the instances) stayed `Unsat(None)`. New `prove_finite_int_quant_unsat_uf_alethe`
  (`quant_finite_cert.rs`): builds the ground instances, **Ackermann-abstracts** the UF residual
  via `eliminate_functions` (fresh same-sorted `v_k = f(v)`), gates on `check_with_lia_simplex(abstraction) == Unsat`,
  emits the `lia_generic` tail over the abstraction, and splices per-instance `forall_inst_guarded`
  → `resolution` → (assume the fresh `v_k=f(v)` definition) → `eq_transitive` (`v_k=f(v)=c ⊢ v_k=c`),
  so each abstracted instance flows from the universal. Reuses `Evidence::UnsatGuardedQuantAletheProof`
  + `check_alethe_lra_guarded_inst` (validates all three rule families: the custom
  `forall_inst_guarded` hook, base `eq_transitive`/`symm`, and `lia_generic`). Self-validating
  (emit only on re-check) + tamper test (out-of-range witness AND corrupted `eq_transitive`
  bridge both rejected). Ordered after the pure-LIA finite-`∀` path; strictly additive. Certifies
  the target + a wider-range twin; pure-LIA finite-`∀`, gap-C UFLIA, and a SAT UF-universal all
  unregressed. fmt + clippy + doc + full suite + Carcara (54) green. **Assurance (honest):** same
  tier as the finite-`∀` cert — in-tree-checked custom rule, NOT Carcara/Lean cross-checked, and
  the `check_alethe_lra_guarded_inst` re-check verifies the instantiation + rule structure but
  **trusts the emitter's ground-fact/abstraction-def `assume`s** (it doesn't cross-verify them
  against the original assertions). Sound in practice (the emitter uses the original assertions +
  genuinely-fresh `eliminate_functions` vars), but closing this to a fully assume-independent
  check is a real follow-up (see frontier). Sub-agent + soundness review.

- **2026-06-19** — **P3.3: certified `bv2nat`-bound `unsat` (gap D) — last self-contained
  certification gap from the proof-completeness map.** `bv2nat(x) ≥ 16` for a 4-bit `x` (and
  similar int-blast bound contradictions) was a bare `Evidence::Unsat(None)`; it now carries an
  independently-checkable `lia_generic` certificate. `bv2nat_bound_certificate` clones the arena,
  abstracts each `bv2nat(b)` (w-bit) to a fresh Int `n` with the range axiom `0 ≤ n ≤ 2^w−1`
  (parity with `auto`'s divmod elimination), and emits `prove_lia_unsat_alethe` over the pure-LIA
  abstracted query (re-checked by `check_alethe_lra`), attached as `Evidence::UnsatArithAletheProof`.
  **Honest partial-trust** (zero-trust would need a `bv2nat`→bit-literal emitter, which doesn't
  exist — not forced): `trusted_steps = [(IntBlast, false), (Farkas, true)]` — the LIA refutation
  is certified, only the `bv2nat`-range/width-bridge axiom (ADR-0014) is trusted (reused the
  existing `IntBlast` TrustId — no new ADR). Wired after `guarded_quant_alethe_certificate` and
  before the bare fallback; declines (`None`) without an abstractable `bv2nat`, so plain
  LIA/UFLIA/zero-trust paths are never shadowed. Tamper test (drop closing step → reject) proves
  the check is real. New `tests/evidence_bv2nat_cert.rs`; plain QF_LIA keeps its Farkas-only cert
  (no spurious IntBlast hole), QF_BV unchanged, SAT `bv2nat=7` never reported unsat. fmt + clippy +
  doc (z3-feature) + full suite + Carcara green. Strictly additive. From the 6th pass. (Sub-agent
  used `git stash` once against protocol to confirm a pre-existing Z3Backend doc error — verified
  contained, stash empty, concurrent `nra.rs` unclobbered; noted, not repeated.)

- **2026-06-19** — **P3.3: certified finite-`∀` `unsat` — a first checkable quantifier proof
  (Lean-parity quantifier-proof keystone, scoped slice).** A finite-expansion guarded-`Int`
  universal `∀x:Int. (lo≤x≤hi) ⇒ inner` decided `unsat` (e.g. `∀x:Int.(0≤x≤2)⇒x≥5`) was a bare
  `Evidence::Unsat(None)`; it now carries an independently-checkable certificate. **Feasibility
  finding:** the in-tree `check_alethe` base kernel has NO native quantifier-instantiation rule,
  but `check_alethe_with`'s `extra` hook lets a custom rule be re-checked by a callback (the
  pattern `prove_quant_unsat_alethe` already uses for EUF). New `quant_finite_cert.rs`
  (`prove_finite_int_quant_unsat_alethe`): emits an `assume` of the universal, a
  `forall_inst_guarded` step per `v∈[lo,hi]` delivering `inner[x:=v]`, `resolution` to the
  instance unit, and the `lia_generic` ground tail spliced from `prove_lia_unsat_alethe`;
  `check_alethe_lra_guarded_inst` chains a hook that re-derives **both** the structural
  substitution **and** the guard truth (`lo≤v≤hi`) with the arith checker — so the
  instantiation is **certified, not trusted** (zero-trust on the quantifier step; the ground
  refutation records the certified `Farkas` step). New
  `Evidence::UnsatGuardedQuantAletheProof { proof, universal }` (carries the form to re-check
  arena-free), wired into `produce_evidence` after all ground certs (which decline on
  quantifiers). **Tamper test** with two mutations (out-of-range witness → guard re-check
  fails; non-instance literal → structural match fails) proves the check is real. New
  `tests/evidence_quant_cert.rs` (7); QF_LIA/QF_BV ground certs unchanged. The custom
  `forall_inst_guarded` is in-tree-checked (not a standard Alethe rule, so outside Carcara/Lean
  cross-check — a lower assurance tier than the standard emitters, noted). General `forall_inst`
  over infinite domains / arbitrary bodies stays the keystone (needs the rule in the
  `axeyum-cnf` kernel — coordination-gated). From the 6th pass; sub-agent + soundness review.

- **2026-06-19** — **P3.3: zero-trust certificate for mixed QF_UFLIA/UFLRA `unsat` (gap C) —
  the Ackermann cert family extends from UF-over-BV to UF-over-arithmetic.** A mixed
  `f(x)=1 ∧ f(y)=2 ∧ x=y` (f:Int→Int and the Real twin) was a bare `Evidence::Unsat(None)`;
  it now carries an independently-checkable, **zero-trust-hole** certificate. New module
  `qfuflia_alethe.rs` (`prove_qf_uflia_unsat_alethe`): gates on every UF application being
  arithmetic-sorted (BV-sorted UF → `None`, leaving the BV path; arrays/datatypes/quantifiers
  → `None`), Ackermann-abstracts each app to a fresh same-sorted constant, derives the
  functional-consistency consequents `(= vᵢ vⱼ)` via `eq_congruent`/`eq_transitive`/`symm`,
  and hands the pure-LIA/LRA residual to `prove_lia_unsat_alethe`/`prove_lra_unsat_alethe`;
  the congruence steps are spliced over the residual's `assume`s into one proof re-checked
  end-to-end by `check_alethe_lra` (base congruence rules + the `lia_generic`/`la_generic`
  arith clause). Self-validates (emit only if the re-check passes). **Refactor:** the
  Ackermann-congruence prefix of `prove_qf_ufbv_unsat_alethe` was extracted into a shared
  `AckermannCongruence` (`build_ackermann_congruence`) — a pure refactor, QF_UFBV emission
  byte-identical (**Carcara cross-check confirms**). Wired into `produce_evidence` after
  `zero_trust_alethe_certificate` (QF_UFBV keeps its BV cert) and before
  `arith_alethe_certificate` (LIA/LRA emitters decline any UF app); `trusted_steps` empty
  (congruence + arith both re-derived — no trusted reduction). Tamper test (drop the closing
  step → `check` rejects) proves the verification is real. New `tests/evidence_uflia_cert.rs`
  (7); 999-test suite + clippy + doc + fmt + Carcara (54) green. Strictly additive. From the
  6th capability-gap pass (proof-completeness map); sub-agent + soundness review.

- **2026-06-19** — **ROBUSTNESS: BMC honors its own "unsupported is not an error" contract.**
  `run_bounded_model_check` drives the warm `IncrementalBvSolver`, which rejects `Op::Apply`;
  a transition relation with an uninterpreted step function (`x' = f(x)`) made the
  `SolverError::Unsupported` escape via `?` as a hard `Err`, even though the module docstring
  promises "a solver timeout/unsupported at some depth is not an error — it is reported as
  `BmcOutcome::Unknown`" (and the "unknown is never an error" hard rule). Fix: a
  `unsupported_to_unknown(err, steps)` helper maps `Unsupported` → `BmcOutcome::Unknown { steps,
  Incomplete }` at the per-depth solver operations (init/bad/trans asserts + the check), popping
  the scope first to keep the solver warm; any other `SolverError` still propagates. New
  in-module test (`UfStepper`: `x'=f(x)` → `Ok(Unknown)`, not `Err`); full suite + clippy + fmt
  green. From the 5th capability-gap pass (Track-4 + FP surfaces — which found NO soundness
  issues: FP arithmetic/conversions are bit-exact, BMC/k-induction/symexec decide correctly).
  **Symexec given the same treatment:** `SymbolicExecutor::branch`/`status` (feasibility
  *decision* queries) now map a backend `Unsupported` (a branch over an uninterpreted
  `Apply` — the canonical way to model an unmodeled call) to the existing
  `PathStatus::Unknown` ("may be feasible, not pruned") via a `status_or_unknown` helper,
  instead of a hard `Err`; new in-module test (`branch_over_uninterpreted_call_is_unknown_not_error`).
  `assume` (a stateful constraint-add, not a decision) keeps propagating. The FP conversions
  being constant-fold-only stays a coordination-gated `axeyum-fp` follow-up.

- **2026-06-19** — **P2.6: vacuous-`∀` elimination — a first sound cut into `∃∀`.**
  `∃y.∀x. x+y≥x` returned `Unknown` (after skolemizing `∃y→c`, `∀x. x+c≥x` is valid only
  when `c≥0`, so the valid-universal pass can't decide it; instantiation only refutes). New
  `quant_vacuous_universal.rs` (`eliminate_vacuous_universals`), hooked in `solve` after
  `eliminate_valid_universals`: for a top-level `∀x. body` (QF body, `x:Int`/`Real`), a Boolean
  descent (`not`/`and`/`or`/`implies`/`xor`/`ite`) reaches the atoms, and a self-contained
  affine collector (over `Rational`; handles `+`/`-`/neg/`*`-by-const + the `to_real` embed)
  declares `x` **vacuous** iff *every* arithmetic atom's net `x`-coefficient of `lhs−rhs` is 0
  **and** `x` occurs in no non-linear / UF-arg / array / BV / `div`/`mod`/`abs` position
  (any such occurrence bails). Then `∀x. body ⟺ body[x:=0]` (the bound var can't change any
  atom's truth), substituted via `replace_subterms` → the QF dispatch decides. Sound +
  conservative (any doubt ⇒ untouched). Decides `∃y.∀x. x+y≥x` → Sat, `∀x. x*0+y=y` → Sat;
  **soundness-negatives verified** — `∃y.∀x. x≤y`, `∀x. x≥0`, mixed-dependent bodies, and
  `∀x. f(x)=f(x)` (UF arg) are NOT wrongly Sat (the last still decides via the valid-universal
  pass). New `tests/quant_vacuous.rs` (8, incl. 4 soundness-negatives); full suite + clippy +
  fmt green (OS-timeout guarded). Strictly additive. A first slice of the `∃∀` keystone (full
  `∃∀` still needs LIA/LRA quantifier elimination); sub-agent + soundness review.

- **2026-06-19** — **P3.3: QF_LIA `unsat` now carries a checkable certificate in
  `produce_evidence` (gap E).** A pure-integer `unsat` (`x>0 ∧ x<0`) reached the `Other`
  evidence route and ended as a bare `Evidence::Unsat(None)` (`is_certified()==false`), even
  though `prove_lia_unsat_alethe` emits a checkable `lia_generic` Alethe proof (used on the
  SMT-LIB get-proof path). Fix: new `Evidence::UnsatArithAletheProof(Vec<AletheCommand>)`
  variant whose `Evidence::check` re-validates via the **arithmetic-aware**
  `check_alethe_lra` (= `axeyum_cnf::check_alethe_with` + the `la_generic` callback, which
  re-derives the integer/linear Farkas refutation — plain `check_alethe` can't decide
  `lia_generic`). A new `arith_alethe_certificate` helper tries `prove_lia_unsat_alethe` then
  `prove_lra_unsat_alethe` (each self-validating) in `produce_evidence`'s `Other`/`Unsat` arm,
  **after** `zero_trust_alethe_certificate` and **before** the bare/DRAT fallback (the arith
  emitters return `None` for UF/array/datatype, so ordering is safe). `trusted_steps =
  [(Farkas, certified)]` (the reduction is re-derived, not a trust hole). **Tamper test**
  (`tampered_lia_arith_evidence_fails_its_own_check`: drop the closing step → `check` rejects)
  proves the verification is real. Now certifies `x>0 ∧ x<0` and `x+y≥3 ∧ x≤1 ∧ y≤1`; QF_BV /
  QF_UFBV evidence paths unchanged (asserted). Strictly additive (only bare LIA `unsat` →
  certified). New `tests/evidence_lia_cert.rs` (5); full suite (977) + clippy + fmt green.
  From the 4th capability-gap pass; sub-agent + soundness review.

- **2026-06-19** — **P4.3 OMT robustness + completeness: optimizer honors timeout, decides
  div/mod, never errors (gaps A/B/D).** The optimizer's feasibility probes called
  `check_with_lia_dpll` directly and no path threaded `config.timeout`. Three fixes in
  `optimize.rs`: (B, completeness) reroute the LIA bound-search + Pareto probes
  (`decide_with_objective`, `pareto_probe`) through the full `check_auto` dispatcher, so
  objectives/constraints with `mod`/`div`-by-constant now optimize (`x∈[0,10] ∧ x mod 2=0`,
  max x → **10**; `x/3≤5`, max x → 17 — were hard `Err`); (D, hard rule "unknown is never an
  error") `probe_unsupported_to_unknown` maps a fragment-`Unsupported` (objective over a
  UF/`bv2nat`/nonlinear term) to a graceful `OptOutcome::Unknown` / `LexOutcome::Stopped{Unknown}`
  / `ParetoOutcome::Unknown` instead of propagating the error (min `x*x` → Optimal(0) via NRA;
  max `f(x)` → Unknown, no Err); (A, resource-limit promise) new `*_with_config` variants
  (`maximize_lia_with_config`, …, `optimize_lia_pareto_with_config`) thread a wall-clock
  deadline (Instant + `past_deadline`, wasm-shimmed) into the bound-doubling/binary-search and
  the Pareto/box/lex point loops, returning best-so-far as `Truncated`/`Unknown` on expiry
  (a 101-point Pareto front with a 2 s budget now returns in ~2 s, was minutes); the original
  no-config functions delegate with `SolverConfig::default()`, so all ~54 existing call sites
  and optima are unchanged. New `tests/optimize_robustness.rs` (6); 24 existing optimize tests
  + full suite + clippy + fmt green. From the 4th capability-gap pass (solver surfaces); sub-agent.

- **2026-06-19** — **ROBUSTNESS: integer-NIA solve HANG fixed (regression from the width
  ladder).** `a*b ≠ b*a` (ground integer nonlinear, UNSAT by commutativity) **livelocked**,
  ignoring `config.timeout` — a "never hang" contract violation caught by the 3rd capability
  pass. Root cause: pure-Int nonlinear never reaches the deadline-honoring `check_with_nra`
  (gated on `has_real`), so it fell to `dispatch_int_blast_width_ladder`, which ran ~31
  bit-blast+SAT solves over a hard multiplier-equivalence **with no timeout check between
  widths**; the real relaxation ran only after and abstracted `a*b`/`b*a` as distinct vars.
  Three fixes in `auto.rs`/`int_real_relax.rs`: (1) **deadline** — the ladder now threads
  `config.timeout` (Instant + `past_deadline`, wasm-shimmed) and bails to `Unknown(ResourceLimit)`
  before each width; (2) **trimmed ladder** — dense `4..=16` (where small witnesses live) +
  a sparse coarse tail to `DEFAULT_INT_WIDTH=32` (dropped the 36/40 tail + thinned 17..=31),
  so the no-timeout case is fast and `nia_ground_consistency` (x*x=4/9/25) still passes; (3)
  **commutative canonicalization + reorder** — `int_real_relax` sorts `mul`/`add` operands so
  `a*b` and `b*a` translate to the SAME real term (sound — real `*`/`+` commute), and the
  relaxation now runs **before** the ladder (it only ever returns `Unsat`, so reordering is
  sound and SAT cases like `x*x=4` still reach the ladder). Result: `a*b≠b*a` → **Unsat fast**
  (was a >100s hang), `∀x. x*k=k*x` → Sat, timeout honored. New `tests/nia_commutativity.rs`
  (4, incl. a 500ms-timeout-returns check); fmt + clippy + full suite green under an OS-timeout
  guard. Sub-agent + careful soundness/termination review.

- **2026-06-19** — **P2.5: integer nonlinear UNSAT via real relaxation (gap G3).**
  Sign-based integer-NIA goals (`x*x<0`, `x*x+1≤0` over Int) returned `Unknown`, and
  consequently `∀x:Int. x*x≥0` stayed `Unknown` (the valid-universal pass's `c*c<0` witness is
  integer-NIA). Fix: new `int_real_relax.rs` (`refute_int_via_real_relaxation`) + a fallback at
  the tail of the `has_int` dispatch branch, *after* the exact LIA refuters and the int-blast
  width ladder, fired only when the ladder is `Unknown`. On an isolated arena clone it builds
  the **faithful real reinterpretation** of the query — each `Int` var→a fresh memoized `Real`
  var (same int symbol ⇒ same real var), `int_const`→`real_const`, `IntAdd/Sub/Mul/Neg/Lt/Le/
  Gt/Ge`→the `Real*` counterparts, Bool/`Ite`/`Eq` rebuilt — and runs `check_with_nra`. Since
  integer solutions ⊆ real solutions, **real-`Unsat` ⇒ integer-`Unsat`** (sound); it returns
  *only* `Unsat` (a real model need not be integral), so strictly additive. **Conservative
  allow-list:** any `div`/`mod`/`abs`/coercion/`bv2nat`/BV/array/UF/datatype/quantifier subterm
  aborts the whole relaxation (→ unchanged) — never a guessed translation. One bounded NRA call,
  clone-scoped (no leakage/OOM). Decides `x*x<0`/`x*x+1≤0` → Unsat and **`∀x:Int. x*x≥0` → Sat**
  (the valid-universal sub-check now refutes `c*c<0`); `x*x==2` stays `Unknown` (real-sat √2, no
  wrong unsat), `x*x==4 ∧ x>0` stays `Sat` (width ladder). New `tests/nia_real_relaxation.rs`
  (5); fmt + clippy + full suite green. Final tractable gap from the 2nd capability-gap pass;
  sub-agent + soundness review.

- **2026-06-19** — **P2.4: `bv2nat` out-of-range now refuted UNSAT (gap G2).** `bv2nat(b)` of
  a W-bit `b` is provably in `[0, 2^W-1]`, but `bv2nat(4-bit) >= 16` / `== 20` returned
  `Unknown`: the exact LIA refuters reject a raw `Op::Bv2Nat` (`lra.rs` `Collector::linearize`
  catch-all), so the query fell to the bounded int-blast which returns `Unknown` (never
  `Unsat`) for an in-range integer no-model. Fix: new `bv2nat_bound.rs`
  (`abstract_bv2nat_for_refutation`) + a `refute_bv2nat_out_of_range` hook at the top of the
  `has_int` dispatch branch. On an **isolated arena clone**, each distinct `bv2nat(b)` term is
  replaced by a fresh Int var `n` with the true bound `0 ≤ n ≤ 2^W-1` (hash-consing ⇒ the same
  `bv2nat(b)` ⇒ one var; distinct `b` ⇒ independent), and the exact refuters
  (Diophantine/simplex/DPLL) decide the **relaxation** — `unsat` of the relaxation transfers
  (sound). Returns `Unsat` only on a refutation; otherwise falls through to the original (SAT
  decided by the native int-blast `Bv2Nat` handling, `bv2nat` intact). Width guard
  `MAX_BOUND_WIDTH=62` keeps `2^W-1` exact in `i128` (wider ⇒ unabstracted, graceful). No
  leakage/OOM (clone-scoped). Decides `bv2nat(4-bit)≥16`/`==20`/same-`b` `==5 ∧ ==6` → Unsat;
  preserves `≥8` → Sat and distinct-vector `==5 ∧ ==6` → Sat. New `tests/bv2nat_bound.rs` (6);
  fmt + clippy + full suite green. From the 2nd capability-gap pass; sub-agent + soundness review.

- **2026-06-19** — **P1.6: EUF over the reals (QF_UFLRA) — hard `Err` fixed, now routed
  through the combination (gap G1).** A real-sorted UF application `f(x):Real` returned
  `Err Unsupported("QF_LRA: non-linear or non-real subterm …")` — the pure-real linearizer
  rejects the `Apply` and the dispatch's `has_real` branch *unconditionally returned*
  `check_with_nra`, so it never reached the function handling. The **integer** branch already
  catches `Unsupported` and falls through to `check_with_uf_arithmetic` (that asymmetry is why
  QF_UFLIA worked but QF_UFLRA didn't). Fix (`check_auto_dispatch`): when a function is present,
  the `has_real` branch now falls through on `Unsupported` to the EUF + linear-arithmetic
  combination (`check_with_uf_arithmetic` decides QF_UFLRA the same way as QF_UFLIA). A second
  fix: a Real arith-UF query whose combination result is `Unknown` (the QF_UFLRA *sat-model
  projection* for an arithmetic-sorted UF is not yet built) now **returns that `Unknown`**
  instead of falling through to the eager bit-blast fallback, which errors on `Real` (an Int
  arith-UF can still fall through to int-blast). Upholds "`unknown` is never an error" and
  unlocks EUF+LRA. Now: `f(x)=1 ∧ f(y)=2 ∧ x=y` → **Unsat** (congruence), the Nelson-Oppen
  squeeze `f(a)≤b ∧ b≤f(a) ∧ a=c ∧ f(c)≠b` → **Unsat**, and `f(x)=1.0` → graceful **Unknown**
  (was a hard `Err`; sat-model projection for an arithmetic UF is the remaining follow-up).
  Surgical (only the function-present Real case changes). New `tests/euf_real.rs` (3); fmt +
  clippy + full suite green. From the 2nd capability-gap pass (highest-value finding).

- **2026-06-19** — **P2.6: valid-universal elimination handles NESTED `∀` prefixes (gap G4).**
  `eliminate_valid_universals` previously bailed when a `∀x. body` had a quantifier in its
  body, so `∀x.∀y. x+y==y+x` (valid) stayed `Unknown`. `try_eliminate` now **peels the entire
  leading `∀` prefix** (`∀x.∀y.…` ⇒ vars `[x,y]`, innermost body), substitutes *all* bound
  vars with fresh `!vu_*` constants at once, and checks the negated innermost (QF) body unsat
  — sound by the same closure argument (`∀x.∀y. b` valid iff `¬b[x:=cx,y:=cy]` unsat). Now
  decides `∀x.∀y. x+y==y+x` and `∀x.∀y. x=y ⇒ f(x)=f(y)` (Sat); a non-valid nested universal
  (`∀x.∀y. x=y`) is not mis-proven valid (verified — never wrongly Sat). 3 new tests; fmt +
  clippy + full suite green. (Remaining from the 2nd gap pass: G1 EUF-over-Real hard `Err`,
  G2 `bv2nat` width bound, G3 nonlinear-body validity, G5 `∃∀` skolem-then-validity.)

- **2026-06-19** — **P2.6: sat-side universal-validity elimination — valid `∀` now decided
  (were `Unknown`).** A standalone `∀x. body` with a quantifier-free body is **valid** (hence
  the assertion is satisfiable — true in every model) **iff** `¬body[x:=c]` is UNSAT for a
  fresh constant `c`. New `quant_valid_universal.rs` (`eliminate_valid_universals`), hooked in
  `solve` before `check_with_quantifiers`: for each top-level `∀x. body` (QF body; nested
  quantifiers skipped), mint a fresh `!vu_*` constant of `x`'s sort, substitute via
  `replace_subterms`, and decide `¬body[x:=c]` with the **quantifier-free** `check_auto`
  (no re-entry → terminates in one bounded QF solve). `Unsat` ⇒ the universal is valid ⇒
  replace with `true` (exact); `Sat`/`Unknown` ⇒ leave it for the existing instantiation/MBQI
  path. Sound + strictly additive (only `Unknown`→decided; a proven-valid universal is `true`
  everywhere, an unprovable one is never dropped). Leverages the existing exact deciders:
  `c+0≠c`/`c·0≠0` (LIA), `f(c)≠f(c)` (EUF), `c·c<0` (NRA sign rule). Now decides
  `∀x:Int. x+0=x`, `x·0=0`, `x≥0 ∨ x<0`, `∀x. f(x)=f(x)`, `∀x:Real. x²≥0`. UNSAT-by-
  instantiation (`∀x. f(x)=0 ∧ f(a)=1`) and non-valid universals unaffected (verified). New
  `tests/quant_valid_universal.rs` (8); one guarded-int test relaxed (its formula is validly
  `Sat` now — a sound improvement). fmt + clippy + full suite green. Capability-gap pass;
  sub-agent + independent soundness review (the alarming compile diagnostics were a stale
  analyzer cache — the code builds and the suite is green).

- **2026-06-19** — **QF_NIA: ground-vs-`∃` inconsistency fixed (small nonlinear-int SAT
  now decided).** `x*x==4 ∧ x>0` (ground) returned `Unknown` ("overflowed at width 32") while
  the equivalent `∃x. x*x==4` returned `Sat` (skolemize → bounded blast finds x=2) — same
  satisfiability, two answers. Root cause: the integer bit-blast fallback used a single fixed
  width (`DEFAULT_INT_WIDTH=32`), and at width 32 the SAT solver may pick a *wrapping* witness
  (`x` with `x*x ≡ 4 mod 2^32` but `x*x ≠ 4`) that fails the exact-integer replay → `Unknown`.
  Fix (`auto.rs::dispatch_int_blast_width_ladder`): for a pure-integer fallback query, iterate
  the blast width small→large (4..=32, then 36, 40 — a deterministic, finite ladder that
  still includes the old width 32) on an arena clone per width, returning the **first
  replay-checked `Sat`**. **Sound by construction:** `check_with_all_theories` returns `Sat`
  only after replaying the model against the originals, and returns `Unknown` (never `Unsat`)
  for an integer query with no model within a width (`combined.rs:88`), so the ladder never
  produces a wrong `unsat` and a too-narrow width simply climbs. Strictly additive (only
  `Unknown`→`Sat`); `x*x==2` (no integer root) stays soundly `Unknown` (out of scope —
  needs genuine NIA unsat reasoning). New `tests/nia_ground_consistency.rs` (6, replay-verified).
  **Follow-up:** the ladder runs up to ~31 solves for an integer query that is `Unknown` at
  every width — bounded and OOM-safe (one arena clone at a time, width cap 40) but worth a
  smarter width schedule / shared budget later. Driven by the capability-gap pass; sub-agent +
  independent soundness review.

- **2026-06-19** — **P2.6: guarded-finite Int universals now decided (were `Unknown`).**
  A universal `∀x:Int. (lo≤x≤hi) ⇒ body` is logically *equivalent* to the finite conjunction
  `⋀_{v=lo}^{hi} body[x:=v]` (outside `[lo,hi]` the implication is vacuously true), so it is an
  exact, sound rewrite — both sat and unsat transfer. New `quant_guarded_int.rs`
  (`expand_guarded_int_universals`), hooked into `check_with_quantifiers` as a pre-pass before
  `axeyum_rewrite::expand_quantifiers` (which rejects Int domains): detects `∀x:Int.(⇒ guard
  inner)` where `guard` is a conjunction of a lower- and upper-bound atom isolating the bare
  bound var against **literal** Int constants (all `≤`/`≥` orientations), substitutes each `v∈
  [lo,hi]` via `replace_subterms`, and decides the resulting QF conjunction. A deterministic
  `RANGE_SIZE_CAP = 4096` (checked arithmetic) means an inverted/unbounded/huge range never
  expands → graceful `Unknown` (never OOM); nested quantifiers / non-literal bounds / escaping
  var → passthrough. Sat replay anchors on the equivalence-preserving `guard_expanded` (the
  ground evaluator can't evaluate a raw Int `∀`). Strictly additive (only `Unknown`→decided).
  Decides `∀x.1≤x≤3⇒x²≤9` (Sat), `∀x.1≤x≤3⇒x≤2` (Unsat), `≥`-oriented, one-point range, and
  over-cap → Unknown. New `tests/quant_guarded_int.rs` (5); full solver suite + clippy + fmt
  green. Driven by the capability-gap pass; done via a focused sub-agent.

- **2026-06-19** — **P2.9/P1.6: datatypes with Int/Real fields now decided (were a hard
  `Err`).** The native datatype solver (`datatype_native.rs`) rejected any datatype carrying
  an `Int`/`Real` field with `SolverError::Unsupported` — blocking `List Int`, `Tree Int`,
  records with numeric fields, and the whole numeric-payload datatype space, even for pure
  congruence with no arithmetic. Fix: `register_datatype` admits `Int`/`Real` field sorts;
  `build_sym_vars` already declares a field var of the field's own sort with the
  well-founded-default guard (`well_founded_default` returns `Int(0)`/`Real(0)`);
  `value_to_term` renders `Int`/`Real` defaults. The datatype-free residual (tags as BV,
  field vars as Int/Real + the original arithmetic) re-dispatches through the existing
  `solve → check_auto` path, which routes Int/Real to the LIA/LRA deciders and BV to
  bit-blasting — no new wiring. Sound: `unsat` equisatisfiable, `sat` projects to
  `Value::Datatype` and **replays** (a projection bug ⇒ replay failure → Unknown, never a
  wrong sat). Now decides: `v(x)=1 ∧ v(y)=2 ∧ x=y` (UNSAT, congruence), `is-cons(l) ∧
  head(l)=5` (SAT), `v(x)+1=4` (SAT), recursive `List Int`, multi-ctor `Either Int`. New
  `tests/datatype_int_fields.rs` (5); existing datatype tests + full solver suite (926) +
  clippy + fmt green. Driven by a measured capability-gap pass; done via a focused sub-agent.
  Closes the P0 finding from that pass (also upholds "unknown is first-class, never an error"
  — the hard `Err` is gone).

- **2026-06-19** — **P3.5: Ackermann cert widened to congruence-closure arg-equalities
  (e-graph fallback).** `prove_qf_ufbv_unsat_alethe` now discharges an argument pair equal
  by **congruence** (not just transitive closure of asserted edges) — e.g.
  `f(g(a))=k ∧ a=b ∧ f(g(b))≠k`, where the args `g(a)`, `g(b)` are equal because `a=b`.
  A new `CongBridge` builds an `axeyum_egraph::EGraph` over the rewritten assertions + the
  abstraction defining equations `v_i=f(args_i)` (all nodes added before any merge, so
  congruence edges survive); when the asserted-edge BFS declines, `emit_arg_units` walks
  `EGraph::explain_steps` and converts `Input`→assume / `Congruence`→`eq_congruent`
  (recursing on args) threaded through `eq_transitive` — exactly the `prove_qf_uf_unsat_alethe`
  pattern. **Strictly additive**: the identical / direct-assert / transitive-BFS paths are
  byte-unchanged, and the whole emitter is self-validated by `check_alethe` (a bad fallback
  ⇒ `None`, never a wrong proof). Carcara accepts the nested-congruence proof
  (`ufbv_nested_congruence_is_accepted_by_carcara`; the EUF `eq_symmetric`+resolution flip
  was swapped for the `symm` rule which both `check_alethe` and Carcara accept). Done via a
  focused sub-agent; independently re-validated (clippy clean, qfufbv_proof 7, carcara 54,
  full solver suite 920). **Lean loop now CLOSED for the congruence fragment** (follow-on):
  `reconstruct.rs` gained `symm`-rule reconstruction (`reconstruct_symm`, mirroring
  `reconstruct_eq_symmetric`'s kernel-gated `Eq.rec` transport), so
  `end_to_end_qf_ufbv_congruence_derived_to_false` reconstructs `f(g(a))=k ∧ a=b ∧ f(g(b))≠k`
  to a kernel-checked Lean `False` — the congruence fragment is now validated at all three
  levels. **Remaining follow-up:** the array-elim index fragment
  (`term_to_alethe` renders only symbols/bv-consts) would need application-valued indices to
  benefit, left untouched to protect the validated array cert.

- **2026-06-19** — **Datatype evidence routing fixed + datatype zero-trust cert wired.**
  `evidence_route` (the `produce_evidence` classifier) ignored datatype sorts/ops, so a
  datatype query whose top-level terms are all Bool/BitVec (e.g. `select_0(mk(a,b))=#b00
  ∧ a≠#b00`) misrouted to `EvidenceRoute::QfBv` → `produce_qf_bv_evidence` → raw `DtSelect`
  to the BV backend → `Unsupported` error. Fixed: detect `Sort::Datatype` +
  `DtConstruct`/`DtSelect`/`DtTest` in `evidence_route` so datatype queries route through
  `solve` (which has the datatype dispatch). New `tests/datatype_solve_path.rs` (UNSAT via
  solve / via produce_evidence / SAT via solve). **With routing fixed, the datatype
  read-over-construct cert (`prove_qf_dt_unsat_alethe_via_simplification`) is now also wired
  into `zero_trust_alethe_certificate`** — so QF_DT unsat carries a zero-trust-hole Alethe
  proof too (projection folded by `eq_transitive`/ι-reduction). Found while wiring the
  evidence certs; fixed via a focused sub-agent. Full solver suite (917 tests) + clippy green.

- **2026-06-19** — **P3.5: zero-trust-hole Alethe certs WIRED into the evidence path.**
  `produce_evidence`'s `unsat` branch previously tried only the array
  read-over-write-same direct cert, then fell back to a *trusted* DRAT reduction
  certificate (recording `TrustId::Ackermann` / `ArrayElim` as trust holes). It now
  also tries the Ackermann (`prove_qf_ufbv_unsat_alethe`) and array-elimination
  (`prove_qf_abv_unsat_alethe_via_elimination`) certs via a new
  `zero_trust_alethe_certificate` helper — so a QF_UFBV / QF_ABV `unsat` in the
  covered fragment now carries a `check_alethe`-validated Alethe proof that *derives*
  the functional/read-consistency reduction by `eq_congruent` (`trusted_steps` empty —
  **no reduction trust hole**), instead of the trusted DRAT. The certs were previously
  only test-exercised; they are now actually USED on the evidence path, retiring the
  Ackermann/ArrayElim trust holes **in practice** for the covered fragment. Each emitter
  self-validates and returns `None` cheaply outside its fragment, so trying them in
  order is sound and changes nothing for other fragments. New test
  (`qf_ufbv_unsat_carries_a_zero_trust_alethe_certificate`: `UnsatAletheProof` evidence,
  zero `trusted_steps`, self-`check`s). (Ledger stays "trust hole" — coverage is the
  derivable-equality fragment, not universal; ROW-distinct / non-derivable equalities
  still fall to trusted DRAT.)

- **2026-06-19** — **P3.5: array-elimination (read-consistency) Alethe certificate
  widened to transitive index-equalities.** Same generalization as the Ackermann cert,
  applied to `prove_qf_abv_unsat_alethe_via_elimination`: a read-consistency constraint
  `i=j ⇒ select(a,i)=select(a,j)` is now discharged when the index equality `i=j` holds
  by **transitive closure** of asserted equalities (`i=k ∧ k=j`), via an `eq_transitive`
  chain over the `!sel_a` unary select function — previously only direct index equalities
  were certified. Strictly additive (direct/identical indices unchanged), `check_alethe`
  self-validated, and externally **Carcara-validated**
  (`abv_select_consistency_transitive_is_accepted_by_carcara`). Index-unit derivation
  factored into `emit_index_equality_unit`. Widens the array-elim trust-hole certificate
  (Track 3, ADR-0010). New self-check + Carcara tests; solver clippy + qfabv_elim_proof +
  carcara crosscheck green (53 carcara tests). **Lean loop closed for the widened
  fragment:** the transitive Ackermann cert also reconstructs to a kernel-checked Lean
  `False` (`end_to_end_qf_ufbv_transitive_congruence_to_false`), so the transitive certs
  validate at all three levels (in-tree `check_alethe`, external Carcara, Lean kernel).
  Full solver suite green (77 results, 0 failures).

- **2026-06-19** — **P3.5: Ackermann Alethe certificate widened to transitive
  argument-equalities.** `prove_qf_ufbv_unsat_alethe` previously discharged a
  functional-consistency constraint's antecedent only when each argument pair was
  *directly* asserted equal (or identical). It now also discharges pairs equal by
  **transitive closure** of the asserted equalities (`a=b ∧ b=c ⊢ a=c`): a BFS over
  the asserted-equality graph finds the chain, each edge (an original assertion) is
  `assume`d, and one `eq_transitive` step + resolution derives the argument equality
  feeding `eq_congruent` — so `f(a)=k ∧ a=b ∧ b=c ∧ f(c)≠k` now emits a checkable
  certificate (previously declined → `None`). Strictly additive: directly-asserted
  and identical pairs keep their exact prior steps (no change to the existing
  Carcara-validated certs), and the new path is gated by `check_alethe`
  self-validation (a non-derivable chain ⇒ `None`, never a wrong proof). 2 new
  self-check tests (unary chain; binary with one direct + one chained arg) + a new
  **Carcara crosscheck** (`ufbv_transitive_congruence_is_accepted_by_carcara`) so the
  transitive fragment is externally validated. Widens the Ackermann trust-hole
  certificate coverage (Track 3, ADR-0013). Full solver clippy + qfufbv_proof +
  carcara crosscheck green.

- **2026-06-19** — **NRA OOM gap CLOSED: deterministic cross-product admission bound
  (graceful `unknown`, never OOM).** `check_with_nra` now refuses any query with > 2
  distinct-operand cross-products (`a·b`, `a ≠ b`) up front — *before* building lemmas or
  solving — returning `Unknown(ResourceLimit)`. Root cause (measured under the new 64 GiB
  `ulimit` cap): the 3-variable case `a²+b²+c² ⋈ ab+bc+ca` (three cross-products) blows up
  the DPLL(T)/exact-rational LRA relaxation *inside a single solve call* — so the per-round
  and per-node wall-clock checks never get a turn — and **bounds do not tame it** (the
  bounded variant `SIGABRT`ed at the memory cap; McCormick just adds more lemmas). The bound
  counts **only** cross-products: squares are cheap (no monotonicity/SOS lemmas) so
  square-only multi-variable instances (`x²+y²+z²+1=0`) and the 2-var SOS frontier
  (`a²+b²<2ab`, one cross) stay decidable — verified, no regression. 3 new tests (unbounded
  + bounded both degrade; square-only not gated); all 27 NRA + 5 Spivak tests green. Updates
  the standing `Graceful unknown` rule; multi-variable SOS / Cauchy–Schwarz is now explicitly
  gated on a future nlsat/CAD (or exact-rational work-budget) engine. Also landed
  `scripts/mem-run.sh` + `just test-guarded` (64 GiB `ulimit -v` wrapper) so build/test/bench
  can never OOM the host, and fixed a pre-existing `clippy::many_single_char_names` lint in
  the `theory_combination` test module (the P1.6 commits had left `clippy --all-targets` red).

- **2026-06-18** — **Crash-hardening sweep: never panic on arithmetic-sorted UF sat-model
  projection.** `Value::scalar_code` panics on Int/Real; all three solver callers of
  `project_model` (euf / combined / aufbv) now degrade to a sound `Unknown` for an
  arithmetic-sorted uninterpreted function instead of crashing. Found via `solve` on a
  quantified UF+LIA query (now decides UNSAT, was a panic). Upholds 'graceful unknown,
  never crash'. Full solver suite green (77 binaries).

- **2026-06-18** — **QF_UFLIA / QF_UFLRA complete (conjunctive UNSAT) via eager EUF+arith
  combination.** `check_with_uf_arithmetic` switched to eager Ackermann elimination →
  `check_auto`: all congruence constraints asserted up front, so nested `f(g(a))≠f(g(b))∧a=b`,
  `f(x+0)≠f(x)`, result-in-arithmetic `f(p)+1=f(q)∧p=q`, and the squeeze all decide UNSAT
  (the lazy CEGAR was incomplete — arithmetic solvers leave intermediate abstraction vars
  unconstrained). Also hardened the default-on preprocessing to be fully best-effort (any
  reduction/dispatch/reconstruction error → solve the original). 7 UF-arith tests; ledger +
  golden matrix updated; full solver suite green (77 binaries).

- **2026-06-18** — **P1.6: EUF + linear-arithmetic combination (QF_UFLIA / QF_UFLRA).**
  Widened `declare_fun` to admit Int/Real UF sorts; refactored the functional-consistency
  CEGAR (`check_with_function_consistency`) and added `check_with_uf_arithmetic` (solves the
  Ackermann abstraction with the arithmetic dispatcher, not bit-blasting) — the classic
  Nelson–Oppen case `f(a)≠f(b) ∧ a≤b ∧ b≤a` now decides **UNSAT** (LIA forces a=b →
  congruence forces f(a)=f(b)), in both LIA and LRA. Wired into `check_auto`. New theory
  coverage axeyum could not even *declare* before. Full solver suite green (77 binaries).

- **2026-06-18** — **P1.6 T1.6.2 th_eq bus** — `EGraph::theory_var_classes` (e-graph
  readout of classes carrying theory vars) + `interface_th_eqs` (solver-side: emit
  cross-theory interface equalities, spanning chains over classes spanning ≥2 theories).
  The bus a merge in one theory uses to propagate an equality to another. With the four
  combination primitives, P1.6's machinery (shared / propose / classify / arrangement /
  th_eq-bus) is in place; the remaining slice is the online multi-theory loop that drives it.

- **2026-06-18** — **P1.6 combination — arrangement-consistency check**
  (`combination_conflict`): one model-based-combination iteration — does a BV model's
  equal/distinct arrangement of the shared terms agree with the EUF congruence? Returns the
  first conflicting pair (model-distinct vs congruence-equal, or model-equal vs
  congruence-refuted), else `None`. Composes `shared_terms`+`classify` into the core
  combination step. Four P1.6 combination primitives now exist (shared / propose / classify
  / arrangement-check); the remaining slice is the online loop that blocks a conflicting
  arrangement and re-solves (P1.5 T1.5.1–4 online drive).

- **2026-06-18** — **P1.6 combination — interface-equality classification against
  congruence** (`classify_interface_equalities` + `InterfaceStatus`). Decides each
  proposed equality Entailed/Refuted/Undetermined via the e-graph congruence closure of
  the EUF assertions — Entailed covers congruence-derived equalities (`f(a)=f(b)` from
  `a=b`), Refuted uses asserted disequalities. With `shared_terms` (T1.6.1) +
  `propose_interface_equalities`, the model-based-combination core (shared → propose from
  a BV model → confirm/refute against EUF) is now in place; remaining is the online
  CDCL(T) drive that loops propose↔split↔re-solve (P1.5 T1.5.1–4).

- **2026-06-18** — **P1.6 combination — model-based interface-equality proposal**
  (`propose_interface_equalities`). Given a one-theory model, proposes equalities between
  equal-valued shared terms (spanning chain per value group, deterministic) — the
  *propose* half of Z3-style model-based combination, building on T1.6.1's `shared_terms`.
  Next: assert/confirm-or-split the proposed equalities against the congruence closure
  (T1.6.3), which needs the online CDCL(T) drive (P1.5 T1.5.1–4 — a substantial slice).

- **2026-06-18** — **P1.6 theory combination — T1.6.1 shared-term discovery**
  (`theory_combination::shared_terms`, the plan's named next task). Identifies the
  bit-vector-sorted Nelson–Oppen interface terms between the EUF and BV theories
  (arg/result of `Op::Apply` ∩ operand/result of an interpreted BV op) — pure,
  deterministic structural discovery, the foundation for T1.6.2 (`th_eq` bus) and T1.6.3
  (interface-equality case-splitting). 4 tests.

- **2026-06-18** — **Foundational QF_BV refutation checked by the real Lean kernel**
  (destination-3). Added a gated real-lean cross-check for the bit-blasting → resolution
  path (`a≤b ∧ b<a`); `#print axioms` shows no `sorryAx`. Independent-kernel validation now
  spans **7 fragments**: QF_BV / QF_UFBV / QF_ABV / datatypes / LRA / ∀ / ∃ — the core
  bit-level path plus the theory fragments.

- **2026-06-18** — **Datatype refutations checked by the real Lean kernel** (destination-3).
  Added a gated real-lean cross-check for algebraic datatypes (read-over-construct unsat,
  via datatype simplification → QF_UFBV); `#print axioms` shows no `sorryAx`. Real-kernel
  validation now spans **6 fragments**: QF_UFBV / LRA / ∀ / ∃ / QF_ABV / datatypes.

- **2026-06-18** — **QF_ABV refutations now checked by the real Lean kernel** (destination-3).
  Added a gated real-lean cross-check for arrays (read-consistency unsat, reconstructed via
  array elimination → QF_UFBV); `#print axioms` shows no `sorryAx`. The independent-kernel
  validation now spans QF_UFBV / LRA / ∀ / ∃ / **QF_ABV**. (Pure-QF_BV-value and direct ROW
  reconstruction to Lean remain frontier gaps — the Lean emitter is narrower than the Alethe one.)

- **2026-06-18** — **Bounded strings: `str.to_code` / `str.from_code`** (SMT-LIB 2.6
  char-code ops) added to the byte-string theory. `to_code` → (is_single, byte-as-BV8);
  `from_code` → the length-1 string for a byte. Bounded BV formulas; tested incl.
  round-trip. Narrows the string-theory gap vs z3 within the bounded fragment.

- **2026-06-18** — **FP `to_real` confirmed format-general** (F16/BF16/TF32/FP8 E5M2,
  not just F32/F64): corrected the stale doc and added small-format coverage (incl.
  subnormals and ∞/NaN→None). With `from_real` (all modes) and the int/bv→fp conversions,
  the FP↔Real/Int conversion surface is complete across the supported IEEE formats.

- **2026-06-18** — **FP `from_real`: all five rounding modes** (RNE/RNA/RTZ/RTP/RTN).
  `round_rational_rne` gained per-mode rounding (`round_up_decision`) and overflow
  (`overflow_bits`, ±inf vs max-finite, direction-aware). Validated against
  `rustc_apfloat`'s correctly-rounded division for every mode and sign — an independent
  IEEE oracle. `to_fp` from real is now complete for all SMT-LIB rounding modes.

- **2026-06-18** — **FP `from_real` now rounds non-dyadic rationals** (exact-integer RNE,
  `round_rational_rne`): 1/3, 1/10, 22/7 → correctly-rounded F32/F64, no f64
  double-rounding. `round_rational_to_format` kept dyadic-only (smtlib parser depends on
  its contract); `from_real` falls back to the integer path. Cross-checked vs the f64
  path on dyadic (incl. F16 subnormal/tie) and vs native casts on non-dyadic. The `to_fp`
  source set (int→fp, bv→fp, real→fp) is complete for NearestEven.

- **2026-06-18** — **FP `from_real`** (`axeyum_fp::from_real`): `to_fp` from a rational
  constant. Dyadic rationals (power-of-two denominator, <2^53 numerator) round soundly via
  the validated `round_rational_to_format` (exact f64 → `round_to_format`); non-dyadic
  (1/3, 1/10) return `Ok(None)` (decline — exact rational rounding needs >i128, a planned
  follow-up). Completes the `to_fp` source set for the dyadic case (int→fp, bv→fp, real→fp).

- **2026-06-18** — **Optimization/constraint API feature-complete + full Solver façade.**
  Session run (all green, committed): FP integer→float (`from_ubv`/`from_sbv`); all 3 z3
  OMT modes (box, lexicographic, Pareto) across **LIA + BV**; model-returning MaxSAT;
  strict PB (`pb_lt`/`pb_gt`); cardinality `between`/`at_most_one`/`exactly_one`; BV
  `repeat`; and `Solver` façade methods for the whole optimization/MaxSAT/unsat-core
  surface. `preprocess` flipped default-on (guarded, validated). **Next frontiers** (all
  larger / coordination-gated): deeper word-level reduction (other agent's `axeyum-rewrite`
  lane); a kissat-class SAT core (long game, the search-bound Timeout band); unbounded
  strings / uninterpreted sorts / full MBQI / NRA-CAD; and `to_fp`-from-real (needs exact
  rational rounding — f64 bridge is unsound for sub-f64 formats).

- **2026-06-18** — **Solver façade `unsat_core`**: `Solver::unsat_core(arena)` returns a
  deletion-minimized unsat core (assertion indices) — the z3 get-unsat-core API on the
  high-level façade. Test verifies the irrelevant assertion is excluded.

- **2026-06-18** — **Word-level preprocessing flipped default-ON** (commit `6cb2f1b`,
  ADR-0034/0037 staged step). `SolverConfig::default().preprocess == true`; the default
  `solve()`/`check_auto` path runs the model-sound reduction pipeline. Guarded so it is
  never a correctness dependency: skipped on quantified queries (QF transform), and
  best-effort (any reduction-pass error → solve the ORIGINAL). Validated by a
  full-workspace behaviour check (103 test binaries green) — the gate ADR-0037 required.
  Caught + fixed a real regression in the check: preprocessing errored on
  uninterpreted-function applications (canonicalize fold) → the best-effort fallback.

- **2026-06-18** — **BV `repeat`** (`bv_repeat`, z3 `(_ repeat n)`): derived concat fold,
  no new IR Op/lowering. Completes the common z3 BV op set (nand/nor/xnor/comp/rotate
  already present). Test incl. exhaustive BV4 symbolic duplication.

- **2026-06-18** — **BV Pareto** (`optimize_bv_pareto`): completes the OMT trio across
  both theories — box, lexicographic, and Pareto now all span LIA + BV. Test: BV8 front
  {(1,3),(2,2),(3,1)}. 24 OMT tests.

- **2026-06-18** — **Cardinality convenience**: `between(lo,hi)`, `at_most_one`,
  `exactly_one` (one-hot) — compose the existing at-most/at-least/exactly forms. 2 tests.

- **2026-06-18** — **Solver façade OMT/MaxSAT methods**: `Solver::{maximize_lia,
  minimize_lia, optimize_lexicographic, optimize_pareto, max_satisfiable}` optimize over
  the active assertions — the optimization work is now reachable via the high-level API.

- **2026-06-18** — **PB strict comparisons** (`pb_lt`/`pb_gt`, pseudo-Boolean `<`/`>`):
  compose the non-strict forms (≤k-1 / ≥k+1, with sound k-edge handling). 2 tests.

- **2026-06-18** — **MaxSAT model-returning variant** (`max_satisfiable_model` /
  `_weighted_model`, commit `daced10`). Returns `MaxSatOutcome::Optimal { weight, model,
  satisfied }` — the witnessing assignment + which soft constraints hold, the actual
  solution z3's MaxSAT yields (previously only the optimal weight). Sound: pins the
  weight-sum at the optimum, witnesses a model via `check_auto`, re-evaluates each soft
  constraint; surprise unsat/unknown folds to `Unknown`. Test cross-checks `satisfied`
  flags against the model. Working-agreement loop increment 7.
- **2026-06-18** — **P4.3 OMT: Pareto + box modes complete the z3 OMT trio.**
  `optimize_lia_pareto` (commit `75205b7`) enumerates the Pareto front by guided
  improvement, each point *verified* Pareto-optimal (confirmed-unsat domination query),
  with deterministic point (256) / push (64) caps → `Truncated`/`Unknown` rather than
  unbounded enumeration. With `optimize_lia_box` (`ecabf53`) and the lexicographic modes
  below, **axeyum now has all three z3 OMT modes (box, lexicographic, pareto)**. 22 OMT
  tests incl. the {(1,3),(2,2),(3,1)} front. Working-agreement loop increments 4–6.
- **2026-06-18** — **P4.3 OMT breadth: lexicographic multi-objective optimization**
  (`optimize_lia_lexicographic`, commit `b852ddf`). Optimizes integer-linear objectives
  in order, pinning each at its optimum before the next (z3's default lexicographic
  combination); sound + terminating (bounded composition of the checked
  `maximize/minimize_lia`); `LexOutcome::Stopped` at the first non-finite objective.
  4 API-level tests (order-dependence, mixed max/min, stop-on-unbounded). Reachable via
  the solver API. **Extended to BV** (`optimize_bv_lexicographic`, signed/unsigned, commit
  `f57e5f3`, +2 tests) — lexicographic OMT now spans LIA and BV. Second/third breadth
  increments of the new working-agreement loop.
- **2026-06-18** — **Plan revised from measured learnings + breadth pivot.** Per a
  strategy check-in: revised PLAN.md (front #1 reframed to word-level *reduction* as
  the destination-2 lever with the EncodingBudget/search-bound/large-CNF partition;
  both-in-parallel on the SAT core; new standing rule *graceful `unknown`, never
  OOM/crash*; multi-agent coordination rule — `axeyum-rewrite`/`axeyum-smtlib` are the
  other agent's reduction lane). Active focus set to **breadth toward feature-parity**.
  First breadth increment: **FP integer→float conversion** (`from_ubv`/`from_sbv`,
  commit `f7b43db`) — see P2.8 row; differential-tested vs native `as f32`/`as f64`.
- **2026-06-18** — **Known robustness gap found (NRA can OOM on unbounded multi-product
  nonlinear queries).** Probing whether the SOS lemmas generalize to 3 variables
  (`a²+b²+c² ≥ ab+bc+ca`) revealed that `check_with_nra` on an **unbounded** 3-variable
  nonlinear query **OOMs** rather than degrading to `Unknown`. Diagnosis: unbounded vars
  can't be box-split (`widest_split` → `None`), so it never branches — the blowup is in
  the **root refinement loop**, where the ~6-product case generates a much larger boolean
  product-lemma set and/or escalating exact-rational witnesses that the existing
  wall-clock deadline + `too_large_to_refine` (2³¹) guards don't bound *as memory*. The
  2-variable SOS win is unaffected (committed, green). A correct fix needs a deterministic
  memory/work bound that does **not** regress currently-working *bounded* multi-product
  cases (those terminate via McCormick) — scoped as future work, to be developed against a
  controlled small repro (NOT the 123 GB-OOMing 3-var case). Multi-variable SOS is gated on
  this. **Do not run unbounded ≥3-variable nonlinear NRA queries without a memory bound.**
- **2026-06-18** — **P2.5 NRA breadth: sum-of-squares lemmas prove AM–GM₂**
  (commit `8a7d31f`). `nra::sos_lemmas` adds `(a±b)² ≥ 0` (= `r_aa+r_bb∓2·r_ab ≥ 0`)
  over the abstracted products of each variable pair — sound (true in every real
  model), restoring the cross-product correlation the independent product abstraction
  drops. **`a²+b² ≥ 2ab` / AM–GM₂ is now proved** (`a²+b²<2ab` → `Unsat`); the Spivak
  SOS-frontier test is promoted from prompt-`Unknown` to proved. A negative test pins
  soundness (`a²+b²=2ab` stays satisfiable, `x=y`). Closes a documented NRA frontier
  gap; higher-degree/multi-var SOS (Bernoulli, general Cauchy–Schwarz) + nlsat/CAD
  remain. Built on the incremental-eval primitive landed earlier this session.
- **2026-06-18** — **P1.8 tactics: or-else portfolio combinator** (`solve_with_portfolio`
  + `recommended_portfolio`, commit `cda1f55`). Runs strategies in order, first to
  decide wins, falls through `Unknown`/errors (Z3's `or-else`; sound — a later strategy
  runs only when earlier ones returned `Unknown`). `recommended_portfolio` routes by
  query shape (heavy-arith → `[LazyBvAbstraction, EagerPureRust]`; structural → `[Auto]`),
  composing the destination-2 levers with fallback power over a single `Auto` pick.
  Pure-Rust, collision-free, 3 tests. Full workspace suite green (103 test binaries, 0
  failures).
- **2026-06-18** — **Destination-2 lever found & measured: word-level preprocessing
  doubles the eager decided count (2 → 4 of 113), after fixing the unbounded
  preprocessor.** Acting on the lazy-bv null result below, profiled the preprocessing
  passes on the 17.6 MB / 340 k-node giant: `solve_eqs` was the sole hog (**>150 s**
  there; every other pass <0.5 s). Added a **deterministic node-fuel budget**
  (`axeyum_rewrite::solve_eqs_bounded` / `DEFAULT_SOLVE_EQS_FUEL`, commit `96e55b6`) —
  charges per-round rebuild work (shared-memo node count, never wall-clock), bails to
  a **sound partial reduction** (un-eliminated equalities stay assertions; trail
  reconstructs). Giant now clears the whole pipeline in ~1.5 s. Wired into
  `check_with_preprocessing` + the bench. **Fair `--preprocess` measurement** (sat-bv,
  same budgets as the eager baselines, Z3 oracle, DISAGREE=0, 0 replay failures
  throughout): **3 s → 4 sat vs eager 2; 20 s → 7 sat vs eager 3** — more than doubling
  eager at both tiers, the gain *growing* with budget. The newly-decided instances drop
  out of `EncodingBudget` (13 → 11 at 3 s), i.e. preprocessing shrinks them below the
  bit-blast-size ceiling. First (and decisive) destination-2 gain on this corpus from
  *reduction* (the "not-building-the-mountain" lever), not abstraction — ratified in
  **ADR-0037** (reduction is the destination-2 priority; batsat stays default; custom
  cores specialized). Baselines
  `bench-results/baselines/qf-bv-p4dfa-fair-sat-bv-preprocess-vs-z3-{3s,20s}-*.json`,
  `just bench-public-qfbv-preprocess-fair-{3s,20s}`. Probe:
  `axeyum-bench/examples/preprocess_timing.rs`. **Wired into the product:** the full
  model-sound pipeline now runs on the default `solve()`/`check_auto` path when
  `preprocess` is set (`check_auto_preprocessed`, reconstructs + replays), and
  **`Strategy::Auto` composes both levers** — lazy-bv for arithmetic-heavy queries,
  eager-with-preprocessing for structural ones. Full solver suite green.
  **Timeout-boundedness measured (kissat probe):** the 99 Timeouts split by CNF size —
  **~9 (≤300k clauses) are SAT-search-bound** (kissat 4.0.4 cracks them 2–18 s where
  batsat times out @20s; `mobiledevice_paired` 2 s vs >20 s), the **~90 larger
  (≥~650k) defeat even kissat** (reduction-bound). So **both levers are data-justified,
  partitioned by size** (ADR-0037 trigger partially fired): a competitive default SAT
  core for the small-CNF Timeouts, word-level reduction for the large-CNF bulk +
  6 EncodingBudget. **But the core bar is kissat-class:** the in-tree `xor_cdcl` core
  *also* fails `string1x8.4` (>120 s vs kissat 8.3 s), so converting the search-bound
  band needs a kissat-class solver (major P1.3; out of scope as a pure-Rust *default*,
  kissat is only a benchmark oracle). **Practical upshot: reduction is the higher-ROI
  near-term lever even for the search-bound band** (shrinking the CNF brings it within
  reach of the core we ship). Probes: `axeyum-bench/examples/{dump_dimacs,xor_cdcl_probe}.rs`.
  **Next:** (a) deeper reduction — `axeyum-rewrite` P1.2, the **other agent's active
  area; do not edit `canonical.rs`**; (b) flip `preprocess` default-on after a
  full-suite check; (c) long-term, close the SAT-core gap to kissat-class. Track
  **Timeout→decided** as the destination-2 pulse.
- **2026-06-18** — **Destination-2 fair re-measurement: lazy-bv vs Z3 on the public
  p4dfa 113 at the standing budgets — confirmed a no-op on this corpus.** Ran the
  built-but-fair-unmeasured `LazyBvBackend` head-to-head vs Z3 4.13.3 on the
  committed 113-file `20221214-p4dfa` public QF_BV slice at **identical node/CNF
  budgets to the eager `qf-bv-p4dfa-fair` baselines**, both tiers, `--jobs 2`:
  - **3 s** (node 200k, cnf 2M/5M): **lazy 3 sat / 110 unknown, DISAGREE=0, 0 replay
    failures** (eager 2/111). **20 s** (node 300k, cnf 3M/8M): **lazy 4 sat / 109
    unknown, DISAGREE=0, 0 replay failures** (eager 3/110). Baselines committed:
    `bench-results/baselines/qf-bv-p4dfa-fair-lazy-bv-vs-z3-{3s-n200k-cnf5M,20s-n300k-cnf8M}.json`;
    reproduce via `just bench-public-qfbv-lazy-fair-{3s,20s}`.
  - **Honest finding:** `lazy_ops_total == 0` on **all 113** files (`grep` census:
    **0/113** contain any of `bvmul/bvudiv/bvsdiv/bvurem/bvsrem/bvsmod`); **0
    instances refined any op**; every decided instance was plain bit-blast. The
    consistent +1 over eager is a solve-path margin (the extra instances have
    `ops_total=0`), **not** a CEGAR win. lazy arithmetic-CEGAR is **structurally
    inert** on this arithmetic-free DFA/protocol slice. The 109–110 unknowns are
    87–98 Timeout (huge CNFs batsat can't crack) + 10–13 EncodingBudget + 1–10
    NodeBudget — the **eager-CNF-size wall**, not the multiplier wall.
  - **The number says:** the destination-2 lever for this corpus is **word-level
    reduction before blasting** (P1.2), which is blocked on the **unbounded
    preprocessor** (`solve_eqs`/canonicalize blow-up on the 17.6 MB / 215k-`ite`
    giants). NEXT: give the preprocessing passes a deterministic work budget so
    `--preprocess` bails instead of hanging → then measure `--preprocess` on the 113
    (the second committed measurement) → then the batsat-vs-custom-core ADR. See
    [lazy-bitblasting-p21-findings.md](docs/research/05-algorithms/lazy-bitblasting-p21-findings.md).
- **2026-06-18** — **P3.7 destination-3 milestone: reconstructed refutations checked
  by a REAL Lean 4 kernel.** Installed a real Lean toolchain (elan + `leanprover/lean4`
  stable 4.31; the gold-standard checker, analogue of the Z3 oracle — a CI/cross-check
  tool, not a build dependency) and made the in-tree reconstruction externally
  verifiable end-to-end:
  - **`Kernel::render_lean_module`** (`axeyum-lean-kernel::lean_pp`): renders a
    self-contained `prelude`-mode Lean 4 module — every environment declaration
    reachable from goal+proof (transitive const-closure + topological sort;
    inductive/ctor/recursor emitted as `axiom`s carrying their kernel types), then
    `theorem axeyum_refutation : False := <proof>` + `#print axioms`. Numeric name
    components sanitized (`atom.0`→`atom._0`); `Succ` chains collapsed to numerals.
  - **`prove_unsat_to_lean_module`** (solver + façade): like `prove_unsat_to_lean`
    but also returns the Lean source. Same soundness gate (kernel-checks to `False`).
  - **Gated cross-check** (`tests/lean_crosscheck.rs`, skips without `lean`): the
    QF_UFBV (congruence), LRA (Farkas), ∀ (instantiation), and ∃ (skolemization)
    refutations each **type-check in real Lean 4** with `#print axioms` showing only
    the axeyum-declared logical/carrier/uninterpreted/`em`/hypothesis axioms — **no
    `sorryAx`**. The real Lean kernel independently corroborates the in-tree check.
    Honest boundary: inductive recursors are rendered as axioms (their generation is
    trusted, same as in-tree); a later slice can render real `inductive` commands to
    let Lean *derive* the recursors.
- **2026-06-17** — **Track-1 complement sweep (four lanes, alongside the proof/Lean
  agent).** Non-colliding Track-1 increments, each its own sound + tested + pedantic-
  clippy-clean commit:
  - **Differential soundness net** (`tests/differential_qfbv_backends.rs`): seeded
    random QF_BV cross-check across eager `SatBvBackend`, the new `LazyBvBackend`,
    and (feature `z3`) the oracle — DISAGREE=0 + every-`sat`-replays, 200 always-on +
    1500 ignored, 3-way clean. Guards both agents' solver churn.
  - **P1.2 / T1.2.4 `elim_unconstrained`** (`axeyum-rewrite`): unconstrained single-
    use invertible-op elimination, trail-reconstructed, wired into the opt-in
    `check_with_preprocessing`.
  - **P1.7 PBLS** (`pbls.rs`): word-level WalkSAT portfolio engine, one-sided sound
    (`Sat`/`Unknown`, never `Unsat`), deterministic.
  - **P1.3 SAT-core modernization** (`proof_sat.rs`): VSIDS + phase saving + Luby
    restarts on the proof-producing CDCL core (DRAT-checked ⇒ sound regardless).
  - **Round 2** (one more increment per lane): `elim_unconstrained` now peels
    `bvmul` by an odd constant (2-adic inverse); the CDCL core gained local
    learned-clause minimization (self-subsumption); PBLS switched to incremental
    scoring (re-eval only the moved variable's incidence set); and the soundness
    net's larger sweep now includes `PblsBackend` (one-sided `Sat` verdicts
    replayed + cross-checked at scale). All DRAT/replay-guarded, clippy clean.
- **2026-06-17** — **Fair public-QF_BV measurement + graceful oversized-encoding
  refusal (the "1/113" gap, diagnosed)**. The headline "sat-bv decides ~1/113 on
  public QF_BV" was an artifact of `--node-budget 1000` (refusing 112/113 at the
  DAG gate, all 1.3k–340k nodes), itself forced by a robustness bug.
  - **Fix (sat_bv_backend, P1.2 robustness):** a pre-lowering bit-blast-size
    *estimate* (per-op cost in result width: mul ~`w²`, div/rem ~`4w²`, shifts
    ~`w·log w`, else linear; `~3×` for Tseitin) now refuses oversized queries as
    `Unknown(EncodingBudget)` **before `lower_terms` allocates** — so a wide
    multiply degrades cleanly instead of OOMing. Absolute 64M-clause ceiling for
    the no-budget case. Regression test `oversized_multiply_is_refused_gracefully_not_oom`.
  - **Fetched the real 113-file public slice** (SMT-LIB 2024 QF_BV, Zenodo 11061097,
    `20221214-p4dfa-XiaoqiChen`) and ran the fair head-to-head vs Z3 4.13.3.
  - **Result (node 200k, 5M-clause cap, 3s):** **2 sat decided, 0 disagreements,
    0 replay failures, 111 unknown** = 88 **Timeout** (admitted + bit-blasted to
    140k–4.6M-clause CNFs, BatSat can't solve in 3s), 13 EncodingBudget, 10
    NodeBudget. **101/113 lowered without OOM** (RSS ~1.5GB — fix works).
  - **Ceiling (node 300k, 8M-clause cap, 20s):** **3 sat decided**, 110 unknown
    (99 Timeout, 10 EncodingBudget, 1 NodeBudget). 6.7× more time + bigger budgets
    moved decided only 2→3.
  - **Diagnosis:** the gap is **architectural, not robustness (fixed) and not a
    timeout/budget knob.** Eager bit-blasting these word-level instances yields
    ~million-clause CNFs our SAT path can't crack in seconds, while Z3 reasons at
    the word level (~1s each). The honest fair number is **2–3 / 113**, with the
    bottleneck precisely located → Track 1: word-level preprocessing (P1.2), lazy/
    word-level bit-blasting (P2.1), SAT-core modernization (P1.3). Baselines:
    `bench-results/baselines/qf-bv-p4dfa-fair-sat-bv-vs-z3-{3s-n200k-cnf5M,20s-n300k-cnf8M}.json`.
- **2026-06-17** — **Curriculum backlog Tier A–D built (19 items): NT/poly/algebra/LA
  families + 2 sound NRA engine fixes**. Worked the curriculum
  [BACKLOG.md](docs/curriculum/BACKLOG.md) end to end; drawn from Stein/Shoup/VMLS
  (see [foundational-books/source-tocs.md](docs/curriculum/foundational-books/source-tocs.md)).
  - **Tier A (decidable, #1–8):** `Family::NumberTheory` += CRT-witness, quadratic
    residue (SAT) / non-residue (UNSAT), sum-of-two-squares (SAT + `n≡3 mod 4`
    UNSAT), Pythagorean triple; `Family::Polynomial` += factor-theorem identity;
    `Family::Algebra` += 𝔽ₚ-all-invertible (UNSAT) / composite-modulus
    non-invertible (SAT, via a `∀b` finite-domain quantifier). Solver/LRA tests:
    **linear algebra over ℚ** (`Ax=b` solvability + Farkas-refuted inconsistency,
    `tests/linear_algebra_rational.rs`); **rationals node** (density/antisymmetry/
    transitivity, Farkas-certified, `tests/rationals.rs`); **proofs node via
    pigeonhole** (`PHP(5,4)` UNSAT with a re-checked certificate + permutation SAT,
    `tests/pigeonhole_proof.rs`).
  - **Tier B (#9–13):** `Family::Predicate` += Fermat's little theorem at fixed
    `p∈{3,5}` (`∀a`); `Family::Polynomial` += division-with-remainder identity;
    `Family::NumberTheory` += RSA round-trip (`(mᵉ)ᵈ≡m mod 33`, modular-exp with
    per-step reduction); `Family::LinearAlgebra` += 3×3 `det(AB)=detA·detB` over 𝔽₂;
    #13 ("watch a formula become CNF→SAT") realized by the existing
    `scenario_pipeline_report`/`curriculum_demo`/`BvLayerStats` observability.
  - **Tier C — NRA/prove engine (#14–16), measured & sound:** **#14** the
    `prove`/`produce_evidence` front door now **dispatches nonlinear real goals to
    NRA** (`produce_nra_evidence`) instead of hard-erroring `Unsupported`;
    soundness-probed (NRA does not claim `x²<0` Sat). **#15** NRA now honors a
    **wall-clock deadline** threaded through `branch_and_bound` + the refinement
    loop (the `a²+b²≥2ab` case returns `Unknown` in ~5s instead of hanging 60s+;
    the Spivak SOS-frontier test is now active, not `#[ignore]`d). **#16** a real
    SOS/positivstellensatz that *proves* the SOS inequalities is genuine P2.5/L
    work — **designed and deferred** (sketch in spivak.md), not faked.
  - **Tier D (#17–19):** decidable-geometry node — the *linear* slice (midpoint
    equidistance/betweenness, LRA Farkas, `tests/decidable_geometry.rs`; polynomial
    geometry is #16-gated); Peano-induction **reconstruction-target stubs**
    (`docs/curriculum/reconstruction-targets/`: `.smt2` + Lean, *targets not
    benchmarks*); **"fill the proof step" grader** — `check_alethe` accepts a
    complete proof and rejects one missing its closing step
    (`tests/proof_step_grading.rs`).
  - **Verified:** 57 `axeyum-scenarios` tests + new solver tests (decidable_geometry
    2, proof_step_grading 2, linear_algebra_rational 3, rationals 3, pigeonhole_proof
    3, spivak 5) all green; fmt/clippy/doc/link-check clean. (Transient: the
    concurrent CDCL(XOR) WIP in `axeyum-cnf` intermittently blocked the solver build;
    re-ran green once fixed.)
  - **References noted:** Software Foundations being translated to Lean + Verso
    (`docs/curriculum/foundational-books/proof-assistants.md`) — the Lean-horizon
    curriculum to align with.
- **2026-06-17** — **Spivak *Calculus* Ch.1 benchmark + the "decidability-ceiling"
  curriculum docs**. Engaged Spivak (and foundational texts) honestly: most of the
  book is ε-δ (Lean-horizon), but **Chapter 1 — the ordered-field axioms P1–P12 and
  the foundational inequalities — is the decidable shadow** where axeyum's LRA/NRA
  live. New (Opus-research-driven):
  - **`crates/axeyum-solver/tests/spivak_inequalities.rs`** — a certificate-bearing
    benchmark. **Order transitivity** proved via the `prove` front door (Farkas,
    re-checked); a **monotonicity inequality** (`x≥1 ∧ y≥1 ⇒ xy≥1`) proved by NRA.
    The **sum-of-squares inequalities** (`a²+b²≥2ab`, AM–GM₂, Cauchy–Schwarz) are
    the **NRA frontier** — kept `#[ignore]`d (they don't terminate promptly). 3
    active tests pass, 1 ignored.
  - **Two measured engine findings** (recorded in
    [formal-mathematics-tour.md](docs/research/08-planning/formal-mathematics-tour.md)):
    (1) `prove` has **no LRA→NRA dispatch** (rejects nonlinear real goals as
    `Unsupported`); (2) the linearization NRA (ADR-0024) **cannot prove SOS
    inequalities — even `a²+b²≥2ab`** — because it abstracts the squares to
    independent variables; sharp motivation for an SOS/positivstellensatz/CAD path
    in P2.5. (The initial assumption that NRA proves these was *wrong*; the probe
    corrected it — what a benchmark is for.)
  - **Curriculum honesty docs**: `docs/curriculum/DEPTH.md` (the map-vs-territory
    scope ceiling — `covered` ≠ textbook depth; the decidability ceiling) and
    `docs/curriculum/foundational-books/` (README + `spivak.md`: how canonical texts
    project onto the LRA/NRA/Lean-horizon split).
  - **`Family::NumberTheory` extended**: `pythagorean_triple` (`a²+b²=c²`, witness
    (3,4,5)) — number theory meets geometry, SAT-by-witness.
  - 57 scenarios tests green; Spivak suite green; clippy/doc/link-check clean in
    isolation.
- **2026-06-17** — **CDCL(XOR) foundation — path 2 of the multiplier wall, 3 sound
  slices + design record** (commits b745772, 8a3415a, 8b21359, 3099964). The
  diagnosed perf lever for the curated unknowns (var*var multiplier-equivalence with
  exponential resolution lower bounds — no path-1 rewrite cracks them) is now an
  *engine*, built in `axeyum-cnf` as three independently-tested slices:
  - **`gf2.rs`** — GF(2) linear (XOR) system solver: `Gf2System` Gaussian-eliminates
    `(⊕ of a var set) = parity` constraints (bit-packed `Vec<u64>` rows, duplicates
    cancel by parity) to RREF; `0=1` row ⇒ `Unsat`, else a satisfying assignment +
    `implied_units` (single-var rows) + `implied_equalities` (two-var rows). 16 tests,
    backbone invariant "the assignment satisfies every input constraint."
  - **`xor_extract.rs`** — sound XOR-gate extraction: `extract_xors(cnf)` recognizes a
    width-`k` gate **only** when a variable-set group is the exact `2^(k-1)`-clause
    complete one-parity encoding (rhs derived from that parity; `k≤8`). Exact ⇒ false
    positives impossible (missing/extra/dup/mixed-parity/over-cap ⇒ not recognized).
    19 tests incl. a brute-force truth-table parity check + the no-false-positive set.
  - **`xor_propagate.rs`** — preprocessing pass in the `simplify`/`eliminate_variables`
    idiom: `xor_propagate(cnf) -> { Unsat, Propagated { formula, stats } }`. A
    contradictory entailed XOR subsystem proves the formula UNSAT; the solver's implied
    units (entailed ⇒ model-preserving) are appended. Brute-forced over all `2^n`
    assignments: model-set preservation, UNSAT soundness **and its converse** (a sat
    formula is never reported unsat), no-op. `implied_equalities` substitution deferred.
  - **Slice 4 DONE & measured** (commits edf65b8, 160408c): `xor_propagate` wired into
    `sat_bv_backend`'s `inprocess` (behind `cnf_inprocessing`, off by default; sound
    Propagated branch only, 20k-clause Gaussian cap). Curated slice (`--inprocess`, 2 s):
    **33 decided, DISAGREE=0, 0 replay failures, PAR-2 0.968 vs 0.963 plain** — sound, no
    regression. **Extraction fired on 20/43 files → 12 908 XOR gates but only 1 implied
    unit** ⇒ on-corpus proof that multiplier parity forces ~no units at preprocessing.
    **Slice 5 (equality substitution) measured & deprioritized** (commit 2a6190d): the
    gates expose **351 equalities** but they concentrate on the AC-structured commute/
    distrib/bit-counting instances (commute08=101, distrib04=40), **~0 on the genuine
    multiplier unknowns** (mulhs16=1, stp_samples=0, calypto_9=1) — they'd only help
    instances the AC canonicalizer already targets. **Static-preprocessing path 2 is
    closed: neither units nor equalities crack the curated multiplier unknowns.**
    **Slice 6 (the real lever):** full CDCL(XOR) — in-search Gaussian on the CDCL trail
    (CryptoMiniSat `gaussian.cpp`), the only form that sees the nonlinear AND-gate
    partial-product structure static preprocessing can't; reuses the validated `gf2`/
    `xor_extract` foundation. Design note has the full measurement.
  - **Slice 6 primitive DONE** (commit 9b449b7): `xor_search::xor_implications(constraints,
    num_vars, assignment: &[Option<bool>]) -> { Conflict{reason}, Implied{lits+reasons} }`
    — the pure propagation primitive the in-search Gaussian calls at each CDCL node. Folds
    the partial assignment into the system and reuses `gf2.rs` (Unsat ⇒ Conflict; reduced
    `implied_units` ⇒ forced literals); reasons are a sound (non-minimal) component
    over-approximation. 18 brute-force tests (conflict/implication soundness over all
    completions, completeness on small systems, reason soundness, 3^n exhaustive
    cross-check, empty-assignment vs `Gf2System::solve`). 187 cnf tests green.
  - **Slice 6 integration validated** (commits 858a644 design, d7a8cd0 decider): the
    proof/trust crux is resolved in
    [cdcl-xor-integration-design.md](docs/research/05-algorithms/cdcl-xor-integration-design.md)
    — XOR reasoning isn't resolution, so XOR-assisted `unsat` becomes a ledgered
    **`TrustId::XorGaussian`** hole (no false DRAT), demotable via an algebraic/PAC
    certificate (path 3); `sat` is already free (model replays). First integration landed:
    `xor_dpll::solve_with_xor` — a correctness-first XOR-aware DPLL (clause-UP ⇄
    `xor_implications` fixpoint, chronological backtrack, no learning/proof yet, step-budget
    → Unknown). **400 brute-force-oracle + 300 batsat differential checks, zero
    disagreement**; every `Sat` model satisfies clauses AND XOR constraints. 196 cnf tests.
  - **Decision ratified — ADR-0035 accepted** (commit 2ea892e): CDCL(XOR) search
    acceleration with a ledgered `XorGaussian` trust hole (no false DRAT; `sat` free;
    demotable via path-3 PAC certificate). The protocol gate is cleared.
  - **Competitive CDCL(XOR) solver DONE** (commit 024596b): `xor_cdcl::solve_with_xor_cdcl`
    — conflict-driven search with clause learning + **watched-literal XOR propagation**
    (CMS `gausswatched` style: a constraint forces its last unassigned var with a minimal,
    **antecedent-valid** reason — the other vars of that constraint, all pre-assigned — which
    is what 1-UIP needs; the Gaussian `xor_implications` component-reasons are not
    antecedent-valid, so the watched scheme is used in-search). XOR antecedents enter 1-UIP as
    synthesized reason clauses. Search-only (no DRAT); isolated (models on `proof_sat`, does
    not touch it). **1,500-formula differential (brute oracle + batsat + `xor_dpll`), zero
    disagreement**; parity-chain UNSAT cases confirm learning fires. 209 cnf tests. Complete
    Gaussian-on-trail (row-provenance reasons) for the parities the watched scheme misses is
    the deferred enhancement.
  - **PATH-2 THESIS CONFIRMED + sped up — CDCL(XOR) cracks the small multiplier wall**
    (commits 577c973 harness, b863d1c note, fea810a VSIDS, aadd0da correction). Robust win on
    `mulhs08` (655 v/2716 cl): **batsat `unknown`@2s (reproducibly) → `solve_with_xor_cdcl`
    UNSAT** — a multiplier-equivalence instance plain CDCL provably cannot crack. Adding the
    P1.3 modernization (**VSIDS + phase saving + Luby restarts**) cut it **20.1 s → ~5.0 s
    (~4×)**, verdict + all ~1,500-formula soundness differentials unchanged. So the
    decomposition is confirmed AND acted on: XOR propagation = the capability, competitive
    heuristics = the speed. (Correction: `calypto_9` is *borderline* for batsat — ~1.1 s some
    runs — so not a clean separator; `mulhs08` is the solid one.) **Honest ceiling:** `mulhs16`
    / larger `stp_samples` still don't decide in minutes even with VSIDS — the next size class
    needs the **complete Gaussian-on-trail propagator** (watched-literal XOR is sound but
    incomplete) and/or more SAT-core work. 212 cnf tests; clippy/fmt clean.
  - **Wired into the product `solve()` path** (commit 6505441, ADR-0035): new
    `SolverConfig::xor_cdcl_fallback` (default OFF) — on a batsat `Unknown` over an
    XOR-structured formula (≤50k clauses), runs `solve_with_xor_cdcl`; **`unsat` = the new
    `TrustId::XorGaussian` ledgered hole** (no DRAT — XOR isn't RUP; backed by the differential
    validation), **`sat` replays** through the existing AIG/model/term path (no trust cost).
    Default-off ⇒ zero baseline change. **`mulhs08` now returns UNSAT through `SatBvBackend`
    with the flag on** — the breakthrough is reachable through the product, not just a test.
    Trust ledger now has 6 holes (added `xor-gaussian`); 8 new tests; full solver suite green.
  - **Measured negative — complete backstop must be incremental** (commit ca19a5f): calling
    the complete `xor_implications` Gaussian as a fixpoint backstop is sound (differentials
    green) but a net regression — from-scratch Gaussian per decision level makes `mulhs08`
    2.3× and `calypto_9` 19× slower and still doesn't crack `mulhs16`/`stp_samples`. Reverted.
    The next size class needs a **true incremental GF(2) matrix** (row-reduce-on-assign /
    restore-on-backtrack, CMS `gausswatched.h`/`packedmatrix.h`), not repeated rebuilds.
  - **Incremental matrix built + 2nd measured negative** (commits 83b99b2 matrix, 6c4407a
    note): `IncrementalXorMatrix` (RREF over free columns, per-assign column-substitution,
    backtrackable, **bit-for-bit oracle-validated** vs `xor_implications` over 100s of random
    systems×sequences; 14 tests) is built and committed as the foundation. But wiring it into
    `xor_cdcl` (sound — all differentials green) made `mulhs08` go 5 s → **>280 s**: it's
    called on every trail assignment and still scans all rows mentioning the var
    (`O(rows·words)`). Reverted. **Twice-confirmed sharp requirement: the propagator must be
    the watched-echelon-row scheme** (CMS `gausswatched.h` — each echelon row watches two free
    vars, so an assign touches only `O(1)` rows). The validated matrix is the foundation; the
    two-watch index over its rows is the remaining decisive optimization. `xor_cdcl` keeps the
    cheap incomplete watched-literal XOR prop until then.
  - **Watched-echelon-row index DONE + 3rd result = course correction** (commits 3ca0340
    matrix watch index, 9c49437 note): the watch index landed (**~25× fewer rows examined per
    assign**, full RREF for completeness, all oracle differentials green). Re-integrated into
    `xor_cdcl` — **sound** (every differential green; parity chains close at level 0) but
    `mulhs08` **still** regressed past 300 s. Decisive cause: **`mulhs08` has ~1 XOR gate among
    655 vars** — the matrix adds no propagation power while replacing the near-free
    watched-literal scheme with overhead. **`mulhs08` was cracked by `xor_cdcl`'s competitive
    CDCL core (VSIDS/restarts/1-UIP), NOT by XOR reasoning.** The curated unknowns are *not
    XOR-dense*, so in-search Gaussian is the wrong lever for them. Integration reverted; the
    watched-row matrix stays a **validated, unwired component** for an XOR-dense corpus (behind
    a density guard + incremental journal). **For the curated next size class the lever is
    P1.3 SAT-core modernization, not more XOR machinery.**
  - **P1.3 clause deletion DONE + localizes the next blocker** (commit 839518e): LBD-based
    learned-clause deletion added to `xor_cdcl` (the standard missing piece — clause DB grew
    unboundedly before). Sound (differentials green), `mulhs08` 5.3 s **no regression**, DB now
    memory-bounded. Honest measurement: `mulhs16`/`stp_samples` still UNKNOWN — they exhaust the
    **2M-conflict budget** (182 s/433 s), i.e. hit the conflict CEILING, not a clause-DB wall.
    So the curated next-size-class blocker is **branching/restart strength / the conflict
    ceiling**, not clause management.
  - **Next options (fresh context):** (a) more P1.3 — stronger branching/restarts (the now-
    localized curated blocker), though Kissat-class is a long road with diminishing per-step
    returns; (b) **Lean kernel inductive layer** (deepest open destination-3 slice — studied,
    soundness-careful port of nanoda's 1677-LOC inductive.rs); (c) broaden Track 2/3/4 (e.g.
    wire the integer-systems Diophantine certificate into evidence/get-proof).
  - **Next (fresh context, ADR-cleared):** wire `xor_implications` into the *production*
    proof-producing CDCL core (`proof_sat`, which has 1-UIP + watched literals) as a
    search-only theory propagator — DRAT suppressed when an XOR reason participates, the
    `unsat` carrying the new `XorGaussian` trust id (land `trust.rs` + golden ledger +
    trust-ledger.md **with** this producer, not before it). Then dispatch wiring +
    curated-multiplier measurement (`DISAGREE=0`) — the first technique that *can* reach
    `mulhs*`/`stp_samples`/`calypto`. The naive `xor_dpll` decider validates soundness; the
    production core (learned clauses) is what makes it competitive. Soundness-critical
    proof-core surgery ⇒ fresh context.
  - All verified **per-crate** (`axeyum-cnf`: 168 tests; `axeyum-solver`: full suite
    green; clippy `-D warnings` + fmt clean) — and now the **full workspace builds +
    test-compiles** (the concurrent math-tour errors resolved). std only, no new deps.
- **2026-06-17** — **Math-tour curriculum — Predicate logic + Number systems;
  coverage now 14/23 nodes**. Two more research→build cycles, oracle-free (ADR-0008):
  - **`Family::Predicate`** (`predicate`): closed quantified theorems the evaluator
    decides by finite-domain expansion — `forall_additive_identity` (∀x. x+0=x),
    `forall_exists_inverse` (∀x ∃y. x+y=0, genuine **quantifier alternation**),
    `exists_square_root` (∃x. x²=4, SAT). Exercises the finite-domain quantifier
    path. → mathtour `predicate-logic` Covered.
  - **`Family::NumberSystem`** (`number_system`): order + Peano structure —
    `signed_trichotomy`, `order_transitivity` (→ `integers`), `unsigned_non_negative`,
    `successor_injective` (→ `naturals`). Exhaustive UNSAT-of-negation over signed/
    unsigned BV. → mathtour `integers` + `naturals` Covered.
  - mathtour.rs ↔ curriculum.toml ↔ node markdown synced (invariant test enforces).
    Curriculum coverage **11 → 14 of 23 nodes** (added predicate-logic, naturals,
    integers). 57 `axeyum-scenarios` tests green; fmt/clippy/doc/link-check clean in
    isolation.
  - Remaining gaps: SAT/CNF, bit-blasting, proofs, decidable-geometry, calculus,
    sequences-limits, cardinality, complex, rationals, reals (number-systems upper
    rungs + lean-horizon analysis). NEXT high-value: ℚ/NRA (linear algebra solving,
    calculus RCF inequalities) → the corpus P2.5 lacks; proofs via a DRAT/Alethe demo.
- **2026-06-17** — **Math-tour curriculum — 3 more families (Polynomials,
  Verification, Sets) + ring/field structure; coverage now 11/23 nodes**. Continued
  the research→build cycles; all oracle-free (ADR-0008), inside the BV subset:
  - **`Family::Polynomial`** (`polynomial`): `binomial_square` ((x+y)²=x²+2xy+y²),
    `difference_of_squares`, `quadratic_root` (x²−5x+6=0, root `x=2` witness). →
    mathtour `polynomials` Covered.
  - **`Family::Verification`** (`verification`, Opus-research-driven): the
    "Hello, World" of program safety — `abs_non_negative_bug` (SAT, `INT_MIN`
    counterexample), `midpoint_overflow_bug` (SAT, the Bloch binary-search bug,
    witness `lo=hi=2^(w−2)`), `max_is_an_upper_bound`, `unsigned_overflow_idiom`,
    `saturating_add_safe` (UNSAT-of-negation theorems). → flips the **solver-capability
    concept `SoftwareVerification`** from gap to Covered (concept.rs).
  - **`Family::Sets`** (`sets`): set-algebra laws over subset bitmasks —
    `distributivity`, `absorption`, `complement_union_is_universe` (set algebra IS
    Boolean algebra). → mathtour `sets` Covered.
  - **`Family::Algebra` extended**: `zero_divisor` (SAT — ℤ/2ʷ is a ring but not an
    integral domain) and `field_failure_even` (UNSAT — even elements have no inverse,
    so ℤ/2ʷ is not a field). → mathtour `rings` + `fields` Covered.
  - **mathtour.rs ↔ curriculum.toml ↔ node markdown synced** (the
    `covered_nodes_have_a_family_realized` invariant test enforces it). Curriculum
    coverage **7 → 11 of 23 nodes** (now: propositional-logic, sets, divisibility,
    modular-arithmetic, groups, rings, fields, polynomials, counting, number-theory,
    linear-algebra).
  - **54 `axeyum-scenarios` tests green; fmt/clippy(pedantic)/doc/link-check clean in
    isolation.** Each family doubles as theory coverage (BV bitwise/arith, signed/
    unsigned comparisons, div/mul, ite) on structured, scalable, oracle-free instances.
  - NEXT (still gaps): SAT/CNF, bit-blasting, proofs, decidable-geometry, calculus,
    sequences-limits — plus ℚ/NRA variants (the corpus P2.5 lacks).
- **2026-06-17** — **Math-tour curriculum advanced — 3 more families built (Opus
  sub-agent + web research)**. Three Opus research sub-agents (pigeonhole/proof
  complexity, finite-algebra/quasigroup encodings, linear-algebra-over-finite-fields)
  informed three new self-checking families, all oracle-free (ADR-0008) and inside
  the BV subset:
  - **`Family::LinearAlgebra`** (`linear_algebra` module): `2×2` matrix identities
    over `BitVec` — `det_product_2x2` (det(AB)=detA·detB), `transpose_product_2x2`
    ((AB)ᵀ=BᵀAᵀ), `mult_associative_2x2` (over 𝔽₂), exhaustive UNSAT of the negation;
    `linear_solve_2x2` (Ax=b, solution as witness). Covers mathtour `linear-algebra`.
  - **`Family::Counting`** (`counting` module): the **pigeonhole principle**
    (`pigeonhole`, n+1 pigeons → distinct hole indices is UNSAT, PHP(5,4)=1024 cases
    exhaustive) + `permutation_exists` (n→n distinct is SAT, identity witness). A
    proof-complexity landmark (Haken 1985; Beame–Pitassi–Impagliazzo 1993). Covers
    mathtour `counting`.
  - **`Family::Algebra`** (`algebra` module): group axioms over ℤ/2ʷ —
    `addition_associative`, `additive_inverse` (exhaustive UNSAT of negation) +
    `subtraction_not_associative` (SAT counterexample, witness `(0,1,1)` — shows
    subtraction is not a group operation). Covers mathtour `groups`.
  - **mathtour/TOML/markdown synced:** `groups`, `counting`, `linear-algebra` flipped
    to `covered` in both `curriculum.toml` and `mathtour.rs` (the invariant test
    `covered_nodes_have_a_family_realized_by_a_self_checking_scenario` enforces the
    sync). Curriculum coverage now **7 of 23 nodes** with a self-checking exercise.
  - **48 `axeyum-scenarios` tests green; fmt/clippy(pedantic)/doc/link-check clean in
    isolation.** (Full `just check` still blocked only by the other agent's in-progress
    `axeyum-smtlib`/`axeyum-rewrite` WIP — transient.)
  - **Each family doubles as theory test coverage:** number theory + counting + algebra
    + linear algebra stress BV multiply/add/sub and the bit-blast→SAT path on
    structured, scalable, oracle-free instances. NEXT: ℚ/NRA linear algebra
    (Farkas-certified solving, det identities) and calculus RCF inequalities → the
    NRA corpus P2.5 lacks.
- **2026-06-17** — **Formal Mathematics Tour — curriculum knowledge graph + first
  destination built**. A structured, machine-readable curriculum derived by working
  *backward* from calculus / number theory / linear algebra to foundations, with
  axeyum's decidable/computable fragment per node.
  - **Knowledge graph** at [`docs/curriculum/`](docs/curriculum/README.md): an
    authoritative `curriculum.toml` (23 nodes, prerequisite edges, decidability +
    family + status metadata) + a README index (DAG, decidability/status legends)
    + **one markdown file per node** across `00-foundations/` (7), `01-number-systems/`
    (5), `02-structures/` (8), `03-destinations/` (3), each with summary · role ·
    prerequisites/unlocks · *testable in axeyum* (with example exercises) ·
    Lean-horizon · references. Grounded in Lean Mathlib, Metamath set.mm, and
    bridge-course canon.
  - **Decidability lens (the load-bearing filter):** each node's testable slice maps
    to an axeyum theory (number theory → BV/LIA, linear algebra → LRA/NRA, calculus
    → NRA); ∀-general theorems (infinitude of primes, ℝ-completeness, ε–δ) are
    flagged `lean-horizon`, never benchmarks. So building math-tour exercises *also*
    grows the arithmetic-theory corpora axeyum lacks (esp. NRA / P2.5).
  - **Code mirror:** `axeyum-scenarios::mathtour` — a queryable `MathNode` table
    mirroring the TOML, with topological teaching order and invariant tests (acyclic,
    prerequisites exist, every `Covered` node's family is realized by a self-checking
    scenario). 6 tests.
  - **First destination built:** `Family::NumberTheory` (`number_theory` module) —
    Bézout's identity (witness from extended Euclid), modular inverse (Hensel-lifted),
    "product of consecutive integers is even", "x² ≡ x (mod 2)". Oracle-free
    (SAT-by-witness / UNSAT-by-exhaustive), inside the BV subset. 4 tests; wired into
    the coverage aggregator and the mathtour `Covered` mapping.
  - Research note: [formal-mathematics-tour.md](docs/research/08-planning/formal-mathematics-tour.md).
  - **41 `axeyum-scenarios` tests green; fmt/clippy(pedantic)/doc/link-check clean
    in isolation.** (Full `just check` still blocked only by the other agent's
    in-progress `axeyum-smtlib` parse.rs — transient.)
- **2026-06-17** — **Double-duty educational layer — FIRST CUT BUILT (ADR-0033)**.
  The self-checking scenarios now double as curriculum, built bottom-up across
  ADR + 5 modules + an integration demo, all within `axeyum-scenarios`' existing
  deps (no new solver surface, no DAG change):
  - **ADR-0033** ratifies the double-duty artifact contract (concept-DAG node +
    statement/solution renderers + *measured* difficulty; grading via the trusted
    checker, never the search) and the crate boundary (extend `axeyum-scenarios`;
    extract `axeyum-edu` later per ADR-0001).
  - **`concept`** — a 15-node curriculum DAG derived from `foundational-dag.md`:
    acyclicity-checked `prerequisites`, deterministic `topological_order`,
    `frontier(mastered)`. 6 tests.
  - **`render`** — `Renderable` (problem statement + worked solution from the
    witness/UNSAT evidence). 2 tests.
  - **`exercise`** — `Exercise` with curriculum placement, measured `Difficulty`,
    and a **sound auto-grader**: a candidate is judged by `Scenario::is_satisfied_by`
    (the evaluator), so a wrong/empty witness is *rejected by evaluation*, never
    silently accepted. 5 tests.
  - **`coverage`** — the concept DAG as a test-coverage map; the key test
    (`every_declared_family_is_realized_by_a_self_checking_scenario`) fails if a
    concept claims coverage no self-checking scenario provides. 8/15 concepts
    covered; 7 gaps tracked honestly. 5 tests.
  - **`logic`** — propositional `Family::Logic` (modus ponens, excluded middle,
    De Morgan, contradiction, a SAT clause) proven by exhaustive truth tables —
    closes the bottom-rung `PropositionalLogic` concept. 2 tests.
  - **`axeyum-bench` `curriculum_demo` example** — ties it together end to end and,
    for the De Morgan BV identity, emits a **136-command Alethe proof re-checked
    VALID in-tree by `check_alethe`** (proof as worked solution; length as a
    proof-level difficulty signal). Demonstrates the whole thesis in one run.
  - **31 `axeyum-scenarios` tests green; fmt/clippy(pedantic)/doc clean in
    isolation.** Full `just check` is red only on the *other agent's* in-progress
    `axeyum-smtlib` parse.rs (concurrent PLAN build) — transient, not from this work.
  - Docs: rev-2 example-suites note (educational lens), ADR-0033, and a new
    "Curriculum / Educational Layer" section in consumer-scenario-models.md.
- **2026-06-17** — **P1.2: opt-in `preprocess` flag on the `solve`/`check_auto`
  façade**. New `SolverConfig::preprocess` (+ `with_preprocess`), default **off** —
  mirrors the existing `cnf_inprocessing` lever. When set, `check_auto` runs the
  denotation- and symbol-preserving canonicalizer over the assertions before its
  existing coercion-rewrite chain and dispatch; the returned `sat` model is
  unchanged (no variables eliminated) and still satisfies the originals. Makes
  word-level preprocessing reachable through the main `solve()` entry point, not
  just `check_with_preprocessing`: a 32-bit `(not (= (a*b) (b*a)))` via
  `solve(..with_preprocess(true))` returns unsat **instantly, no multiplier blast**
  (new `solve` test). Default-off ⇒ zero change to existing behavior/baselines; full
  gate green. Flipping the default remains a separate measured decision (ADR).
- **2026-06-17** — **P1.2: canonicalizer wired into `check_with_preprocessing`**.
  The denotation-preserving canonicalizer (`canonicalize_terms`) is now the FIRST
  pass in `check_with_preprocessing`, ahead of `propagate_values` + `solve_eqs`. It
  eliminates no variables (symbol-preserving), so it needs no reconstruction trail —
  the model still replays against the original assertions. This activates the prior
  commit's commutative-operand ordering in an actual solver path: a 32-bit
  `(not (= (a*b) (b*a)))` is now refuted **instantly by canonicalization, with zero
  multiplier bit-blasting** (new test returns in 0.00 s where a genuine 32×32 blast
  would be slow). Closes the "canonicalizer dormant in the product" gap for the
  opt-in preprocessing path. 6 preprocess tests green. (Default `solve()` still does
  not preprocess — making it the default is a separate decision, likely an ADR.)
- **2026-06-17** — **Research note: foundational example & benchmark suites**
  ([docs/research/08-planning/foundational-example-suites.md](docs/research/08-planning/foundational-example-suites.md)).
  Research-first, no code. Scopes the next wave of example suites by
  *decidability*, not appetite: (A) a self-checking software-verification
  "Hello, World" tier (SV-COMP `ReachSafety`/`NoOverflows` shape, hand-ported,
  reusing BMC/k-induction/symexec — **recommended first**, satisfies the open
  Phase 7 verification-audience criterion); (B) decidable geometry / real-closed
  fields as the QF_NRA/P2.5 corpus that's currently missing (witness-checked
  `sat`; `unsat` exposes the NRA-certificate evidence gap); (C) a low-cost
  finite/modular "math 101" extension of `Family::Identity`. The prompt's
  "Peano 101 / real analysis 101" is split out: induction-bearing arithmetic and
  the ε–δ layer are **undecidable → Lean-horizon proof-reconstruction targets
  (P3.6/P3.7), not benchmarks**; only the RCF-reducible fragment (geometry,
  MetiTarski-style inequalities) is reachable now. Surveys SV-COMP, SMT-LIB
  QF_NRA/meti-tarski, GeoCoq/Tarski, TPTP as yardsticks (mine for shape; do not
  ingest/sweep). Proposes **ADR-0033** to ratify the A/B/C-build, D-target tier
  split. Next: design suite A's first cut.
- **2026-06-17** — **Educational/double-duty lens added (rev 2 of the example-suites
  note)**. Thesis: the architecture that makes an artifact a good *test* is the same
  that makes it good *educational content* — a self-checking, seeded,
  evidence-exhibiting scenario placed in a concept DAG **is** a homework problem
  with a sound auto-grader and a worked solution. axeyum has the four otherwise-hard
  assets: (1) **sound auto-grading for free** because grading is *trusted checking*
  (`eval`/`evidence.check`/`check_alethe`), not search; (2) **certified procedural
  generation** (ADR-0008's SAT-by-execution / UNSAT-by-identity are the two
  procedural-content patterns, with machine-checked answer keys); (3) **measured
  difficulty** (CDCL conflicts, CNF size, Alethe/LRAT proof length); (4) **the
  concept DAG already exists** as the engineering gate (`foundational-dag.md`) —
  formalizing it gives curriculum order + a test-coverage audit + the gate (triple
  duty). Angle 1 (generate): homework banks from generators, a `check_alethe`-graded
  "fill the proof step" tutor, DAG-frontier sequencing — solver
  generates/grades/certifies/sequences *formal* exercises only, narrative stays
  human/LLM. Angle 2 (teach about): glass-box pipeline → a course map keyed to
  axeyum's own layers, with suite D reframed as a *lesson on undecidability*. Adds
  three thin, ADR-gated, no-solver-surface capabilities (rendering layer,
  machine-usable concept-DAG, concrete-execution trace = worked solution). Hard
  rules recorded: education is a consumer/lens that must not starve a foundation
  phase; grading must route through the trusted checker, never the search. ADR-0033
  scope extended to ratify the double-duty artifact contract.
- **2026-06-17** — **P1.2: commutative-operand canonicalization (word-level
  preprocessing)**. The denotation-preserving canonicalizer now sorts the operands
  of commutative ops (`and`/`or`/`xor`/`=`, `bvadd`/`bvmul`/`bvand`/`bvor`/`bvxor`/
  `bvnand`/`bvnor`/`bvxnor`) by ascending `TermId`, so `(bvmul a b)` and `(bvmul b a)`
  hash-cons to the **same** term — composing with the existing
  `=`-structurally-identical rule to fold `(= (bvmul a b) (bvmul b a))` → `true` with
  no bit-blasting. Strictly excludes non-commutative ops (`bvsub`, div/rem, shifts,
  comparisons, `concat`, and crucially `apply` — UF arg order is meaningful).
  Denotation verified by exhaustive 3-bit evaluator equivalence. **Curated slice with
  `--rewrite default`: 33/43 decided (was 32), 10 unknown (was 11), PAR-2 1.010 (was
  1.062), DISAGREE=0** — a real, sound +1 (cracks `calypto_problem_9`). **Honest
  caveat:** the targeted `wienand commute08/16` stay unknown — they are
  associativity+commutativity over multiplier *trees* with intermediate `var`
  bindings, not flat `a*b==b*a`; cracking them needs multiplier-tree AC-normalization
  + intermediate-equality inlining (a larger, separate task). Also: the bench default
  is `--rewrite Off`, so this only helps when rewriting is enabled — wiring the
  canonicalizer into the default `sat-bv` path is a follow-up.
- **2026-06-17** — **Benchmarking checkpoint: no regression + the perf ceiling
  diagnosed**. Re-ran axeyum (`sat-bv`, 2 s) over the committed 43-file curated QF_BV
  slice after the session's 21 proof-track commits: **32/43 decided (8 sat + 24
  unsat), 11 unknown, PAR-2 = 1.062 s** — matches the committed baseline (32/43,
  PAR-2 ≈1.07 s) exactly, so the proof work caused **zero performance regression**.
  All 11 unknowns are **`rustsat-batsat` SAT-solver timeouts** on multiplier-heavy
  instances (`brummayerbiere3 mulhs08/16/32/64`, `calypto`, `wienand-cav2008
  commute08/16`, `stp_samples`), with small-to-mid CNFs (2.7k–200k clauses) —
  i.e. **SAT time, not encoding, dominates**. Crucially, CNF preprocessing
  (subsumption T1.1.1 + bounded variable elimination T1.1.2) is **already wired**
  into the `sat-bv` path (`sat_bv_backend.rs`), and these still time out — so the
  next real perf lever is **SAT-solving power** (the custom CDCL core, ADR-0002, +
  multiplier-aware inprocessing), whose priority the methodology gates on exactly
  this "SAT time dominates" measurement. That gate is now met on the curated slice.
- **2026-06-17** — **`(get-proof)` now serves THREE theories (QF_BV + EUF + LRA)**.
  `solve_smtlib_get_proof` tries, in order, the `QF_BV` bitblast driver, the EUF
  congruence emitter (`prove_qf_uf_unsat_alethe`), and the LRA Farkas emitter
  (`prove_lra_unsat_alethe`), returning the first that yields a proof its
  fragment-appropriate checker re-validates (`check_alethe` for BV/EUF,
  `check_alethe_lra` for LRA). So a standard SMT-LIB `(get-proof)` now returns a
  checkable Alethe certificate for bit-vector, uninterpreted-function, AND
  linear-real-arithmetic `unsat`s — the three externally-Carcara-validated proof
  families, unified behind one front-door call. `Ok(None)` only when no supported
  fragment can prove it (e.g. an unsat needing shift semantics: `a=1 ∧ a≪1=0`).
  5 tests (BV/EUF/LRA proofs + sat→None + shift-semantics→None).
- **2026-06-17** — **`(get-proof)` in the SMT-LIB front door (P4.4 + proof surface)**.
  New `solve_smtlib_get_proof(input, config) -> Result<Option<String>, SolverError>`:
  parses a script, and when the assertions are `unsat` in the QF_BV Alethe fragment,
  returns the textual Alethe proof (`bitblast_*` → CNF-intro → resolution to `(cl)`),
  re-validated by `check_alethe` before return; `Ok(None)` for sat/unknown or
  out-of-fragment (shifts/div/rem, non-QF_BV). The parser now recognizes-and-ignores
  the `(get-proof)` command (was rejected). This is the user-facing z3-parity entry
  point for the whole session's proof machinery — a standard SMT-LIB `(get-proof)`
  now yields a Carcara-and-self-checkable certificate. 3 tests (checkable proof, sat
  → None, shift → None). Next: shift/div-rem `hole`+miter; then P3.5/P3.6.
- **2026-06-17** — **QF_BV Alethe proof wired into the evidence pipeline (first-class
  self-checking output)**. New `Evidence::UnsatAletheProof(Vec<AletheCommand>)` whose
  `check` route is `check_alethe` (internal re-validation). `produce_qf_bv_evidence`
  now, on the `>20`-bit `unsat` path that previously emitted plain DRAT (bit-blast
  *trusted*, `BitBlast=false`), first tries `prove_qf_bv_unsat_alethe` and — if it
  returns a proof that re-checks — emits the Alethe certificate with **`BitBlast`,
  `Tseitin`, `SatRefutation` all CERTIFIED** (the `bitblast_*` steps check the
  reduction itself, closing the bit-blast trust hole on that route). Precedence:
  term-level enumeration (≤20 bits, trusts only the evaluator) > Alethe proof >
  plain DRAT (out-of-fragment fallback unchanged). A 24-bit in-fragment `unsat`
  (`(bvult a b)∧(bvult b c)∧(bvult c a)`) now carries an Alethe proof that re-checks
  `Ok(true)`; a `bvshl` instance still falls back to DRAT. 20 evidence tests green.
  **The whole session's QF_BV proof machinery is now a product output**, dual-checkable
  (Carcara external + `check_alethe` internal). Next: shift/div-rem `hole`+miter;
  then the P3.5 reductions (arrays/functions/int-blasting) and P3.6 Lean kernel.
- **2026-06-17** — **axeyum SELF-CHECKS its own full QF_BV proofs (internal checker
  complete)**. Ported the `bitblast_*` reconstructions (all 17: var/const/not/
  and/or/xor/xnor/add/neg/**mult**/ult/slt/equal/comp/extract/concat/sign_extend) and
  the `and` clausification into `check_alethe`, mirroring `bitblast_alethe.rs` /
  Carcara's `bitvectors.rs` (`build_term_vec` over `AletheTerm`, width recovered from
  `@bbterm` arity / max `@bit_of` index). **`check_alethe(prove_qf_bv_unsat_alethe(…))
  == Ok(true)` for ALL 9 driver instances** (eq+ult, eq+neq, ult-cycle, slt, +
  bitwise/arith/nested compound) — new `qfbv_self_check.rs`. So a QF_BV `unsat` proof
  is now validated by **both** the external Carcara binary AND axeyum's own in-tree
  checker (no external dependency). One soundness-critical refinement: the resolution
  entailment mapping (`cnf_lit`/`register_atom`) now parity-folds leading syntactic
  `(not …)` so `(not φ)`-as-atom and `φ`-negated normalize identically (a genuine
  logical equivalence, still anchored by the DRAT re-check; all rejection tests hold).
  116 cnf-alethe tests + 9 self-check tests green. **The QF_BV proof system is now
  dual-checkable end-to-end.** Next: shift/div-rem via `hole`+miter for full QF_BV;
  wire the driver into the evidence pipeline (now that an internal checker exists).
- **2026-06-17** — **`check_alethe` gains the Boolean CNF-introduction rules**
  (`equiv1`/`equiv2`/`not_equiv1`/`not_equiv2`, `equiv_pos1/2`, `equiv_neg1/2`,
  `xor_pos1/2`, `xor_neg1/2`) — the Tseitin tautologies axeyum's QF_BV driver emits,
  transcribed literal-for-literal from Carcara's `tautology.rs` (polarities/order
  strict). With the `refl`/`symm`/`trans`/`cong` family from the previous commit,
  axeyum's own checker now validates the **Boolean layer** of its QF_BV proofs
  internally; only `bitblast_*` (BV reconstructions) and the `and` clausification
  remain to port for full self-checking (the latter deferred: a structural `and`
  would flip an existing `UnsupportedRule` test, so it lands with that test update).
  12 new rules, each with positive + rejection tests, + 2 end-to-end Boolean
  refutations to `(cl)`. 105 cnf-alethe tests green. **Next: port `bitblast_*` (+ the
  `and` clausification) into `check_alethe` → axeyum self-checks full QF_BV proofs.**
- **2026-06-17** — **`check_alethe` gains the general equality rules
  `refl`/`symm`/`trans`/`cong`**. axeyum's OWN Alethe checker now structurally
  verifies reflexivity, symmetry, transitivity chains, and congruence (matching
  Carcara's `reflexivity`/`extras`/`transitivity`/`congruence` rules: `trans` by
  premise adjacency, `cong` by one-premise-per-differing-argument-position over a
  shared `App`/`Indexed` head + arity). This is the step toward axeyum checking its
  *own* QF_BV bitblast proofs internally (currently only Carcara can) — `cong`/`trans`
  are exactly the bridge's reduction rules — and it strengthens EUF proof checking
  too. Premises must be unit positive `(= a b)` clauses; rejects head/arity mismatch,
  broken chains, unjustified positions. Dispatch refactored into
  `check_structural_rule` (behavior-preserving, to stay under the clippy line cap).
  4 new tests + an end-to-end `cong`+`trans`→`(cl)` refutation; all 91 cnf-alethe
  tests green. **Remaining for internal QF_BV checking: the `bitblast_*` rules in
  `check_alethe` (port Carcara's reconstructions).**
- **2026-06-17** — **QF_BV proof driver extended to COMPOUND terms (Carcara-`valid`)**.
  `prove_qf_bv_unsat_alethe` now reduces predicates over compound bit-vector operands
  — bitwise, arithmetic (`bvadd`/`bvneg`/`bvmul`), `bvcomp`, structural
  (`extract`/`concat`/`sign_extend`) — **nested to arbitrary depth, shared-DAG
  subterms bit-blasted once**. The uniform front-end (`BbReducer`): bottom-up, every
  term gets an `@bbterm`-form equality via `cong` (over children's equalities) +
  `bitblast_<op>` (over the `@bbterm`-form children) + `trans`; predicates then
  `cong`→`bitblast_<pred>`→`trans` to the bit-level Boolean, feeding the unchanged v1
  Tseitin+LRAT refutation. Factored `bitblast_op_step` to emit a gadget over already-
  rendered operands; switched the bitwise/`bvnot`/`bvxnor`/`extract` arms to
  `build_term_vec` (correct for `@bbterm`-form children; no-op for the IR path). **5
  compound unsat instances Carcara-`valid`** incl. nested `(bvand (bvor a b) c)` and
  arithmetic `(bvadd a b)` conflicts; `None` for shift/div subterms (out of fragment).
  Now `None` only for shifts, div/rem, zero_extend, rotates, `bvsub`/`bvnand`/`bvnor`.
  **Next: shift/div-rem via `hole` + the in-house miter side-cert → full QF_BV.**
- **2026-06-17** — **`prove_qf_bv_unsat_alethe` driver — first AUTOMATED full QF_BV
  `unsat` proof, Carcara-`valid` (T3.3 capstone, v1 fragment)**. New
  `qfbv_alethe.rs`: given QF_BV assertions, confirms `unsat` (SAT-BV path) then emits
  a complete Alethe proof an external checker accepts — no hand-construction. v1
  fragment: predicates `=`/`bvult`/`bvslt` and their negations over bit-vector
  **variables/constants** (any width; compound subterms → `None`, a later increment
  via the validated `cong`/`trans` path). Pipeline: `bitblast_step` →
  `equiv1`/`equiv2`+`resolution` (Boolean form) → hand-rolled Tseitin CNF-introduction
  (each Boolean gate as its own variable, justified by `and_pos`/`and_neg`/`or_pos`/
  `or_neg`/`equiv_pos*`/`equiv_neg*`/`xor_*`) → the in-tree `solve_with_drat_proof` →
  LRAT replayed as Alethe `resolution` to `(cl)`. **4 distinct unsat instances are
  Carcara-`valid`** (incl. a 42-step `(bvult a b) ∧ (bvult b a)` nested-ladder
  refutation), + `None` for sat and for compound-term inputs. Deterministic
  (BTreeMap/insertion-ordered). **This is the first time axeyum AUTOMATICALLY produces
  a complete, externally-checkable QF_BV `unsat` certificate.** Next: extend to
  compound terms (`cong`/`trans`, mechanism already validated) + the
  shift/div-rem `hole`s backed by the miter cert. A predicate over a *compound* BV term (`(bvand a a)` inside
  `(= (bvand a a) a)`) does not project compound bits directly, and Carcara has NO
  `((_ @bit_of i) (@bbterm …))` reduction rule (`refl`/`all_simplify` both reject it).
  The mechanism, now validated end-to-end: bitblast each operand bottom-up, **`cong`**
  to substitute the `@bbterm` forms into the predicate, **`trans`** + `bitblast_equal`
  to the bit-level Boolean, then `equiv*`/`not_equiv*`/`and`/`and_pos`/`and_neg` +
  `resolution` to `(cl)`. Locked in as `full_qf_bv_compound_term_proof_is_accepted_by_carcara`
  (the `bitblast_and`/`bitblast_var` steps from the production emitter). **Every bridge
  rule pattern the general QF_BV driver needs is now empirically pinned against the
  binary** — both variable and compound cases. **Next: the general
  `prove_qf_bv_unsat_alethe` driver (bottom-up term bitblast + cong/trans reduction +
  Tseitin-of-B with CNF-intro + the SAT refutation).**
- **2026-06-17** — **First FULL QF_BV `unsat` proof is Carcara-`valid` end-to-end
  (T3.3 bridge validated)**. Hand-validated against the binary, then locked in as a
  committed regression test (`full_qf_bv_unsat_proof_is_accepted_by_carcara`): for
  `(= a b) ∧ (bvult a b)` (1-bit), the proof composes the **production
  `bitblast_step` emitter** (the `bitblast_equal`/`bitblast_ult` steps) with the
  bridge — `equiv1` + `resolution` to derive each assertion's Boolean form, then
  CNF-introduction (`and` with an `:args` conjunct index; `equiv2`) + `resolution`
  to the empty clause `(cl)`. **Carcara `valid`.** This resolves the last unknowns of
  the bridge (the exact rule inventory + that `and` needs `:args (i)`). Remaining to
  *automate* a general QF_BV proof: a Tseitin encoder turning an arbitrary
  bitblasted Boolean `B` into clauses with CNF-intro justifications, wired over the
  already-valid `lrat_to_alethe` resolution layer. **Next: the general
  `prove_qf_bv_unsat_alethe` driver (Tseitin-of-B + the SAT refutation bridge).**
- **2026-06-17** — **T3.3.1 step 2 complete: bitblast emitter covers Carcara's
  entire non-hole QF_BV operator set**. Added `bvmul` (shift-add multiplier,
  transcribed from Carcara's `shift_add_multiplier` — correct on the first run incl.
  width-1, width≥2, and n-ary left-fold), `bvextract`/`bvconcat`/`bvsign_extend`
  (the structural ops; extract/sign_extend use the `Indexed` LHS, concat is
  low-arg-bits-first). One oracle-forced fix: `sign_extend` with `i==0` is the plain
  `(= ((_ sign_extend 0) x) x)` (Carcara `assert_eq(x,res)`), not a `@bbterm`.
  32 cross-check cases, all Carcara rule-accepted. **Every QF_BV operator Carcara has
  a structural `bitblast_*` rule for is now emitted and empirically validated.** Still
  `None` (the Carcara *holes*): shifts (`bvshl`/`bvlshr`/`bvashr`), div/rem
  (`bvudiv`/`bvurem`/`bvsdiv`/…), zero_extend, rotates — these get `hole` + the
  in-house miter side-cert in a later increment. **Next: the predicate-bitblast +
  Tseitin-CNF bridge to compose these definitional steps into a full QF_BV `unsat`
  proof closing to `(cl)` via the Carcara-valid `lrat_to_alethe` resolution layer.**
- **2026-06-17** — **T3.3.1 step 2 (arithmetic + comparison): bitblast emitter
  extended**. `bitblast_step` now also emits Carcara-valid steps for `bvadd`
  (ripple-carry, n-ary left-fold), `bvneg` (two's-complement adder with verbatim
  `false`/`true` carry-ins), `bvult`/`bvslt` (the comparison ladders, slt with its
  sign-bit final step + width-1 special case), BV `=` (`bitblast_equal`), and
  `bvcomp`. This added the **two further output shapes** beyond the bitwise
  `(= t (@bbterm …))`: predicate ops conclude `(= <pred> <bool>)` (no `@bbterm`),
  and `bvcomp` wraps its single Bool in `@bbterm`. **All six Carcara rule-accepted
  on the first run** (gated per-operator tests; shapes transcribed directly from
  `bitvectors.rs`). 25 cross-check cases total. Still `None` (next increments):
  `bvmul` (shift-add multiplier), structural ops (extract/concat/sign_extend),
  shifts, div/rem. **Next: `bvmul`, then the predicate-bitblast + Tseitin-CNF bridge
  to close a full QF_BV refutation to `(cl)`.**
- **2026-06-16** — **T3.3.1 step 2 (first slice): per-operator bitblast emitter
  (bitwise fragment)**. New `axeyum_solver::bitblast_step(arena, term, id)` emits the
  definitional `(= <T> (@bbterm b0…b_{n-1})) :rule bitblast_<op>` step for the
  bitwise QF_BV fragment — `var`, `const`, `bvnot`, `bvand`, `bvor`, `bvxor`,
  `bvxnor` — building each bit LSB-first via `(_ @bit_of i)` projections exactly as
  Carcara reconstructs (left-fold for n-ary and/or/xor; `(= a_i b_i)` for xnor;
  `true`/`false` per const bit). **All seven operators are Carcara rule-accepted**
  (gated tests: emitted step parses and the `bitblast_*` rule checks — only the
  empty-clause conclusion is absent, since a lone definitional step is not a
  refutation). Every shape matched the binary on the first run (derived from
  `bitvectors.rs`). `bv_term_to_alethe` renders BV terms to matching SMT-LIB syntax
  (`#b…` consts, `bvand`/… heads); anything outside the fragment → `None`. 6 unit
  tests + 7 gated carcara tests. **Next: arithmetic/comparison ops (`bvadd`/`bvmult`/
  `bvult`/`bitblast_equal`), then the predicate-bitblast + Tseitin-CNF bridge to
  close a full QF_BV refutation to `(cl)`.**
- **2026-06-16** — **T3.3.1 step 1: `AletheTerm` indexed-operator IR extension**.
  Added `AletheTerm::Indexed { op, indices: Vec<i128>, args }` so SMT-LIB indexed
  applications like `((_ @bit_of 0) x)` (and bare `(_ @bit_of 1)`) are first-class —
  the bounded prerequisite for the per-operator `bitblast_*` emitter (the old
  `App(String, …)` head + atom-only parser couldn't represent a list-headed
  application). `key`/`write`/`parse` handle applied vs bare forms with exact
  round-trip; an `Indexed` term is an opaque atom to the theory rules (the only
  match sites needing an arm were `real_term`/`int_term` in `alethe_lra.rs` →
  `None`). Purely additive: existing `Const`/`App` output byte-identical, all ~82
  cnf tests + EUF/LRA/resolution emission unchanged. **A gated Carcara test confirms
  the IR renders exactly the syntax Carcara accepts**: a `bitblast_var` step built
  via the IR + `write_alethe` parses and the rule checks (`!parser error` &&
  "does not conclude empty clause"). 4 new IR tests + 1 carcara test (10 cross-check
  total). **Next: T3.3.1 step 2 — per-operator bitblast emitter from `axeyum-bv`.**
- **2026-06-16** — **QF_BV bitblast→Carcara contract reverse-engineered & recorded
  (T3.3.1 design)**. Empirically confirmed against the built Carcara binary the
  exact shape it requires for per-operator `bitblast_*` steps: the `@bbterm`
  operator + indexed `(_ @bit_of i)` bit-extraction (**spelling is `@bit_of`, not
  `@bit`**), e.g. `bitblast_var` accepts
  `(= x (@bbterm ((_ @bit_of 0) x) ((_ @bit_of 1) x)))` — this **parses and checks
  valid** (a lone step only lacks the empty-clause conclusion). Recorded the full
  rule-name set and the L-sized implementation body in
  `docs/research/07-verification/scalable-bitblast-certification.md`: (1) extend
  `AletheTerm` to represent the indexed `(_ @bit_of i)` head (parse/write/`key`
  round-trip) — the current `App(String, …)` can't; (2) per-operator emitter from
  `axeyum-bv`'s lowering, div/rem/shift as `hole` + miter side-cert; (3) bridge via
  Tseitin CNF rules to the already-Carcara-valid `lrat_to_alethe` resolution layer.
  This is the external-checker analogue of the in-house miter certificate (path B);
  no code emitted this turn — deliberately scoped as design so the L-task starts
  correct. **Next action: T3.3.1 step 1 — the `AletheTerm` indexed-op IR extension.**
- **2026-06-16** — **Resolution/clausal layer now Carcara-`valid` (T3.3.3)** — the
  Boolean-refutation rung of a full QF_BV proof. A CNF UNSAT goes CDCL → DRAT →
  LRAT → Alethe (`lrat_to_alethe`) and is now accepted end-to-end by Carcara
  against the asserted input clauses. The cross-check surfaced **two latent bugs
  our lenient `check_alethe` masked**, now fixed in `lrat_to_alethe`: (1) command
  ids were bare numerals (`1`, `2`) — invalid Alethe symbols; now prefixed
  (`a{n}`/`t{n}`); (2) an `assume (or φ…)` introduces the disjunction as a *unit*
  clause, not the clause `(cl φ…)` — each multi-literal input clause now gets an
  explicit `:rule or` unpacking step before resolution consumes it. `check_alethe`
  learned the `or` rule (entailment-checked, like resolution). All `assume`s emit
  before steps (no checker warnings). 82 cnf tests + 9 cross-check cases green.
  This is the third externally-validated proof family (EUF, LRA, now clausal
  resolution) and the closing step a full QF_BV bitblast proof will reuse.
- **2026-06-16** — **LRA Carcara cross-check now covers equality assertions**.
  `FarkasCertificate` gained a `pub origins: Vec<usize>` field (`origins[i]` = the
  source assertion index of atom `i`; an equality contributes two atoms sharing one
  origin). `farkas_args` now groups multipliers by origin instead of assuming a 1:1
  atom↔assertion map: a single-atom assertion (inequality) keeps its multiplier
  (byte-identical output); a two-atom equality `a=b` emits the **signed** coefficient
  `m1−m0` (confirmed sign against Carcara — the mixed equality+inequality case
  disambiguates the global sign), rendered with negatives as `(- n)` / `(- (/ p.0
  q.0))`. Orientation is robust (`is_negation_of` verifies the two atoms are exact
  negatives before trusting push order, else bails to no-args). **Three new
  equality refutations pass Carcara** (`x=1∧x=2` → `((- 1) 1)`; mixed
  equality+inequality; coefficient-bearing equality). 8 cross-check cases total; the
  inequality-only fragment is unchanged. Remaining LRA gap: assertions splitting into
  >2 atoms (conjunctions) still emit no args.
- **2026-06-16** — **LRA `la_generic` proofs now Carcara-`valid` (Farkas `:args`)**.
  The Alethe `Step` IR gained an `args: Vec<AletheTerm>` field (parse + write
  round-trip; emitted after `:premises`, only when non-empty so all ~80 existing
  cnf-alethe tests and EUF/LIA emission stay byte-identical).
  `prove_lra_unsat_alethe` now attaches one Farkas coefficient per clause literal,
  derived from `lra_farkas_certificate` (mapped 1:1 to assertions; equality/`and`
  assertions that split into two bounds emit no args and stay axeyum-checked-only).
  Coefficients render as bare integer numerals or `(/ p.0 q.0)` reals (verified
  against Carcara's `as_fraction`). **Three diverse LRA refutations now pass Carcara
  end-to-end** (unit `(1 1)`, non-unit `(1 2)`, multi-variable `(1 1 1)`) — LRA
  joins EUF as an externally-validated proof family. Carcara re-derives the
  contradiction from the args, so `valid` is the soundness oracle, not the
  coefficients themselves.
- **2026-06-16** — **Carcara third-party cross-check harness landed**
  (`crates/axeyum-solver/tests/carcara_crosscheck.rs`, plan task T3.3.5). axeyum's
  emitted Alethe proofs are now validated by the **independent Rust Carcara
  checker** (shares none of our code), not just our own `check_alethe`: the proof
  is serialized via `write_alethe` + matching `.smt2` via `write_script`, handed to
  `carcara check`. **EUF transitivity and congruence proofs both return `valid`**
  end-to-end. The test runtime-skips (prints a note, passes) when the Carcara
  binary is absent, so CI stays green; build it via
  `cargo build --release -p carcara-cli` in `references/carcara` (override the
  pinned toolchain with `RUSTUP_TOOLCHAIN=…`) or set `AXEYUM_CARCARA_BIN`.
  **Cross-check findings recorded as the next P3.3 tasks:** (1) our `la_generic`
  (LRA) step is rejected by Carcara — it requires the Farkas coefficient `:args`
  (one rational per clause literal); we already compute these
  (`lra_farkas_certificate`) but the Alethe `Step` IR has no `:args` field yet, so
  adding it + emitting the multipliers is the next increment; (2) `lia_generic` is
  a *Carcara hole* (unimplemented there) — Carcara reports `holey`, so the integer
  arithmetic rung needs either an int→real reduction proof or to stay
  axeyum-checked-only. EUF is the first proof family externally validated.
- **2026-06-16** — **`lia_generic` integer Alethe checking + emission**
  (`prove_lia_unsat_alethe`, exported). Integer counterpart to `la_generic`:
  the `la_generic_check` dispatch gained a `lia_generic` arm decided by the
  integer-complete `check_with_lia_simplex` (honoring integrality), plus an int
  parser (constant-factor-guarded `*`, plain-`i128` numerals) and an emitter
  self-validated by `check_alethe_lra`. A dedicated test pins the integer/real
  distinction: `(cl (<= x 0) (>= x 1))` is accepted by `lia_generic`, rejected
  by `la_generic`. 4 new tests; `just check` green.
- **2026-06-16** — **P1.5 online decider wired as the QF_UF fast path** (pending
  commit). `auto::check_auto_dispatch` now tries `solve_qf_uf_online` (online
  DPLL(T) on the backtrackable e-graph) **before** the offline `check_qf_uf`; on
  `Unknown` it falls through to the offline enumeration, then bit-blasting — so the
  change is zero-risk (unknown-safe backstop) and only ever fast-paths a sound
  answer. Full solver suite (incl. functions/aufbv/function_scenarios) green: no
  regression.
- **2026-06-16** — **P1.5 online DPLL(T) decision procedure** (commit 8bbdb9d).
  `solve_qf_uf_online`: extends the refutation engine to a full decider —
  `Unsat`/`Sat(model)`/`Unknown`. On a theory-consistent total assignment it builds
  a model from the e-graph classes (`EufTheory::model`) and **replays it against the
  original assertions** (the soundness gate: a non-replaying model → `Unknown`, never
  a wrong `sat`); no equality atoms / un-encodable structure → `Unknown` (same
  conservative boundary as the offline `check_qf_uf`). `prove_unsat_qf_uf_online` now
  delegates to it. 3 tests incl. a **400-formula differential vs `check_qf_uf`**
  (no Sat/Unsat clash where both decide) + a replay-checked sat model. The online
  QF_UF *decision procedure* on one backtrackable e-graph is complete.
- **2026-06-16** — **P1.5 online DPLL(T) refutation engine** (commit 223230b).
  `prove_unsat_qf_uf_online`: a self-contained online DPLL(T) for QF_UF — Tseitin
  CNF of the Boolean skeleton (and/or/not/xor/implies/ite gates; un-encodable
  structure → sound give-up) driving the online `EufTheory`. Interleaves Boolean
  unit propagation with `EufTheory::propagate`, mirrors eq-atom assignments via
  `assert` (theory `push` per decision, `pop` per backtrack — lockstep), learns
  `¬⋀core` on theory conflicts, chronological backtracking. Returns `true` only at
  a root-level conflict (sound UNSAT). **Differentially validated vs the offline
  `prove_unsat_lazy` on 500 random QF_UF formulas (exact agreement) + 4 crafted
  cases** (disjunction, transitivity, congruence, a SAT case). This is the *online
  search* atop the online theory — the offline SAT-enumeration loop replaced by one
  incremental backtrackable e-graph. (Implemented by a sub-agent; reviewed in full —
  Tseitin gates are equivalence-correct, the UNSAT verdict is sound, push/pop stays
  balanced — and the differential count was raised 50→500.)
- **2026-06-16** — **P1.5 online theory propagation (`EufTheory::propagate`)**
  (commit a3cea13). Extends the online theory with sound EUF propagation: the
  unassigned equality atoms whose sides are already congruent, each entailed `true`
  with the asserted equalities that force it (`TheoryProp{lit, reason}`).
  Assigned-state is now tracked and backtracked in lockstep (per-`push`
  `(diseqs, assigned_log)` markers), so entailments retract on `pop`. 2 added tests
  (transitivity+congruence propagation with reasons; retraction on backtrack).
  The online theory now has the full assert/propagate/explain/backtrack surface a
  CDCL(T) loop drives.
- **2026-06-16** — **P1.5 online `TheorySolver` trait + `EufTheory`** (commit afec596).
  First slice of the *online* CDCL(T) theory interface (vs the offline
  `prove_unsat_lazy` model-enumeration): `TheorySolver` (`assert(atom,value)` →
  `Ok` or a conflicting `Vec<TheoryLit>`; `push`/`pop`) and `EufTheory`, an EUF
  solver over **one** backtrackable keystone `EGraph` kept in sync with the search.
  Asserting `eq` merges sides (reason = atom index, so `EGraph::explain`
  reconstructs the conflict core); asserting `¬eq` records a disequality; conflicts
  = a violated disequality or two distinct constants forced equal. 4 tests
  (congruence conflict + explained core, merge backtracked on `pop`, constant
  collision, transitivity core). Exported; lays the theory side of the CDCL(T) loop
  that P1.6 combination builds on.
- **2026-06-16** — **P2.6 congruence-only nested trigger test** (commit 8e0a61c).
- **2026-06-16** — **P2.6 multi-round instantiation test** (commit 8d0a9e4).
  Added `instantiation_loop_refutes_across_multiple_rounds`: a refutation that
  only closes because round 1 (`∀x. f(x)=g(x)` over ground `f(a)`) introduces
  `g(a)`, which round 2 (`∀x. g(x)=0`) can then match — proving the fixpoint loop
  genuinely chains instances across rounds, not just single-shot.
- **2026-06-16** — **P2.6 keystone wired into `solve` dispatch** (commit 2a6d4bd).
  The infinite/too-wide-domain quantifier fallback in `solve` now tries the
  congruence-aware `prove_quantified_unsat_via_egraph` (keystone) **before** MBQI:
  finite-domain expansion refuses domains wider than `QUANT_EXPAND_BIT_LIMIT`
  (2¹⁰), and since UF is finite-scalar-only in the IR, a `∀x:BV32. f(x)=…`
  quantifier surfaces there — exactly where e-matching modulo the ground
  congruence refutes (fire `f(x)` at ground `f(a)`). Only ever returns `unsat`
  (sound, instances implied) or falls through to MBQI on `unknown`. New
  `auto::tests` dispatch test proves the `solve` → keystone route end to end.
- **2026-06-16** — **P2.6 multi-pattern trigger inference** (commit c82c175).
  `select_triggers` infers a (possibly multi-term) trigger set from the body when
  no single subterm covers all bound variables — single-cover preferred, else a
  greedy set cover over function-app candidates. `instantiate_forall_via_egraph`
  e-matches each trigger and joins the per-trigger substitutions consistently on
  shared variables (`merge_substitutions`), so `∀x,y. f(x)=g(y)` instantiates from
  `{f(x), g(y)}`. 9 qinst tests.
- **2026-06-16** — **P2.6 e-matching instantiation loop** (commit 6902f84).
  `prove_quantified_unsat_via_egraph`: split ground/universals, then instantiate →
  re-check (`check_auto`) → fixpoint; ground-unsat ⇒ sound refutation. Closes the
  e-matching vertical slice on the keystone (e-graph → ematch → instantiation →
  ground refutation). 8 qinst tests.
- **2026-06-16** — **P2.6 multi-variable quantifiers** (commit 0fdf634).
  `instantiate_forall_via_egraph` now peels nested `∀x.∀y.…`, requires a trigger
  covering all bound variables, maps each to its own `Var(index)`, and builds the
  full substitution. With nested/multi-arg trigger support, the keystone
  instantiation covers single/multi-var quantifiers with `f(g(x))` / `g(x,y)`
  triggers. 6 qinst tests.
- **2026-06-16** — **P2.6 nested/multi-arg triggers** (commit c658839).
  `instantiate_forall_via_egraph` generalized from unary to arbitrary triggers via
  the full `ematch` engine: `f(g(x))`, `g(x, a)` (ground parts matched by class).
  5 qinst tests.
- **2026-06-16** — **P2.6 keystone quantifier instantiation** (commit 5ac7343).
  `instantiate_forall_via_egraph` wires `ematch` into instantiation: builds the
  ground e-graph (merging ground equalities), e-matches a unary trigger, emits
  congruence-aware instances (a=b ⇒ f(a),f(b) fire once). The keystone now drives
  EUF and quantifier instantiation end to end. 3 tests.
- **2026-06-16** — **P2.6 e-matching engine** (commit 30ebec9). `EGraph::ematch`:
  full single-pattern matching modulo congruence (nested patterns, repeated-variable
  consistency, all substitutions) — the matching engine quantifier instantiation
  runs. Built on the keystone; matching is intrinsically up to congruence. 23 tests.
- **2026-06-16** — **P2.6 e-matching foundation** (commit ff53168).
  `EGraph::enumerate_apps(decl)` — distinct applications of a function symbol modulo
  congruence (one per class, canonical arg roots), the single-symbol trigger that
  drives quantifier instantiation. The first step toward e-matching / unbounded
  quantifiers (the biggest functional gap; today only finite-domain expansion).
- **2026-06-16** — **QF_UF upgraded to checked** (commit 799cd43); **T1.2.8 AIG
  rewrite attempted + reverted** (regressed a borderline FP128 instance — negative
  result recorded).
- **2026-06-16** — **EUF dispatch path hardened** (commit 21ca0a9). 120-iteration
  randomized differential test: random pure equality/UF formulas decided by both
  `check_qf_uf` and Ackermann must agree. Hardens the now-production EUF fast-path.
- **2026-06-16** — **EUF e-graph path wired into `check_auto`** (commit 6ce85b0).
  UF instances try `check_qf_uf` (congruence fast-path) before the Ackermann
  bit-blast; sound for QF_UFBV (replay-checked sat, re-checked unsat), Ackermann
  fallback on unknown. Full solver test suite + micro bench regression-free.
- **2026-06-16** — **T1.5.5 `check_qf_uf` with replay-checked sat models** (commit
  c08c763). Full QF_UF decision on the e-graph: lazy DPLL(T) + a candidate model
  built from e-graph classes (distinct class values, constants pinned, function
  interpretations) replayed against the originals as the soundness gate. Decisions
  + models differentially agree with Ackermann on all 6 cases. The "model replays"
  half of T1.5.5.
- **2026-06-16** — **EUF prover differentially validated** (commit a73d34a).
  `tests/euf_egraph_diff.rs` cross-checks `prove_unsat_lazy` against the trusted
  Ackermann `QF_UFBV` path: 6 instances (congruence/transitivity/two-arg conflicts,
  a disjunctive refutation, two sat) all agree. The "verified against the eager
  path" check (T1.5.4).
- **2026-06-16** — **P1.5 lazy DPLL(T) loop** (commit 8d97081). `prove_unsat_lazy`
  lifts the conjunctive prover to arbitrary boolean structure: equality atoms →
  fresh Boolean vars, boolean skeleton solved by sat-bv, model theory-checked on
  the e-graph, conflicts turned into explain-based blocking clauses, re-solve to
  fixpoint. Sound EUF UNSAT over disjunctions the conjunctive pass can't see. 8
  euf_egraph tests.
- **2026-06-16** — **P1.5 first slice: EUF congruence UNSAT prover** (commit f69aa40).
  `axeyum-egraph` wired into the solver; `prove_unsat_by_congruence` abstracts
  assertions as uninterpreted equality logic and proves UNSAT by congruence +
  constant distinctness (sound, incomplete), every conflict re-checked by the
  independent `check_congruence` and carrying an UNSAT core. 5 tests. The EUF-on-
  the-e-graph core; next is the lazy boolean loop for full QF_UF.
- **2026-06-16** — **P1.4 e-graph keystone COMPLETE: T1.4.4–T1.4.6** (commits
  c47dc0c, 2c735b5, d81bf46). T1.4.4 backtrackable push/pop trail (path compression
  dropped; every mutation trailed; 150-iteration rebuild property test). T1.4.5
  independent `check_congruence` (own union-find + congruence closure re-validates
  every `explain`). T1.4.6 per-class theory-variable lists (the interface-equality
  bus, merge-propagated + backtracked). The e-graph is now a complete keystone;
  next is P1.5 CDCL(T).
- **2026-06-16** — **T1.4.3 e-graph explanations** (commit 0c5840f). Nieuwenhuis–
  Oliveras proof forest alongside the union-find; `merge(a,b,reason)` records edges;
  `explain(a,b)` returns the minimal input-reason set entailing the equality
  (explain-to-LCA, congruence premises recovered recursively). Soundness
  property-tested (replay named merges → re-derives the equality). 9 tests.
- **2026-06-16** — **P1.4 e-graph keystone started: T1.4.1+T1.4.2** (commit eb3e9e6).
  New dependency-free `axeyum-egraph` crate (ADR-0032): hash-consed e-node creation
  over a root-keyed signature table, path-compressing union-find, and the
  deferred-merge cascade that re-canonicalizes parents to close transitive
  congruence. 5 tests incl. a 300-iteration brute-force congruence-oracle property
  test. Next: T1.4.3 explanations.
- **2026-06-16** — **bench `--preprocess` + measurement** (commit 0c594ac).
  propagate_values+solve_eqs wired into the bench setup phase; trail threaded to
  reconstruct the model before the original-assertion replay. Curated A/B: 32/43,
  agree=32, DISAGREE=0, 0 replay failures, PAR-2 1.060 s (≈ baseline 1.063);
  DAG reduced on 5/43. `just bench-qfbv-curated-preprocess`,
  `qfbv-curated-sat-bv-preprocess-vs-z3-2s.json`.
- **2026-06-16** — **`check_with_preprocessing` wrapper** (commit 86cd28a). Façade
  entry that runs propagate_values+solve_eqs before a backend, composes their
  ModelReconstructionTrails, and on `sat` reconstructs + replays against the
  original assertions (mirrors check_with_array_elimination; wraps at the
  `&mut`-arena layer). 5 integration tests through the real sat-bv backend. Not yet
  on the bench/default path — see Current focus for the setup-phase wiring approach.
- **2026-06-16** — **T1.2.3 solve_eqs** (commit e1682ce). Top-level `(= x t)`
  oriented to `x := t` with a memoized occurs-check, substituted to a fixpoint,
  recorded in the trail; generalizes propagate_values. DAG interning keeps
  substitution linear. 200-trial randomized chain-of-definitions reconstruction
  test. axeyum-rewrite at 36 tests. Next: wire propagate_values+solve_eqs into the
  solve path (the `check_with_preprocessing` wrapper) and measure.
- **2026-06-16** — **P1.2 started: T1.2.1 model-reconstruction trail + T1.2.2
  propagate_values** (commit d5c49b6). New `axeyum_rewrite::ModelReconstructionTrail`
  (eliminated-symbol → defining-term steps, reverse-replay `reconstruct`, composable
  `append`) generalizing the bit-blast-lift / array-`project_model` / BVE-reconstruct
  patterns. First consumer `propagate_values`: top-level `var = const` (and bare /
  negated Boolean) facts substituted to a fixpoint, model-sound via the trail
  (proven end to end). Pure axeyum-rewrite, 32 tests. **Next:** `solve_eqs` (T1.2.3,
  `var = term` elimination — the big variable-count win) and wiring the preprocessing
  pipeline into the solve path + measuring the curated slice.
- **2026-06-16** — **T1.1.4 inprocessing made near-linear + time-bounded.**
  `simplify` → forward one-watch occurrence-list subsumption (variable-keyed
  signature so self-subsuming witnesses aren't false-rejected); `bve` → full
  literal occurrence lists + touched-variable queue (lazy clause removal,
  resolution-budget safety net), running to a fixpoint in one drain. Added
  `simplify_within`/`eliminate_variables_within` deadline variants; `sat_bv`
  bounds inprocessing to ≤50% of the remaining solve budget and the old 512/2048
  size guard was lifted to a 200k/1M admission ceiling. Two new 400-formula
  randomized brute-force tests (subsumption equivalence, BVE equisatisfiability +
  reconstruction). Curated A/B: 32/43 decided, agree=32, DISAGREE=0, 0 replay
  failures, PAR-2 1.095 s — no regression vs baseline; the prior 13–22 s pass
  hangs and 3-instance regression are gone. The 11 unknowns stay unknown because
  they are multiplier-structural (BVE ≈0% on `mulhs*`) or reduced-but-still-hard,
  i.e. SAT-search-bound (→ P1.3). Commits 4c99d7e (a), 154936d (b), this (c).
- **2026-06-16** — **T1.1.3 inprocessing wired into the bit-blast→CNF→solve
  pipeline + measured on s4.** New `SolverConfig::cnf_inprocessing`
  (`with_cnf_inprocessing`, off by default); `sat_bv_backend` runs
  `simplify`+`eliminate_variables` on the Tseitin formula behind a
  `maybe_inprocess` size guard, solves the reduced formula, DRAT-checks /
  `prove_unsat`s the reduced formula, and lifts a reduced `sat` model back via
  `Reconstruction::extend` before the original-term replay (`inprocess_ms`
  folded into `translate`; per-pass stats recorded). 3 A/B tests
  (`tests/sat_bv.rs`), bench `--inprocess` flag (config + JSON metadata + run
  fingerprint), `just bench-qfbv-curated-inprocess`, committed artifact
  `qfbv-curated-sat-bv-inprocess-vs-z3-2s.json`. **Measurement:** with the
  current `O(clauses²)` subsumption + per-candidate-rescan BVE, inprocessing is a
  net regression (13–22 s passes blow a 2 s budget) and decides none of the 11
  unknowns; correctness is intact (DISAGREE=0, 0 replay failures). Guarded to
  ≤512 vars/≤2048 clauses → decision-identical to baseline (32/43, PAR-2 1.071 s).
  Real win deferred to T1.1.4 (occurrence-list indexing).
- **2026-06-15** — Cloned full reference set (added Z3 to `scripts/fetch-references.sh`).
  Ran five Opus sub-agents over Z3 core, Z3 theories, bitwuzla+CaDiCaL/Kissat,
  proof/Lean, and an axeyum self-audit. Authored the end-to-end plan under
  `docs/plan/` with this STATUS tracker and the master `PLAN.md` index.
- **2026-06-15** — **P3.0 done.** New `axeyum_solver::trust` module (`TrustId`,
  `TrustStep`, `ALL_TRUST_IDS`, `trust_ledger_markdown`); `EvidenceReport.trusted_steps`
  records per-result trust dependencies across all producers; golden test +
  `docs/research/08-planning/trust-ledger.md`; 4 per-result tests; ADR-0031.
  Trusted base is now countable: 5 trust holes (array-elim, ackermann, int-blast,
  datatype-elim, fpa2bv) — the targets for Track 3 P3.5.
- **2026-06-15** — **T1.1.1 subsumption pass.** New `axeyum_cnf::simplify`
  (`SubsumeStats`): model-preserving tautology removal + forward subsumption (64-bit
  signature fast-reject) + self-subsuming resolution; 7 tests incl. brute-force
  equivalence and SAT/DRAT preservation. P1.1 → WIP.
- **2026-06-15** — **P4.5 (WIP) + s4 transition.** Bench harness worker stack
  raised to 512 MB (deeply-nested-term stack-overflow fix); committed curated
  QF_BV slice `corpus/qfbv-curated/` (36 files) + `just bench-qfbv-curated`;
  GPU horizon note; `docs/plan/host-setup.md` transition checklist. Full baseline
  OOM-killed the host — deferred to s4 with memory caps.
- **2026-06-15** — **T1.1.2 bounded variable elimination.** New `axeyum_cnf::bve`
  (`eliminate_variables`, `BveOptions`, `BveOutcome`, `BveStats`, `Reconstruction`):
  Davis–Putnam resolution with the CaDiCaL non-increasing/size/occurrence bounds and
  a reverse-replay reconstruction stack (equisatisfiable, not model-preserving — the
  reduced model extends via `Reconstruction::extend`). 6 tests incl. brute-force
  equisatisfiability + per-model reconstruction + bound-respect + SAT/DRAT preservation.
