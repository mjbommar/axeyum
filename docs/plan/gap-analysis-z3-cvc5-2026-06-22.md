# Z3/cvc5 gap analysis (2026-06-22; amended 2026-06-23)

Status: current audit, amended after the online-combination / vivification /
route-telemetry push  
Scope: top-down, practical delta between axeyum's current capability ledger and
the public Z3/cvc5 surfaces.

This is not a replacement for the track plans. It is the current priority map:
what still separates axeyum from Z3/cvc5, why it matters, and what concrete
increment should close each gap.

## Inputs

Local sources:

- `PLAN.md` and `STATUS.md`
- `crates/axeyum-solver/src/capabilities.rs`
- `docs/research/08-planning/capability-matrix.md`
- `docs/plan/01-dependency-dag.md`
- `docs/plan/references/{z3-core,z3-theories,proof-and-lean,axeyum-current-state}.md`

External target anchors checked for this audit:

- Z3 Guide: bit-vectors, quantifiers, tactics, optimization, fixedpoints/SPACER,
  and sequences:
  <https://microsoft.github.io/z3guide/docs/theories/Bitvectors/>,
  <https://microsoft.github.io/z3guide/docs/logic/Quantifiers/>,
  <https://microsoft.github.io/z3guide/docs/strategies/summary/>,
  <https://microsoft.github.io/z3guide/docs/optimization/intro/>,
  <https://microsoft.github.io/z3guide/docs/fixedpoints/intro/>,
  <https://microsoft.github.io/z3guide/docs/theories/Sequences/>.
- Z3 internals draft for nlsat/QSAT/SPACER architecture:
  <https://z3prover.github.io/papers/z3internals.html>.
- cvc5 main docs: theory references and proof production:
  <https://cvc5.github.io/docs-ci/docs-main/theories/theories.html>,
  <https://cvc5.github.io/docs-ci/docs-main/proofs/proofs.html>.
- cvc5 NEWS for current proof, interpolation, abduction, SyGuS, and
  experimental-theory status:
  <https://github.com/cvc5/cvc5/blob/main/NEWS.md>.

## Executive read

The earlier framing still holds, but the emphasis has shifted again after the
latest Track 1/2/4 push:

1. **The categorical feature hole is mostly gone at the API/engine-seed level.**
   Axeyum now has first slices for interpolation, CHC/PDR-style invariant
   discovery, and abduction. They are verify-guarded and honest, but narrow.
2. **The online-combination gap narrowed materially.** Online LRA/LIA theory
   solvers and online UFLRA/UFLIA Nelson-Oppen-style combination are now the
   default `check_auto` route for mixed UF+arithmetic, with eager Ackermann as a
   fallback. This is no longer "build the second theory"; it is "turn the
   enumerative DPLL(T) spine into a real CDCL(T) spine."
3. **The real gap is production depth.** Z3/cvc5 have mature reductions,
   inprocessing, strategy selection, theory plugins, and broad command surfaces.
   Axeyum has many columns, but too many are eager, bounded, partial, or
   validated instead of proof-carrying.
4. **The keystone gap is now quality and migration, not existence.** Z3's
   productive pattern is SAT + e-graph + theory extensions + tactics. cvc5's
   productive pattern is DPLL(T) + broad theories + proof accounting. Axeyum has
   the pieces and a default online UF+arith route; remaining work is theory
   propagation, 1-UIP over theory explanations, relevance, and migrating arrays,
   BV laziness, datatypes, and quantifiers onto the spine.
5. **Axeyum's differentiator is real.** Pure Rust default, universal model replay,
   DRAT/Farkas/miter checking, and verify-before-return generators are stronger
   than a normal "young SMT solver" story. Do not lose that by copying Z3/cvc5
   features without checkers or trust-ledger entries.

Practical conclusion: **do not chase new theory columns next.** Close the
performance and integration gap first, then deepen the existing columns.

## What Z3 and cvc5 are asking us to match

Z3 is the performance/integration target:

- Per-logic tactic scripts and probes choose preprocessing, bit-blasting, SMT,
  fixedpoint, or optimization paths dynamically.
- Its QF_BV strength is not just bit-blasting. It is `solve_eqs`,
  value propagation, unconstrained elimination, `bv_slice`, bounds, sharing,
  lazy/delayed hard-operator blasting, AIG simplification, and a mature SAT core.
- Its SMT strength is the e-graph/CDCL(T) loop: theory plugins, explanations,
  relevancy, interface equalities, and model construction.
- Its verification strength for CHC is muZ/SPACER, not just bounded model
  checking or k-induction.

cvc5 is the breadth/proof/interface target:

- It documents support for all standardized SMT-LIB theories plus extensions
  such as bags, datatypes, finite fields, separation logic, sequences, sets and
  relations, strings, and transcendentals.
- It exposes proof production with CPC and external proof formats, and its NEWS
  tracks increasing proof coverage.
- It exposes SyGuS, interpolation, abduction, next-solution APIs, model blocking,
  diagnostic outputs, and many SMT-LIB command surfaces.
- It accepts that some extensions are experimental or outside safe mode. That is
  a useful precedent: breadth is allowed, but it must be labeled.

## Gap 1: measured performance, not feature count

Current axeyum state:

- Full scalar QF_BV lowering exists and `sat` replay is strong.
- Native proof-producing CDCL has become competitive with the current Rust SAT
  route on the profiled hard instance.
- The current tracker records near-parity on the small p4dfa pulse, but not broad
  Z3-class performance. A HEAD re-measure after 100+ commits was sound
  (0 disagreements / replay failures / errors) but load-sensitive at the 20 s
  boundary: 7/113 under contention versus the committed 8/113 baseline.
- Route-trace telemetry exists, so future benchmark artifacts can explain which
  path declined instead of just counting `unknown`.

Z3/cvc5 gap:

- Z3 has years of reduction, tactic selection, and SAT inprocessing before the
  final SAT solve. cvc5 often delegates SAT to modern engines and has broad
  preprocessing/proof infrastructure.

Practical next move:

- Keep the KPI as **Timeout -> decided** on the committed public slice.
- Split every unknown into `EncodingBudget`, `SearchBound`, `LargeCnf`,
  unsupported, and real timeout.
- Re-run the authoritative QF_BV pulse under idle-machine conditions and include
  route traces / inprocessing stats.
- Refresh `docs/plan/references/axeyum-current-state.md`; it is now stale
  relative to the capability ledger and STATUS.

Exit signal:

- A committed head-to-head artifact where the same query set, same wall budget,
  same memory cap, and same replay policy show competitive PAR-2 and no
  disagreements.

Do not:

- Sweep the full public corpus.
- Tune the SAT core in isolation when reduction is still producing oversized CNF.

## Gap 2: word-level reduction before bit-blasting

Current axeyum state:

- The canonicalizer is sound and conservative.
- The model-reconstruction trail, `propagate_values`, `solve_eqs`, and
  `elim_unconstrained` have landed as opt-in preprocessing.
- The plan correctly identifies reduction as the near-term lever after the p4dfa
  reframe.
- The repo already has a coordination rule: another agent owns
  `axeyum-rewrite` / `axeyum-smtlib`, so this needs coordination.

Z3/cvc5 gap:

- Z3's tactic stack routinely applies `solve_eqs`, value propagation,
  unconstrained elimination, bit-vector slicing, bounds simplification, term-ITE
  handling, sharing maximization, and AIG cleanup before SAT.

Practical next move:

1. Measure the landed preprocessing on the public p4dfa pulse under the same
   admission caps.
2. Add `max_bv_sharing` and `bv_slice` / upper-bit constant extraction next.
3. Add AIG two-level cleanup only after the word-level passes show their effect.
4. Re-measure after each pass and keep the route/decline reasons in the artifact.

Exit signal:

- More p4dfa instances move from `EncodingBudget` to decided under the same CNF
  caps, with original-query replay preserved.

Do not:

- Add equisatisfiable reductions without model projection and tests.

## Gap 3: SAT inprocessing with proof accounting

Current axeyum state:

- The proof-producing CDCL core emits DRAT and is checked.
- It has modern basics now: 1-UIP, watches, VSIDS heap, packed arena, learned
  clause minimization.
- Subsumption, self-subsuming resolution, BVE, compaction, and the XOR
  preprocessing foundation have landed and are wired behind config.
- Vivification has landed in `axeyum-cnf` with DRAT accounting and randomized
  equivalence/model-preservation checks. It still needs benchmark-pipeline
  integration and measurement.
- Glue-tier deletion policy, SCC/equivalent-literal substitution, probing, and
  proof accounting for every enabled pipeline route remain.

Z3/cvc5 gap:

- Z3 has BVE, subsumption, self-subsuming resolution, SCC/equiv-lit
  substitution, vivification, probing, BIG, AIG/XOR recovery, clause trimming,
  and DRAT/RAT handling for simplifying steps.
- cvc5 has improved proof support over its SAT backends, including CaDiCaL
  proof support in recent releases.

Practical next move:

1. Wire optional vivification into the SAT-BV inprocessing pipeline, with stats
   and a deadline cap.
2. Measure `subsumption+BVE+compact` versus `+vivify` on the same admitted
   instances.
3. Add glue/LBD tiering for learned-clause retention.
4. Emit and check DRAT/RAT for every enabled inprocessing route before
   enabling by default in proof mode.

Exit signal:

- Fewer CNF variables/clauses and lower PAR-2 on the same admitted instances,
  with DRAT still checked in proof mode.

Do not:

- Enable inprocessing in high-assurance mode until its proof steps are checked
  or explicitly ledgered.

## Gap 4: strategy and tactic assembly

Current axeyum state:

- `check_auto_explained` and `RouteTrace` have landed as a verdict-invariant
  diagnostic layer: the central dispatcher records every route tried and every
  decline reason without changing control flow.
- This is not yet a tactic language: no probe-guided scheduler, no per-logic
  scripts, and no benchmark-visible strategy tree beyond the trace.

Z3/cvc5 gap:

- Z3 exposes a large tactic/probe system and per-logic strategy scripts.
- cvc5 exposes many options and diagnostic outputs that let users and
  developers understand the chosen route.

Practical next move:

- Feed `RouteTrace` into benchmark artifacts and the SMT-LIB diagnostics surface.
- Build the small scheduler: `Strategy = probe -> ordered routes`, with
  per-logic scripts for `QF_BV`, `QF_UF`, `QF_LRA/LIA`, `QF_NRA/NIA`, strings,
  and reachability.
- Keep the recorder verdict-invariant; strategy changes must be separate,
  benchmarked deltas.

Exit signal:

- The benchmark artifact explains which route was chosen and why every fallback
  happened.

## Gap 5: the e-graph/CDCL(T) spine

Current axeyum state:

- There is an e-graph crate and it already supports important pieces:
  congruence, explanations, UF, and e-matching.
- Online LRA and LIA theory solvers exist with backtrackable assert/push/pop and
  differential validation against the trusted offline arithmetic routes.
- Online UFLRA and UFLIA combination are now the default mixed UF+arithmetic
  routes in `check_auto`; they handle Boolean structure through enumerative
  DPLL(T) and theory-conflict blocking, with eager Ackermann as fallback.
- Arrays, BV laziness, datatypes, and quantifiers are not yet migrated onto this
  common online spine.

Z3/cvc5 gap:

- Z3's mature path uses SAT assignment + e-graph + theory plugins +
  lazy explanations.
- Theory solvers share equalities, propagate consequences, explain conflicts,
  and construct one coherent model.

Practical next move:

1. Replace model-enumeration/blocking with real CDCL(T): theory propagation,
   lazy antecedents, and 1-UIP conflict learning over theory explanations.
2. Add relevance filtering so irrelevant atoms do not flood theories.
3. Migrate lazy arrays and lazy BV onto the spine first; they are the direct
   performance unlocks.
4. Then migrate datatypes and quantifier rounds.

Exit signal:

- A mixed UF+arith query is solved by online CDCL(T) with learned theory clauses
  and propagated literals, not by propositional-model enumeration; every theory
  conflict has an independently checkable explanation or a ledgered trust ID.

Do not:

- Build special lazy loops per theory. The value is the shared spine.

## Gap 6: arrays and symbolic memory

Current axeyum state:

- Eager read-over-write + Ackermann elimination remains the broad fallback.
- Lazy select-congruence and array-extensionality refutations have landed for
  useful unsat cases.
- Symbolic memory works, but the warm incremental path is not yet a full lazy
  array solver over store chains.

Z3/cvc5 gap:

- Lazy read-over-write instantiation, extensionality lemmas, array models with
  finite maps and else values, and integration with the equality bus.

Practical next move:

- Implement lazy `select(store(...))` axiom instantiation on e-graph class
  merges; this is the missing store-chain scalability step.
- Add on-demand diff skolems for the remaining extensionality/model cases.
- Build array model projection with explicit else values.

Exit signal:

- BMC/symexec over store chains scales without re-eliminating the full memory
  formula at every depth.

## Gap 7: LIA depth

Current axeyum state:

- LIA is validated, with branch-and-bound/simplex and checked bounded UNSAT
  export in some routes.
- Interpolation for LIA exists via rational relaxation plus verification.
- Multi-equation Diophantine infeasibility now decides equality systems that
  are rational-feasible but integer-infeasible.
- Online LIA, `mbp_lia`, LIA PDR, and LIA IMC exist; each is verify-guarded.
- Inequality-integrated cuts and Gomory/cube-style cuts remain.
- Disjunctive integer interpolation is still partial: LIA IMC uses the
  conjunctive interpolant and honestly declines where the LRA CNF route can
  handle disjunctive fixpoints.

Z3/cvc5 gap:

- Mature integer arithmetic uses GCD tests, Gomory cuts, HNF/cube tests,
  Diophantine reasoning, branch-and-bound, and careful explanation production.

Practical next move:

1. Add a disjunctive `lia_interpolant_cnf` analogue, or a guarded fallback, so
   LIA IMC does not stop at Boolean-structured frontiers.
2. Extend the Diophantine/GCD route from equality systems into inequalities
   where a small, checkable contradiction row exists.
3. Add Gomory fractional cuts with explanation.
4. Add cube/HNF cuts only after the first three measurably reduce unknowns.

Exit signal:

- The cuts-needed LIA interpolation/refutation examples no longer decline, and
  generated cuts carry checkable or re-verifiable explanations.

## Gap 8: NRA/NIA proof and classification

Current axeyum state:

- NRA has a strong CAD decision side and exact algebraic witnesses.
- NIA has sound small-witness SAT and narrow unsat deciders, but real
  multivariate nonlinear integer completeness remains open.
- General CAD UNSAT proof/evidence is not yet at the Lean/checker bar.

Z3/cvc5 gap:

- Z3 has nlsat and nonlinear arithmetic integration; cvc5 has cylindrical
  algebraic covering work and proof-mode constraints around safe features.

Practical next move:

1. Promote the fuzz unknown deltas to reproducible bench artifacts.
2. Classify remaining QF_NIA unknowns into proof gap, true nonlinear-int
   incompleteness, and resource refusal.
3. Add evidence for general CAD UNSAT before expanding more nonlinear syntax.

Exit signal:

- A committed artifact explains every remaining NRA/NIA unknown bucket, and at
  least one general CAD UNSAT route carries independent checker evidence or a
  precise trust-ledger entry.

## Gap 9: quantifiers

Current axeyum state:

- Finite-domain expansion, e-graph-aware e-matching, a fixpoint loop, MBQI, and
  LRA/LIA MBP first slices exist.
- Trigger inference has landed for the current e-matching path.
- This is enough for selected refutations and PDR prerequisites, not
  production quantifier solving.

Z3/cvc5 gap:

- Z3 has pattern inference, MAM-style e-matching, instance cost/fingerprint
  management, MBQI, QSAT, and MBP across theories.
- cvc5 has strong SyGuS/quantifier integration, pools, and enumerative
  instantiation options.

Practical next move:

1. Add deterministic instance fingerprints, cost controls, and telemetry.
2. Extend MBP beyond the current one-variable/unit-coefficient slices.
3. Integrate quantifier rounds into the CDCL(T) final-check loop, not as a
   separate eager pass.

Exit signal:

- Quantified UFLIA examples produce a bounded sequence of explained
  instantiations and either a checked ground refutation or honest `unknown`.

## Gap 10: strings and sequences

Current axeyum state:

- Strings are bounded and BV-lowered, with many operations wired but still
  experimental.
- There is no first-class unbounded sequence solver.

Z3/cvc5 gap:

- Z3 has strings, regex, sequences over arbitrary base sorts, map/fold, and
  length-guided solving.
- cvc5 supports standardized strings and extended sequences, with strong
  string/sequence-specific solving.

Practical next move:

- Stop adding bounded string operators unless they are needed for a benchmark.
- Write the native unbounded string/sequence design first:
  length arithmetic, concat decomposition, regex automata, word equations, and
  model construction.
- Decide which part rides the CDCL(T) equality bus and which part is a
  specialized solver.

Exit signal:

- A small QF_SLIA corpus solves without a global byte bound and returns concrete
  string models.

## Gap 11: breadth tail

Current axeyum state:

- The backlog is counted: sequences, sets/bags/relations, separation logic,
  finite fields, co-datatypes, recursive functions, and the NIA tail.

Z3/cvc5 gap:

- cvc5 is materially ahead on sets, bags, finite fields, separation logic, and
  SyGuS-facing breadth.
- Z3 is materially ahead on recursive functions, sequences, fixedpoints, and
  tactic integration.

Practical next move:

- Keep every item behind the e-graph/CDCL(T) gate unless a customer benchmark
  forces it.
- If one breadth item must start early, finite fields are the cleanest because
  they can share polynomial machinery with the NRA/NIA work.

Exit signal:

- A new breadth item gets its own phase doc, capability row, semantics note,
  model replay, and proof/trust entry before becoming public surface.

## Gap 12: CHC/PDR beyond the first slice

Current axeyum state:

- `prove_safety_pdr` provides verify-guarded single-predicate IC3/PDR over
  transition systems.
- `Safe` is checked by initiation, consecution, and safety queries; `Reachable`
  is BMC-confirmed.
- LRA and LIA MBP exist as predecessor-generalization primitives.
- LRA/LIA PDR and LRA/LIA IMC exist. The LIA IMC path is partial where
  disjunctive interpolation is needed.
- `solve_horn` now handles single-predicate, acyclic multi-predicate,
  mutually-recursive linear systems, and stratified-nonlinear bodies by verified
  reduction/projection.

Z3/cvc5 gap:

- Z3's muZ/SPACER is a full CHC/fixedpoint engine with multi-predicate Horn
  clauses, theory-aware generalization, and rich front-end support.

Practical next move:

1. Add the disjunctive LIA interpolant needed by integer IMC.
2. Add genuine nonlinear recursive Horn support, not only stratified folding.
3. Push Horn parsing / fixedpoint command support only for the shapes
   `solve_horn` can verify.
4. Start proof/evidence packaging for returned Horn invariants beyond the
   current verify-before-return checks.

Exit signal:

- A multi-predicate linear-arithmetic CHC benchmark proves safe without reducing
  to a single transition system, and the returned invariant is independently
  checked.

## Gap 13: interpolation, abduction, and synthesis surfaces

Current axeyum state:

- Interpolation covers LRA, LIA, EUF, SAT, QF_BV, UFLRA, and UFLIA, all
  verify-before-return.
- Abduction is no longer only a syntactic-atom enumerator: it can synthesize
  shared-term equalities and arithmetic comparisons, a SyGuS-lite slice.
- There is not yet a full SMT-LIB `(get-interpolant)` / `(get-abduct)` parser
  surface, and no SyGuS grammar-driven synthesis engine.

Z3/cvc5 gap:

- cvc5 exposes grammar-restricted abduction/interpolation and next-solution
  APIs, plus SyGuS solving.

Practical next move:

1. Add the SMT-LIB parse/driver surface for `get-interpolant` and `get-abduct`
   in coordination with the `axeyum-smtlib` owner.
2. Extend abduction from atom enumeration to grammar-restricted CEGIS.
3. Share the candidate verifier with SyGuS solution checking.

Exit signal:

- Text input can request an interpolant or abduct, the answer is verified before
  printing, and unsupported grammars decline cleanly.

## Gap 14: proof production above CNF

Current axeyum state:

- Strong pieces exist: model replay, DRAT, Farkas, bit-blast miter,
  checkable PDR obligations, and verify-before-return generators.
- Alethe and Lean work is no longer just planned: the repo has an in-tree
  Alethe checker/emitter path, external Carcara cross-check coverage for key
  fragments, a Lean-grade kernel, and Lean reconstruction for several fragments.
- Covered array/Ackermann/datatype fragments already have zero-trust or
  self-checking Alethe routes in the evidence path.
- The remaining proof gap is specific: reductions and theory families such as
  general read-over-write, int-blast, preprocessing eliminations, general
  CAD/NRA, NIA cuts, strings, and FP arithmetic are not yet systematically
  proof-carrying.

Z3/cvc5 gap:

- cvc5 exposes CPC and translations to external proof formats; its safe/stable
  modes are explicitly tied to proof/model robustness.
- Z3 has proof infrastructure, but its practical user story is less proof-first
  than cvc5's.

Practical next move:

1. Stabilize/extract the typed Alethe IR boundary so it is not just an internal
   proof utility.
2. Close the remaining QF_BV arithmetic bitblast and Carcara coverage gaps.
3. Finish the open reduction seams: general ROW-distinct/read-over-write,
   int-blast rewrites, and preprocessing eliminations.
4. Start evidence for the hard theory frontiers: CAD/NRA and NIA cuts, then
   strings and FP arithmetic.

Exit signal:

- A reduction-heavy UNSAT query outside the already-covered fragments produces
  an SMT-level proof checked by the in-tree route and, where applicable,
  Carcara/Lean.

## Gap 15: command surface and developer diagnostics

Current axeyum state:

- SMT-LIB parsing is good for the supported benchmark slice and some string
  surface.
- Full command support is not there: interpolation/abduction text commands,
  reset/option surfaces, fixedpoint, SyGuS, richer diagnostics.
- Route-trace diagnostics exist at the Rust API level but are not yet surfaced
  through text or benchmark artifacts.

Z3/cvc5 gap:

- Both solvers are tools as much as libraries: users can inspect options,
  assertions, proofs, models, learned literals, unsat cores, diagnostic outputs,
  optimization state, and fixedpoint/SyGuS results.

Practical next move:

- Add command support in the order that exposes already-verified engines:
  `(get-interpolant)`, `(get-abduct)`, `(get-proof)` for supported proof routes,
  then route-trace / reason-unknown diagnostics.

Exit signal:

- A benchmark or user script can reproduce the same Rust API behavior through
  SMT-LIB text, including checked declines.

## What axeyum should deliberately not copy

- Do not make native C/C++ solver dependencies part of the default path.
- Do not expose a feature column just because Z3/cvc5 have it; require replay,
  checker, or a trust-ledger entry.
- Do not build per-theory ad hoc laziness. The shared CDCL(T) spine is the
  compounding asset.
- Do not treat "experimental" as a problem. cvc5 uses that category too. The
  problem is unlabeled experimental behavior.
- Do not claim parity from first slices. PDR, interpolation, and abduction are
  opened, not done.

## Recommended next 10 increments

1. Refresh `docs/plan/references/axeyum-current-state.md` against the current
   ledger and STATUS; the 2026-06-15 audit predates major interpolation/PDR/NRA,
   online-combination, vivification, Horn, and route-telemetry work.
2. Commit a reproducible current Z3 head-to-head dashboard for the small QF_BV
   pulse and the easy public slice, with route traces and inprocessing stats.
3. Wire optional vivification into the SAT-BV inprocessing pipeline; measure
   `subsumption+BVE+compact` versus `+vivify`.
4. Add and measure `max_bv_sharing` or `bv_slice` as the next word-level
   reduction variable.
5. Turn online UF+arith from enumerative DPLL(T) into real CDCL(T): theory
   propagation, lazy antecedents, and 1-UIP theory-clause learning.
6. Migrate lazy arrays/store axioms onto the online spine.
7. Add disjunctive LIA interpolation to close the integer IMC frontier.
8. Add SMT-LIB `(get-interpolant)`, `(get-abduct)`, and route-trace /
   reason-unknown surfaces once parser coordination is clear.
9. Continue the NRA/NIA certify-gap: general CAD UNSAT and NIA cuts first.
10. Stabilize/extract the typed Alethe boundary and close remaining reduction
    proof seams: general ROW, int-blast rewrites, preprocessing eliminations.

## Bottom line

The gap is no longer "we lack the big three engines." It is:

- **Z3-class performance discipline:** reductions, inprocessing, tactics, and
  measured routing.
- **Z3-class integration quality:** online e-graph/theory combination exists for
  UF+arith; the gap is now true CDCL(T) propagation/learning/relevance and
  migration of arrays/BV/datatypes/quantifiers onto that path.
- **cvc5-class breadth and surfaces:** strings/sequences, sets/bags, finite
  fields, separation logic, SyGuS, proof commands, diagnostics.
- **Axeyum-class proof rigor:** carry the current checkability discipline upward
  instead of diluting it as breadth grows.

The constructive route is therefore narrow but compounding: reduce before SAT,
proof-account inprocessing, make CDCL(T) the spine, and retire trusted
reductions with Alethe one at a time.
