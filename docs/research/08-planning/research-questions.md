# Research Questions

Status: draft
Last updated: 2026-07-22

## Purpose

Track the questions that should drive experiments and architecture decisions.

## Scope

In scope:

- Open questions across logic, architecture, data structures, algorithms, verification,
  and Rust implementation.

Out of scope:

- Issue tracker replacement.

## Core Claims

- Research questions should be written down before implementation choices harden.
- Each question should eventually resolve into an ADR, benchmark, implementation
  result, or explicit deferral.

## Questions

### Logic And IR

- [x] Should `Bool` and `BV(1)` be distinct in every layer?
  - Answer: yes for the current public IR and backend surface; see
    [ADR-0003](../09-decisions/adr-0003-m0-ir-representation.md).
- [x] Should arrays be in the first public IR?
  - Answer: arrays were added after the scalar core was solid, not in the very
    first IR. The IR now has an `Array` sort and `select`/`store` with a direct
    read-over-write evaluator; see
    [ADR-0010](../09-decisions/adr-0010-arrays-via-eager-elimination.md).
- [x] Should uninterpreted functions be first-class early?
  - Answer: yes, as a first-class IR construct (declarations with a typed
    signature, `Op::Apply`, and a `FuncValue` interpretation in the model that
    the evaluator honors), eliminated to `QF_BV` by Ackermann reduction — the
    same eager strategy as arrays. Sub-increments 1 (IR + evaluator) and 2
    (`eliminate_functions` + `check_with_function_elimination` end-to-end
    `QF_UFBV` solving with `FuncValue` model projection) are done, as is the
    SMT-LIB I/O round-trip (n-ary `declare-fun` + applications) and `QF_AUFBV`
    theory composition (`check_with_arrays_and_functions`: array then function
    elimination with combined model projection and replay) and oracle-free
    `QF_UFBV` scenarios (`function_catalog`). The EUF rollout now matches the
    array track end to end. Array equality is no longer wholly deferred:
    canonical ABV/AUFBV has bounded diff witnesses and candidate-guided observed
    reads; each flag retains its original equality on live backtrackable
    `EufTheory`, true direct-symbol classes share one replayed model, and
    candidate-violated base and store-parent reads follow explanation-guarded
    final e-class merges (ADR-0073/0077/0078/0080). Violated local ROW sites and
    pair-generated UF/select/extensionality scalar interfaces now append or
    activate aligned theory atoms and permanent clauses inside the same retained
    canonical search (ADR-0081/0082). Canonical finite-scalar
    admission now covers Bool or BitVec independently at each component while
    other component theories still decline (ADR-0079). Array-valued function
    results now retain their original application parents on the e-graph,
    project fresh result arrays by final parent class, build function tables
    after array projection, and replay through `select`, `store`, array `ite`,
    equality, and nested scalar-UF use (ADR-0084). Exact array-ITE equality
    decomposition and bounded observed-read-preserving store/ITE/constant class
    realization now close the structural total-model boundary (ADR-0085).
    Bounded warm structural ownership is retained by ADR-0086; ADR-0087 makes
    its exact transitive summaries candidate-triggered and persistent. ADR-0088
    retains scalar-keyed array-valued UF application parents, conditional read
    congruence, and full-value result projection on the same warm path. Warm
    projection-owned equality and exact structural diff witnesses now stay warm
    under ADR-0089. ADR-0090 retains positive structural equality, ADR-0091
    retains Boolean relation flags, ADR-0092 admits direct array-valued UF
    parameters, ADR-0093 admits supported structural array-valued UF
    parameters, and ADR-0094 admits supported nested array-valued application
    keys; nested/extended array operators and proofs remain.
    See
    [ADR-0013](../09-decisions/adr-0013-uninterpreted-functions.md) and
    [ADR-0084](../09-decisions/adr-0084-array-valued-uf-results-on-the-canonical-array-bus.md),
    followed by
    [ADR-0085](../09-decisions/adr-0085-bounded-structural-array-class-equations.md),
    [ADR-0086](../09-decisions/adr-0086-retained-warm-structural-array-reads.md),
    and
    [ADR-0087](../09-decisions/adr-0087-candidate-triggered-retained-warm-row.md),
    followed by
    [ADR-0088](../09-decisions/adr-0088-retained-warm-array-valued-uf-parents.md)
    and
    [ADR-0089](../09-decisions/adr-0089-retained-warm-array-relations.md),
    [ADR-0090](../09-decisions/adr-0090-retained-warm-structural-array-equality.md),
    [ADR-0091](../09-decisions/adr-0091-retained-warm-boolean-array-relation-flags.md),
    [ADR-0092](../09-decisions/adr-0092-retained-warm-direct-array-valued-uf-parameters.md),
    [ADR-0093](../09-decisions/adr-0093-retained-warm-structural-array-valued-uf-parameters.md),
    and
    [ADR-0094](../09-decisions/adr-0094-retained-warm-nested-array-valued-uf-parameters.md).
- [ ] How should undefined or partial operations be represented?
- [ ] What public support matrix should define the first release boundary
      across IR, evaluator, SMT-LIB, oracle, pure Rust backend, and evidence?

### Rewriting

- [x] Which rewrites are always-on?
  - Answer: the first default set is exact-denotation only: Boolean/BV
    constant folds, simple Boolean identities, equality and ITE identities,
    and BV zero/one/all-ones, shift-zero, whole-extract, zero-extension, and
    rotate-zero identities. Equisatisfiability-only rewrites remain disabled
    until model projection exists.
- [x] How are rewrite proofs or obligations represented?
  - Answer: the Phase 3 manifest records stable rule IDs, preconditions,
    preservation class, projection obligations, and required test routes; see
    [ADR-0005](../09-decisions/adr-0005-phase3-query-evidence-rewrite-contracts.md).
- [ ] Should equality saturation be an optional optimizer?
- [x] Are equisatisfiability-only rewrites allowed before model projection is
      implemented, or must the first default rule set be denotation-preserving?
  - Answer: they may be recorded while disabled, but default rewrites must be
    denotation-preserving until model projection is implemented and tested; see
    [ADR-0005](../09-decisions/adr-0005-phase3-query-evidence-rewrite-contracts.md).

### Solvers

- [x] What is the first native backend?
  - Answer: Z3 as a feature-gated oracle; see
    [ADR-0001](../09-decisions/adr-0001-vertical-slice-first.md) and
    [ADR-0002](../09-decisions/adr-0002-ground-up-identity-oracle-bootstrap.md).
- [x] Which pure Rust SAT solver is the first adapter?
  - Answer: `rustsat-batsat` through RustSAT; see
    [ADR-0007](../09-decisions/adr-0007-first-pure-rust-sat-adapter.md).
- [x] When is a custom CDCL implementation justified?
  - Answer: a first *proof-producing* core is justified now by proof production
    (not performance) — DPLL with conflict-cube learning that emits DRAT,
    verified by `check_drat`, giving end-to-end checked `unsat`; see
    [ADR-0012](../09-decisions/adr-0012-proof-producing-sat-core.md). The core
    now uses **1-UIP** conflict analysis and **two-watched-literal**
    propagation (validated by a randomized differential test vs the adapter);
    restarts/heuristics and becoming the default solver remain gated by the
    benchmarking methodology on SAT time dominating.
- [x] What is the minimum incremental-solving API?
  - Answer: a warm SAT layer with monotone clause addition plus
    one-shot assumption literals, and a high-level `Solver` façade exposing
    `assert`/`push`/`pop`/`check`/`check_assuming` over it; `push`/`pop` map to
    selector (assumption) literals. Implemented as `IncrementalSat`
    (`axeyum-cnf`), persistent `IncrementalLowering`/`IncrementalCnf`, and
    `IncrementalBvSolver`; see
    [ADR-0009](../09-decisions/adr-0009-incremental-sat-and-solving.md).
    [ADR-0201](../09-decisions/adr-0201-first-class-incremental-solver-trait.md)
    adds an object-safe `IncrementalSolver` trait only for genuinely retained
    sessions; one-shot snapshot resubmission does not satisfy that cost model.
- [x] Should Phase 2 include a second native SMT backend?
  - Answer: defer it until a concrete Phase 5 differential-testing or
    trait-design need appears; see
    [ADR-0004](../09-decisions/adr-0004-defer-second-native-backend.md).

### Encodings

- [x] AIG first, or direct CNF?
  - Answer: AIG first, then simple Tseitin CNF; direct term-to-CNF lowering is
    not a public Phase 4 path. See
    [ADR-0006](../09-decisions/adr-0006-phase4-bit-order-and-lowering-entry-contract.md).
- [x] What bit-order convention is public across evaluator values, wire
      vectors, DIMACS lift maps, and model reconstruction?
  - Answer: LSB-first. A `BV(w)` lowers to wires where element `i` is SMT-LIB
    bit index `i` with numeric weight `2^i`; constants, models, and lift maps
    all use the same shared conversion routines. See
    [ADR-0006](../09-decisions/adr-0006-phase4-bit-order-and-lowering-entry-contract.md).
- [ ] How are symbolic shifts encoded?
- [x] When do multiplication and division enter the supported subset?
  - Answer: all entered in Phase 5 (2026-06-13). Multiplication (`bvmul`,
    truncated shift-and-add), unsigned division/remainder (`bvudiv`/`bvurem`, a
    combinational restoring divider with SMT-LIB divide-by-zero totality), and
    signed division/remainder/modulo (`bvsdiv`/`bvsrem`/`bvsmod`, sign-handling
    wrappers over the unsigned divider) all lower, each verified exhaustively
    against the ground evaluator. This completes the **full scalar QF_BV
    operator set** for the pure-Rust backend; see the roadmap Phase 5 note and
    [foundational DAG](foundational-dag.md).
- [x] What array lowering comes first?
  - Answer: eager elimination to QF_BV — read-over-write plus Ackermann
    reduction — reusing the bit-blasting pipeline, with array-model projection;
    a lazy lemmas-on-demand procedure is deferred until eager blow-up is
    measured. See
    [ADR-0010](../09-decisions/adr-0010-arrays-via-eager-elimination.md).

### Evidence

- [x] What is the first checkable evidence artifact?
  - Answer: `sat` model replay through the ground evaluator, implemented in
    the solver tests and benchmark harness; see
    [ADR-0001](../09-decisions/adr-0001-vertical-slice-first.md).
- [ ] Should unsat proof checking be required in high-assurance mode?
  - In progress: an independent in-tree DRAT checker exists (RUP + RAT,
    `axeyum_cnf::check_drat`,
    [ADR-0011](../09-decisions/adr-0011-drat-unsat-proof-checking.md)), and a
    proof-producing SAT core (`solve_with_drat_proof`,
    [ADR-0012](../09-decisions/adr-0012-proof-producing-sat-core.md)) emits DRAT
    that the checker verifies — end-to-end checked `unsat` exists for the
    proof-core path. Making it the *required* high-assurance mode (and wiring it
    into `SatBvBackend` for QF_BV `unsat`) is the remaining step.
- [ ] How are model-lift maps serialized?
- [x] How should infinite-domain quantified `sat` witnesses be represented so
      the public result satisfies the original-term replay invariant?
  - Finding (2026-07-11): the current `∀∃` Skolem-witness and almost-uninterpreted
    MBQI checks can validate a quantified sentence mathematically, but return an
    ordinary `Model` that carries neither the Skolem function nor a replayable
    quantified certificate. The benchmark correctly rejects such a result when
    `eval` cannot enumerate `Int`/`Real`. Do not credit additional quantified
    `sat` rows until an ADR chooses between first-class Skolem/function models,
    a separately checked quantified-sat evidence artifact, or another route that
    preserves the hard rule that every public `sat` checks the original query.
  - Boundary update (2026-07-11): the UNSAT side does not wait on this decision.
    [ADR-0095](../09-decisions/adr-0095-checked-euclidean-residue-quantifier-evidence.md)
    establishes the targeted-CEGQI pattern: every accepted schema gets a
    separate original-IR checker and no search trace is trusted. The open choice
    here is specifically how a `sat` result discharges infinite-domain replay.
  - Answer (2026-07-11):
    [ADR-0096](../09-decisions/adr-0096-quantified-sat-skolem-certificates.md)
    keeps `CheckResult::Sat(Model)`, stores deterministic typed Skolem
    certificates in `Model`, and makes `check_model` the canonical replay front
    door. The certificate owns an affine recipe over original-arena atoms, so a
    cloned backend cannot leak synthesized `TermId`s. The first checker handles
    exact `forall* exists` affine/reflexive tautologies; ADR-0098 adds one exact
    positive-`or` guarded unit-gap theorem and recovers `sygus-infer-nested` with
    the global successor witness. Neither checker calls the search stack.
    [ADR-0121](../09-decisions/adr-0121-checked-reflexive-bitvector-skolem-witnesses.md)
    adds only the exact same-width BV identity encoding and reflexive
    signed/unsigned non-strict order. It recovers `issue4328-nqe`; all modular
    affine, offset, composite, and piecewise BV recipes remain rejected.
    [ADR-0122](../09-decisions/adr-0122-checked-vacuous-bitvector-guard-models.md)
    adds a separate outer-witness certificate: below one outer BV existential
    and a nonempty direct Bool/BV quantifier prefix, the checker independently
    proves an exact binder-to-constant equality antecedent false. It recovers
    `issue5365-nqe` without inspecting the implication consequent or granting
    general free-BV model/QE support.
    [ADR-0123](../09-decisions/adr-0123-checked-boolean-discharge-of-quantified-bv-closures.md)
    extends ADR-0107's syntax admission to Bool/Int/BV while keeping every
    non-reflexive BV predicate opaque. A carried complete free-Boolean model may
    certify the closure only when three-valued original-IR evaluation proves all
    BV values irrelevant; unresolved BV closures decline before LIA fallback.
    This recovers `model_6_1_bv` without adding general BV model construction.
    [ADR-0124](../09-decisions/adr-0124-source-bound-counterexamples-for-bv-quantifier-alternation.md)
    adds one checked UNSAT alternation class: concrete outer Bool/BV values are
    substituted into an exact closed `forall+ exists+` source matrix,
    existential binders are deterministically freshened, and a source-matched
    residual QF_BV DRAT is rechecked. Search remains untrusted and incomplete;
    broader QSAT, open formulas, functions, arithmetic, and Lean reconstruction
    remain open.
    [ADR-0125](../09-decisions/adr-0125-scaled-source-bound-bv-alternation-counterexamples.md)
    scales only that certificate's total-binder cap from 128 to 1,024, retaining
    the 4,096-node matrix cap and all replay conditions. This recovers the
    530-binder `bug802` hardware fixpoint without adding a new theorem matcher or
    general QSAT engine.
    [ADR-0126](../09-decisions/adr-0126-evaluator-replayed-negated-existential-witnesses.md)
    adds the direct dual source certificate for one exact top-level negated
    existential over a bounded closed Bool/BV body. Search proposes complete
    typed values, while the checker independently evaluates the untouched
    positive body to true. This recovers `NUM878`, `ari-syqi`, and
    `ari118-bv-2occ-x` without trusting NNF conversion or admitting open/nested
    formulas, arithmetic binders, functions, or general QSAT.
    [ADR-0127](../09-decisions/adr-0127-source-bound-conjunctive-bv-universal-instances.md)
    adds a premise-aware open-formula slice: one unique universal reached only
    through top-level conjunction nodes is weakened to a complete concrete
    Bool/BV source instance, and the checker regenerates the whole residual and
    rechecks its QF_BV DRAT/LRAT proof. This recovers
    `cond-var-elim-binary` without admitting non-conjunctive polarity contexts,
    multiple selected universals, functions, or general QSAT.
    [ADR-0128](../09-decisions/adr-0128-checked-vacuous-existential-prefix-counterexamples.md)
    adds a distinct closed-source UNSAT class: a checker proves a nonempty
    leading Bool/BV existential block absent from the following closed
    universal body, validates complete universal values, and directly evaluates
    the untouched body to false. This recovers `issue2031-bv-var-elim` without
    trusting prefix rewriting, inversion search, or general QSAT.
    [ADR-0140](../09-decisions/adr-0140-kernel-checked-vacuous-bv-existential-prefixes.md)
    closes its proof boundary with genuine `Exists.rec`, typed universal
    application, and kernel-checked computational AIG reduction.
    [ADR-0129](../09-decisions/adr-0129-checked-paired-existential-witness-transfer.md)
    adds a premise-aware paired-existential UNSAT class: a checker alpha-aligns
    equal typed witness tuples under exact shared ground premises and replays
    every target conjunct by identity, a source-bound `QF_BV` proof, or an exact
    signed-add lemma with all no-wrap side conditions. This recovers
    `nested9_true-unreach-call` without trusting existential normalization,
    model-guided projection, or general QSAT.
    [ADR-0130](../09-decisions/adr-0130-checked-affine-lsb-quantified-bv-models.md)
    adds the first relevant free-BV model class: exact affine GF(2) LSB
    invariants prove direct positive universals, while complete typed values
    evaluator-replay directly negated universals. This recovers
    `smtcomp-qbv-053118` without trusting quantifier erasure, MBQI candidates,
    parity normalization, or a solver-only witness.
    [ADR-0131](../09-decisions/adr-0131-checked-signed-interval-quantified-bv-models.md)
    adds a separate directly negated existential class: exact ground replay
    validates all division-bearing free-model facts and a nonempty signed
    interval proof establishes `lower <= upper <= cap`. This recovers
    `intersection-example-onelane` without trusting QF candidate obligations,
    division normalization, or implication vacuity.
    [ADR-0132](../09-decisions/adr-0132-checked-zero-product-quantified-bv-models.md)
    adds another separate directly negated existential class: a direct
    binder-free signed-division factor must evaluator-replay to zero before an
    exact source matcher annihilates its binder-bearing product and proves the
    signed nonnegativity leaf. This recovers `gn-wrong-091018` without
    interpreting its nonlinear binder polynomial or trusting a candidate
    rewrite.
    [ADR-0133](../09-decisions/adr-0133-checked-residual-qfbv-free-boolean-models.md)
    adds a distinct free-Boolean positive-universal route: bounded CEGIS uses
    source instances only as search refinements, while the checker rebuilds the
    exact negated `QF_BV` residual under the complete model and rechecks its
    source-bound DRAT/LRAT proof. This recovers `psyco-001-bv` without trusting
    quantifier erasure, candidate simplification, or accumulated instances.
    [ADR-0134](../09-decisions/adr-0134-checked-query-scoped-qfbv-universal-instances.md)
    gives accumulated instances a separate UNSAT contract: the checker binds
    the exact query, validates complete typed source tuples, rebuilds the
    positive-universal weakening and every instance, and rechecks the final
    QF_BV DRAT/LRAT proof. This recovers `psyco-107-bv` without trusting CEGIS
    candidate models, quantifier erasure, instance selection, or heuristic
    candidate blocks.
    [ADR-0135](../09-decisions/adr-0135-kernel-checked-query-scoped-bv-instances.md)
    reconstructs that bounded source shape with genuine typed universals:
    carried bindings become constructor witnesses, every residual assumption
    is derived from an untouched query axiom, and a compact named-gate Alethe
    tail is kernel-checked. Corpus-scale proof sharing remains a performance
    task rather than permission to weaken the source boundary.
    [ADR-0141](../09-decisions/adr-0141-checked-source-term-bitvector-skolem-witnesses.md)
    advances the nested-SAT boundary beyond the ADR-0121 identity: one exact
    source-reachable BV term over the universal binders, including a total UF
    application, may witness the existential only when independent substitution
    makes the untouched equality or non-strict order reflexive. Search cannot
    synthesize a detached recipe or grant SAT.
    Piecewise/general function interpretations, free-BV models beyond these
    affine-LSB/direct-witness/signed-interval/zero-product classes, broader
    free-Boolean residual proofs and general nested/alternating QSAT,
    serialization, and Alethe/Lean reconstruction remain implementation tasks,
    not permission to return an unchecked empty model.
- [x] How should targeted infinite-domain quantified `unsat` schemas receive
      evidence before a general quantifier proof format exists?
  - Answer (2026-07-11): search may propose only genuine universal instances
    and a ground refutation, but public certification comes from a separate
    small checker that independently re-matches an exact theorem over the
    original IR. [ADR-0095](../09-decisions/adr-0095-checked-euclidean-residue-quantifier-evidence.md)
    establishes the Euclidean-residue pattern;
    [ADR-0097](../09-decisions/adr-0097-checked-affine-growth-quantifier-evidence.md)
    confirms it on a positive-slope piecewise theorem using two consecutive
    counterexamples; [ADR-0099](../09-decisions/adr-0099-checked-nested-xor-quantifier-refutation.md)
    extends the pattern to one exact nested Boolean theorem using hierarchical
    universal instantiation; and
    [ADR-0100](../09-decisions/adr-0100-evaluator-replayed-closed-universal-counterexamples.md)
    makes a concrete original-binder assignment the generic certificate for a
    closed quantifier-free scalar universal, checked only by evaluating the
    untouched body; and
    [ADR-0101](../09-decisions/adr-0101-checked-finite-equality-partition-quantifiers.md)
    certifies closed nested Bool/Int formulas when every Int binder is observable
    only through finitely many equality-to-constant predicates. None of these
    checkers calls the search matcher or broad
    solver; open formulas, broader CEGQI/nested-QE schemas, and function-valued
    counterexamples need their own checker or a general checked proof calculus.
    [ADR-0102](../09-decisions/adr-0102-closed-universal-counterexamples-to-lean.md)
    separately closes the Lean boundary for ADR-0100's two current Int-equality
    rows by applying the original universal to its checked witnesses and proving
    the ground arithmetic result in the kernel; it deliberately does not turn
    the other structural certificates into opaque refuter axioms.
    [ADR-0103](../09-decisions/adr-0103-nested-xor-quantifiers-to-lean.md)
    applies the same bar to ADR-0099's complete signed/swapped nested-XOR class:
    two outer pivot applications plus one adjacent nested application close in
    the kernel through `Iff`, classical case analysis, and integer normalization.
    [ADR-0104](../09-decisions/adr-0104-euclidean-decomposition-prelude-and-quantifier-proofs.md)
    closes ADR-0095's two canonical residue rows by explicitly adding one
    standard existential Euclidean-decomposition theorem to the trusted integer
    prelude, then eliminating its quotient/remainder witnesses. This is a
    documented trusted-base expansion, not a query-specific refuter axiom, and
    introduces no div/mod proof operations.
    [ADR-0105](../09-decisions/adr-0105-affine-growth-quantifiers-to-lean.md)
    reuses that one theorem for ADR-0097's full checked affine-growth class:
    exact guarded proposition semantics for integer `ite`, two consecutive
    universal instances, positive-slope monotonicity, and a constructive
    double-negation argument close without another arithmetic or classical
    axiom.
    [ADR-0106](../09-decisions/adr-0106-single-pivot-equality-partitions-to-lean.md)
    closes the current ADR-0101 proof boundary for one literal per Int binder:
    genuine Bool/Int quantifiers are recursively eliminated with `Bool.rec` and
    one explicit standard integer equality-decidability theorem. The executable
    finite quotient remains untrusted guidance, and multi-constant partitions
    remain outside Lean proof credit.
    [ADR-0107](../09-decisions/adr-0107-checked-boolean-guard-models-for-quantified-sat.md)
    extends checked SAT replay to free-Boolean models of positive Bool/Int
    universals. Candidate generation may erase quantifiers, but replay rebuilds
    the exact negated universal closure, lifts integer `ite` with guarded
    equalities, source-binds LIA-DPLL theory cores, and uses DRAT for large
    propositional closure. Counterexample cubes affect search only. This closes
    both measured SAT affine-ITE rows without claiming general MBQI or function
    model construction.
    [ADR-0108](../09-decisions/adr-0108-checked-counterexample-covers-for-quantified-unsat.md)
    gives those sufficient cubes a separate UNSAT contract: each retained cube
    is independently refuted with an exact source-instantiated universal, and
    the complete set is accepted only when the weakened original skeleton plus
    every cube block is source-bound QF-unsatisfiable. The first Lean slice
    applies the original universal to every carried tuple and closes a bounded
    excluded-middle tree, so no cover-search result or evaluator fact becomes a
    refuter axiom. This closes the measured division at 12/12 checked/certified,
    8/8 kernel-checked UNSAT, and 12/12 dominant. ADR-0109 preserves repeated
    closed kernel-DAG nodes as deterministic Lean definitions and renders the
    computational `Bool` as a real inductive; the public module falls from
    151,845,067 to 2,682,977 bytes without changing evidence or trust. General
    alternation, functions, and sharing under open binder contexts remain open.
    [ADR-0110](../09-decisions/adr-0110-justified-lazy-quantifier-clause-scheduling.md)
    resolves the first lazy-clause soundness boundary: ground unit
    equality/disequality justifications may suppress a true instance or
    prioritize an all-false/unit-like one, but the solver still asserts the
    complete genuine source instance. A bare remaining literal is deferred
    until the online SAT/e-graph context can replay why every sibling is false.
    Incremental MAM matching and those detached-literal justifications remain
    open. [ADR-0111](../09-decisions/adr-0111-shared-incremental-ematching-session.md)
    resolves the first MAM ownership/performance boundary: compile and intern
    triggers once, extend one ground bridge monotonically, and share one
    round-local class/application index across all patterns. Public witness APIs
    remain complete and evidence still consumes genuine source instances. True
    [ADR-0112](../09-decisions/adr-0112-revision-checked-ematch-index-and-candidate-queues.md)
    adds revision-checked persistent class/application indexes plus root-symbol
    queues: add-only rounds extend from the node suffix and execute only affected
    patterns, while every real merge conservatively invalidates all patterns.
    [ADR-0113](../09-decisions/adr-0113-inverted-parent-merge-queues.md)
    resolves that merge boundary: union journals update retained indexes,
    transitive e-class parent paths queue only reachable trigger roots, and
    cached joins compare current roots.
    [ADR-0114](../09-decisions/adr-0114-compiled-ematch-parent-path-tries.md)
    compiles every occurrence's exact declaration/argument path into one shared
    trie and queues reached pattern terminals instead of all patterns sharing a
    root declaration.
    [ADR-0115](../09-decisions/adr-0115-eclass-label-and-ground-argument-path-filters.md)
    maintains exact backtrackable declaration sets on e-class roots, then checks
    nested occurrence labels and direct nullary ground siblings while traversing
    those paths.
    [ADR-0116](../09-decisions/adr-0116-generation-delta-ematch-candidate-queues.md)
    retains complete match caches but updates them only from newly added or
    merge-reached top applications. Every current bridge term is active-source
    relevant, so a relevance bit would be a no-op; generation-cost scheduling
    and bytecode remain measurement-gated.
    [ADR-0117](../09-decisions/adr-0117-source-bound-detached-quantifier-literal-propagation.md)
    closes the first detached-literal boundary: a public certificate reconstructs
    the exact source instance and replays each false sibling from named original
    equality/disequality facts before the remaining literal enters QF search.
    [ADR-0118](../09-decisions/adr-0118-bounded-recursive-quantifier-ground-provenance.md)
    closes the generated-premise chain: every admitted generated
    equality/disequality retains an exact-instance or prior-propagation
    derivation, and a depth/node-bounded checker requires the exact canonical
    table before that premise can justify a later detached literal.
    [ADR-0119](../09-decisions/adr-0119-checked-quantifier-clauses-in-retained-cdclt.md)
    closes direct equality-clause insertion: one retained CDCL(T)+EUF session
    backtracks each batch to level zero, appends root-stable atoms, and accepts
    only checked derivations. Online SAT is not a quantified verdict, and online
    UNSAT requires ordinary QF replay of the exact admitted set. Non-equality
    antecedents, SAT-trail-driven matching, and serialized online proof forms
    remain open.
    [ADR-0120](../09-decisions/adr-0120-scoped-sat-candidate-equality-ematching.md)
    resolves the measured trail-matching shape at final check rather than on
    every assignment: true candidate equalities enter one rollback matcher
    scope, exact merge paths queue only affected patterns/quantifiers, concrete
    tuples are materialized, and the scope is popped before complete source
    instances enter the checked retained-clause path. Candidate equalities can
    neither justify propagation nor enter evidence. High-frequency callbacks
    remain measurement-gated; non-equality antecedents and serialized online
    proof forms remain open.
- [x] What evidence envelope should carry semantics version, rewrite-rule
      version, bit-blaster version, CNF encoder version, SAT backend version,
      seed, resource limits, corpus hash, model replay, lift maps, and future
      proof artifacts?
  - Answer: use a layered, versioned envelope with source/query provenance,
    logic and semantics version, query schema, rule-set and later layer
    versions, resource config, replay results, projection/lift-map references,
    proof/checker references, and separated triage; see
    [ADR-0005](../09-decisions/adr-0005-phase3-query-evidence-rewrite-contracts.md).
    A first concrete `Evidence` type now realizes this:
    `axeyum_solver::Evidence` pairs a result with its justification (a `sat`
    model or an `unsat` DIMACS+DRAT certificate) and self-checks via
    `Evidence::check` (model replay / `check_drat` re-run). Versioned provenance
    fields are the remaining extension.
- [ ] How should evidence production expose the decisive route, ordered
      certificate attempts, source-to-lowered obligation identity, checker, and
      first uncertified boundary without conflating them with the arena-level
      auto-solver `RouteTrace`?
  - Proposed answer: a distinct, versioned `EvidenceTrace` threaded as an
    optional recorder through the same evidence-production control flow, with
    existing APIs as recorder-free wrappers and exact report/trace invariance
    gates; see
    [ADR-0341](../09-decisions/adr-0341-preregister-source-bound-evidence-route-telemetry.md).

### Incrementality And API

- [x] Assumptions-first or push/pop-first public API?
  - Answer: assumptions-first. `axeyum-query` carries assertions,
    assumptions, and scopes; one-shot solvers enforce assumptions as assertions,
    while future incremental backends can map them to native assumptions; see
    [ADR-0005](../09-decisions/adr-0005-phase3-query-evidence-rewrite-contracts.md).
- [x] What survives across queries: learned clauses, bit-blast caches, phases?
  - Answer: both. Stage 1 keeps the SAT clause database and learned clauses warm
    across solves (`IncrementalSat`); stage 2 keeps the bit-blast caches warm —
    a persistent AIG + term memo (`IncrementalLowering`) and per-node Tseitin
    (`IncrementalCnf`), driven by `IncrementalBvSolver`. Both implemented
    2026-06-13; see
    [ADR-0009](../09-decisions/adr-0009-incremental-sat-and-solving.md).
- [x] How must whole-snapshot and first-class direct-delta client profiles
      distinguish work?
  - Answer: a versioned warm record must name its entry mode and partition the
    complete query, translated roots, and root encodings into persistent versus
    temporary work. Historical snapshot schemas remain readable but cannot be
    silently reinterpreted; see
    [ADR-0202](../09-decisions/adr-0202-direct-delta-warm-profile-contract.md).
- [x] May depth-only direct-delta ownership replace serial snapshot sibling
      reuse by default?
  - Answer: no. Equal-depth siblings are not source-identical, and sharing a
    direct session by depth produced real wrong verdicts. Exclusive direct
    ownership restores soundness and beats equivalent snapshot entry, but
    fails the current serial-snapshot production time/RSS gate. ADR-0204 now
    supplies exact immutable source ancestry for the next candidate, but
    default admission still waits for both repeated controls; see
    [ADR-0203](../09-decisions/adr-0203-defer-glaurung-direct-delta-default.md)
    and
    [ADR-0204](../09-decisions/adr-0204-source-identity-direct-sibling-prefixes.md).
    The resulting two-driver production comparison passes, but the direct
    default remains deferred for `tcpip`/`dxgkrnl` widening and a rejected
    exclusive-control Z3-drift alarm; see
    [ADR-0205](../09-decisions/adr-0205-accept-source-prefix-production-gate.md).
- [x] May a synchronized direct-delta `Unknown` receive one same-session check
      under a fresh deadline by default?
  - Answer: yes, but only after the caller separately selects direct delta.
    The exact public replay accepts the mechanism and the repeated native
    production-topology gate binds findings, source-owner/serial-lease work,
    independent model replay, implementation revisions, time, RSS, and
    variance. One continuation defaults on with an explicit fail-closed off
    control; repeated nondecisions remain `Unknown`. Direct delta itself stays
    opt-in; see
    [ADR-0210](../09-decisions/adr-0210-exact-ordered-timeout-continuation-replay.md)
    and
    [ADR-0211](../09-decisions/adr-0211-accept-native-timeout-continuation-default.md).
- [ ] May source-identity direct delta become the downstream default across
      wider drivers?
  - Current boundary: not yet. A complete `dxgkrnl.sys` native replay proves
    exact no-op functionality when continuation is enabled, but the ordinary-
    core repetitions fail the predeclared 3% timing-CV alarm. Slower-core
    calibration crosses the 250 ms first-check boundary and changes actual
    outcomes, so it is not an exact no-op control. `win32k.sys` is a system-
    service/callout module rather than an IOCTL workload and cannot count as a
    zero-query success. Repeat in a quieter environment or add another valid
    no-timeout IOCTL driver; see
    [ADR-0212](../09-decisions/adr-0212-defer-dxgkrnl-direct-delta-admission.md).
- [x] What evidence boundary governs Axeyum/Glaurung paper performance claims?
  - Answer: product admission and optimization screening retain their exact
    work, replay, finding, resource, RSS, and regression-variance gates, but a
    headline paper claim additionally requires per-query paired both-decided
    statistics over at least five fixed-work repetitions, a topology-equivalent
    warm Z3 baseline plus a neutral backend, authoritative finding parity with
    canonical model selection where needed, and multi-oracle correctness
    support. Strict typing is the lead contribution; aggregate ratios remain
    descriptive until that boundary passes. See
    [ADR-0213](../09-decisions/adr-0213-publication-grade-glaurung-evidence-gate.md).
    The paired trace schema and analyzer mechanism are accepted in
    [ADR-0214](../09-decisions/adr-0214-paired-glaurung-trace-analysis.md). Its
    first clean DptfDevGen N=5 by three-timeout exercise passes, but it is an
    easy-driver no-timeout control. ADR-0215/0217 subsequently close the fair
    four-cell map; ADR-0222/0223/0232 add neutral cold-reset and retained
    topology controls; and ADR-0229 closes bounded four-driver sole-authority
    finding parity. ADR-0233 closes the timeout-sensitive neutral formula
    control with complete four-population accounting at 50/100/250/1000 ms and
    an all-decided 1000 ms tier. ADR-0236 then records the first stable tcpip
    any-model finding divergence and closes one opt-in canonical-authority cell
    with exact output and exploration-counter parity. Because canonicalization
    changes the shared finding population, wider/coverage-union authority work
    remains open, and none of the formula or authority controls replace fair
    retained-warm performance evidence. ADR-0237 separately closes the
    independent correctness-oracle gate: 12,000/12,000 QF_BV formulas agree in
    Axeyum, direct Z3, cvc5, and Bitwuzla; 4,471 SAT models replay and all 14
    declared edge families are nonvacuous under a correctness-only resource
    bound. This does not change the remaining wider real-manifest and
    finding-authority requirements.
- [x] How should a real-client shadow run preserve decided/nondecided splits?
  - Answer: only under an explicit combined-shadow diagnostic, atomically write
    the exact content-addressed SMT-LIB bytes and stable backend result classes
    whenever exactly one backend decides SAT/UNSAT. Do not count both-unknown
    rows, store unstable error text, or treat zero SAT/UNSAT disagreements as
    parity when unknown splits exist; see
    [ADR-0206](../09-decisions/adr-0206-glaurung-shadow-unknown-split-corpus.md).
- [x] What may an exact-verdict cache reuse without weakening evidence?
  - Answer: initially only an exact scalar SAT duplicate inside the same
    arena-bound `IncrementalBvSolver`, keyed by exact ordered assertion terms,
    scope boundaries, and one-shot-assumption terms and accepted only after
    original-term model replay. Ordinary UNSAT, `Unknown`, errors, and strict prefixes are
    not verdict-cache entries; UNSAT requires a source-bound rechecked proof,
    while prefixes reuse retained solver state. Storage and eviction are
    deterministic, bounded, observable, and disabled by default; see
    [ADR-0189](../09-decisions/adr-0189-replay-checked-same-arena-sat-duplicate-cache.md)
    and its bounded implementation in
    [ADR-0190](../09-decisions/adr-0190-opt-in-bounded-replay-checked-sat-cache.md).
    [ADR-0191](../09-decisions/adr-0191-glaurung-replay-sat-cache-measurement-control.md)
    wires the same boundary into a default-off path-owned Glaurung control;
    [ADR-0192](../09-decisions/adr-0192-accept-glaurung-path-owned-replay-cache-default.md)
    accepts that downstream default after the clean repeated client gate while
    leaving Axeyum's generic cache opt-in. Model verification on both fresh and
    cached SAT results shares only same-assignment evaluator values within one
    replay, under a fixed cross-root retention bound; it never persists trusted
    values across models or checks; see
    [ADR-0193](../09-decisions/adr-0193-bounded-shared-memo-model-replay.md).
    Empty warm-theory projection discovery may be bypassed only after the same
    complete scalar model is built and only when every active/one-shot array
    and UF projection class is empty; validation and original replay remain
    unchanged; see
    [ADR-0195](../09-decisions/adr-0195-skip-empty-warm-theory-model-projection.md).
- [x] Should solver cancellation support memory budgets as well as time?
  - Answer: yes; `SolverConfig` carries timeout, deterministic resource,
    memory, and node budgets. Memory-budget exhaustion is an `Unknown`
    classification, not an error.
- [ ] Frozen-arena type-state or runtime single-writer discipline?

### Formats

- [x] Full SMT-LIB script support or benchmark-slice parsing first?
  - Answer: benchmark-slice parsing first, implemented by ADR-0018 in
    `axeyum-smtlib`. The parser later expanded through arrays, UF, incremental
    queries, and additional theories; do not reuse the original slice boundary
    as current status. The live surface is the generated
    [command/API matrix](../../plan/generated/smtlib-api-conformance.md), and
    full ordered-session work is proposed in ADR-0342.
- [ ] Which SMT-LIB standard/theory versions should be pinned in artifacts
      and tests before adding conversion operators or future logics?
  - Proposed answer for the command/session surface: pin the official SMT-LIB
    2.7 release dated 2025-07-07 and implement the transactional state contract
    in [ADR-0342](../09-decisions/adr-0342-preregister-ordered-smtlib-session.md).
    The question remains open until the proposed transcript and Rust gates pass;
    theory-version pins remain separate per-theory obligations.
- [ ] When does BTOR2 import earn its keep?
- [x] Where does the format parser crate boundary land?
  - Answer: `axeyum-smtlib` is a dedicated crate because parsing/writing is
    exercised by solver tests and the benchmark harness, not just a CLI.

### Parallelism

- [ ] Is portfolio dispatch in scope for the first public release?
- [ ] What must be `Send`/`Sync` to make portfolio solving natural?

### Measurement And Benchmarking

- [ ] How should heterogeneous benchmark regimes share provenance without
      producing a false global parity score?
  - Proposed answer:
    [ADR-0343](../09-decisions/adr-0343-preregister-cross-regime-measurement-provenance.md)
    gives raw occurrences, normalized paths, exact contents, selection policy,
    row-local scoring, and oracle evidence separate identities. The first
    prototype finds 778 unique byte contents behind the scoreboard's 927
    file-backed occurrences and 99 exact-content overlaps with the 228-file
    public inventory. Acceptance remains open; semantic near-duplicate policy,
    official selection, and matched neutral-oracle populations are not yet
    resolved.
- [ ] What makes an interrupted distributed benchmark run safely resumable and
      its final population scoreable?
  - Proposed answer:
    [ADR-0344](../09-decisions/adr-0344-preregister-resumable-distributed-benchmark-execution.md)
    requires immutable per-result checkpoints, exact run/environment identity,
    explicit accounting for terminal-less attempts, complete shard manifests,
    strict merge, and aggregate resource enforcement. Its v2 correction adds
    typed process outcomes, observed/admitted verdict separation, per-result
    attempt ownership, and content-addressed outputs. The checked prototype
    exercises 18 invariants across 28 scenarios and makes deterministic
    interrupted/resumed scoring output byte-identical to an uninterrupted
    control. E1a passes local kill tests; the question remains open until E1b
    runner/solver/lease/output integration and E2-E3 resource/multi-host gates
    pass. The 64,345-case candidate must not be rerun first.

### Horizon: General Reasoning And Proving

- [x] What binder representation (de Bruijn, locally nameless, named with
      alpha-canonicalization) should the IR adopt when quantifiers arrive,
      and which arena/interning decisions today would foreclose options?
  - Answer (first slice): **named bound variables, reusing `SymbolId`** —
    `Op::Forall(SymbolId)`/`Op::Exists(SymbolId)` over a `Bool` body, so the
    ground evaluator works immediately by binding the symbol over its finite
    domain. Alpha-canonical interning is deferred (an efficiency, not soundness,
    concern); the binder representation may migrate to de Bruijn when
    capture-avoiding instantiation is built. See
    [ADR-0016](../09-decisions/adr-0016-quantifiers-binder-representation.md).
- [x] Which arithmetic enters first: QF_LRA simplex or QF_LIA on top of it?
  - Answer: **`QF_LIA` (integers) first, via bounded bit-blasting** onto the
    existing `QF_BV` pipeline — the cheapest trust-preserving first procedure
    (reuses model replay and the proof core); `sat` is sound and replayable,
    out-of-range is honest `unknown`, never `unsat`. Reals/simplex follow under a
    later ADR. The `Int` sort + evaluator and the bounded bit-blasting procedure
    (`check_with_int_blasting`: blast → solve → exact-integer replay) are both
    done. See [ADR-0014](../09-decisions/adr-0014-first-arithmetic-fragment.md).
    **Reals (`QF_LRA`) follow with an exact-rational simplex** (not a BV
    reduction): the `Real` sort + `Rational` + evaluator are done; the simplex
    procedure is next. See
    [ADR-0015](../09-decisions/adr-0015-linear-real-arithmetic.md).
- [x] What proof format covers theory lemmas once proofs extend beyond
      clausal DRAT/LRAT — adopt Alethe/CPC or design Axeyum-native?
  - Answer: **Alethe is the SMT-level interchange and reconstruction format**;
    DRAT/LRAT remains the clausal substrate. Emit standard rules where possible,
    self-check in-tree, cross-check with Carcara, and keep any Axeyum-only rule a
    narrow, named residual rather than inventing a parallel proof language. The
    trust ledger records unsupported reductions, while Alethe→Lean reconstructs
    checked artifacts into kernel terms. ADR-0011 established the format ladder,
    ADR-0031 made the residual trust countable, and ADR-0075 demonstrates the
    policy on array `select`: one standard-rule artifact checks in-tree, in
    Carcara, and in Lean with no array-elimination trust step.
- [x] How must the embedded Lean kernel combine proof irrelevance with
      elimination from potentially-`Prop` inductives?
  - Answer (2026-07-15): use Lean's syntactic-subsingleton criterion. A
    provably non-`Prop` result, an empty proposition, or a sole constructor whose
    non-proof fields are exact result arguments receives a fresh elimination
    universe; every other potentially-`Prop` family keeps a recursor fixed to
    `Sort 0`. A generated adversarial matrix and a mandatory real-Lean
    flat-inductive/iota CI test guard the boundary. See
    [ADR-0165](../09-decisions/adr-0165-lean-compatible-prop-large-elimination.md).
- [x] How should the independent Lean kernel represent natural literals before
      it implements literal typing and reduction?
  - Answer (2026-07-22): use a canonical `NatLit` newtype over pure-Rust
    `BigUint`, parse official decimal payloads without any fixed-width
    conversion, and keep inference fail-closed until the separately gated
    TL2.7 slice. Values around and far above `2^128` must round-trip through
    interning, structural operations, rendering, and importer validation. See
    [ADR-0346](../09-decisions/adr-0346-arbitrary-precision-lean-nat-literals.md).
- [x] When may raw Lean Nat literals receive a type, and how much constructor
      conversion belongs before accelerated Nat operations?
  - Answer (2026-07-22): only after the fresh checked environment contains the
    canonical `Nat`/`Nat.zero`/`Nat.succ` bootstrap. Type raw values as `Nat`,
    reproduce Lean's zero/successor offset equality, one-step successor
    reduction, and literal-major recursor conversion, but leave every other Nat
    operation to TL2.8. See
    [ADR-0347](../09-decisions/adr-0347-checked-lean-nat-literal-semantics.md).
- [x] How can the streaming `lean4export` reader publish a checked environment
      atomically without cloning or rolling back kernel arenas?
  - Answer (2026-07-22): stage the complete stream in a private owned `Kernel`
    and return a field-private `CompletedImport` only after EOF and every
    translation/admission check succeed. Errors carry no kernel or arena handle;
    the caller-supplied mutable-kernel API is removed rather than retained as a
    documented footgun. See
    [ADR-0348](../09-decisions/adr-0348-owned-lean-import-publication.md).
- [x] Can format-3.1 record-boundary truncation be detected from the bare
      NDJSON stream, and how should the importer mutation corpus classify it?
  - Answer (2026-07-22): not in general. The upstream grammar has initial
    metadata followed by a backward-referencing record sequence but no footer,
    expected count, or root manifest, so a complete-record prefix is a valid
    unsealed stream. Generate every prefix and record-body truncation, classify
    accepted prefixes as `published-unsealed` with no exact-artifact credit,
    and assign authenticated completion to TL0.3/TL1.6/TL1.9. See
    [ADR-0349](../09-decisions/adr-0349-generated-lean-import-mutation-corpus.md).
- [x] Which identity should bind imported Lean axioms, declaration content, and
      direct dependencies without depending on wire or arena order?
  - Answer (2026-07-22): retain TL0.4's rendered-type SHA-256 for axiom-ledger
    comparison, but use a complete domain-separated structural Merkle encoding
    for declaration content. Bind each sorted direct dependency name to its
    admitted content digest so dependency mutations propagate without changing
    the dependent declaration's own content identity. See
    [ADR-0350](../09-decisions/adr-0350-canonical-lean-declaration-identity.md).
- [x] How should the remaining recursive-indexed, reflexive, mutual, nested,
      and well-founded official Lean cases be measured before independent
      admission widens?
  - Answer (2026-07-22): freeze minimal source cases first; export
    every selected root twice; freeze exact official wire features with the
    independent Python reader before running Axeyum; then pair every typed Rust
    decline with the existing direct-recursive positive control and generate an
    assurance-separated matrix. Source family and elaborated core form remain
    separate facts. M0 and Stage A now freeze the exact seven-case source
    population. Stage B now freezes five byte-identical official streams and
    their full independent group metadata. M3 now freezes two current-product
    outcomes per row beside ten passing direct-recursive controls, without
    changing semantics. M4 now generates seven implication-checked assurance
    rows. M5 closes the bounded validation, documentation, decision, and remote-
    ref gates without changing importer or kernel semantics. See
    [accepted ADR-0351](../09-decisions/adr-0351-preregister-official-lean-construct-matrix.md)
    and the
    [execution plan](../../plan/lean-official-construct-matrix-plan-2026-07-22.md)
    plus the
    [Stage A result](../../plan/lean-official-construct-matrix-stage-a-2026-07-22.md).
    The measured wire forms are in the
    [Stage B result](../../plan/lean-official-construct-matrix-stage-b-2026-07-22.md).
    The typed declines are in the
    [M3 product result](../../plan/lean-official-construct-matrix-product-2026-07-22.md).
    The generated selected-family result is in the
    [M4 assurance report](../../plan/lean-official-construct-matrix-m4-2026-07-22.md).
    The exact gate and handoff record is in the
    [final result](../../plan/lean-official-construct-matrix-final-2026-07-22.md).
- [x] Which exact strict-positivity rule must guard the next Lean inductive
      admission widening, and when must it run?
  - Answer (2026-07-22): reproduce pinned Lean 4.30's WHNF-based
    single-family rule exactly for the currently representable profile. Accept
    no occurrence; recurse through a `Pi` codomain only when its domain contains
    no family occurrence; otherwise require the exact family application with
    fixed parameters, complete index arity, and occurrence-free indices. Run
    this as a fail-closed preflight before provisional inductive environment
    insertion. Positive recursive-indexed/reflexive shapes retain their feature
    declines until TL2.12. See
    [accepted ADR-0352](../09-decisions/adr-0352-preregister-lean-strict-positivity.md),
    the [TL2.11 execution plan](../../plan/lean-strict-positivity-tl2.11-plan-2026-07-22.md),
    and the [final result](../../plan/lean-strict-positivity-final-2026-07-22.md).
- [x] What exact induction-hypothesis and computation-rule construction should
      admit recursive-indexed and reflexive/higher-order fields without
      duplicating trusted semantics?
  - Answer (2026-07-22): treat direct, indexed, higher-order, and
    combined indexed+higher-order recursive fields as empty/nonempty cases of
    one rule. If `u : Pi xs, I P indices`, generate
    `u_ih : Pi xs, motive indices (u xs)` and pass
    `fun xs => I.rec P motive minors indices (u xs)` to the minor premise.
    Preserve all constructor fields first and IHs second in source order; use
    one WHNF telescope-tail helper for minor types and rule right-hand sides;
    remove the importer's reflexive policy decline only after native support.
    Mutual groups remain TL2.13 and frontend nested/well-founded lowering
    remains TL2.14. See
    [accepted ADR-0353](../09-decisions/adr-0353-preregister-lean-recursive-induction-hypotheses.md)
    and the
    [TL2.12 execution plan](../../plan/lean-recursive-induction-hypotheses-tl2.12-plan-2026-07-22.md).
    [M0](../../plan/lean-recursive-induction-hypotheses-m0-2026-07-22.md)
    now freezes the explicit-recursor source, two official root streams, and
    exact metadata/claim boundary before product implementation. The
    [M1 result](../../plan/lean-recursive-induction-hypotheses-m1-2026-07-22.md)
    routes direct recursion through the shared classifier/reopener with exact
    declaration/computation identity and both declines unchanged. M2-M4 close
    native semantics, official import, and selected computation; the
    [M5 result](../../plan/lean-recursive-induction-hypotheses-final-2026-07-22.md)
    closes all bounded gates and marks TL2.12 DONE. TL2.13 mutual groups are
    the next atomic semantic widening.
- [ ] What is the trusted admission/publication unit for mutual inductive
      groups, and how must motives, minors, positivity, indices, and recursive
      target families be ordered?
  - Proposed answer (2026-07-22): use one atomic ordered group, never repeated
    single-family calls. Check common universe parameters and definitionally
    equal shared parameter telescopes, equivalent result universes, and the
    complete group occurrence set before publication. Order motives by family
    and minors by family then constructor. For a field
    `u : Pi xs, I_j params indices`, generate
    `Pi xs, motive_j indices (u xs)` and call `I_j.rec` with every group motive
    and minor. Each owner-family recursor then binds its own indices/major and
    returns its own motive. Restrict mutual predicates to `Prop`, disable mutual
    K-like reduction, infer-check every recursor, and commit all declarations or
    none. Preserve `add_inductive` as a singleton wrapper and keep TL2.14
    frontend lowering separate. See
    [proposed ADR-0354](../09-decisions/adr-0354-preregister-lean-mutual-inductive-groups.md)
    and the
    [TL2.13 execution plan](../../plan/lean-mutual-inductive-groups-tl2.13-plan-2026-07-22.md).
    M0 now freezes both explicit official computations and their complete wire
    inventories without Axeyum product credit. In both streams, family order is
    `Even, Odd` while wire recursor order is dependency-ordered `Odd.rec,
    Even.rec`; importer comparison must therefore use checked recursor identity
    and owned rules rather than array position. See the
    [M0 result](../../plan/lean-mutual-inductive-groups-m0-2026-07-22.md).
    The
    [M1 result](../../plan/lean-mutual-inductive-groups-m1-2026-07-22.md)
    now makes the ordered group a public kernel input, preserves singleton
    declarations/computation/errors exactly, and checks group-local names,
    definitionally equal shared parameters, per-family indices, and equivalent
    result universes inside a scalable insertion-log transaction. A valid
    multi-family group still receives a typed policy decline. The
    [M2 result](../../plan/lean-mutual-inductive-groups-m2-2026-07-22.md) now
    implements the native positivity/constructor/motive/minor/recursor/
    publication rule through one group path. Eighteen public rows and focused
    mutation/late-rollback tests cover the registered native matrix without
    importer widening. The
    [M3 result](../../plan/lean-mutual-inductive-groups-m3-2026-07-22.md) now
    repeats 720 unique public-path cases byte-identically with 432 positive
    inference/iota contracts, 288 typed rollbacks, direct motive/minor-order and
    target-rule oracles, and retained 768/840 controls. The question remains
    open until M4's official import/computation comparison and M5's final gates
    close.
- [x] Should the proof-assistant bridge export obligations to Lean, import
      checked rewrite rules from Lean, or both — and how early is a
      Lean-checked rewrite-rule library worth prototyping?
  - Answer (2026-07-21): **both, sequenced**. Preserve the existing
    fail-closed source-export/official-check lane, then import pinned official
    `lean4export` NDJSON and independently admit supported declarations.
    Selected theorem-backed rewrite/CAS tactic slices follow the importer and
    the 65-row prelude-assumption inventory. Native parser/macros, elaboration,
    modules/Lake, a late untrusted version-specific `.olean` reader, LSP,
    compiler/runtime, and full pinned-mathlib compatibility are separately
    gated later phases rather than permanent exclusions. See
    [ADR-0345](../09-decisions/adr-0345-preregister-lean-system-interoperability.md),
    [compatibility roadmap](../../plan/lean-system-compatibility-roadmap-2026-07-21.md),
    and [implementation plan](../../plan/lean-system-implementation-plan-2026-07-21.md).
- [x] When two theories exist, is Nelson-Oppen combination implemented
      directly or via a CDCL(T) core from the start?
  - Answer: expose each live combined theory through the shared `TheorySolver`
    contract and let canonical `CdclT` own Boolean structure, interface-variable
    branching, propagation, and conflict learning. A direct conjunctive
    Nelson-Oppen search remains the replay/model-reconstruction oracle and a
    conservative fallback, not a second production Boolean loop. QF_UFLIA,
    QF_UFLRA, and the bounded scalar QF_UFBV route now follow this architecture;
    the latter combines an e-graph with exact warm BV checks over explicit
    argument/result interface equalities. See
    [ADR-0060](../09-decisions/adr-0060-arith-online-cdclt-default-dispatch.md),
    [ADR-0066](../09-decisions/adr-0066-canonical-online-qf-ufbv-combination.md),
    and [P1.6](../../plan/track-1-engine/P1.6-theory-combination.md).

### Rust And Packaging

- [x] How many crates should exist in the first implementation?
  - Answer: start with two crates per
    [ADR-0001](../09-decisions/adr-0001-vertical-slice-first.md); later
    `axeyum-smtlib` and `axeyum-bench` splits were introduced after the
    format and benchmark boundaries were exercised by use.
- [ ] Should optional native backends be separate crates or features?
- [ ] Is `no_std` relevant for any low-level crate?

## Resolution Process

When a question is answered, write a decision record in
[`09-decisions/`](../09-decisions/README.md) using its template
(Context / Decision / Evidence / Alternatives / Consequences), and link it
from the question entry above.

## Open Questions

This file is itself the current open-question register. When individual items are
resolved, keep the resolved question in place long enough to preserve context and
link to the decision note or implementation PR that closed it.

### Pareto strategy (axeyum + glaurung, added 2026-07-18)

Full plan: [axeyum-glaurung-pareto-strategy.md](./axeyum-glaurung-pareto-strategy.md).

- [ ] Do the two artifact-admitted symbolic-CVE findings reproduce exactly
  within each authority across runs and machines, while preserving identical
  finding/work identity across Axeyum and Z3 authority?
  - [ADR-0302](../09-decisions/adr-0302-preregister-symbolic-cve-reproducibility.md)
    freezes the two-authority/two-repetition protocol and keeps arbitrary but
    replay-valid model witnesses separate from finding identity. One host is
    explicitly incomplete; at least two genuine machines are required.
- [ ] Does bounded symbolic memory + warm reuse Pareto-dominate eager any-model
  concretization on coverage AND reproducibility for driver bug-finding?
- [x] Is solver-internal warm reuse additive over a bounded GREEN-style
  engine-level constraint cache on a fixed Glaurung query stream?
  - The first
    [opportunity analysis](../../../bench-results/glaurung-constraint-cache-opportunity-20260720/README.md)
    finds a 45.48% exact and 66.37% unbounded exact-plus-implication structural
    ceiling. It does not measure cache cost or additivity;
    [ADR-0303](../09-decisions/adr-0303-preregister-engine-constraint-cache-factorial.md)
    froze the implemented bounded six-mode producer, runner, and analyzer, but
    its first campaign is rejected on textual-query versus canonical-set exact
    classification drift. [ADR-0304](../09-decisions/adr-0304-correct-canonical-cache-identity-and-rerun.md)
    freezes the corrected opportunity v2 and a fresh otherwise-identical rerun.
    That successor passes all gates: warm reuse is additive under exact caching
    on 2/4 drivers and structural caching on 3/4, while cache-on slows every
    already-warm path with a variance-qualified contrast and adds 7.6%--67.3%
    mean maximum RSS. The bounded answer is mixed but sufficient: retain warm
    reuse, and do not promote the experimental engine cache into Axeyum core.
- [ ] Is disjoint projected enumeration cheaper than per-expression optimization
  (least-unsigned probing cost measured at 27x solves) for deterministic diverse
  concretization?
- [ ] Which QF_BV regime does an in-process pure-Rust solver win against a *warm*
  z3 once the FFI floor is isolated, and how large is that regime on real corpora?
- [ ] Can incremental abstraction-refinement (mul/div/rem) close the cold
  bit_blast/cnf gap (currently ~84% of cold cost) without regressing the warm path?
- [ ] Are proof-carrying "infeasible path" certificates useful enough downstream
  (agent verdicts, CI determinism) to justify their cost?
  - First bounded cell complete:
    [ADR-0278](../09-decisions/adr-0278-preregister-glaurung-infeasible-path-certificate.md)
    accepts one explicit, off-trait Glaurung path-verdict attachment with exact
    source rebinding and pinned `drat-trim` consumption. The fixed proof is only
    an empty-clause trace over complementary input units, so usefulness and cost
    remain open. Any continuation must preregister a real workload and measure
    proof prevalence, nontrivial traces, and requested second-pass cost;
    ordinary pruning cost and whole-CFG proof coverage remain separate.
- [x] Can replay-checked solver countermodels become deterministic fuzz-seed
  corpora and compiled regression tests without relabeling `Unknown`, trusting
  raw models, or losing full-width Rust values?
  - [ADR-0339](../09-decisions/adr-0339-preregister-deterministic-witness-seed-corpus.md)
    accepts one typed solver-to-corpus path over panic, postcondition, and
    equivalence countermodels. Replay passes before canonical JSON or test
    source exists; exact full-width signed rendering is regression-owned; and
    the committed 1,404-byte JSON plus 712-byte Rust source reproduce
    byte-for-byte, compile, and execute. T5.4.3/4 directed-unknown handoff and
    coverage accounting remain separate.
- [ ] Can a structured solver `Unknown` become deterministic guarded fuzz work
  without relabeling errors, replay failures, samples, or dropped work as proof?
  - [ADR-0340](../09-decisions/adr-0340-preregister-reason-preserving-directed-fuzz-handoff.md)
    freezes a QF_BV-only hybrid outcome: checked proofs and replayed solver
    refutations remain decided branches; only `ProofOutcome::Unknown` emits an
    exact reason-preserving target plus a source-oracle-checked `fuzzed-only`
    report. The implementation checkpoint is pushed at `3d75d407`; branch and
    callback separation, replay/disagreement failures, deterministic reruns,
    full-width sampling, JSON escaping, and independently parsed violation
    semantics pass. The question stays open until exact fixtures, the complete
    rejection-family/mutation matrix, and all frozen acceptance gates pass.
    T5.4.4 still owns coverage accounting, and Glaurung must first stop
    flattening `UnknownReason` before consuming this route.
- [ ] Can one structured LLVM syntax/semantics front end feed both Axeyum term
  reflection and a hardened Glaurung LLIR lowerer without coupling either
  consumer to the other's execution policy?
  - [ADR-0279](../09-decisions/adr-0279-gate-glaurung-llvm-frontend-on-llir-contract.md)
    rejects a direct importer into current LLIR. Axeyum P5.1/T5.1.2 owns the
    first prerequisite: structured parsing with diagnostics. A second lowerer
    requires explicit LLIR widths/successors plus a fail-closed LLVM semantics
    profile before a shared crate boundary is considered.
  - [ADR-0281](../09-decisions/adr-0281-preregister-typed-llvm-scalar-definedness.md)
    accepts the first semantic step: typed scalar instructions and explicit
    LLVM definedness predicates.
  - [ADR-0282](../09-decisions/adr-0282-preregister-typed-llvm-cfg-validation.md)
    freezes typed PHIs/terminators and whole-function graph validation before
    any checked graph executor is admitted. It does not admit a shared crate or
    Glaurung lowering; checked CFG execution and memory semantics remain
    prerequisites.
  - [ADR-0283](../09-decisions/adr-0283-preregister-checked-acyclic-llvm-cfg-execution.md)
    accepts bounded acyclic execution with selected-edge PHIs,
    path-conditioned immediate UB, explicit branch/switch condition
    definedness, and `unreachable => defined=false`; its proof migration keeps
    value claims explicitly conditioned on defined execution. Cycles, memory,
    LLIR hardening, and Glaurung lowering remain separate prerequisites.
  - [ADR-0284](../09-decisions/adr-0284-preregister-canonical-llvm-cfg-rendering.md)
    accepts the missing parse-print-parse boundary over that typed scalar graph,
    including exact LLVM `\XX` identifier escapes. The canonical path preserves
    checked value+definedness proofs and adds reproducible syntax, not memory,
    module resolution, a shared crate, or a second consumer.
  - [ADR-0286](../09-decisions/adr-0286-preregister-bounded-llvm-byte-memory.md)
    accepts the first T5.1.5 memory slice: one explicit initialized bounded
    byte object, typed `inbounds` GEP plus `i8` load/store, pointer/byte
    definedness, final-memory joins, canonical syntax, compiler fixtures, and
    replay-checked proofs. It does not admit
    general provenance, multiple/aliasing objects, MIR writes, LLIR lowering,
    or a shared crate.
  - [ADR-0287](../09-decisions/adr-0287-preregister-reproducible-mir-capture.md)
    accepts T5.1.3's first enabling slice: exact compiler identity and argv,
    raw MIR bytes, committed source/output/provenance hashes, stable-CI drift
    checks, exact-toolchain byte replay, and fail-closed tamper/regeneration
    tests. Capture alone adds no MIR semantics; checked writes and non-panicking
    reflection remain separately gated.
  - [ADR-0288](../09-decisions/adr-0288-preregister-checked-mir-byte-memory.md)
    accepts the semantic continuation: a named function from the authenticated
    module parses through a strict typed non-panicking MIR subset; every access
    derives its own bounds failure; stores and branch-local final memory join;
    source replay and the same bounded LLVM/MIR roundtrip spec pass. Whole-crate
    build selection and general MIR places remain open.
  - [ADR-0289](../09-decisions/adr-0289-preregister-cargo-owned-mir-selection.md)
    accepts the next T5.1.3 prerequisite: one explicit Cargo manifest,
    package, target, function, compiler, target width, target directory, and
    output must flow through the checked MIR path in one command before a raw
    artifact is retained. Two runs reproduce 1,438 raw bytes and the typed/term
    summary; source replay and stable no-partial-output failures pass. This is
    target-build selection, not broader MIR semantics or LLIR admission.
  - [ADR-0290](../09-decisions/adr-0290-preregister-reflection-semantics-gate.md)
    accepts T5.1.6 before another semantic widening: 62 source-derived checked
    LLVM/MIR variants have exact manifest ownership with proof/spec plus
    deterministic fuzz/replay evidence. The scalar matrix proves 96 goals and
    exhausts 11,248 bounded rows; 11 cross-IR pairs agree on 110,000 tuples; all
    five refutations replay. One mutation-tested runner is wired into `just`
    and dedicated CI. This validates the admitted fragment; it does not admit
    LLIR, loops, general places, or wider memory.
  - [ADR-0291](../09-decisions/adr-0291-preregister-typed-canonical-llvm-loop-bridge.md)
    accepts the first T5.1.4 cycle route: normalize only a structurally
    unique implicit numeric entry predecessor, detect one canonical scalar
    self-loop in the typed CFG, preserve checked value/definedness in an
    automatic `TransitionSystem`, and reproduce the existing `capsum8`
    invariant proof. The accepted gate proves the formulas independently,
    fuzzes 20,000 recurrence tuples with zero disagreement, and source-replays
    the abstract reachable row. Exit abstraction is explicit: safe invariants
    are sound, while abstract reachability requires separate source replay. This does not
    admit MIR, multi-block/nested/memory loops, unrolling fallback, or LLIR.
  - [ADR-0292](../09-decisions/adr-0292-preregister-single-latch-llvm-natural-loop.md)
    accepts the next T5.1.4 route after auditing the bounded fallback: one
    checked transition from a real single-latch natural loop with an acyclic
    internal region, reusing existing replay-checked BMC k-unrolling. The exact
    `capdiv` module preserves path-conditioned UB: `d=0` is permitted on the
    even path that skips `udiv` and forbidden on the odd path that executes it.
    Independent formulas, 50,000 tuples, k-induction/BMC, and source replay
    pass. General rejected-loop unrolling, MIR, multi-latch/early-exit/switch/
    memory loops, and LLIR remain open.
  - [ADR-0293](../09-decisions/adr-0293-preregister-glaurung-llvm-loop-shape-census.md)
    accepts the exact reproducible 12-source result: 11 rows match the existing
    ADR-0291 structural shape and the sole rejected row is the early-exit
    `mathlib_is_prime` loop. One function in one source fails the frozen
    two-function/two-source diversity rule, so no new implementation is
    selected. Structural matching is not semantic eligibility; the next loop
    step must measure real semantic rejection or independently broaden the
    population.
  - [ADR-0294](../09-decisions/adr-0294-preregister-glaurung-llvm-loop-semantic-census.md)
    preregisters that semantic measurement over all 12 exact loop functions.
    It preserves the existing typed-parser and loop-reflector error kinds,
    retains every diagnostic, tries all non-Boolean PHIs only to remove
    property-name bias, and forbids dropped rows. A strict-plurality rejection
    bucket must span two functions and two sources before it can select a next
    audit lane. The first artifact observed 12 typed-CFG
    `unsupported_instruction` declines but was rejected because
    `llvm-extract`'s temporary ModuleID path changed all extracted-file hashes.
    The rejected artifact is retained. The corrected result then reproduces
    exactly: 0/12 accepted, all 12 at typed-CFG `unsupported_instruction`, with
    seven one-source wide-memory rows, three cross-source call rows, one
    `alloca`, and one non-scalar result. The frozen bucket selects a T5.1.2 audit
    lane, not code; no individual mechanism receives retroactive authorization.
  - [ADR-0295](../09-decisions/adr-0295-preregister-checked-llvm-direct-body-calls.md)
    accepts the separately gated executable call experiment. The two PAC loops
    use an explicitly supplied, exact checked `leaf` body as an
    opt-in inlining baseline; the unchanged default still rejects ordinary
    calls, and `puts` receives no effect-erasing model. Exact compiler/source/
    function identity, independent value+definedness and transition formulas,
    100,000 tuples at zero disagreement, source replay, precise call-boundary
    negatives, canonical rendering, and the expanded nine-binary/88-test
    standing semantics gate pass. This is a T5.2.4 prerequisite, not modular
    contracts or a revised 12-row census; next compose an explicit contract and
    compare it with this inlined baseline.
  - [ADR-0296](../09-decisions/adr-0296-preregister-verified-scalar-contract-composition.md)
    accepts that first composition rule without trusting a summary or
    erasing failed preconditions. One exact scalar contract must verify against
    the exact `leaf` body once; caller reflection then retains only the verified
    contract and must match the ADR-0295 inlined baseline. Version one permits
    only a universally true requirement and exact functional result, deferring
    nontrivial call-site obligations, havoc, annotations, recursion, memory,
    and external effects until their soundness boundaries are explicit. The
    exact contract and inlined formulas match modulo a small checked
    conjunction rule, 100,000 modular/inlined tuples have zero disagreement,
    every component mutation is refuted, and the body is discarded before
    caller lowering. A rejected general nonlinear-equivalence query OOM event
    is retained; the accepted verifier uses structural exactness plus a bounded
    replayed fallback.
  - [ADR-0297](../09-decisions/adr-0297-preregister-call-requirement-obligations.md)
    accepts the next composition rule: verify a nontrivial scalar
    requirement, assume it only after exposing its path-conditioned complement
    as a replayable `TransitionSystem::bad` obligation, and retain exact
    call-site attribution. Its 100,000 rows split 33,334 valid / 33,334 defined
    violation / 33,332 source undefined with zero disagreement or dropped work;
    depth-1 PAC and path-conditioned natural-loop witnesses replay. It adds
    neither annotation syntax nor relational havoc.
  - [ADR-0298](../09-decisions/adr-0298-preregister-relational-scalar-call-results.md)
    accepts the checksum-module composition rule: one
    fresh internal scalar result per straight-line call, a separately exposed
    `ensures` relation rather than fabricated poison, exact body verification,
    a replayed weak-postcondition havoc countermodel, and 100,000 inputs with
    200,000 fully classified valid/violating result choices. The standing gate
    passes 76 variants / 16 groups / ten binaries / 108 tests. Loop havoc, MIR
    calls, annotations, and effects remain outside this experiment; MIR-side
    checksum composition is the next P5.2 boundary.
  - [ADR-0299](../09-decisions/adr-0299-preregister-checked-mir-relational-calls.md)
    accepts that MIR boundary. The located typed parser gains only the
    source-derived checksum scalar operations and assigned direct-call
    terminator. A separate MIR resolver proves the shared relational contract
    against the checked MIR `sum16` body and independently proves its panic term
    false before body discard; the LLVM proof does not stand in for that gate.
    The modular MIR and LLVM callers use separate havoc symbols and relations;
    each passes 100,000 valid plus 100,000 violating choices and replays a
    weak-contract countermodel. The standing gate is 81 variants / 17 groups /
    ten binaries / 114 tests. General panic contracts, annotations, unwind
    paths, memory, loops, recursion, and effects remain outside this result.
  - [ADR-0315](../09-decisions/adr-0315-preregister-modular-mir-panic-contracts.md)
    accepts the next smallest P5.2 boundary: verify one explicit
    input-dependent MIR `panic_when` summary against the checked callee body,
    propagate it into the caller panic term, and guard the fresh-result
    relation by normal return. The fixed two-function experiment requires exact
    modular/inlined panic equality, all 256 `u8` rows at 255 normal/one panic, a
    concrete callee-panic witness, mutation teeth, and the 117-test standing
    semantics gate pass. Annotations and unwind cleanup remain separate.
  - [ADR-0316](../09-decisions/adr-0316-preregister-source-contract-annotations.md)
    accepts the first annotation slice after auditing the source verifier: it
    retains the previously discarded scalar tail result and distinguishes a
    normally returning postcondition counterexample from the existing panic
    replay. The exhaustive straight-line `u8` gate observes 255 admitted rows,
    zero safe violations, and 255 mutated-postcondition violations with zero
    evaluation errors or dropped rows. Branches, loops, calls, modular summary
    emission, and source-to-MIR identity remain separate questions.
  - [ADR-0317](../09-decisions/adr-0317-preregister-authenticated-source-contract-mir-bridge.md)
    accepts the smallest identity bridge: one total annotated
    `u8::wrapping_add` function lowers into the existing
    `ScalarCallContract`, matches a hand-built declaration exactly, and both
    independently verify against 10,124 byte-identical checked-MIR bytes from
    the same registered source and owning Cargo build. Both modular routes
    equal the inlined control over all 256 inputs; mutations and zero resources
    fail closed. The registered compiler's exact qualified wrapping-add
    intrinsic is typed and isolated from relational calls. Nontrivial
    `requires`, panic-summary authoring, broader source syntax, and source-to-
    LLVM generation remain separate.
- [x] Can the accepted checked-MIR byte-region surface discharge a complete
  page-table-shaped obligation family without adding a new memory model?
  - [ADR-0318](../09-decisions/adr-0318-preregister-reflected-page-table-walk-obligations.md)
    rejects the first two-level four-entry byte-table cell before capture or
    proof. The operation/block probe fit the accepted fragment, but the real
    owning-Cargo path exposed unowned nested compiler `scope` metadata and
    failed strictly at `scope 1 {`. No artifact was retained and the fixture
    was restored. A separate metadata-grammar decision is required before the
    bounded obligation may be retried.
  - [ADR-0319](../09-decisions/adr-0319-preregister-checked-mir-scope-metadata.md)
    accepts that exact prerequisite: bare decimal `scope N {}` nesting may
    contain only admitted typed locals, debug declarations, and nested scopes;
    locals flatten into the existing inventory while scope/debug metadata has
    no execution semantics. The 64-level cap, strict brace/header/content/
    duplicate/type mutations, and structured-noise gates pass, and the exact
    walk fixture now reaches the existing checked-memory profile. No raw walk
    artifact or page-table result is admitted; a retry needs a fresh ADR.
  - [ADR-0320](../09-decisions/adr-0320-preregister-bounded-reflected-page-table-evidence.md)
    accepts that fresh evidence-only retry: four byte-identical captures,
    authenticated raw bytes and typed summaries, seven universal good-case
    claims, three replayed broken controls, and exactly 4,096 sampler rows at
    zero disagreement/error/panic/drop. It adds no production semantic form
    and closes only the bounded four-entry obligation shape, not an MMU claim.
- [x] Can an authenticated compiler-reflected Rust step function refine the
  shipped declarative handshake transition system and transport safety?
  - [ADR-0321](../09-decisions/adr-0321-preregister-reflected-handshake-fsm-refinement.md)
    accepts one scalar deterministic identity-refinement cell: eight universal
    per-event proof groups, complete transition-relation equality, PDR-safe
    spec and reflected implementation systems, a PDR/BMC/source-replayed
    blind-injection control, and exactly 2,048 exhaustive reflection/spec/Rust
    rows at zero disagreement/error/panic/drop. It adds no public refinement
    API and makes no liveness or real-protocol claim.
- [x] Can the accepted P5.3 evidence be documented as a reviewer-facing
  capability catalog without collapsing unequal authenticity or claim scopes?
  - [ADR-0322](../09-decisions/adr-0322-preregister-p5.3-obligation-catalog.md)
    accepts one comparison index and separate control-flow constant-time,
    bounded-memory/page-table, and FSM-refinement pages. Each records the exact
    goal, admitted fragment, evidence route, worked example, reproduction,
    control, and residuals. The catalog explicitly retains T5.3.1's weaker
    MIR-text provenance and the bounded teaching-model scope of T5.3.2/3.
- [x] Can Axeyum reproducibly capture and admit the complete full-width Maestro
  device-number bijection from the exact external project's owning LLVM build?
  - [ADR-0323](../09-decisions/adr-0323-preregister-maestro-device-id-llvm-capture.md)
    freezes exact upstream/source/toolchain identities and rejects the first
    official run at its two-root full-module byte-identity gate: both builds
    finish below 1 GiB peak RSS, but sizes and hashes differ. Extraction and
    parser admission never run. A separately preregistered root-drift
    diagnostic is required before any canonical identity, inverse-property
    query, or scoreboard row.
  - [ADR-0324](../09-decisions/adr-0324-preregister-maestro-llvm-root-drift-diagnostic.md)
    diagnoses broad drift: 319,598 changed lines, seven absolute dependency-
    source paths per module, and three changed selected symbols/canonical
    hashes. The final-crate-only remap missed Maestro's path dependencies.
    Every selected scalar body is admitted, but symbol drift fires the frozen
    negative branch and grants no capture credit. Next preregister a fresh
    dependency-wide remapped build; do not normalize these modules.
  - [ADR-0325](../09-decisions/adr-0325-preregister-dependency-wide-maestro-path-remap.md)
    rejects v2 after both modules eliminate every real-root token but still
    differ in size and hash. Root-specific remap-rule inputs remain a build-
    identity variable. Extraction never runs. Next preregister two independent
    trees at one identical virtual source/target path; do not normalize output.
  - [ADR-0326](../09-decisions/adr-0326-preregister-stable-virtual-root-maestro-capture.md)
    closes that final route negative. The corrected stable-root namespace
    reaches Cargo, but upstream build logic requires an unregistered network
    font input and emits no LLVM under frozen isolation. No extraction, parser,
    proof, or capture credit exists; a v4 relaxation is forbidden.
- [x] Can Axeyum reproducibly capture and verify Tock's full-width integer-log
  helpers from the exact owning LLVM 22 kernel build?
  - [ADR-0327](../09-decisions/adr-0327-preregister-tock-log2-reflection.md)
    accepts the one bounded frontend prerequisite for the two selected
    source-used `u32`/`u64` helpers: typed non-wrapping call-result `range`
    poison plus scalar `llvm.ctlz` zero-poison semantics, canonical syntax,
    independent 32/64-bit proofs, exhaustive widths 1--8, deterministic wide
    rows, and replayed mutations. It adds no IR operator. The next step is a
    separately preregistered authenticated external capture; no target bytes,
    proof, or scoreboard row exist yet.
  - [ADR-0328](../09-decisions/adr-0328-preregister-tock-log2-llvm-capture.md)
    preregisters the next zero-result boundary: two independently archived
    complete trees at identical virtual roots, validated locked offline cache,
    raw full-module identity, hash-pinned LLVM 22 extraction/assembly, exact
    two-symbol checked admission, atomic local output, and no property query.
    Its pushed producer and exact registration now close v1 negatively at the
    pre-build cache gate: locked-offline metadata cannot find cached `ghash
    0.4.4`. Zero builds or target bytes exist. Do not refill the ambient cache
    and rerun v1; a successor must first preregister a dedicated checksum-
    validated cache preparation and inventory.
  - [ADR-0329](../09-decisions/adr-0329-preregister-tock-dedicated-cargo-cache.md)
    preregisters that input-only successor: one fresh dedicated Cargo home,
    exact locked fetch, network-isolated read-only replay of the v1 metadata
    gate, canonical whole-tree inventory, and no compilation/capture/query.
    Its pushed producer closes preparation v2 negatively before download: the
    constructed root omits the runtime target of the host `resolv.conf`
    symlink, so Flux DNS resolution fails. No cache byte or inventory exists.
    A successor must separately preregister the minimal resolver-file input and
    an actual DNS probe; the no-op namespace probe was insufficient.
  - [ADR-0330](../09-decisions/adr-0330-preregister-tock-cache-resolver-correction.md)
    freezes that narrow preparation-v3 correction: bind only the exact
    hash/mode/size-pinned systemd-resolved stub at the selected path, require a
    pinned real `getent` IPv4 lookup, then retain every ADR-0329 non-network
    gate. Its pushed producer proves DNS and completes the locked fetch, then
    closes v3 negatively because the frozen inventory rejects Cargo/libgit's
    legitimate firmware pack-index hard link. No cache survives. A successor
    must preregister canonical hard-link owner/alias rows before another fetch.
  - [ADR-0331](../09-decisions/adr-0331-preregister-tock-cache-hardlink-inventory.md)
    freezes that preparation-v4 rule: one lexicographic owner plus explicit
    alias rows bind every in-cache path and shared mode/size/hash/link count;
    outside-root aliases fail and inode numbers are excluded. Pushed v4 proves
    that inventory, then closes on an invalid 162-resolved-versus-169-locked
    count equality. A successor must structurally authenticate every resolved
    package ID against the exact lockfile and record, not expect, the count.
  - [ADR-0332](../09-decisions/adr-0332-preregister-tock-cache-structural-metadata.md)
    freezes that preparation-v5 validator: closed unique package/node/edge IDs,
    exact external lock identities and checksums, in-tree path manifests, one
    workspace kernel, and a canonical active digest/count recorded only as
    results. Pushed v5 accepts a 3,077-row hard-link-aware inventory (`fd6ee33d`)
    and 162-node/814-edge active graph (`da6971e4`) against 169 lock entries;
    independent replay and zero OOM deltas pass. It authorizes only a fresh
    capture-v2 ADR; no build, target byte, query, or scoreboard row exists.
  - [ADR-0333](../09-decisions/adr-0333-preregister-tock-llvm-capture-v2.md)
    preregisters that build boundary: recompute and mount the exact dedicated
    cache read-only, structurally replay locked-offline metadata, then run the
    unchanged two-root raw-module/LLVM-22 extraction/admission gates. Its thin
    outer-atomic wrapper, compact registration, eight focused plus 33 inherited
    protocol tests, local-result/inventory replay, and cache-path identity checks
    pass pre-build. Pushed `9bff9d2e` then closes v2 before Cargo/build because
    structural replay receives the merged capture registration without cache-
    only `expected_lock_packages` and raises `KeyError`. Cleanup leaves no output
    or OOM delta. A v3 ADR must freeze the one-argument correction before another
    invocation; no official build/query exists.
  - [ADR-0334](../09-decisions/adr-0334-preregister-tock-llvm-capture-v3.md)
    freezes that correction: validate and pass the exact pinned full ADR-0332
    cache registration only to unchanged structural replay, while inheriting
    every v2 source/build/module/identity/atomicity/no-query gate. Pushed v3
    accepts two raw-identical 2,651,673-byte modules (`f9a1e155...`), admits both
    selected helpers, records 1,105/1,033 ms and 289,104/288,312 KiB, and has
    zero path leaks/partial/OOM deltas. T5.5.2 closes; no property query or
    scoreboard row exists.
  - [ADR-0335](../09-decisions/adr-0335-preregister-tock-log2-proof-scoreboard.md)
    freezes the separate measured result: eight defined/zero/floor-log/MSB
    proof rows with checked pure-Rust QF_BV evidence, six wrong-index/
    inverted-zero/high-partition controls replayed against reflection and a
    native oracle, exact limits, pushed-HEAD isolation, and an atomic two-target
    scoreboard. The ignored runner/producer/registration, five focused producer
    tests, independent-spec test, strict Clippy, and full package suite pass with
    the authenticated test skipped. Pushed preflight rejects HEAD's unrelated
    sole absolute corpus symlink before Cargo. Pushed correction `8d059285`
    skips exactly that link while hash-checking all required regular inputs;
    local HEAD/tracking/remote and the repeated capture/registration/archive
    preflight pass. The sole v1 invocation is frozen negative because archived
    HEAD's stale committed `Cargo.lock` fails `--locked --offline` before
    compilation. Zero queries or rows run and no output survives. V2 may change
    only to a committed matching lock snapshot and a new output path.
  - [ADR-0336](../09-decisions/adr-0336-preregister-tock-log2-proof-v2.md)
    freezes that successor: corrected committed lock hash, otherwise identical
    proof/control/solver/trust/replay/resource policy, versioned schemas, new
    output, and a pushed-HEAD non-authenticated build preflight before one run.
    Pushed producer `07b22549` passes that fresh locked/offline preflight with
    one independent-spec test, the authenticated test filtered out, and no v2
    output. Commit/push the zero-query gate before the single official run.
    That sole run is now frozen negative: the first target query returns
    `Proved`, but BitBlast is uncertified while Tseitin and SatRefutation are
    certified. The all-certified gate credits no row and cleanup leaves no
    output. Audit existing lowering evidence before proposing new proof work.
  - [ADR-0337](../09-decisions/adr-0337-preregister-tock-end-to-end-proof-v3.md)
    records that the checker already exists: v3 selects the dual-DRAT
    `certify_qf_bv_unsat_end_to_end_within` route for positive rows, retains
    controls unchanged, and reports its distinct enforceable proof policy.
    Commit/push the zero-result ADR before implementation; no v3 query exists.
    V3 implementation now requires dual recheck plus artifact hashes/sizes,
    preserves controls, and passes ten producer tests, two ordinary Rust tests,
    a non-target route smoke, and targeted Clippy. Push before archive preflight.
    Pushed producer `c22734c3` passes that fresh locked/offline preflight with one
    independent-spec pass, two filtered tests, and no authenticated output.
    The sole v3 run then completes its Rust test but closes negative because the
    test harness prefixes the first proof marker and the column-zero parser sees
    7/8 rows. No result is credited. V3 is frozen; only prefix-aware extraction
    and failure source/log retention may change in a successor.
  - [ADR-0338](../09-decisions/adr-0338-preregister-tock-proof-v4-marker-parser.md)
    freezes that successor as exact parser-only normalization of one proof marker
    after the authenticated test-harness prefix; every v3 gate remains unchanged.
    Accepted v4 then records 8 dual-DRAT proofs, 6 replayed controls, UNKNOWN=0,
    DISAGREE=0, 12.700 s total query time, 1,256,496 KiB peak RSS, and zero OOM
    deltas. T5.5.3 closes. The bounded
    [Tock case study](../../consumer-track/verify/tock-log2-external-case-study.md)
    compares coverage, trust, effort, and measured cost, records that no target
    bug was found, and closes T5.5.4/P5.5 without a rerun or speed claim.
- [x] Can one flat append-only CNF formula representation reduce the retained
  allocation footprint and total cold CNF time without changing any clause,
  proof, verdict, or replay identity?
  - [ADR-0285](../09-decisions/adr-0285-preregister-flat-cnf-formula-arena.md)
    freezes a literal arena, monotone clause ends, reusable Tseitin scratch,
    complete public-consumer migration, exact storage accounting, and a fixed
    structural-then-paired client-corpus gate. Missing scratch prototypes are
    motivating evidence only. The candidate preserves every structural identity
    but fails its frozen per-instance storage gate on 5/162 rows; timing is not
    run and production is restored.
- [ ] Can dense `TermId` indexing reduce full bit-lowering memo cost without
  changing lift maps, exact construction, warm reuse, or client correctness?
  - [ADR-0300](../09-decisions/adr-0300-preregister-dense-bit-lowering-memo.md)
    isolates `Vec<Option<Vec<AigLit>>>` from the absent reported `Rc` prototype.
    Representation-neutral telemetry must first capture the BTree baseline;
    exact 162-query structure/storage gates then precede balanced bit-blast,
    cold-total, family, variance, and RSS timing. This cannot soften IR errors
    or become a performance-lead claim.

## Source Pointers

- Axeyum research index: ../README.md
- Pareto strategy + downstream/SOTA analysis:
  ./axeyum-glaurung-pareto-strategy.md
