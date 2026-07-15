# Research Questions

Status: draft
Last updated: 2026-07-11

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
  - Answer (stage 1): a warm SAT layer with monotone clause addition plus
    one-shot assumption literals, and a high-level `Solver` façade exposing
    `assert`/`push`/`pop`/`check`/`check_assuming` over it; `push`/`pop` map to
    selector (assumption) literals. Implemented as `IncrementalSat`
    (`axeyum-cnf`) and the `Solver` façade (`axeyum-solver`); see
    [ADR-0009](../09-decisions/adr-0009-incremental-sat-and-solving.md). Stage 2
    (incremental bit-blasting through the same warm layer) is planned there.
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
- [x] Should solver cancellation support memory budgets as well as time?
  - Answer: yes; `SolverConfig` carries timeout, deterministic resource,
    memory, and node budgets. Memory-budget exhaustion is an `Unknown`
    classification, not an error.
- [ ] Frozen-arena type-state or runtime single-writer discipline?

### Formats

- [x] Full SMT-LIB script support or benchmark-slice parsing first?
  - Answer: benchmark-slice parsing first, with explicit Unsupported errors
    for arrays, UF, and incremental commands; implemented in `axeyum-smtlib`.
- [ ] Which SMT-LIB standard/theory versions should be pinned in artifacts
      and tests before adding conversion operators or future logics?
- [ ] When does BTOR2 import earn its keep?
- [x] Where does the format parser crate boundary land?
  - Answer: `axeyum-smtlib` is a dedicated crate because parsing/writing is
    exercised by solver tests and the benchmark harness, not just a CLI.

### Parallelism

- [ ] Is portfolio dispatch in scope for the first public release?
- [ ] What must be `Send`/`Sync` to make portfolio solving natural?

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
- [ ] Should the proof-assistant bridge export obligations to Lean, import
      checked rewrite rules from Lean, or both — and how early is a
      Lean-checked rewrite-rule library worth prototyping?
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

## Source Pointers

- Axeyum research index: ../README.md
