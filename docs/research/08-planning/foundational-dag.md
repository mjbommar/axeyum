# Foundational Logic And Math DAG

Status: draft
Last updated: 2026-06-12

## Purpose

Make the step-by-step dependency order explicit from the standpoint of logic,
semantics, and evidence. The roadmap says which engineering phases happen in
which order; this note says which mathematical contracts must exist before a
layer is allowed to depend on another layer.

## Scope

In scope:

- Dependency graph from the current Bool/BV core through pure Rust QF_BV.
- Entry and exit gates for adding logics, operators, rewrites, encodings, and
  proof evidence.
- Requirements that prevent the Z3 oracle from becoming part of the trusted
  core.

Out of scope:

- Detailed API design for each crate.
- Performance schedules or release-date commitments.
- Full proof calculus design for arithmetic, quantifiers, or first-order
  proving.

## Core Claims

- Semantics come before optimization. A term, rewrite, encoding, or backend is
  not a foundation until its denotation and checker are written down.
- The trusted base is a chain of small contracts: typed IR, evaluator, rewrite
  equivalence, bit lowering, CNF equisatisfiability, SAT assignment or proof,
  and model/proof lifting back to the original query.
- Z3 and other native solvers are oracles, not foundations. They can provide
  differential evidence and baseline answers, but they do not discharge the
  pure Rust path's own obligations.
- Every new logic rung must add a semantics source, a representation contract,
  an evidence story, and benchmark coverage before it becomes public surface.

## The Dependency DAG

```text
authoritative semantics
  -> typed sorts and operators
  -> term arena and stable handles
  -> ground evaluator
  -> SMT-LIB parser/writer for the supported fragment
  -> oracle backend translation and model lifting
  -> public corpus baseline
  -> rewrite rules and query object
  -> rewrite equivalence checks and model projection
  -> bit-vector-to-bit lowering
  -> circuit/AIG representation
  -> Tseitin CNF and DIMACS
  -> SAT trait and assignment model
  -> pure Rust BV backend
  -> layered SAT/BV evidence artifacts
  -> custom SAT core and proof logging
  -> arrays/EUF and later theory layers
  -> unified `solve` front door (any theory/quantifier mode)
  -> SMT-LIB text front door (`solve_smtlib`: text -> checked answer)
```

Read every arrow as a proof obligation, not just an implementation dependency.
For example, "rewrite rules -> bit-vector-to-bit lowering" means the
bit-blaster consumes rewritten terms only after the rewrite layer has shown
that it preserves satisfiability and model projection for the supported query
shape.

## Layer Contracts

| Layer | Depends on | Contract | Required check |
|---|---|---|---|
| Authoritative semantics | External standard or local ADR | Operators have total, versioned meanings. | Source link and ADR when diverging. |
| Typed IR | Semantics source | Ill-sorted terms are rejected before solving. | Sort-checking tests and constructor failures. |
| Term arena | Typed IR | Handles are stable, lifetime-free IDs; sharing is observable. | DAG/tree metrics and deterministic traversal tests. |
| Evaluator | Typed IR | Ground interpretation matches the semantics source. | Exhaustive small-width tests and edge-case tests. |
| SMT-LIB import/export | Evaluator | Parsed/exported terms preserve sorts, names, and meaning. | Round trips plus oracle/evaluator replay. |
| Oracle backend | Evaluator and solver trait | Native solver results lift to Axeyum symbols. | Every `sat` model evaluates original assertions. |
| Public baseline | SMT-LIB and oracle backend | Unsupported cases are classified; supported cases agree with expected status. | Versioned benchmark artifact. |
| Rewriter | Evaluator | Rewrites preserve denotation or equisatisfiability with model projection. | Per-rule tests, random evaluator checks, oracle checks. |
| Query planner | Rewriter | Scopes, assumptions, slicing, and caches preserve query meaning. | Projection/replay tests and structural-cache tests. |
| Bit lowering | Evaluator | Each BV term maps to ordered Boolean wires with the same value. | Per-operator bit equivalence tests. |
| Circuit/AIG | Bit lowering | Structural hashing preserves Boolean function identity. | Circuit evaluator and AIGER smoke tests. |
| CNF/Tseitin | Circuit/AIG | CNF is equisatisfiable with the circuit and liftable. | CNF evaluator, DIMACS round trips, lift-map tests. |
| SAT adapter | CNF | SAT assignment satisfies CNF; UNSAT without proof is capability-marked lower assurance. | Assignment replay and capability reporting. |
| Pure Rust BV backend | SAT adapter and lift maps | Backend answers original QF_BV queries without native SMT dependency. | Oracle agreement, model replay, layer timings. |
| SAT proof path | SAT core or proof-capable adapter | UNSAT is checkable outside the solver. | DRAT checker done (`check_drat`, ADR-0011) + proof-producing core (`solve_with_drat_proof`, ADR-0012): end-to-end checked `unsat`. |
| Arrays/EUF | Stable scalar core | Extensionality, select/store, and congruence have evidence hooks. | ADR plus array/EUF-specific model/proof story. |

## Phase Gates

### Current Foundation: Bool And Scalar BV

Bool and fixed-width BV are the current trusted mathematical base. Before more
operators or logics are exposed, the following must remain true:

- The SMT-LIB FixedSizeBitVectors version is recorded in the relevant note or
  ADR.
- Every supported operator has builder sort checks, evaluator semantics, parser
  coverage if it appears in SMT-LIB, writer coverage if it is exported, and at
  least one oracle replay test.
- Operations with surprising totality rules, especially division and remainder
  by zero, have direct tests.

### Phase 2 Exit: Oracle Baseline

Phase 2 is complete only after the public QF_BV baseline records:

- corpus source, hash, selected logic, selected families, timeout, seed, and
  backend version;
- counts for parsed, unsupported, errored, `sat`, `unsat`, `unknown`, status
  agreement, and disagreement;
- shape metrics that identify blow-up risks before rewriting or bit-blasting;
- model replay results for every `sat`;
- a triage list for unsupported constructs, separated from soundness failures.

### Phase 3 Entry: Rewriting And Query Planning

Before implementing always-on rewrites, each rewrite class needs:

- a rule ID that is stable enough for logs and future certificates;
- an explicit precondition over sorts and widths;
- a statement of whether it preserves denotation exactly or only
  equisatisfiability;
- a model-projection story for equisatisfiability-only rewrites;
- a test route: exhaustive small-width, randomized evaluator, oracle
  differential, or later proof obligation.

The query object must land before serious slicing or caching. Slicing without a
first-class assertion/assumption/scope model is a soundness risk because it can
silently change what a model is required to satisfy.

The entry contract is now recorded in
[ADR-0005](../09-decisions/adr-0005-phase3-query-evidence-rewrite-contracts.md):
`axeyum-query` owns assertions, assumptions, and scopes; `axeyum-rewrite` owns
the manifest contract; default rewrites stay denotation-preserving until model
projection is implemented and replay-tested.

The first default canonicalizer now follows that contract: enabled rules are
exact-denotation Boolean/BV identities and constant folds with identity model
projection, focused evaluator-equivalence tests, and Z3 oracle differential
tests. Its first public-corpus artifact records node reductions, rule counts,
original-vs-rewritten oracle comparison, and model replay against original
assertions.

The first query planner keeps the same trusted shape: structural cache keys are
computed from term structure rather than rendered text or arena-local IDs, and
target-support slicing is accepted as a solver fast path only when a sliced
`sat` model replays against every original assertion and assumption. A sliced
`unsat` result is safe because the submitted constraints are a subset of the
original conjunction.

### Phase 4 Entry: Bits, Circuits, And CNF

Bit-blasting may start only after the bit-order convention is recorded. For
each lowered operator:

- input and output wire order must be documented;
- constants and model values must convert through one shared routine;
- the operator must have an evaluator-vs-bits test at small widths;
- the lowering must produce lift maps from SAT variables back to wires and
  from wires back to original terms.

The first CNF encoder should be simple Tseitin. More aggressive encodings only
earn their place after the simple path has a benchmark artifact and a checker.

The Phase 4 entry contract is now recorded in
[ADR-0006](../09-decisions/adr-0006-phase4-bit-order-and-lowering-entry-contract.md):
BV wire vectors are LSB-first, value/model conversions go through shared
helpers, lowering proceeds through AIG before simple Tseitin CNF, and every
`sat` assignment must lift back through explicit maps to replay the original
query.

The first implementation slice now provides those shared conversion helpers in
`axeyum-ir` and a standalone `axeyum-aig` graph/evaluator layer. `axeyum-bv`
now lowers constants, symbols, Boolean connectives, BV bitwise operators,
equality, `ite`, `bvcomp`, concat/extract, zero/sign extension, `bvneg`,
`bvadd`, `bvsub`, unsigned/signed comparisons, `bvshl`, `bvlshr`, `bvashr`,
and constant rotates, with explicit term-bit and symbol-input maps.
`axeyum-cnf` now provides simple Tseitin encoding from AIG, DIMACS parse/write,
CNF evaluation, CNF-variable-to-AIG lift maps, and the first `rustsat-batsat`
SAT adapter path. `sat` assignments now replay through CNF variables, AIG node
values, reconstructed symbol models, and original terms. `axeyum-aig` now
provides deterministic ASCII AIGER debug export. The
[Phase 4 exit audit](phase4-exit-audit.md) records the completed gates and the
explicit deferrals: multiplication/division/remainder lowering, pure-Rust
benchmark-artifact integration, binary AIGER import/export, and proof-backed
UNSAT. Of those, all arithmetic lowering — multiplication (`bvmul`), unsigned
division/remainder (`bvudiv`/`bvurem`), and signed division/remainder/modulo
(`bvsdiv`/`bvsrem`/`bvsmod`) — was subsequently added in Phase 5 (2026-06-13),
each verified exhaustively against the evaluator, completing the full scalar
QF_BV operator set; no arithmetic lowering deferral remains.

### Phase 5 Entry: Pure Rust BV Backend

The pure Rust path can become the default for its supported subset when:

- the backend has no required native C/C++ dependency in the default feature
  set;
- every `sat` model replays against the original, pre-rewrite term;
- every unsupported operator or logic returns a structured unsupported result
  rather than falling back silently to Z3;
- QF_BV public baseline results agree with the oracle on the supported slice;
- timing separates parse, rewrite, bit-blast, CNF, SAT, and model lift costs.

At that point, Z3 is demoted from normal solver dependency to differential
oracle and CI cross-check for the supported subset.

The first Phase 5 implementation slice now provides `SatBvBackend` as a
native-free `SolverBackend` for the supported lowering subset. `sat` answers
are lifted through CNF assignment, AIG node values, Axeyum symbol models, and
ground evaluator replay against the original query. Unsupported lowering
operators return structured `Unsupported` errors. `axeyum-bench` artifact
version 4 introduced the selected backend kind plus AIG/CNF layer statistics
for the pure Rust path, artifact version 5 adds node-budget provenance and
optional Z3 oracle comparison, artifact version 6 adds explicit CNF
variable/clause admission budgets plus submitted query-plan mode and replay
policy, and artifact version 7 adds replay-refinement configuration and
per-instance refinement telemetry. Artifact version 8 records the harness
`jobs` setting for deterministic corpus-level parallel diagnostics. Artifact
version 9 records replay-refinement batch size for exact-target refinement
runs, and artifact version 10 records adaptive-batch policy plus backoff
counts. Artifact version 11 records replay-refinement selection policy.
Artifact version 12 records the bounded plan-aware selection option and the
current root-direct assertion CNF encoder behavior. The
first public QF_BV supported-slice baseline against Z3 is now
recorded: with a 1000-node admission budget, `sat-bv` decides one public `sat`
instance, agrees with Z3 on that decision, reports 112 larger instances as
structured `unknown`, and records zero unsupported cases, errors, oracle
disagreements, or model replay failures. A guarded rerun raises node admission
to 5000 only behind CNF caps; it still decides one public `sat`, classifies one
newly admitted candidate as `EncodingBudget`, and records zero soundness
alarms. A replay-refinement run now grows sliced support sets from failed
full-query replays and accepts `sat` only after the full original query replays;
on the current public slice it recovers the same one decision and records zero
soundness alarms, but does not expand decisions under the current CNF caps and
BatSat timeout. Follow-up sparse-CNF passes use directional signed-comparison
lowering plus private XOR/mux, private AND-tree, OR-of-private-AND, and positive
root-only parity/equality helper recognition during CNF encoding, preserving
explicit lift maps by replaying skipped helper nodes from their children. This
materially reduces the immediate MobileDevice encoding through the sixth
support set, but the seventh support set still stops above the committed
20,000-clause cap. A relaxed-admission public run at 30,000 clauses and a 10s
timeout now reaches 2 public `sat` decisions with Z3 agreement and no soundness
alarms, including the MobileDevice target. A follow-up exact-target relaxed
run keeps those 2 decisions, reduces submitted public DAG shape, eliminates
node-budget unknowns in that profile, and leaves all remaining public unknowns
as `EncodingBudget`. The remaining Phase 5 gate is to reduce the exposed
CNF/SAT cost or improve encodings until the admitted public slice is
representative enough to choose the next encoding, budget, or SAT-core
priority.

### Phase 6 Entry: Custom SAT Core

The custom CDCL core is an identity goal, but it should not cut ahead of
encoding work unless benchmark evidence says SAT time dominates. Before Phase 6
implementation starts, write or update an ADR covering:

- chosen SAT trait shape and whether it is IPASIR-compatible or a strict
  superset;
- proof-logging target: DRAT first, LRAT directly, or another staged path;
- clause database representation and determinism requirements;
- adapter baseline to beat or replace;
- which proof checker discharges UNSAT in high-assurance mode.

### Phase 7 And Horizon Entry

Arrays, EUF, arithmetic, theory combination, quantifiers, and first-order
proving are not just more operators. Each one adds new model and proof
structure. Entering a new rung requires an ADR with:

- logic fragment and decidability assumptions;
- representation changes to `Sort`, terms, binders, or values;
- solver capability flags and unsupported classifications;
- model construction and replay requirements;
- proof/evidence format and checker plan;
- a corpus slice that exercises the new theory.

## Support Matrix

> **Authoritative assurance/evidence per capability lives in the golden-tested
> [capability matrix](capability-matrix.md)**, generated from
> `axeyum_solver::capabilities::CAPABILITIES` (a test fails if the doc drifts).
> The table below is a coarser *planning checklist* (IR / evaluator / SMT-LIB /
> oracle / pure-Rust / evidence per fragment), maintained by hand — prefer the
> capability matrix when the two disagree, and migrate stale rows here over time.

Use this table as the planning checklist before declaring a fragment public.

| Fragment | IR | Evaluator | SMT-LIB | Oracle | Pure Rust | Evidence |
|---|---|---|---|---|---|---|
| Bool | Done | Done | Partial via QF_BV scripts | Z3 | Done for `sat-bv` subset | Model replay |
| Scalar BV | Done | Done | Benchmark-slice parser/writer | Z3 | Full scalar `QF_BV` op set in `sat-bv` | Model replay plus Z3 differential |
| Arrays over finite scalars | `select`/`store` done for Bool/BitVec components | Read-over-write done | Reader + writer done (non-extensional) | Direct Z3 array differential | Eager elimination to QF_BV (ADR-0010) plus replay-guided select interfaces (ADR-0071), lazy ROW (ADR-0072), candidate-guided equality/diff observations (ADR-0073), majority-default models (ADR-0074), original equality flags plus direct-symbol class models (ADR-0077), explanation-guarded base/store-parent scheduling (ADR-0078/0080), Bool/BitVec component admission (ADR-0079), same-search local ROW insertion (ADR-0081), same-search pair-generated scalar interfaces over pre-observed terms (ADR-0082), and array-valued UF result projection by final application class (ADR-0084); structural store/ITE/default class ownership and warm depth remain | Model projection + evaluator replay; 2,592 online/analytic/eager/front-door/Z3 comparisons, including 384 Bool/mixed, 384 structural-store, 384 dynamic-ROW, 384 dynamic-interface, and 288 array-result cases; direct equal-array select congruence checks in-tree/Carcara/Lean without a reduction trust step (ADR-0075) |
| EUF | `declare_fun`/`apply` done for scalar and flat array results (ADR-0013/0084) | `Op::Apply` against a full-value `FuncValue` model | Reader + writer round-trip done (`declare-fun` n-ary + applications, including array results) | Direct Z3 comparison after canonical abstraction | Eager Ackermann elimination plus abstraction-only lazy solving; bounded scalar QF_UFBV combines the e-graph and warm BV solver through canonical `CdclT` (ADR-0066), exact ground-distinct pruning (ADR-0069), and replay-guided dynamic interface materialization (ADR-0070); array-result UFs use the canonical AUFBV bus while eager elimination declines them (ADR-0084) | Model projection + original-query replay; `function_catalog`, eager/online, front-door, and Z3 differentials, including 288 array-result comparisons |
| QF_AUFBV / QF_AUFLIA (arrays + UF + ints) | Composed from arrays + EUF + LIA | Composed | Composed (all passes) | Direct Z3 QF_AUFBV differential; arithmetic mixes reduce first | QF_AUFBV composes lazy ROW/base-select/equality arrays → functions, keeps array equality on live `EufTheory`, schedules explanation-guarded base/store/application-parent reads, appends candidate-violated scalar UF/select/extensionality interfaces inside one retained search, and projects finite-scalar array-valued UF results by final e-class (ADR-0071/72/73/77/78/79/80/81/82/84); QF_AUFLIA retains the stacked/lazy routes | Combined array-first/function-second projection + original replay; integer-bearing `unsat`/overflow → `unknown`; structural store/ITE/default class ownership and non-finite/warm depth remain |
| QF_LIA (integers) | `Int` sort + linear ops done (ADR-0014) | `Int` arithmetic over `i128` reference | Reader + writer round-trip done (`Int`, literals, `+`/`-`/`*`/`<`…, `QF_LIA`) | Rejected (blasted to BV first) | Bounded bit-blasting done (`check_with_int_blasting`); `integer_catalog` differential | Integer model read-back + exact replay; bounded `unsat`/overflow → `unknown` |
| QF_LRA (reals, conjunctive) | `Real` sort + exact `Rational` + linear ops done (ADR-0015) | Exact rational arithmetic | Reader + writer round-trip done (`Real`, `n.0`/`(/ ..)` literals, numeral coercion, `QF_LRA`) | n/a (own procedure) | Fourier–Motzkin over exact rationals (`check_with_lra`); `real_catalog` differential | Rational model + evaluator replay; `unsat` lower-assurance (Farkas pending); `or`/disequality need DPLL(T) |
| Quantifiers | `forall`/`exists` (named binders, ADR-0016) | Finite-domain enumeration (Bool/BV) | Reader + writer round-trip (binder form, fresh-symbol scoping) | n/a (expanded first) | Finite-domain expansion (`check_with_quantifiers`); E-matching pending | Original-formula replay via enumerating evaluator |
| Proof artifacts | Envelope ADR | N/A | Exportable DIMACS + DRAT text (`export_qf_bv_unsat_proof`) | Oracle-specific | DRAT checker (ADR-0011) + proof-producing core (ADR-0012) | DRAT (RUP+RAT) checked in-tree and re-checkable externally (drat-trim) |
| Front door | n/a | n/a | `solve_smtlib`: SMT-LIB text → checked answer (ADR-0018) | via `solve` | `solve` routes any theory/quantifier mode; `solve_smtlib` adds the text path | Decision cross-checked against script `:status`; model replay inside `solve` |

## Web And Reference Refresh Gates

Use web search or refreshed local references at design gates, not constantly.
Required refresh points:

- before changing BV semantics or SMT-LIB support, check the current SMT-LIB
  FixedSizeBitVectors theory page and benchmark release notes;
- before choosing a replacement or second Rust SAT adapter, compare RustSAT,
  splr, varisat, and any maintained proof-capable options against the benchmark
  methodology;
- before proof-format commitments, refresh cvc5 proof-format docs, Alethe,
  Carcara, DRAT/FRAT/LRAT tooling, and verified checker status;
- before arrays/EUF, refresh Bitwuzla/cvc5/Z3 behavior and SMT-LIB logic
  definitions for QF_ABV and QF_AUFBV;
- before horizon work, refresh primary papers and active implementations for
  simplex/branch-and-bound, Nelson-Oppen or CDCL(T), E-matching, MBQI, and
  superposition.

## Design Implications

- Roadmap phases should name not just deliverables, but the contract each
  deliverable proves.
- `Unknown` and `Unsupported` remain distinct: resource limits are not missing
  features, and missing features are not solver uncertainty.
- Generated artifacts need stable provenance fields: semantics version, rewrite
  rule set version, bit-blaster version, CNF encoder version, SAT backend
  version, seed, resource limits, and source corpus hash.
- Avoid adding public operators whose model replay cannot be implemented yet.
- Treat model projection as a first-class output of every transformation, not a
  side table that can be dropped after solving.

## Risks

- A phase can appear complete while an arrow in the DAG is unproven. Mitigate
  by tying every phase exit to required checks above.
- Oracle agreement can hide matching bugs if both paths share a wrong
  translation. Mitigate with independent evaluator tests and small exhaustive
  checks.
- Adding arrays, EUF, or arithmetic before scalar BV evidence is solid can
  multiply proof obligations faster than the checker infrastructure grows.

## Open Questions

- [x] What exact evidence envelope should carry model replay, lift maps, and
      future proof artifacts?
  - Answer: ADR-0005 records the layered evidence envelope; shared concrete
    evidence types are deferred until a second artifact producer needs them.
- [ ] Which public support matrix should ship in the README or rustdoc for the
      first release?
- [x] Should equisatisfiability-only rewrites be allowed before model
      projection is implemented?
  - Answer: they may be recorded while disabled, but must not be default until
    projection is implemented and replay-tested; see ADR-0005.
- [x] Which proof checker is the default high-assurance gate once UNSAT proofs
      exist?
  - Answer: an in-tree DRAT checker (RUP + RAT, `axeyum_cnf::check_drat`),
    chosen and built first as the trust anchor; see
    [ADR-0011](../09-decisions/adr-0011-drat-unsat-proof-checking.md). A DRAT
    producer (proof-capable adapter or the custom CDCL core) is the remaining
    piece to make UNSAT high-assurance end to end.

## Source Pointers

- SMT-LIB FixedSizeBitVectors: https://smt-lib.org/theories-FixedSizeBitVectors.shtml
- SMT-LIB benchmarks: https://smt-lib.org/benchmarks.shtml
- cvc5 proof production: https://cvc5.github.io/docs/latest/proofs/proofs.html
- RustSAT: https://github.com/chrjabs/rustsat
- Alethe proof format: https://verit.gitlabpages.uliege.be/alethe/
- Carcara Alethe checker: https://github.com/ufmg-smite/carcara
- DRAT-trim: https://github.com/marijnheule/drat-trim
- FRAT format: https://github.com/digama0/frat
