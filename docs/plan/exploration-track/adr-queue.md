# ADR queue

Per CLAUDE.md, decisions are not made silently in code. Every question below came
out of a branch review and must be closed with an ADR (template in
[`docs/research/09-decisions/README.md`](../../research/09-decisions/README.md))
before its dependent tasks land. Cross-check against
[`research-questions.md`](../../research/08-planning/research-questions.md) and the
[foundational DAG](../../research/08-planning/foundational-dag.md).

## Blocking — a phase cannot start without these

| # | Question | Phase | Why it blocks |
|---|---|---|---|
| A1 | **Direction algebra scope**: the 4-element verdict-preserving lattice (MVP) vs the partial-verdict-map monoid. Decided by whether the search alphabet will ever contain negation/duality/abduction edges. | 1 | Choosing wrong makes negation edges either unrepresentable forever or silently unsound. MVP recommendation: make them unrepresentable and record the restriction. |
| A2 | **Bridge boundary and dependency direction**: where CAS certificate types and checkers live, given the solver must not depend on a 47k-line search crate. Options: extract a small shared poly kernel; certificate-only module in `axeyum-solver`; CAS as out-of-process search (the polyrith model). | 5 | Task zero for every lateral bridge; a careless edge inverts ADR-0301. |
| A3 | **External CDCL as untrusted conquer engine**: subprocess DIMACS-in/proof-out, native recheck mandatory, default build untouched. Must be fenced against ADR-0002. | 6 | Determines whether the open-problem lane is compute-feasible at all. |
| A4 | **Policy artifact contract**: format, versioning, hash-pinning, regeneration gates, and the rule that learning happens only in offline releases. | 3 | This is a new *public determinism surface* and deserves ADR-0001-class standing. |
| A5 | **Agentic loop boundary**: where the driver lives; whether an HTTP client is acceptable in-workspace vs a script outside the crate graph; the explicit statement that no default build or gate contacts a network. | 7 | Touching the no-C-dep, wasm-clean default build. |
| A6 | **Open-problem artifact family and claim-label extension**: new `artifacts/open-problems/` tree vs reuse; the `shadow.json` schema; the bounded-sweep display row; validator vocabulary changes. | 8 | Every artifact in the phase is shaped by it. |
| A7 | **Extend `axeyum-egraph` vs adopt egg/egglog**; eqsat driver placement; `TrustId::RewriteChain`. | 4 | Recommendation is *extend* (egglog has no proof production — disqualifying); record it. |
| A8 | **Second-kernel program scope**: adopt the nanoda-bin contract + Arena entry; versioning policy (exact-pin vs 3.1.x semver range); the lineage-qualified diversity claim language; the decline taxonomy. | 9 | Shapes the checker binary's contract. |

## Structural — needed before the corresponding surface goes public

| # | Question | Phase |
|---|---|---|
| B1 | **Soundness-direction vocabulary placement**: a new artifact-level taxonomy vs fields on `TrustId`/`TrustStep` (which would touch the golden-tested ledger). | 0, 1 |
| B2 | **Descriptive vs prescriptive catalogue**: does dispatch ever *consume* the artifact, and what re-validation gates the flip? Pre-commit the gate: byte-identical `RouteTrace` on the full corpus. | 0, 3 |
| B3 | **Route labels as public API**: promoting `&'static str` labels to a registry makes them a determinism-promise surface. Naming/stability policy. | 0 |
| B4 | **Atlas granularity**: add rows for exercised combination fragments (QF_BVLIA/bv2nat, QF_UFLRA, QF_LIRA, QF_AUFBV, strings) vs allow feature-mask fragment expressions. Also reconcile the atlas's prose `solver_routes[].name` with catalogue edge ids. | 0 |
| B5 | **Evidence format change**: does `EvidenceReport` grow composed-direction + chain-provenance fields (a `SEMANTICS_VERSION`-governed change)? Must consumers distinguish "unsat, licensed, uncertified" from today's bare `Unsat(None)`? | 1 |
| B6 | **Model-lift typing**: is mandatory replay-against-source sufficient (lift maps as optimization), or must lift totality be a typed per-edge obligation? Relevant for quantified models with Skolem certificates. | 1 |
| B7 | **Reward scalarization and assurance modes**: α/β weights; `evidence-required` vs `verdict-only`; the ruling that certified-weaker outranks uncertified-stronger by default. A project-wide semantics decision about what "better" means. | 2 |
| B8 | **Chain trust composition**: formalize "trust of a chain = meet of edge trust classes," mapping `axeyum-rewrite` manifest contracts and atlas `proof_routes.status` onto one lattice. | 2, 5 |
| B9 | **Feature extraction as public surface**: versioned artifact (determinism applies to exact values) or internal detail? Are probing features (a bounded solver call inside feature extraction) acceptable under "explicit resource limits"? | 2 |
| B10 | **New `TrustId`s**: `Nullstellensatz`; Smith/Hermite as new id vs certified sub-case of `Diophantine`; whether WZ registers at all given it has no solver traffic. | 5 |
| B11 | **Certificate domain policy**: i128 vs BigInt coefficients in serialized certificates; monomial-order field in the certificate format. | 5 |
| B12 | **Two-tier determinism contract for parallel search** (verdict-deterministic unconditionally; trace-deterministic mode; wall clocks only at kill boundaries). Extends rather than weakens the public promise. | 6 |
| B13 | **Proof format at scale**: LRAT-first for cube proofs? On-the-fly vs post-hoc checking? Per-cube retention policy (check-then-delete with a signed ledger vs archival). | 6 |
| B14 | **Cube manifest as a public evidence artifact**: is (manifest, tautology proof, ledger) a first-class evidence type with model-grade replay guarantees? | 6 |
| B15 | **Hint-channel contract**: an ADR-0050-style invariant for externally supplied hints — hint classes, what "checked before use" means per class, and the verdict-invariance differential gate. | 7 |
| B16 | **Crediting policy**: do agent-assisted decides count in SCOREBOARD decide-rate, a separate row, or not until baked into a deterministic route? Recommendation: separate row + ledger hash. | 7 |
| B17 | **Evidence-ladder rungs as public API**: the R0–R6 enumeration in `EvidenceReport`; the R6 self-challenge artifact format; the rule tying R4+ claims to axiom-ledger discharge state. | 9 |
| B18 | **Shadow trust tier**: is a derived shadow publishable at `replay-only`, or does any public claim require Lean-elaborated decidability and/or the `decide` tie-back? Proposed: `derivation = reviewed` vs `lean-confirmed`, with witness claims requiring the latter. | 8 |
| B19 | **Default arithmetic route for shadows**: ground evaluator vs `axeyum-cas` exact integers vs BV-with-width-disclosure. | 8 |

## Deferred — record the trigger, decide later

| # | Question | Trigger |
|---|---|---|
| C1 | Parameterized bridges: chain-level parameters frozen in policy vs runtime ladders. Decides whether offline MCTS is ever needed. | T3.7/T3.9 plateau vs virtual-best |
| C2 | Batched/deferred congruence mode in `axeyum-egraph` (changes stated invariants and trail/proof-forest interaction). | G2 measurements demand it |
| C3 | Extraction cost-function contract as a public deterministic promise; whether ILP/DAG-aware extraction is ever in scope given no-C/C++-deps constrains solver choice. | tree-cost extraction measurably leaves value on the table |
| C4 | Shared MCTS skeleton across bridge search and cube generation (AlphaMapleSAT precedent). | both phases reach their MCTS tasks |
| C5 | Parallel kernel architecture for the Lean checker (sharded interner is ready; `&mut self` is not). | T9.10 profiling shows it binds |
| C6 | Local/fine-tuned sampler for the agentic loop. | ~10⁵ attempts/month, or air-gapped reproducibility required |
| C7 | Cloud burst policy for cube manifests; what the reproducibility artifact must capture (engine binary hash per cube). | a target exceeds the workstation band |
| C8 | SOS search phasing beyond LDLᵀ/DSOS: building rational SDP; degree-escalation budget semantics. | B3-lite saturates |
| C9 | Upstream engagement policy for formal-conjectures (Google CLA); whether misformalization findings publish before upstream acknowledgment. | first real signal found |
| C10 | Quantifier/preamble trace coverage: do quantifier engines get route labels or a separate trace type? | T0.6 |
