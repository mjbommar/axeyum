# Phase 4 — equality saturation and the walk-back contract

Verdict from review: **needs revision — the direction is right, the central
capability claim is overstated by one word: "saturation."**

**Contains gate G2** (task T4.6): measure explanation-chain size before
committing to the upper walk-back tiers.

## The correction

`crates/axeyum-egraph/src/lib.rs` (2,355 lines, single file) is a
**proof-producing, backtrackable congruence-closure engine with e-matching** — a
CDCL(T) and quantifier-instantiation keystone. It is **not** an equality-saturation
engine.

**Present:** lifetime-free `Copy` handles; hash-consed e-node creation with
congruent-node dedup (`add`, :833); backtrackable union-find without path
compression (deliberate, for O(1) undo, :863-878); eager congruence closure via
deferred-merge worklist (`process_pending`, :983-1075); `push`/`pop` trail with 10
`Undo` variants including proof-forest restore; Nieuwenhuis–Oliveras proof forest
with re-rooting and explain-to-LCA (:1081-1231); `explain` (:1130) and structured
`explain_steps -> Vec<ProofStep>` (:1154-1202); an **independent** checker
`check_congruence` (:1293-1354) sharing no state with the incremental engine;
e-matching single/batch/persistent-indexed/candidate-restricted (:474-567);
deterministic count-based work caps (`MAX_MATCH_FRONTIER` 4096,
`MAX_MATCH_WORK_PER_BATCH` 20M, `MAX_CANDIDATE_SUBSTITUTIONS` 65536) — clock-free
and wasm-safe; theory-variable lists and the `theory_var_classes` th_eq bus;
`#![forbid(unsafe_code)]`, zero dependencies.

**Missing — everything that makes "equality saturation" a distinct thing:** no
rewrite-rule application engine (`Pattern` is match-only; no RHS instantiation, no
`Rewrite`/`Applier`), no saturation loop or `Runner`, **no extraction at all**
(`grep extract|cost` finds nothing), no e-class analyses, no deferred rebuilding,
and no reusable IR bridge (four hand-rolled `TermId↔ENodeId` bridges exist:
`euf_egraph.rs`, `qinst_egraph.rs`, `qfufbv_alethe.rs`, `euf_interpolant.rs`).

**The inverse is the good news.** The usual situation — everyone can translate
forward, nobody can walk back — is *inverted* here. The intra-theory walk-back
already works end to end for EUF:

`explain_steps` → Alethe `eq_transitive`/`eq_congruent`/`eq_symmetric`,
**self-validated by `check_alethe` before return** (`euf_alethe.rs`,
`qfufbv_alethe.rs:945-1110`) → Lean-kernel-checked proof terms including n-ary
`eq_congruent` (`reconstruct/equality.rs:315-367`) → plus the independent
non-proof-forest re-validator `check_congruence`.

**Say this in the plan:** axeyum can walk back but cannot yet saturate. Three
M-sized tasks of new code sit behind the word "saturation."

Note also: the repo already did this analysis —
`docs/prover-track/research/12-elaboration-egraphs-fmf.md` §2 reaches the same
conclusion with primary sources, and flags two `[unverified]` numbers that G2 must
measure. `docs/prover-track/design/03-architecture.md:152` wrongly names "egg's
explain_equivalence output" when no egg dependency exists — correct it to
`axeyum_egraph::ProofStep`.

## The rewrite-rule seam

`crates/axeyum-rewrite` is better designed for this than expected.
`RewriteRuleId` is validated, charset-restricted, and version-suffixed (~74
constants in `canonical.rs:17-73`). `RewriteRule` carries `precondition`,
`Preservation::{Denotation, Equisatisfiable}`, `ModelProjection::{Identity,
Required, Implemented}`, and an already-anticipated
`RewriteTestRoute::ProofObligation` (`lib.rs:108-120`) that **nothing consumes
yet** — exactly where a per-rule Lean lemma obligation plugs in.
`RewriteReport`/`RuleApplication {rule_id, before, after}` is a per-application
trail already recorded in deterministic order.

**The catch:** rules are *procedural Rust match arms*, not pattern data. They
cannot be fed to `ematch` as-is. This is a genuine, unbudgeted cost.

**The gate:** only `Preservation::Denotation` rules may enter the e-graph.
Equisatisfiable transforms are not equalities — and several *intra*-theory
preprocessing steps (`solve_eqs_bounded`, `elim_unconstrained` in
`preprocess_reduce`) are equisat-only and carry a `ModelReconstructionTrail`. This
means the correct regime boundary is **equivalence-preserving vs
equisatisfiability-only**, not intra-theory vs inter-theory. Redraw it.

## The walk-back contract

Every bridge ships, at registration, its evidence-crossing behavior per verdict:

```
lift_sat:     Model(Q') → Model(Q)      — total; acceptance = replay-eval of Q's
                                          ORIGINAL assertions (existing Hard Rule)
lift_unsat:   Cert(Q') → LiftedCert(Q)  — one of three declared modes:
   (a) REDERIVE  deterministic per-query re-derivation composing the far cert
                 (precedents: ArrayElimUnsatCertificate::recheck,
                  AckermannUnsatCertificate, BoundedIntBlastCertificate)
   (b) LEMMA     each step is an instance of a proved rule; the far cert composes
                 with per-step lemma instances into one checkable proof
                 (the eqsat case; precedent: forall_inst_guarded's checker rule)
   (c) NONE      verdict crosses, evidence does not — TrustStep{certified:false},
                 an honest, ledger-visible trust hole
lift_unknown: identity
```

Current state per TrustId (the six NONE cells are exactly where evidence does not
cross back today, and they are already enumerated by `trust.rs` — so the contract
is largely a **formalization of existing discipline**, not a new invention):

| TrustId | sat back | unsat back |
|---|---|---|
| BitBlast, Tseitin, SatRefutation | yes | yes (DRAT; miter/Alethe route re-derives the reduction) |
| TermLevelEnum, Farkas, LraDpll, Sos, Diophantine | yes | yes (verifier re-derivation) |
| ArrayElim | yes (`project_model`) | eager: REDERIVE; lazy/CEGAR + extensionality: **NONE** |
| Ackermann | yes | eager: REDERIVE; lazy/QF_AUFBV: **NONE** |
| IntBlast | yes | proven-box: REDERIVE; width-ladder/unbounded: **NONE** |
| DatatypeElim | yes | **NONE** (only fully uncertified TrustId) |
| Fpa2Bv | yes | exact-op/FP8 subsets forward-witnessed; rounding ops and large formats: **NONE** |
| XorGaussian | n/a | pure-Gauss: REDERIVE; interleaved CDCL(XOR): **NONE** |

**Rule for the track:** every *new* bridge declares its mode at registration.
NONE is allowed but ledger-visible.

## Proof-format composition, three tiers

- **Tier 0 (day one)** — re-apply the procedural rule to `lhs`, structurally
  confirm `rhs` (REDERIVE); `check_congruence` with rule instances as premises
  confirms the chain entails `t = t'`. Certifies chain *shape*; rule instances
  remain trusted per-rule via existing manifest tests.
- **Tier 1** — Alethe emission with each rule instance as a premise, via an
  extended checker rule `rewrite_rule_inst` validated the way
  `forall_inst_guarded` already is.
- **Tier 2** — Lean: a lemma library keyed by `RewriteRuleId`; the chain becomes an
  `Eq.trans`/`eq_congruent` spine, already reconstructable. Per
  `docs/prover-track/design/03-architecture.md:182`: **the cost is the spine, not
  the chain.**

Eqsat then runs as a preprocessing bridge of class LEMMA: `Q ≡ Q'`
denotationally, `lift_sat` = identity, `lift_unsat` = prepend the rewrite spine.
It is the one bridge class **fully certifiable from day one at Tier 0**.

## Extend or adopt?

**Recommendation: extend `axeyum-egraph`; do not depend on egg or egglog.**
(a) axeyum-egraph has what egg lacks and axeyum requires — backtracking scopes,
theory variables, an independent checker, deterministic count-based caps,
wasm-safety, zero deps, `forbid(unsafe_code)`; (b) egg is in maintenance mode with
effort moved to egglog, and its `Language` trait would demand the same IR bridge
anyway; (c) **egglog has no proof production** — disqualifying for a
certificate-first stack; (d) determinism is a public API promise here, not there;
(e) ADR-0001 and ADR-0002 both point the same way. Add egg/egglog to
`references/` as design references, the role CaDiCaL and varisat already play.

Design lessons worth copying from egg: the `Runner` budget shape, the
**BackoffScheduler** (deterministic rule throttling), and e-class analyses.
Extraction caution: `reduction_shrinks_encoding`'s own measurements
(`auto.rs:1519-1550`; 062-bench: term DAG 1375→1215 while AIG grew +46%) prove the
true cost is **non-additive and non-local** — extraction must call the capped
lowering probe, not term size. Exact DAG-cost extraction is ILP-hard; start with
bottom-up tree-cost DP.

## Tasks

| id | title | size |
|---|---|---|
| [T4.1](T4.1-adr-extend-vs-adopt.md) | ADR: extend vs adopt; driver placement; `TrustId::RewriteChain` | S |
| [T4.2](T4.2-shared-explain-chain.md) | Shared oriented-chain API `explain_chain(a,b)` | S |
| [T4.3](T4.3-reusable-ir-bridge.md) | Reusable `TermId↔ENodeId` bridge; migrate ≥2 of 4 | M |
| [T4.4](T4.4-rule-ledger-patterns.md) | Rule-instance ledger + pattern-form for ~15 manifest rules | M |
| [T4.5](T4.5-saturation-driver.md) | Saturation driver: rounds, budgets, RHS instantiation | M |
| [T4.6](T4.6-extraction-tier0.md) | Extraction + Tier-0 walk-back; **G2 measurement** | M |
| [T4.7](T4.7-tier1-alethe.md) | Tier-1 Alethe `rewrite_rule_inst` checker extension | L |
| [T4.8](T4.8-tier2-lean.md) | Tier-2 Lean lemma library keyed by `RewriteRuleId` | L |
| [T4.9](T4.9-walkback-contract.md) | `Bridge` walk-back contract retrofitted onto the 14 reductions | M |
| [T4.10](T4.10-crossing-conformance-tests.md) | Evidence-crossing conformance tests | M |

## Risks

- **Semantic overreach** — if the plan ships saying the primitive already exists, a
  later lane will improvise extraction without the ADR.
- **Chain size blowup** — explain-to-LCA is unminimized and congruence premises
  expand recursively (`collect_edge`, :1275-1290, can revisit subchains). FMCAD
  2022 shows proof minimization is NP-complete and gives an O(n log n) greedy.
  G2 measures before anyone commits.
- **Eager congruence under saturation load** — every merge re-canonicalizes parents
  where egg batches it. A batched/deferred mode is an ADR-worthy invariant change.
- **`pop()` nukes retained indexes** (:908-922, clears `merge_events`) — a
  saturation episode must be grow-only within one scope, and chains must be
  harvested *before* popping.
- **Dual rule representations drift** — pattern-form vs procedural-form of the same
  `RewriteRuleId` are two sources of truth; the per-rule differential test is
  mandatory (the `a946f925`/`ba0d9149` class).
- **Reason-space collisions** — `Edge::Input(u32)` means "SAT literal" in CDCL(T)
  consumers and would mean "rule instance" in the driver. One graph, one
  reason-space owner.
- **`check_congruence` does not validate rule instances** (:1298-1300) — a *wrong
  rule instance used as a premise passes*. Tier 0's procedural re-application is
  load-bearing for soundness, and the negative test must corrupt a rule instance
  specifically, not just the chain. It is also O(n²·iterations), so chain
  validation must run over the chain's node subset, not the whole graph.
- **Theory-variable bus ≠ evidence bridge** — `th_vars` is Nelson–Oppen interface
  propagation *within* a solve; the track's bridges are reductions *between*
  problems. Name them differently or a lane will be misdirected.
