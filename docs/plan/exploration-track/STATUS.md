# STATUS — exploration track

The **live tracker** for [`docs/plan/exploration-track/`](README.md).
[`README.md`](README.md) is the map; this file is where we are.

Status legend: `TODO` · `WIP` · `DONE` · `BLOCKED` — matching the root
[STATUS.md](../../../STATUS.md) convention.

> This track is **proposed, not accepted**. Every phase carries an ADR gate
> ([`adr-queue.md`](adr-queue.md)); no task below may land before its blocking ADR.
> The track does not preempt the active QF_BVFP/binary79 focus or the paused CAS
> lane.

## Current focus

Two increments landed 2026-08-01, one per direction the track needs to move.

**Bottom-up — `T9.1 DONE`, `T0.1 WIP`.** The axiom ledger is fully classified
(zero `unclassified`, `--check` passing), and `RouteTrace::to_json()` makes
dispatch order data rather than prose — verified over `corpus/regression` with
all 140 emitted lines parsing as valid JSON, and every pre-merge gate green.

**Top-down.** The track is now indexed in
[`docs/plan/README.md`](../README.md), so it is reachable from the repo's plan
index instead of orphaned.

**Next, in priority order:**

1. **T3.5** — policy-v0 ≡ legacy dispatch. Still the track's highest-value single
   task and the only safe way to touch `auto.rs`.
2. **T0.6** — recorder sites across the `solve()` preamble and quantifier engines,
   plus a `solve_explained` entry point. Newly a prerequisite: T0.1's bench half
   is blocked on it, because the bench calls `solve()` and `solve()` records
   nothing.
3. **T2.5** — public-corpus supplement. Newly motivated: the regression corpus
   exercises only ~half the route labels, so the T0.4 validator would be blind on
   the rest.
4. **T9.3 / T9.2** — the phase-9 consolidation half feeding T9.4 (R6), which needs
   only the small preludes rather than mathlib.

**Blocked and recorded:** discharging the seven `derivable-theorem` rows — see
the changelog entry below for why (an unrunnable official-Lean gate).

See [`sequencing.md`](sequencing.md) for the reasoning and the recommended first
slice.

## Gate state

| Gate | Task | Question | State |
|---|---|---|---|
| **G1** | T2.3 | Is the VBS–SBS PAR-2 ratio above ~1.1 on decidable instances? | `TODO` — **blocks all of phase 3** |
| **G2** | T4.6 | Do congruence-closure explanation chains stay tractable? | `TODO` — blocks phase-4 tiers 1–2 |
| **G3** | T6.10 | What is reachable in the 10²–10⁴ CPU-hour band? | `TODO` — calibrates phase 8 targets |

No gate has reported. **No expensive work starts before its gate reports.**

## Phase state

| Phase | Title | Tasks | State |
|---|---|---|---|
| [0](phase-0-catalogue/README.md) | Bridge catalogue as data | 7 | `WIP` — T0.1 rendering landed |
| [1](phase-1-direction/README.md) | Direction algebra + verdict licensing | 7 | `TODO` |
| [2](phase-2-evaluation/README.md) | Evaluation harness and reward signal | 10 | `TODO` |
| [3](phase-3-policy/README.md) | Searched route policy | 10 | `TODO` |
| [4](phase-4-eqsat-walkback/README.md) | Equality saturation + walk-back contract | 10 | `TODO` |
| [5](phase-5-lateral-bridges/README.md) | Lateral bridges from the CAS | 10 | `TODO` |
| [6](phase-6-parallel/README.md) | Parallel search and cube-and-conquer | 10 | `TODO` |
| [7](phase-7-agentic-loop/README.md) | LLM-in-the-loop proposal layer | 10 | `TODO` |
| [8](phase-8-open-problems/README.md) | Open-problem intake and triage | 10 | `TODO` |
| [9](phase-9-lean-evidence/README.md) | Lean evidence ladder and Comparator | 12 | `WIP` — 1/12 done (T9.1) |

## Changelog

### 2026-08-01 — T0.1 route-trace JSON rendering landed (`WIP`, 2 of 3 files)

`RouteTrace::to_json()` plus a `--json` JSONL mode on `explain_corpus`.
**Dispatch order is now data**, which is the prerequisite the rest of phase 0
and the T0.4 replay validator were blocked on.

Verified end to end over `corpus/regression`: 140 lines emitted, **all 140 parse
as valid JSON**, 127 carrying a trace. Gates green — verdict-invariance
differential 12/12, full solver `--lib` sweep 967/967, `corpus_regression`,
`progress_frontier` 9/9, `cargo doc -D warnings`, and clippy with **zero
findings in either changed file**.

**First measured edge coverage:** the regression corpus exercises **22 distinct
route labels** against roughly 45 in `auto.rs` — about **half** the catalogue.
Recorded in [T0.4](phase-0-catalogue/T0.4-behavioral-replay-validator.md), because
a replay validator that passes while never touching half the edges reads as
"correct" when it is only "consistent on the exercised half."

**Dependency error found in this plan and corrected.** T0.1's bench half is not
merely open, it is **`BLOCKED`**. `axeyum-bench` calls `solve()`, not
`check_auto_explained`, and `solve()` (`auto.rs:318`) has **zero recorder call
sites**; there is no `solve_explained`. Pointing the bench at
`check_auto_explained` would stop it measuring the quantifier preamble — a
measurement-integrity break — and threading a recorder without adding preamble
sites would produce traces that silently omit it, exactly the blindness T0.4
warns about. So **T0.6 is promoted from "independent slice" to a prerequisite of
T0.1**, and its deliverable now explicitly includes a public `solve_explained`
entry point. T0.1, T0.6, the phase README, and this table are updated.

**Gotcha found, worth propagating:** `cargo test -p axeyum-solver --lib`
compiles only **23** tests — the module list lives inside a `full_modules!()`
macro gated on `#[cfg(feature = "full")]` (`lib.rs:34`, `:195`).
`--features full` yields **967**. CLAUDE.md warns `--lib` skips `tests/*.rs`;
this is sharper — bare `--lib` can silently skip *unit* tests too.

**Pre-existing issue, untouched:** `cargo clippy --all-features` fails on
`crates/axeyum-solver/src/qinst_egraph.rs:5082` (`collapsible_match`). That file
is clean in git and the local toolchain is **nightly 1.97** while CI runs stable,
so this is almost certainly a nightly-only lint on committed code. Not mine to
fix under the multi-agent rules — flagged, not touched.

### 2026-08-01 — T9.1 axiom-ledger triage `DONE`

All 65 reconstruction-prelude assumptions classified; **zero `unclassified`,
zero `unreviewed`** (was 65/65 of each). Counts:
**17 primitive-interface · 41 external-assumption · 7 derivable-theorem · 0 defect**;
discharge **58 retained · 7 planned**. `--check` passes — the source inventory
matched with no name or canonical-type drift.

Three substantive findings, each recorded in the affected rows' notes so the
claim is reviewable rather than asserted:

1. **The real profile is not linearly ordered.** It admits neither `le_total`
   nor `eq_em`, so `sq_nonneg` is a genuine assumption there rather than the
   usual case-split consequence. The real prelude is a *partially* ordered
   commutative ring; the integer prelude is the linearly ordered, discrete one.
2. **`integer::eq_em` is a direct instance of `Classical.em`** applied to
   `Eq Z x y`, and `Classical.em` is already declared by
   `crates/axeyum-solver/src/reconstruct.rs` as the reconstruction route's one
   genuine logical axiom. Discharging it removes a *theory-specific* assumption
   in favour of the already-accepted logical one — a strict shrink of the
   integer profile's trusted base, not a relabelling.
3. **Seven rows are derivable from their own prelude's other axioms:**
   `mul_zero` (ring cancellation via `left_distrib`), `mul_nonneg`
   (`mul_le_mul_of_nonneg_left` at `x1 := zero`, plus `mul_zero`), and
   `lt_trans` (`le_of_lt` then `lt_of_lt_of_le`) in both arithmetic preludes,
   plus `integer::eq_em`. Each note carries the derivation and its dependencies.

Files: `docs/plan/lean-axiom-ledger-v1.json`,
`docs/plan/generated/lean-axiom-ledger.md` (regenerated).

Not done, and deliberately out of scope for T9.1: actually *writing* the seven
theorem terms. **That discharge is now `BLOCKED`**, for a reason worth recording
— it was investigated, not skipped. Discharging converts a `Declaration::Axiom`
into a `Declaration::Theorem`, which `lean_pp.rs` renders differently, so the
exported Lean module changes and official Lean must accept the new proof term.
**Neither `lean` nor `elan` is installed here, so the 70/70
`AXEYUM_REQUIRE_LEAN=1` crosscheck cannot run.** The seven rows are also live
(`lt_trans` is used by `reconstruct/arithmetic.rs:4036,4161`), the declaration
order needs fixing, and removing any axiom breaks six hardcoded counts across the
generator and its tests. Full prerequisite list in
[T9.1](phase-9-lean-evidence/T9.1-axiom-ledger-triage.md#follow-on-discharging-the-seven-planned-rows-is-blocked).

### 2026-08-01 — track authored

- Nine independent branch reviews run (read-only, web-enabled), one per branch:
  bridge catalogue, direction algebra, search algorithms, eqsat/walk-back,
  evaluation harness, lateral CAS bridges, parallel/cube-and-conquer, agentic
  loop, Lean/Comparator.
- **No branch returned "sound as proposed."** Eight material corrections recorded
  in [`00-review-synthesis.md`](00-review-synthesis.md); five of them invalidate
  first-instinct designs.
- Plan written: 10 phases, 96 tasks, 3 measurement gates, 8 blocking ADRs +
  19 structural + 10 deferred ([`adr-queue.md`](adr-queue.md)), 30-entry ranked
  risk register ([`risks.md`](risks.md)).
- Not linked from root `PLAN.md`/`STATUS.md` yet — see "Integration" below.

## Integration with the repo's session protocol

Outstanding, deliberately not done unilaterally because these are shared mutable
files that other lanes write to:

- [x] **Done 2026-08-01.** Indexed in [`docs/plan/README.md`](../README.md)
      alongside the other sub-plans, marked "proposed, not accepted", with
      pointers to this file and the ADR queue.
- [x] **Done 2026-08-01.** Root [`PLAN.md`](../../../PLAN.md) § Track map now
      carries the track as an explicitly **cross-cutting, proposed** item rather
      than a numbered track — it spans Track 1 (dispatch/strategy), Track 2 (new
      routes from lateral bridges), and Track 3 (the evidence ladder). This
      reverses the earlier "not until accepted" call: CLAUDE.md's Session
      Protocol names PLAN.md as the file to read *first*, so a track absent from
      it is unreachable by anyone following the protocol. Discoverability and
      acceptance are different things; the entry says "PROPOSED, not accepted"
      in its first line.
- [x] **Done 2026-08-01.** Root [`STATUS.md`](../../../STATUS.md) carries a
      delimited pointer declaring **this file** the authority for the track,
      honouring that file's "each lane owns its own section" convention. The 96
      task rows are deliberately not mirrored there.
- [x] **Done 2026-08-01.** The eight *blocking* ADR questions are registered in
      [`research-questions.md`](../../research/08-planning/research-questions.md)
      § Exploration Track, per CLAUDE.md's rule that decisions are not made
      silently in code. The full 37-item queue stays in
      [`adr-queue.md`](adr-queue.md); only the blocking set is mirrored so the
      standing register remains the entry point.
- [x] **Done 2026-08-01.** [`roadmap.md`](../../research/08-planning/roadmap.md)
      § Beyond Phase 7 carries a short pointer — Session Protocol step 2 sends
      agents to the roadmap, and that file's own convention is to defer detail
      to PLAN.md/STATUS.md.
- [ ] **Deliberately NOT done: `CLAUDE.md`.** That file is settled identity,
      standing rules, and gates — not a plan index. A proposed track does not
      belong there. Revisit only if the track is accepted *and* introduces a
      standing rule or a pre-merge gate an agent must obey (the likeliest
      candidate is a direction-composition invariant from phase 1).
- [ ] **Deliberately NOT done: `foundational-dag.md`.** CLAUDE.md requires a DAG
      check before new *public* operators, rewrites, encodings, backends, or
      logic fragments. Nothing landed so far adds public surface. **Phase 5
      (lateral bridges) will** — `TrustId::Nullstellensatz` and the Smith/Hermite
      and SOS-degree-lift certificates are exactly that, so T5.1's ADR must
      update the DAG before any of them becomes public.
- [ ] **Deliberately NOT done: `docs/PROJECT-STATE.md`.** It is the short public
      account of what is *built and measured*. The track is proposed; it earns a
      line when a phase produces a measured capability claim, not before.

## Task state

`Blocked by` lists only in-track dependencies; ADR gates are in
[`adr-queue.md`](adr-queue.md).


### Phase 0 — Bridge catalogue as data

| id | task | size | state | blocked by |
|---|---|---|---|---|
| [T0.1](phase-0-catalogue/T0.1-route-trace-json-export.md) | RouteTrace JSON export + bench persistence | S | `WIP` — render `DONE`; bench half `BLOCKED` on T0.6 | rendering: none; bench: **T0.6** |
| [T0.2](phase-0-catalogue/T0.2-route-registry.md) | Route registry (`ALL_ROUTES`) + coverage test | M | `TODO` | none (parallel with T0.1) |
| [T0.3](phase-0-catalogue/T0.3-catalogue-artifact.md) | Catalogue artifact, schema, structural + golden validators | M | `TODO` | T0.2 |
| [T0.4](phase-0-catalogue/T0.4-behavioral-replay-validator.md) | Behavioral replay validator | M-L | `TODO` | T0.1, T0.2, T0.3 |
| [T0.5](phase-0-catalogue/T0.5-soundness-direction-audit.md) | Per-edge soundness-direction audit + ADR | M | `TODO` | T0.2, T0.3 |
| [T0.6](phase-0-catalogue/T0.6-coverage-expansion.md) | Trace coverage for `solve()` preamble + quantifier routes, plus `solve_explained` | L | `TODO` — **promoted to prerequisite** | T0.2 |
| [T0.7](phase-0-catalogue/T0.7-measured-cost-model.md) | Measured cost model from bench artifacts | M | `TODO` | T0.1, T0.3 |

### Phase 1 — Direction algebra + verdict licensing

| id | task | size | state | blocked by |
|---|---|---|---|---|
| [T1.1](phase-1-direction/T1.1-direction-monoid.md) | `Direction` monoid + law property tests | S | `TODO` | none |
| [T1.2](phase-1-direction/T1.2-edge-inventory-ledger.md) | Edge inventory + golden direction ledger | M | `TODO` | T1.1, phase-0 T0.5 |
| [T1.3](phase-1-direction/T1.3-bridge-chain-types.md) | `Bridge`/`AppliedBridge`/`Chain`/`LicensedVerdict` + 3 pilot edges | M | `TODO` | T1.1, T1.2 |
| [T1.4](phase-1-direction/T1.4-model-lift-cegar.md) | Model-lift axis + CEGAR combinator | M | `TODO` | T1.3 |
| [T1.5](phase-1-direction/T1.5-soundness-negative-fuzz.md) | Soundness-negative chain fuzz + direction-flip mutation gate | L | `TODO` | T1.1, T1.3 |
| [T1.6](phase-1-direction/T1.6-licensed-verdict-surface.md) | Search surface restricted to `LicensedVerdict`; evidence provenance | L | `TODO` | T1.3, T1.4, T1.5 |
| [T1.7](phase-1-direction/T1.7-adrs.md) | ADRs: direction algebra scope; ledger placement | S | `TODO` | can start first |

### Phase 2 — Evaluation harness and reward signal

| id | task | size | state | blocked by |
|---|---|---|---|---|
| [T2.1](phase-2-evaluation/T2.1-feature-extractor.md) | Deterministic instance-feature extractor | M | `TODO` | none |
| [T2.2](phase-2-evaluation/T2.2-episode-logger-aslib.md) | Episode logger + ASlib-format export | M | `TODO` | T2.1 |
| [T2.3](phase-2-evaluation/T2.3-vbs-sbs-gate.md) | G1: VBS-SBS signal measurement | S | `TODO` | T2.2 |
| [T2.4](phase-2-evaluation/T2.4-graduated-generator-set.md) | Graduated generator eval set | M | `TODO` | none |
| [T2.5](phase-2-evaluation/T2.5-public-corpus-supplement.md) | Public-corpus supplement per atlas row | M | `TODO` | none |
| [T2.6](phase-2-evaluation/T2.6-hardened-pack-variants.md) | Hardened pack variants | M | `TODO` | T2.4 |
| [T2.7](phase-2-evaluation/T2.7-vector-reward.md) | Vector reward + scalarization | S | `TODO` | T2.2, ADR B7 |
| [T2.8](phase-2-evaluation/T2.8-cv-significance-harness.md) | Family-grouped CV + significance harness | M | `TODO` | T2.2, T2.4 |
| [T2.9](phase-2-evaluation/T2.9-dispatch-frontier-ratchet.md) | `dispatch_frontier` ratchet gate | M | `TODO` | T2.4, T2.7 |
| [T2.10](phase-2-evaluation/T2.10-adrs.md) | ADRs: reward semantics, chain trust composition, feature surface, variant policy | S | `TODO` | none |

### Phase 3 — Searched route policy

| id | task | size | state | blocked by |
|---|---|---|---|---|
| [T3.1](phase-3-policy/T3.1-adr-architecture.md) | ADR: three-loop architecture, policy artifact, determinism contract | S | `TODO` | none |
| [T3.2](phase-3-policy/T3.2-chain-space.md) | `ChainSpec` + canonical enumeration + composability gates | S | `TODO` | T3.1 |
| [T3.3](phase-3-policy/T3.3-route-trace-cost-accounting.md) | RouteTrace cost accounting | M | `TODO` | none |
| [T3.4](phase-3-policy/T3.4-chain-executor.md) | Chain executor wrapping existing `dispatch_*` arms | L | `TODO` | T3.2 |
| [T3.5](phase-3-policy/T3.5-policy-v0-no-op.md) | policy-v0 = legacy dispatch differential gate | M | `TODO` | T2.1, T3.3, T3.4 |
| [T3.6](phase-3-policy/T3.6-offline-sweep.md) | Offline sweep harness with cap escalation | M | `TODO` | T3.2, T3.4 |
| [T3.7](phase-3-policy/T3.7-schedule-builder.md) | Schedule builder + policy-v1 + golden regen | M | `TODO` | T3.6, T0.7 |
| [T3.8](phase-3-policy/T3.8-trust-cost-deepening.md) | Trust-cost iterative deepening + certified-only mode | M | `TODO` | T3.5 |
| [T3.9](phase-3-policy/T3.9-survival-model.md) | Survival-model prior for small-n cells | M | `TODO` | T3.6, T3.7 |
| [T3.10](phase-3-policy/T3.10-offline-mcts.md) | Offline MCTS over parameterized strategies | L | `TODO` | T3.7, T3.9 |

### Phase 4 — Equality saturation + walk-back contract

| id | task | size | state | blocked by |
|---|---|---|---|---|
| [T4.1](phase-4-eqsat-walkback/T4.1-adr-extend-vs-adopt.md) | ADR: extend vs adopt; driver placement; `TrustId::RewriteChain` | S | `TODO` | none |
| [T4.2](phase-4-eqsat-walkback/T4.2-shared-explain-chain.md) | Shared oriented-chain API `explain_chain(a,b)` | S | `TODO` | none |
| [T4.3](phase-4-eqsat-walkback/T4.3-reusable-ir-bridge.md) | Reusable `TermId`-to-`ENodeId` bridge | M | `TODO` | none |
| [T4.4](phase-4-eqsat-walkback/T4.4-rule-ledger-patterns.md) | Rule-instance ledger + pattern-form for ~15 manifest rules | M | `TODO` | T4.1 |
| [T4.5](phase-4-eqsat-walkback/T4.5-saturation-driver.md) | Saturation driver: rounds, budgets, RHS instantiation | M | `TODO` | T4.3, T4.4 |
| [T4.6](phase-4-eqsat-walkback/T4.6-extraction-tier0.md) | Extraction + Tier-0 walk-back; G2 measurement | M | `TODO` | T4.2, T4.5 |
| [T4.7](phase-4-eqsat-walkback/T4.7-tier1-alethe.md) | Tier-1 Alethe `rewrite_rule_inst` checker extension | L | `TODO` | T4.6 |
| [T4.8](phase-4-eqsat-walkback/T4.8-tier2-lean.md) | Tier-2 Lean lemma library keyed by `RewriteRuleId` | L | `TODO` | T4.7 |
| [T4.9](phase-4-eqsat-walkback/T4.9-walkback-contract.md) | `Bridge` walk-back contract retrofitted onto the 14 reductions | M | `TODO` | T4.1 (ADR) |
| [T4.10](phase-4-eqsat-walkback/T4.10-crossing-conformance-tests.md) | Evidence-crossing conformance tests | M | `TODO` | T4.9 |

### Phase 5 — Lateral bridges from the CAS

| id | task | size | state | blocked by |
|---|---|---|---|---|
| [T5.1](phase-5-lateral-bridges/T5.1-adr-bridge-boundary.md) | ADR: bridge boundary and dependency direction | S | `TODO` | none |
| [T5.2](phase-5-lateral-bridges/T5.2-cofactor-division.md) | `reduce_with_quotients` in `groebner.rs` | M | `TODO` | T5.1 |
| [T5.3](phase-5-lateral-bridges/T5.3-ideal-membership-certificate.md) | Generator-representation tracking + membership certificate | M | `TODO` | T5.2 |
| [T5.4](phase-5-lateral-bridges/T5.4-nullstellensatz-trustid.md) | `NullstellensatzCertificate` + `recheck()` + `TrustId` | M | `TODO` | T5.3 |
| [T5.5](phase-5-lateral-bridges/T5.5-nia-nra-frontier-ratchet.md) | Corpus + frontier ratchet for newly decided slices | S | `TODO` | T5.4 |
| [T5.6](phase-5-lateral-bridges/T5.6-smith-hermite-certificates.md) | Smith/Hermite integer certificates | M | `TODO` | T5.1 |
| [T5.7](phase-5-lateral-bridges/T5.7-sos-degree-lift.md) | SOS degree-lift phase 1 (LDL^T / diagonally dominant, no SDP) | L | `TODO` | T5.1 |
| [T5.8](phase-5-lateral-bridges/T5.8-wz-evidence-artifact.md) | WZ evidence artifact + minimized independent checker | S-M | `TODO` | T5.1 |
| [T5.9](phase-5-lateral-bridges/T5.9-sturm-shared-artifact.md) | Sturm/RootOf shared artifact | S | `TODO` | T5.1 |
| [T5.10](phase-5-lateral-bridges/T5.10-deferred-bridges.md) | Deferred: recognizers, holonomic counting, F_p irreducibility certificates | L | `TODO` | T5.4-T5.9 evidence |

### Phase 6 — Parallel search and cube-and-conquer

| id | task | size | state | blocked by |
|---|---|---|---|---|
| [T6.1](phase-6-parallel/T6.1-adr-external-conquer.md) | ADR: external CDCL as untrusted conquer engine | S | `TODO` | none |
| [T6.2](phase-6-parallel/T6.2-icnf-cube-manifest.md) | iCNF cube-manifest format: writer/parser/hash | S | `TODO` | none |
| [T6.3](phase-6-parallel/T6.3-lookahead-splitter.md) | Deterministic lookahead splitter + tautology certificate | L | `TODO` | T6.2 |
| [T6.4](phase-6-parallel/T6.4-cube-relative-proofs.md) | Cube-relative proof production in the native CDCL | M | `TODO` | T6.3 |
| [T6.5](phase-6-parallel/T6.5-streaming-drat-lrat.md) | Streaming bounded-memory DRAT checking + per-cube LRAT elaboration | M | `TODO` | none (parallel with T6.3) |
| [T6.6](phase-6-parallel/T6.6-conquer-orchestrator.md) | Parallel conquer orchestrator + budget ledger + deterministic aggregation | M | `TODO` | T6.3, T6.4, T6.5 |
| [T6.7](phase-6-parallel/T6.7-external-conquer-adapter.md) | External conquer adapter (kissat DRAT / CaDiCaL LRAT) | M | `TODO` | T6.1, T6.6 |
| [T6.8](phase-6-parallel/T6.8-hardness-predictor.md) | Hardness predictor + adaptive re-split | M | `TODO` | T6.6 |
| [T6.9](phase-6-parallel/T6.9-mcts-cubing.md) | MCTS cubing sharing the phase-3 search skeleton | L | `TODO` | T6.3, T6.6 |
| [T6.10](phase-6-parallel/T6.10-open-problem-pilot.md) | Pilot: re-derive a known small result with a fully axeyum-checked certificate | M | `TODO` | T6.4, T6.5, T6.6 |

### Phase 7 — LLM-in-the-loop proposal layer

| id | task | size | state | blocked by |
|---|---|---|---|---|
| [T7.1](phase-7-agentic-loop/T7.1-adr-loop-boundary.md) | ADR: loop boundary, dependency policy, ledger provenance, crediting | S | `TODO` | none |
| [T7.2](phase-7-agentic-loop/T7.2-proposal-ledger.md) | Proposal artifact + append-only ledger | S | `TODO` | T7.1 |
| [T7.3](phase-7-agentic-loop/T7.3-decline-corpus-extractor.md) | Decline-corpus extractor | M | `TODO` | none |
| [T7.4](phase-7-agentic-loop/T7.4-hint-channel.md) | Verified hint channel in `check_auto` | M | `TODO` | T7.1 |
| [T7.5](phase-7-agentic-loop/T7.5-proposer-driver.md) | Offline proposer driver + pilot under $100 | M | `TODO` | T7.2, T7.3, T7.4 |
| [T7.6](phase-7-agentic-loop/T7.6-verified-lemma-channel.md) | Verified-lemma channel via abduct-style re-verification | M | `TODO` | T7.4, T7.5 |
| [T7.7](phase-7-agentic-loop/T7.7-bridge-chain-dsl.md) | Bridge-chain DSL | L | `TODO` | phase-0, phase-1, T7.5 |
| [T7.8](phase-7-agentic-loop/T7.8-provenance-integration.md) | Provenance + no-loss integration | S | `TODO` | T7.2, T7.5 |
| [T7.9](phase-7-agentic-loop/T7.9-decline-trace-miner.md) | Decline-trace miner | M | `TODO` | T7.3 |
| [T7.10](phase-7-agentic-loop/T7.10-shadow-generator.md) | Shadow generator for curriculum conjectures | M | `TODO` | T7.2, T7.5 |

### Phase 8 — Open-problem intake and triage

| id | task | size | state | blocked by |
|---|---|---|---|---|
| [T8.1](phase-8-open-problems/T8.1-adr-intake-claims.md) | ADR: intake, artifact family, claim labels | S | `TODO` | none |
| [T8.2](phase-8-open-problems/T8.2-registry-harvest.md) | Registry harvest script (regex, no Lean) | S | `TODO` | T8.1 |
| [T8.3](phase-8-open-problems/T8.3-shape-triage.md) | Token-shape triage + triage dashboard | M | `TODO` | T8.2 |
| [T8.4](phase-8-open-problems/T8.4-pilot-shadows.md) | Pilot: 10 hand-derived shadows from the `decide` seed set | M | `TODO` | T8.1, T8.2, T8.3 |
| [T8.5](phase-8-open-problems/T8.5-shadow-runner-ratchet.md) | Shadow runner + swept-bound ratchet | M | `TODO` | T8.4 |
| [T8.6](phase-8-open-problems/T8.6-lean-decidability-probe.md) | Lean elaboration decidability probe | L | `TODO` | T8.3 |
| [T8.7](phase-8-open-problems/T8.7-lean-tieback.md) | Lean tie-back for witnesses | L | `TODO` | T8.4, T8.6 |
| [T8.8](phase-8-open-problems/T8.8-witness-search-lane.md) | Bucket-B witness-search lane | M | `TODO` | T8.5, T8.7 |
| [T8.9](phase-8-open-problems/T8.9-upstream-contribution.md) | Upstream contribution path | S | `TODO` | T8.4 |
| [T8.10](phase-8-open-problems/T8.10-census-scale-out.md) | Scale-out + published triage census | L | `TODO` | T8.5, T8.6, T8.7, T8.8 |

### Phase 9 — Lean evidence ladder and Comparator

| id | task | size | state | blocked by |
|---|---|---|---|---|
| [T9.1](phase-9-lean-evidence/T9.1-axiom-ledger-triage.md) | Axiom-ledger triage: classify all 65 rows | M | `DONE` 2026-08-01 | none |
| [T9.2](phase-9-lean-evidence/T9.2-lean-checker-binary.md) | `axeyum-lean-checker` nanoda-contract binary | M | `TODO` | none |
| [T9.3](phase-9-lean-evidence/T9.3-evidence-rung.md) | Evidence-ladder rung in `EvidenceReport` | S | `TODO` | none |
| [T9.4](phase-9-lean-evidence/T9.4-r6-self-challenge.md) | R6 self-challenge artifact for one fragment | M | `TODO` | T9.1, T9.2, T9.3 |
| [T9.5](phase-9-lean-evidence/T9.5-arena-submission.md) | Arena submission + local harness | M | `TODO` | T9.2 |
| [T9.6](phase-9-lean-evidence/T9.6-nat-kernel-arithmetic.md) | TL2.8 Nat kernel arithmetic | L | `TODO` | none |
| [T9.7](phase-9-lean-evidence/T9.7-string-literals.md) | String-literal typing/reduction | M | `TODO` | T9.6 |
| [T9.8](phase-9-lean-evidence/T9.8-k-like-reduction.md) | K-like reduction | M | `TODO` | none |
| [T9.9](phase-9-lean-evidence/T9.9-export-pin-limits.md) | Export-pin range 4.30 to 4.32 + limits/memory audit | S | `TODO` | T9.2 |
| [T9.10](phase-9-lean-evidence/T9.10-corpus-ladder.md) | Corpus ladder: `Init` then `Std` | L | `TODO` | T9.6, T9.7, T9.8, T9.9 |
| [T9.11](phase-9-lean-evidence/T9.11-mathlib-comparator.md) | Mathlib + ten-challenges Comparator run | L | `TODO` | T9.10 |
| [T9.12](phase-9-lean-evidence/T9.12-lrat-emission.md) | LRAT emission alongside DRAT | M | `TODO` | none |
