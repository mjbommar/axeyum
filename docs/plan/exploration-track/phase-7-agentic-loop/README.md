# Phase 7 — the agentic loop: the LLM-in-the-loop layer

Verdict from review: **yes, but for a much narrower band than the plan implies —
and the repo has already built the architectural pattern that makes it safe.**

## The pattern already exists

`crates/axeyum-solver/src/abduct.rs` states the required design in its module doc:

> Candidate generation … is entirely untrusted; soundness comes only from
> re-checking every candidate with the trusted decider before it is returned.

The agentic loop is that module with an LLM as the candidate generator. The
precondition FunSearch and AlphaEvolve needed — a fast, automatic, ungameable
evaluator — axeyum already has: `check_auto` + model replay + DRAT/Alethe/Lean
checkers + the oracle-free scenario suite. **That is the strongest argument for
this phase.**

## Where an LLM genuinely adds value, ranked

1. **Per-problem reformulation and encoding hints for the `unknown` bucket** —
   instantiation terms, variable bounds, case splits, cut lemmas, bridge-chain
   selection. Exactly analogous to AlphaGeometry, where the LM proposes only
   auxiliary constructions and the symbolic engine does all deduction.
2. **Bounded shadows of open conjectures** for the curriculum/CAS/Lean side.
3. **Development-time decline-trace mining** — cluster `RouteTrace` output over the
   corpus and propose which *mechanism* closes which bucket. Zero soundness
   surface; output is a ranked engineering backlog.
4. **Candidate rewrite rules and lemmas**, offline only, through the
   denotation-preserving harness plus the mandatory degenerate-argument fuzz.

## Where LLMs add nothing — be blunt

- **Route selection.** `auto.rs` already dispatches across ~60 routes with a probe;
  a measured frontier plus bandit ordering beats an LLM at zero cost and full
  determinism.
- **Search-strategy scheduling.** A portfolio/bandit problem, not a language one.
- **Anything on the soundness-critical path.** The model proposes; it never decides.

## The honest yield caveat

**The measured gap is dominated by `DeclineReason::Unsupported`, not by
`unknown-with-a-clever-encoding`.** The curated residual is 762/992 decided;
strings residual is "QF_SLIA 21 unsupported + 4 unknown, QF_S 32 + 9"; quantified
logics sit near zero because **mechanisms are missing, not because search lacks
imagination**. No runtime LLM loop converts `Unsupported` — only engine code does.

So the loop's honest runtime target is the `Incomplete`/`Budget` slice plus the
open-conjecture and bridge-exploration ambitions, and **its most durable output is
artifacts that get baked back into deterministic routes.** The agentic layer is not
the bottleneck today; the deterministic machinery is. Build it as a small,
ledgered, offline harness and measure its ROI against engine work rather than
assuming it.

## Agent roles and their soundness arguments

| Role | Runtime/offline | Output | Soundness argument |
|---|---|---|---|
| R1 search hints (instantiation terms, bounds, case splits, cut lemmas) | runtime | typed SMT-LIB2 terms over the query's symbols | hints guide an already-sound route; every term is parsed, sort-checked, and *proved admissible* (a cut lemma is used only after `check_auto` proves it entailed — the `abduct.rs` sufficiency pattern) |
| R2 reformulation / bridge-chain choice | runtime | a chain over *declared* bridges + params, restricted DSL | the interpreter executes only registered reductions whose direction is declared (phase 1); verdicts transfer only along the declared direction; `sat` always replays on the original terms |
| R3 bounded shadows of open conjectures | offline | finite instances, width/domain bounds, variant statements | shadows are decided by the checker and *labeled* as shadows; no claim about the conjecture is emitted |
| R4 decline-trace diagnosis → mechanism backlog | offline | ranked markdown/JSON | no solver surface at all |
| R5 rewrite-rule / lemma candidates | offline | candidates into the verification harness | land only via existing gates: denotation-preserving check, degenerate fuzz seed-class, human review, ADR |

**The invariant, stated once:** the only public claims are
`CheckResult`/`EvidenceReport` values produced by the existing trusted path on the
**original** query. A malformed proposal fails the `axeyum-smtlib` parse; a
dishonest one becomes `DeclineReason::VerifierRejected` and burns budget. There is
no code path from model output to a verdict that does not pass through the checker.

## Interface

**Input per attempt:** the SMT-LIB slice (deterministically truncated), logic tag,
the `RouteTrace` rendered via `Display` (route labels and decline reasons are
already stable strings), budget stats, and up to k exemplar (problem, proposal,
outcome) triples from the ledger.

**Output:** one JSON proposal artifact —
`{schema_version, problem_id (content hash), kind, payload (SMT-LIB2 text),
params, seed}` — validated by serde plus the SMT-LIB parser before anything runs.

Raw typed-IR emission is **rejected as an interface**: IR ids are arena-local and
unserializable by design. SMT-LIB text through the existing parser is the correct
boundary. Lean statements are the emission format only for R3 shadows.

## Control loop

```
extract:  explain_corpus over the target population → decline-trace JSONL
generate: Batch API, n proposals × survivors, model per escalation tier
validate: parse → sort-check → admissibility (cheap, deterministic)
evaluate: check_auto under a per-attempt budget; graded fitness =
          decided(1.0) > bound-improved > conjuncts-refuted > parse-ok > malformed;
          the attempt's RouteTrace is the feedback
record:   append-only content-addressed ledger
select:   survivors escalate Haiku → Sonnet → Opus; exemplars refreshed
stop:     per-problem K attempts (default 8) OR decided; global dollar cap
```

No conversation state; every attempt is a fresh, cache-prefixed, batched call.

**Start as best-of-n with exemplar feedback; add an evolutionary database only if
round 2+ measurably justifies it.** FunSearch's own lesson is that the *sampler was
weak* (Codey, not a frontier model) and the **evaluator carried the system** — and
"Simple Baselines are Competitive with Code Evolution" (arXiv:2602.16805) finds
plain repeated sampling with good prompts rivals evolutionary loops.

**Graded fitness is not optional.** Raw sat/unsat/unknown is too flat to drive
anything; FunSearch's score was continuous. Synthesize one from checked
quantities — bound reached before budget, fraction of conjuncts refuted, subgoals
closed — never from solver-reported statistics alone (the `f5b00c72` vacuous-sat
lesson).

## Cost model

Per attempt ≈ 3–6K input tokens (2–4K a cached fixed prefix) + 1–2K output:

| Model | $/MTok in/out | ≈ $/attempt (batched, cached) | $/problem @ K=8 |
|---|---|---|---|
| Haiku 4.5 | 1 / 5 | ~$0.006 | ~$0.05 |
| Sonnet 5 | 3 / 15 | ~$0.02 | ~$0.15–0.30 |
| Opus 5 | 5 / 25 | ~$0.05–0.09 | ~$0.4–0.7 |

- **Cheapest useful configuration:** Haiku 4.5 best-of-8 over the ~230-problem
  curated unknown bucket = **$12–20 per full sweep.** Sonnet sweep $50–70. An Opus
  pass on the ~30 hardest survivors $15–25. **Pilot budget ≤ $100; steady state
  ≤ $500/month.**
- **Never sweep the 45,905-path library with an LLM** (≥ $2–10K even on Haiku, and
  the agent program's rule 11 forbids sweeping for progress). Sample per-logic.
- **Small model + volume + sound filter first**; frontier only on survivors and for
  R4 diagnosis. R3 open-conjecture work is the only place frontier-first is
  defensible.
- **Fine-tuned/local model: no, not initially.** Justified only past ~10⁵
  attempts/month or for air-gapped reproducibility. Defer behind an ADR with a
  volume trigger.

## Determinism seam

**Discovery is nondeterministic and is never a claim. Results are.** A result =
(original query, recorded proposal, `SolverConfig`) → checked outcome + evidence,
fully deterministic and replayable offline.

The **proposal ledger** is the boundary artifact: append-only JSONL,
content-addressed, recording prompt hash, model id, request params, seed, raw
response, fitness, evidence hash. **Replay mode consumes the ledger with zero
network calls; CI and `just check` never invoke an LLM.** SCOREBOARD/bench entries
from agent-assisted runs carry the ledger hash as provenance and are ledgered
*separately* from pure-deterministic decide-rate until an ADR settles crediting.

This mirrors the existing `RouteTrace` philosophy exactly: the nondeterministic
thing (search) is recorded telemetry; the deterministic thing (verdict + evidence)
is the API promise. No change to the public guarantee is needed **if the loop stays
out of the default solve path — which it must.**

## Prior art

- **FunSearch** (Nature 2023) — LLM proposes function bodies in a fixed skeleton, a
  deterministic evaluator scores, island-based evolution feeds best parents back.
  New cap-set constructions. <https://www.nature.com/articles/s41586-023-06924-6>
- **AlphaEvolve** (2025, GA 2026) — evolves whole files via diffs; **model ensemble**
  (Flash for breadth, Pro for depth — the Haiku→Opus ladder); **evaluation cascade**
  (fast screen, then expensive full evaluation on survivors); program database
  driving prompts. All successes had machine-checkable objectives.
  <https://arxiv.org/abs/2506.13131>
- **AlphaGeometry / AG2** — the cleanest architectural match: symbolic engine does
  all deduction, LM proposes only auxiliary constructions.
  <https://www.nature.com/articles/s41586-023-06747-5>
- **AlphaProof** (Nature 2025) — training regime does not transfer; two things do:
  the Lean kernel as the only reward signal, and **test-time RL via problem-variant
  generation**, which is precisely the R3 bounded-shadow role.
- **SATLM / Logic-LM** — LLM translates to SMT-LIB, solver decides; translation
  errors dominate failure, which is why the verdict must attach to the original
  query. **Lemur** — LLM proposes invariants, solver validates, with a sound proof
  calculus around the interaction: the formal template for the hint channel.
- **COPRA** — GPT-4 agent with error feedback in-context; the closest "LLM sees
  failure, reformulates" precedent. <https://arxiv.org/abs/2310.04353>
- **AlphaCode** — mass sampling + filtering made weak models useful; with a *sound*
  verifier, best-of-n is strictly safer than with test-based filters.
- Contrast **"Let's Verify Step by Step"**: learned verifiers are needed only when
  no sound checker exists. **Axeyum should never build one.**

Calibration note: the widely cited "GPT-5 solved 10 Erdős problems" claim was
retracted — Thomas Bloom characterized it as the model finding existing
literature. Later 2026 episodes are more substantive. Treat ~$200/result of
frontier compute as an *upper anchor*, not a validated yield curve — and note every
credible episode ran against an independent checking authority.

## Tasks

| id | title | size |
|---|---|---|
| [T7.1](T7.1-adr-loop-boundary.md) | ADR: loop boundary, dependency policy, ledger provenance, crediting | S |
| [T7.2](T7.2-proposal-ledger.md) | Proposal artifact + append-only ledger | S |
| [T7.3](T7.3-decline-corpus-extractor.md) | Decline-corpus extractor (promote `explain_corpus`) | M |
| [T7.4](T7.4-hint-channel.md) | Verified hint channel in `check_auto` | M |
| [T7.5](T7.5-proposer-driver.md) | Offline proposer driver + pilot under $100 | M |
| [T7.6](T7.6-verified-lemma-channel.md) | Verified-lemma channel via abduct-style re-verification | M |
| [T7.7](T7.7-bridge-chain-dsl.md) | Bridge-chain DSL (depends on phases 0/1) | L |
| [T7.8](T7.8-provenance-integration.md) | Provenance + no-loss integration | S |
| [T7.9](T7.9-decline-trace-miner.md) | Decline-trace miner (R4) | M |
| [T7.10](T7.10-shadow-generator.md) | Shadow generator for curriculum conjectures (R3) | M |

Order: T7.1 → {T7.2, T7.3} → T7.4 → **T7.5 (the measurable pilot)** → decide from
measured yield whether T7.6/T7.7/T7.10 proceed.

## Risks

- **Unsoundness via the hint channel** is the only real soundness surface.
  Mitigation is structural, plus the project's own Hard Rule applied to the agent:
  **the fuzz generator must deliberately emit malformed, dishonest, and adversarial
  proposals** — wrong lemmas, ill-sorted terms, chains against soundness direction —
  and assert `VerifierRejected`/parse failure. A loop tested only on honest model
  output is blind exactly where it is fragile.
- **Cost blowup** — hard dollar cap in the driver, per-attempt budget, Batch API
  only, escalation on survivors, rule 11 inherited verbatim.
- **Reproducibility loss** — model deprecation means old proposals cannot be
  *regenerated*; acceptable because replay never needs the API, unacceptable if
  anyone quotes an unreplayed agent result. **Keep the LLM out of `just check` and
  the pre-push hook** or the determinism promise quietly dies.
- **Evaluator gaming / vacuity** — a graded fitness invites degenerate maxima;
  fitness components must be checked quantities.
- **Low yield / misdirected effort** — if the pilot converts fewer than ~5 problems
  per $100, demote the runtime loop to R4 and R3, which is where FunSearch-style
  loops historically paid off anyway.
- **Training-data contamination** — public SMT-LIB corpora are in every model's
  training set. Soundness is unaffected; capability measurement is inflated. Always
  report scenario-suite (generated, oracle-free) results alongside public-corpus
  results.
- **Process risk** — the dev program already saturates this host; the evaluation
  phase is a corpus sweep and must be scheduled like any other gate.
