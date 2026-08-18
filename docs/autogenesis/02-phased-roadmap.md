# Phased roadmap

## How to read this roadmap

Each phase describes a future system state, the gap from the preceding state,
concrete tasks, and a falsifiable exit gate. Phase completion requires retained
artifacts and negative controls, not a demonstration video or an exit-zero
wrapper.

Task IDs are durable references within this programme. They do not become live
work merely by appearing here; root `PLAN.md` authorizes execution.

## Phase 0 — Bind reality

### Future state

One generated Autogenesis baseline states exactly which loop seams exist, which
are manual, which assurance routes are available, and which facts can
participate in a dependency chain. Contradictory current-state claims fail a
gate.

### Gap from current state

Axeyum has multiple good generated authorities, but no cross-artifact contract
for autonomous acquisition. `gen-plan.py --check` can pass while a next-action
sentence names a fact already closed later in history.

### Tasks

- **AG0.1 — Baseline schema.** Define a generated snapshot containing exact
  commit, fact counts and DAG shape, route/assurance inventory, proof-gap
  population, kernel theorem/fact coverage, and manual seams.
- **AG0.2 — Semantic plan checks.** Reject a `pending` landed row whose commit is
  reachable, a next-target fact that is already settled, and a current defect
  contradicted by a later authoritative result.
- **AG0.3 — Seam census.** Trace one representative fact through selection,
  dispatch, evidence, reconstruction, dependency derivation, closure, and
  replay. Mark every human-authored field and raw-ID boundary.
- **AG0.4 — Stable fixture.** Select one currently solvable, non-load-bearing
  fact fixture plus one negative and one invalid-evidence control.
- **AG0.5 — ADR decision.** Decide the v1 identity, episode, and transaction
  boundaries before public schemas or APIs are introduced.

### Exit gate

The baseline regenerates byte-identically, every count has a source, each seam
has an owner, and mutations that stale a fact target, route capability, or
manual-seam count each fail exactly one intended check.

## Phase 1 — Close one deterministic loop

### Future state

A command selects or accepts one authored open fact, dispatches it through one
existing proof-producing route, constructs a portable episode and evidence
bundle, and stages a ledger transition. A separate clean process independently
replays and applies the transition.

No learning, LLM planning, conjecturing, or code modification belongs in this
phase.

### Gap from Phase 0

The baseline identifies the seams but does not compose them. Current closure
still trusts caller-authored evidence-row structure and shell commands.

### Tasks

- **AG1.1 — Goal snapshot v1.** Content-identify the fact, formal statement,
  dependency closure, library, route policy, and resource budget.
- **AG1.2 — Episode v1.** Record selection, attempts, typed outcomes, artifacts,
  acceptance observations, and impact without editing the fact.
- **AG1.3 — Typed dispatch adapter.** Convert one existing solver result into a
  route-neutral evidence bundle without parsing CLI prose.
- **AG1.4 — Portable identity.** Reparse the original statement in an independent
  arena and reject any evidence that depends on producer-local IDs.
- **AG1.5 — Transactional closer.** Produce a proposed before/after fact delta;
  never modify the ledger if any check, validation, or write step fails.
- **AG1.6 — Clean replay.** Re-run checkers and reconstruction in a fresh process
  using only committed inputs plus the staged artifact.
- **AG1.7 — Controls.** Corrupt statement digest, evidence step, dependency,
  footprint, checker identity, and result status independently; each must fail
  closed.
- **AG1.8 — Determinism.** Repeat the same episode twice and explain or eliminate
  every byte difference.

### Exit gate

One fact closes from a clean checkout with no human-authored proof or evidence
row after selection. The independent replay accepts it; all corruption controls
reject; the existing manual closer remains available as a conservative fallback.

## Phase 2 — Demonstrate compounding

### Future state

The system has enough connected work to select a useful fact, admit it, observe
newly ready descendants, and automatically retry. Autogenesis-1 completes a
two-step acquisition chain.

### Gap from Phase 1

A one-shot pipeline proves composition but not knowledge compounding. The
kernel ledger is already connected enough for a bootstrap replay, but all of
its facts are settled: changing statuses alone would leak the retained proofs.
There is no counterfactual knowledge snapshot for the first chain and no dense
held-out nursery for sustained evaluation afterward.

### Tasks

- **AG2.1 — Counterfactual knowledge snapshot.** Withhold facts and their proof
  terms from eligibility and retrieval without editing the authoritative ledger.
- **AG2.2 — Bootstrap chain.** Qualify a primary and fallback from the existing
  proof-derived kernel graph with fixed budgets and pre-B controls.
- **AG2.3 — Nursery design.** After the bootstrap path is credible, define
  100-300 provenance-classified Nat/Int facts with real dependency depth, route
  diversity, mutations, and held-out components for sustained evaluation.
- **AG2.4 — Scheduler baseline.** Rank dependency-ready facts by assurance
  feasibility, estimated cost, unlock count, and curriculum diversity.
- **AG2.5 — Admission event.** Recompute readiness only after a replayed ledger
  transition, never after a solver's unaccepted success.
- **AG2.6 — Retry policy.** Retry descendants whose blocker set changed; cap
  repeated identical attempts by episode digest.
- **AG2.7 — Two-step chain.** Establish B automatically, use B in the admitted
  library or plan context, then establish previously unreachable A.
- **AG2.8 — Counterfactual.** Replay A against the pre-B snapshot and require it
  to fail or exceed the registered budget for the expected reason.
- **AG2.9 — Human-intervention accounting.** Record every edit, route override,
  and proof repair; the credited chain permits none after launch.

### Exit gate: Autogenesis-1

From fixed inputs and budget, a clean run reproduces the B-then-A sequence,
both results pass independent acceptance, A's dependency on B is derived rather
than asserted, the counterfactual pre-B run does not receive credit, and no
trusted-base growth occurs.

## Phase 3 — Plan and compose proofs

### Future state

Axeyum can solve a goal by decomposing it into typed obligations handled by
different engines, then compose their checked results into one admitted proof.

### Gap from Phase 2

Compounding is restricted to goals already handled by a monolithic route or
hand-encoded reconstruction. The system cannot express a general proof strategy.

### Tasks

- **AG3.1 — Proof-plan ADR.** Fix v1 syntax, typing, scope, failure semantics,
  versioning, and distinction from evidence proof steps.
- **AG3.2 — Static checker.** Validate contexts, introduced variables, child
  obligations, route compatibility, and composition completeness.
- **AG3.3 — Structural core.** Implement introduction, assumption, conjunction,
  cases, contradiction, exact theorem application, and composition.
- **AG3.4 — Equality core.** Implement checked rewriting and normalization with
  stable rule/theorem identities.
- **AG3.5 — Engine adapters.** Add solver and CAS dispatch nodes that preserve
  original-goal mappings and evidence bundles.
- **AG3.6 — Nat induction.** Express the existing guarded induction route as a
  plan that yields base and step obligations and a kernel recursor skeleton.
- **AG3.7 — Premise retrieval baseline.** Compare dependency neighborhood,
  type-directed retrieval, BM25/text retrieval, and proof-term co-occurrence on
  held-out facts.
- **AG3.8 — Search baseline.** Add bounded best-first or beam search over valid
  plan prefixes with deterministic tie-breaking.
- **AG3.9 — Multi-route fixture.** Register a theorem requiring at least two
  engine families and one library application under the chosen budget.
- **AG3.10 — Plan minimization.** Remove unused steps and dependencies before
  admission; reject plans that close only through an unrecorded context item.

### Exit gate

One held-out goal that no registered monolithic route solves is closed through a
typed multi-route plan. Replaying only the plan, named library snapshot, and
evidence bundle reconstructs the same kernel theorem. Removing any essential
step makes the plan fail.

## Phase 4 — Acquire reusable capabilities

### Future state

Autonomous failures are classified into reusable capability gaps. The system
ranks interventions by expected verified unlock value and demonstrates that a
landed capability improves held-out autonomous acquisition.

### Gap from Phase 3

Proof search can compose known capabilities but cannot explain what investment
would most improve it. Backend errors and timeouts do not form a planning
language.

### Tasks

- **AG4.1 — Decline taxonomy.** Define cross-route classes: unsupported
  semantics, missing lemma, missing plan rule, missing certificate,
  representation explosion, resource exhaustion, retrieval miss,
  formalization mismatch, and operational failure.
- **AG4.2 — Minimal blocker extraction.** Reduce a failed episode to the
  smallest stable obligation or missing edge reproducing the decline.
- **AG4.3 — Unlock estimator.** Count ready and near-ready facts sharing the
  blocker, weighted by value, diversity, assurance floor, and estimated cost.
- **AG4.4 — Intervention types.** Distinguish library theorem, checked rewrite,
  solver route, certificate production, representation change, resource repair,
  and planner policy.
- **AG4.5 — Capability proposal.** Emit a bounded work packet with exact
  fixtures, negative controls, expected unlocks, and no-loss gates.
- **AG4.6 — Causal evaluation.** Run identical pre/post episode populations;
  require the named blocker to fall without verdict, assurance, or resource
  regressions.
- **AG4.7 — Retry provenance.** Link descendant success to the capability and
  prior decline without claiming sole causation when other changes intervened.
- **AG4.8 — First acquisition.** Let an observed nursery bottleneck, rather than
  the authored roadmap, choose one reusable implementation increment.

### Exit gate

A capability selected from structured declines lands through the normal ADR and
gate process, eliminates its preregistered blocker, improves held-out autonomous
yield, and enables at least one previously failed knowledge transition.

## Phase 5 — Learn search, not truth

### Future state

Replaceable learned policies improve selection, premise retrieval,
decomposition, route choice, and budget allocation using reasoning episodes.
Acceptance semantics and trusted code are unchanged.

### Gap from Phase 4

All rankings are authored heuristics. Episodes exist but are not yet a
contamination-controlled learning environment.

### Tasks

- **AG5.1 — Dataset contract.** Extract state/action/outcome examples with
  content identities, licensing, provenance, and exact train/validation/test
  splits.
- **AG5.2 — Leakage defenses.** Split by dependency components, theorem families,
  proof templates, and novel premises rather than random rows alone.
- **AG5.3 — Deterministic baselines.** Preserve non-learned retrieval, planning,
  and scheduling policies as mandatory comparisons.
- **AG5.4 — Offline retrieval model.** Rank premises without granting authority
  to hallucinated names or untyped substitutions.
- **AG5.5 — Route/budget policy.** Predict useful route portfolios and budget
  allocation; enforce hard resource ceilings outside the model.
- **AG5.6 — Plan proposal model.** Generate only parseable plan candidates;
  static checking filters invalid actions before execution.
- **AG5.7 — Counterfactual evaluation.** Measure whether the policy solved more
  held-out goals at the same compute and assurance, not merely replayed known
  successful plans.
- **AG5.8 — Stability tests.** Re-evaluate old populations after learning new
  domains; report forgetting and negative transfer explicitly.
- **AG5.9 — Policy registry.** Content-address policy, data, prompt/configuration,
  and evaluator; make rollback trivial.

### Exit gate

A learned policy beats deterministic baselines on held-out autonomous
acquisition at matched compute and assurance, while all accepted results remain
identical under independent replay with the policy removed.

## Phase 6 — Generate conjectures and discoveries

### Future state

Axeyum proposes potentially useful statements, constructions, and algorithms;
filters trivial, duplicate, false, malformed, and low-value candidates; and
settles the survivors through the same acceptance plane.

### Gap from Phase 5

The system becomes better at solving authored goals but does not choose new
knowledge worth seeking.

### Tasks

- **AG6.1 — Candidate schema.** Keep generated conjectures outside the durable
  fact ledger until typed and triaged.
- **AG6.2 — Generators.** Start with controlled generalization, specialization,
  converse, boundary mutation, invariant mining, and lemma abstraction from
  repeated proof plans.
- **AG6.3 — Cheap falsification.** Use finite models, SMT counterexamples,
  property testing, dimensional/type checks, and known-theorem contradiction.
- **AG6.4 — Deduplication.** Detect alpha-equivalence, normalization equivalence,
  theorem subsumption, and likely literature duplicates.
- **AG6.5 — Difficulty targeting.** Prefer candidates near the current capability
  frontier rather than trivial tautologies or unreachable famous conjectures.
- **AG6.6 — Utility scoring.** Estimate descendant unlocks, proof-plan
  compression, domain relevance, and capability-diagnostic value.
- **AG6.7 — Self-play curriculum.** Pair conjecturer and prover, but retain all
  generated populations and compute so selection effects remain auditable.
- **AG6.8 — Algorithm discovery.** Permit executable candidates only behind
  immutable correctness and performance evaluators; formalize successful
  invariants where feasible.
- **AG6.9 — Novelty review.** Treat “proved here” and “new to the literature” as
  separate fields requiring external search and, for serious claims, expert
  review.
- **AG6.10 — Adversarial formalization.** Search for weakened, vacuous, or
  mistranslated statements that are easy to prove but miss the intended claim.

### Exit gate

At least one system-generated candidate is nontrivial under registered filters,
is independently established or refuted, has a formalization mutation test, and
has an honest novelty classification. Generated-volume alone receives no credit.

## Phase 7 — Become a domain-general verified knowledge foundry

### Future state

Domain adapters turn mathematical, software, policy, accounting, scientific,
and agent-behavior inputs into typed claims with appropriate epistemic classes.
The same selection, planning, evidence, replay, and capability-learning loop
operates without pretending every domain fact is a theorem.

### Gap from Phase 6

Discovery is still centered on formal mathematics and algorithmic evaluation.
Existing consumers do not publish through one knowledge-acquisition contract.

### Tasks

- **AG7.1 — Domain adapter contract.** Specify semantics version, observation
  provenance, formalization, allowed inference, evidence type, and publication
  boundary.
- **AG7.2 — Epistemic type system.** Keep deductive, bounded-computational,
  differential, empirical, legal/policy, and assumption-bearing conclusions
  distinct.
- **AG7.3 — Software pilot.** Feed verified Rust/MIR or protocol obligations into
  episodes and publish proofs or counterexamples with exact compiler semantics.
- **AG7.4 — Rules pilot.** Represent one versioned rules-as-code domain where
  conclusions cite rules, facts, conflicts, and assumptions.
- **AG7.5 — Scientific pilot.** Separate model consequence from empirical truth;
  retain dataset/version/statistical provenance.
- **AG7.6 — Cross-domain plans.** Allow a plan to invoke formal deduction,
  bounded computation, data analysis, and external attestation without
  conflating assurance.
- **AG7.7 — Domain isolation.** Prevent private or proprietary premises from
  leaking into public artifacts while keeping public conclusions reproducible
  where possible.
- **AG7.8 — Comparative evaluation.** Measure whether knowledge learned in one
  domain improves another and report negative transfer.

### Exit gate

Two non-mathematical domains complete the acquisition loop on held-out tasks,
with correct epistemic classifications and independently replayable formal
portions. No empirical or policy conclusion is mislabeled as axiom-free theorem.

## Phase 8 — Govern recursive improvement

### Future state

Axeyum can propose bounded changes to its own untrusted search machinery,
evaluate them under immutable contracts, and retain only improvements that do
not weaken correctness, assurance, determinism, or resource behavior.

### Gap from Phase 7

The system learns policies but humans remain the only source of implementation
and evaluator changes. Naive self-modification would let the proposer weaken
the test that judges it.

### Tasks

- **AG8.1 — Improvement envelope.** Restrict autonomous changes initially to
  declarative route policies, prompts, retrieval indices, and proof-plan search
  heuristics.
- **AG8.2 — Privilege separation.** Proposal processes cannot modify kernels,
  checkers, schemas, baselines, held-out populations, or evaluation code.
- **AG8.3 — Immutable evaluation bundles.** Content-address inputs, evaluators,
  resource limits, expected negative controls, and trust budgets.
- **AG8.4 — Evolution archive.** Retain parents, mutations, evaluations,
  rejected candidates, and selection policy.
- **AG8.5 — Adversarial evaluator tests.** Detect reward hacking, test deletion,
  timeout exploitation, population narrowing, and assurance downgrades.
- **AG8.6 — Promotion ladder.** Sandbox, shadow, canary, held-out, then human
  authorization; no direct autonomous merge to trusted or public surfaces.
- **AG8.7 — Trusted-base budget.** Any proposed new axiom, checker rule, unsafe
  code, native dependency, or acceptance relaxation is automatically outside
  autonomous authority.
- **AG8.8 — Reversibility.** Every policy promotion has a one-command rollback
  and knowledge remains valid when the policy is removed.

### Exit gate

The system proposes an improvement to untrusted search, wins on immutable
held-out acquisition metrics at matched resources, survives reward-hacking
controls and full regression gates, and is promoted through an explicit human
authorization boundary. The accepted knowledge remains independently valid
without the improved policy.

## Horizon beyond Phase 8

Later research may include:

- richer dependent proof plans and synthesis of new certified procedures;
- formal scientific model revision and experiment selection;
- cooperative populations of specialized planners with proof-carrying
  communication;
- cross-kernel proof translation and disagreement localization;
- verified compilation of high-level reasoning plans into small kernel terms;
- active acquisition of definitions and representations, not only facts;
- reasoning about temporal, probabilistic, causal, and normative systems; and
- mechanized meta-theory for portions of the planner and checker stack.

These are horizon directions, not reasons to skip the two-step Autogenesis-1
chain.
