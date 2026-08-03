# Phase 3 — the searched route policy

Verdict from review: **needs revision.** The instincts are right — non-committal
exploration, learned priors over reductions, trust-cost as a budget dimension,
machine-checkable reward — but three structural errors must be fixed first.

**Gated on G1** (phase 2, T2.3). Do not start before the VBS–SBS gap reports.

## What the review corrected

**1. MCTS is at the wrong locus.** The chain space is *tiny*: with composability
and reaches-a-decider constraints, at most a few hundred chains survive
applicability gates. **Enumerating all chains is trivially cheap** — the claim
"NOT exhaustive search" is wrong at the graph level. What is expensive is
*executing* chains. Within one query under a timeout you get 3–5 censored,
binary-ish observations; no bandit converges in 5 pulls, and per-instance variance
(the entire motivation for feature-based selection) swamps within-instance signal.

The literature is unambiguous about placement:
- **MCTS offline over a corpus** — Z3alpha (IJCAI 2024): layered and staged MCTS
  run offline on a training corpus, emitting a *static* strategy; 42.7% more QF_BV
  instances than Z3 default; SMT-COMP 2024 entrant.
  <https://arxiv.org/abs/2401.17159>
- **Selection + capped scheduling online** — SATzilla presolvers/backup,
  MedleySolver sequences, aspeed timeout-optimal schedules.

**2. Online learning collides with the determinism promise.** MedleySolver-style
in-flight bandit updates make verdicts depend on query arrival order.

**3. The atlas is not a per-instance feature space.** It is a fragment-level
capability matrix — exactly right for masking illegal arms, wrong as features.

Secondary: bridges are *parameterized families* (IntBlast has a width, budgets are
knobs), so the space is bigger than 14 discrete edges but structured; and reward
must only count decided results that **pass** replay/certificate checks, or
unsound routes poison the prior.

## Architecture — three loops, one artifact

```
OFFLINE (nondeterminism allowed, outputs committed):
  L3 learner:  sweep + survival model + schedule builder (+ later MCTS)
                      │ emits
                      ▼
  policy.json  (versioned, hash-pinned, golden-tested, committed like
                trust-ledger.md — regenerated, never hand-edited)
                      │ input to
ONLINE (pure, deterministic):
  L2 selector:  features(query) → bucket → ordered chain schedule with caps
  L1 executor:  best-first over the chain DAG, lexicographic
                (trust_cost, scheduled order), deterministic budgets
```

Learning becomes a **data-release process**, not a runtime behavior. FastSMT is
the precedent: ship the synthesized program, not the learner.

## Online executor

```
fn check_auto_policy(arena, assertions, config, policy, rec) -> CheckResult:
  fv     := feature_vector(arena, assertions, config.deadline)
  bucket := policy.bucket_of(fv)                 # source-ordered decision list
  sched  := policy.schedule[bucket]              # [(chain_id, caps, params)],
                                                 # caps in DETERMINISTIC units
  # presolvers: fixed cheap certified fast-paths, tiny caps, always first
  for round in 0..policy.max_rounds:             # iterative deepening, TWO dials:
    trust_allow := policy.trust_ladder[round]    #   uncertified-edge count 0,1,2…
    scale       := GEOMETRIC_ESCALATION[round]   #   budget ladder ×4 per round
    for (chain, caps, params) in sched:
      if chain.trust_cost > trust_allow: continue
      if !chain.applicable(fv): rec.declined(NotApplicable); continue
      r := execute_chain(chain, params, caps * scale)
      match r:
        Sat(m)  if replay_ok(m, original)      => return Sat(m)
        Unsat   if certificates_ok(chain, run) => return Unsat
        Sat|Unsat (check FAILED) => rec.declined(VerifierRejected); continue
        Unknown(budget) => continue            # right-censored observation
  return Unknown(best_reason(rec))             # legacy fixed order = backup solver
```

Best-first is honest here only because chains are pre-enumerated: trust_cost is
additive, nonnegative and known exactly, so lexicographic
`(trust_cost, predicted_cost)` ordering degenerates to sorting the schedule.

**Round 0 with `trust_allow = 0` gives a certified-only mode for free.** That
should become a public config bit.

## Offline learner

Phase A **sweep** with CapsAndRuns-style cap escalation to bound total cost;
Phase B **survival model** per (chain, bucket) — AFT log-normal on right-censored
runtimes, falling back to Kaplan–Meier/empirical at small n; Phase C **schedule
construction** — greedy marginal-PAR-2-gain-per-cap set cover subject to a round
budget, **regularized** (Suda 2024) by penalizing chains supported by fewer than
k instances in a bucket; Phase D (later, only if C plateaus vs virtual-best)
**Z3alpha layered/staged MCTS** over parameterized strategies.

## Determinism scheme — the hard constraint

1. **Policy is data, pinned.** `policy.json` committed, hash embedded in every
   `EvidenceReport` and bench artifact; golden test regenerates and diffs.
2. **No learning at solve time.** Identical binary + policy + config ⇒ identical
   verdict, schedule, and trace modulo recorded timing fields.
3. **No RNG at solve time by default**; any tie-break knob is a ChaCha-class PRNG
   seeded from an explicit `SolverConfig` seed and recorded.
4. **All schedule decisions keyed on deterministic budgets** — `resource_limit`
   ticks, `node_budget`, CNF budgets (`backend.rs:129-169` already defines the
   philosophy and the unit-recording rule).
5. **Wall-clock stays an outer kill switch only.** Note honestly in the ADR that a
   wall-clock kill can flip decided→unknown across machines — this is
   *pre-existing* (`check_auto_dispatch` uses `Instant::now` deadlines) and the
   search must not make it worse by putting wall-clock into *ordering* decisions.
6. **Iteration order**: chains by (depth, `ALL_TRUST_IDS`-lexicographic edge
   order); buckets by source-ordered decision list; `BTreeMap`/`BTreeSet` only.

## Cold start

- **Day 0**: encode today's fixed order as `policy-v0.json`, bucket = the current
  if-chain conditions. This makes the refactor a **provable no-op** — differential
  test: policy-v0 executor ≡ current dispatch on the full corpus — before any
  learning exists. This is the single most important risk control in the phase.
- **Day 1**: exhaustive sweep with escalating caps → policy-v1. No model needed;
  with hundreds of chains × hundreds of instances the empirical table *is* the
  prior (Spider did this in 2007 without ML).
- **Uniform-optimistic rule**: any chain with zero observations in a bucket gets
  one scheduled slot at minimum cap in the last round.

## What to measure

VBS gap (policy PAR-2 vs virtual-best-chain PAR-2 per corpus — the honest
headline); coverage, PAR-2, and **trust-clean rate** as three separate numbers per
bucket; selection overhead as % of solve time; censoring rate in the sweep table
(>70% means caps are too low); determinism gate (two runs, byte-identical traces);
`progress_frontier` extended with policy-driven route counts.

## Prior art

Beyond the above: MachSMT and MedleySolver (structure to adopt, learning to move
offline); aspeed (timeout-optimal static schedules as discrete optimization);
Spider/Snake and Suda's regularization work (randomized strategy discovery +
complementarity-based schedule selection + anti-overfitting); E prover's
class-partitioning `auto-schedule` (the simplest viable selector — a static
feature-class → schedule table, deterministic and auditable; **this is the
recommended v1**); Run2Survive and superset learning for right-censored data;
CapsAndRuns / Structured Procrastination for budgeting the sweep itself;
de Moura & Passmore's *Strategy Challenge in SMT Solving* (tactics as a
soundness-by-construction strategy language — quote this in the ADR as the
design's lineage); TacticToe (A*/best-first with a learned prior over a discrete
action set, **no neural net** — the closest ITP analogue).

ITP tactic-prediction systems (HOList, CoqGym, Graph2Tac, LeanDojo/ReProver)
transfer almost nothing architecturally: they face branching factors in the
thousands and need deep models and big data. Axeyum's branching is ~14 ×
parameters. The transferable lesson is Tactician's: **k-NN over hand features is
right when data is scarce and the system must stay self-contained.**

## Tasks

| id | title | size |
|---|---|---|
| [T3.1](T3.1-adr-architecture.md) | ADR: three-loop architecture, policy artifact, determinism contract | S |
| [T3.2](T3.2-chain-space.md) | `ChainSpec` + canonical enumeration + composability gates | S |
| [T3.3](T3.3-route-trace-cost-accounting.md) | RouteTrace cost accounting | M |
| [T3.4](T3.4-chain-executor.md) | Chain executor wrapping existing `dispatch_*` arms (sliced) | L |
| [T3.5](T3.5-policy-v0-no-op.md) | **policy-v0 ≡ legacy dispatch differential gate** | M |
| [T3.6](T3.6-offline-sweep.md) | Offline sweep harness with cap escalation | M |
| [T3.7](T3.7-schedule-builder.md) | Schedule builder + policy-v1 + golden regen | M |
| [T3.8](T3.8-trust-cost-deepening.md) | Trust-cost iterative deepening + certified-only mode | M |
| [T3.9](T3.9-survival-model.md) | Survival-model prior for small-n cells | M |
| [T3.10](T3.10-offline-mcts.md) | Offline MCTS over parameterized strategies (only if T3.7/T3.9 plateau) | L |

## Risks

- **Prior poisoning via unsound wins** — if reward counts any decided verdict, a
  buggy uncertified chain gets scheduled *more*. Only checked results score;
  check-failure is a soundness alarm.
- **The `auto.rs` refactor is the riskiest engineering in the track.** 8,616 lines
  of interleaved order-dependent fast paths; the 829-commit `nia_unsat` bisect
  shows silent frontier regressions ship. T3.5 is the only safe path; do not learn
  until the no-op refactor is proven.
- **Determinism erosion via wall-clock** — keep it strictly at the outer kill.
- **Overfitting to tiny corpora** — regularize, hold out splits, let public slices
  referee.
- **Model-lift composition across chains** — multi-hop chains must compose
  `ModelReconstructionTrail`s correctly; a correctness surface as sharp as any
  solver kernel. Soundness-negative tests per composed pair.
- **Sweep cost and multi-agent hygiene** — chains × corpus × caps is hours in a
  shared checkout. Foreground per the worktree rules; sweeps stay in bench
  artifacts, never in pre-merge gates.
