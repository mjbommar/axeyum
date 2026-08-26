# 265 — Making the agent effective at advancing the frontier

Date: 2026-08-25

## What this document is

A roadmap for the one question a reader asks after watching the loop run: *can
this agent actually do useful things, and what would make it good at them?* It
is grounded in measurements taken on 2026-08-25 (lane `agent-python-layer`), not
in aspiration, and it is deliberately narrower than the programme's conceptual
roadmap. It does not replace those documents — it sequences the specific
producer-capability work the measurements say is now the binding constraint:

- the objects and boundaries: [`01-target-architecture.md`](01-target-architecture.md);
- the full phased programme: [`02-phased-roadmap.md`](02-phased-roadmap.md);
- how bottom-up and top-down compose: [`03-workstreams-and-sequencing.md`](03-workstreams-and-sequencing.md);
- the honesty metrics: [`04-metrics-and-evaluation.md`](04-metrics-and-evaluation.md);
- the obstruction→capability-demand mechanism this roadmap leans on:
  [`260-obstruction-capability-candidates.md`](260-obstruction-capability-candidates.md),
  [`261-capability-candidate-demand.md`](261-capability-candidate-demand.md);
- the reachability half, measured and tooled:
  [`../python-2026-08/14-frontier-reachability.md`](../python-2026-08/14-frontier-reachability.md).

Per the programme's authority rule, any implementation phase below enters the
live queue only through an owned file in [`../plan/status/`](../plan/status/README.md),
and trust-boundary changes still require an ADR.

## The measured starting point

Measured over the ledger on 2026-08-25:

| quantity | value | meaning |
|---|---:|---|
| facts already `proved` | 498 | the closed frontier |
| `open` facts | 146 | the remaining frontier |
| `open` + dependency-ready + train/development | 109 | the eligible pool |
| eligible facts **attemptable today** (frozen export exists) | ~3 | reachable ∩ has a producer schema |
| eligible facts a producer actually **closes** | ~2 | `nat-modeq-symm`, `nat-modeq-trans` |

The "3" decomposes as **reachability × provability**, and the sharp finding is
that the binding constraint is *provability*, not reachability: the
refl/symm/trans/comm shapes the two shipped producers (`modeq_family`,
`bounded_induction`) can close are **already proved**, and every arrow-free
*open* modeq fact is a congruence goal both producers decline. Expanding exports
buys *attempts* (and typed obstruction data) cheaply; it does not buy *proofs*.
New proofs are producer-bound.

## What already works, and must not regress

The architecturally hard part is done and verified end to end:

- The agent produces **machine-checkable proofs** that an **independent second
  kernel** re-derives from the same frozen bytes (`nat-modeq-symm`,
  `nat-modeq-trans`, re-derived at equal binder counts).
- Those proofs are **axiom-free** over the constructed carriers — the project's
  headline metric.
- When it cannot prove a goal it emits an **honest typed obstruction**
  (`retrieval-miss`, a producer `DeclineReason`), never a fabricated verdict.

The lever the whole roadmap pulls on is the identity in one sentence: **untrusted
fast search, trusted small checking.** The kernel check is what makes it safe for
the prover — including an LLM — to be wrong. Today the agent barely uses that
lever: the proving is done by two fixed Rust producers while the model
orchestrates. Making the agent effective means putting more proving power behind
the untrusted boundary without moving the trusted one.

## The metric that defines "effective"

Not theorem count, not benchmark position:

> **open facts the agent proved that nobody hand-proved, verified axiom-free in a
> second kernel — including held-out facts whose family it could not have
> memorized.**

Every phase below must move that number. A phase that does not is infrastructure,
and is labelled so. This is the same funnel [`04-metrics-and-evaluation.md`](04-metrics-and-evaluation.md)
defines; the addition here is that each producer-capability task names the
previously-declined family it is supposed to convert.

## Track A — widen what is *reachable* (cheap; unblocks measurement)

The agent can only attack a fact with a frozen `lean4export` NDJSON. Today ~3 of
146.

- **A1 — batch-export the arrow-free open facts.** `scripts/gen-statement-adapters.py`
  already generates the proof-free adapters and is verified end to end on s5.
  Run it at scale, register the NDJSON in `agent-frozen-export-index-v1.json` (or
  as statement-adapter manifests). *Infrastructure* — no new proofs, but it lifts
  *attemptable* ~3 → ~43 and gives the LLM obstruction data across the real
  frontier, which Track C consumes.
  Exit: `mobility evaluable ≥ 40`.
- **A2 — arrow-capable export path: DONE 2026-08-26.** The earlier diagnosis
  was an output/storage failure, not an exporter ceiling. With the exporter
  stdout streamed off s5, the same lean4export 3.1.0 + Lean 4.30.0 combination
  exported three implication-bearing binomial statements and Axeyum imported
  each proof-isolated with zero axioms and zero theorem proofs. The checked
  receipt is
  [`binomial-arrow-export-capability-v1.json`](../../artifacts/autogenesis/binomial-arrow-export-capability-v1.json).
  The remaining reachability task is operational: batch, retain, and index the
  rest without writing large NDJSON into Git.

## Track B — widen what is *provable* (the real frontier lever)

This is where the metric actually moves, in increasing power and cost.

- **B1 — more pattern producers (incremental; do this next).** Each producer
  encodes one bounded, soundness-tested proof schema, the way `modeq_family`
  does. The first target is written by the measurement: a **congruence producer**
  that unfolds `ModEq → Eq` and applies arithmetic congruence lemmas, closing the
  `n + a ≡ a`-class facts observed declining. B1 is the proof that the loop can
  advance the frontier *at all*, and it validates the producer-authoring loop
  end to end.
  Exit per producer: ≥ N previously-declined *open* facts proved, axiom-free,
  second-kernel-checked; the named congruence family for the first one.
- **B2 — a lemma-composing producer (the general engine).** Bounded best-first
  search over a library of already-proved lemmas (the 498 facts + imported
  Mathlib statements), applying them to close a goal. This is the flywheel's
  "library feeds the solver" arrow, automated — one engine whose power grows with
  the library instead of one producer per shape.
  Exit: proves open facts no single hand-written schema covers.
- **B3 — LLM-proposed proof terms, kernel-checked (the architectural payoff).**
  The LLM proposes a proof term or tactic script (untrusted); the kernel checks
  it (trusted). This is the jump the design was built for: the model's
  mathematical knowledge becomes usable *without being trusted*, because a wrong
  proof cannot pass the kernel. Start narrow — single-step lemma suggestions
  feeding B2's search — and grow to multi-step.
  Exit: the LLM closes an open fact B1/B2 could not, kernel-verified and
  axiom-accounted.

## Track C — close the flywheel (self-improving)

The obstruction→capability-demand scaffolding already exists
([`260`](260-obstruction-capability-candidates.md),
[`261`](261-capability-candidate-demand.md), and the `autogenesis-capability-demand`
/ `autogenesis-producer-outcomes` gates). This track wires it to the producer
work.

- **C1 — proved facts auto-enter the lemma library** B2 searches, so every new
  proof widens the engine.
  Exit: a fact proved in one cycle is used in a later cycle's proof.
- **C2 — obstruction-driven producer synthesis.** The ranked candidate-capability
  demand of [`261`](261-capability-candidate-demand.md) chooses which producer
  B1 authors next — the shape blocking the most open facts, measured, not
  guessed.
  Exit: a producer built from the top of that backlog converts its predicted
  family.
- **C3 — dependency-aware target selection.** The concept DAG says what to prove
  next; prioritize facts whose dependencies were just proved — frontier
  expansion, not random grinding. (`--reachable-first`, landed 2026-08-25, is the
  trivial first version.)

## Track D — keep it honest at scale (non-negotiable)

At N producers the ledger *is* the product, so a checker that cannot fail is
worse than none.

- **D1 — every new producer carries soundness-negative tests**: adversarial
  fixtures over *satisfiable* goals that a forged proof would pass. Mutation
  testing cannot find a distinction the certificate never recorded (the
  `nra_monomial_bound` lesson); for every case the producer distinguishes, write
  a fixture over a SAT query where the certificate's inability to express the
  distinction makes the fixture impossible.
- **D2 — held-out evaluation is the honesty gate.** The nursery preregisters
  held-out families; the real claim is generalization to those, split integrity
  intact (touching one held-out member spends the family — ADR-0542).
  Exit: held-out facts proved.
- **D3 — second-kernel check + axiom-footprint gate on every emitted proof**, with
  the exit status depending on the finding, per producer.

## The critical path

**A1 → B1 (congruence) → C2 → B2 → B3**, with D running from day one.

A1 is a week and makes everything measurable. B1's congruence producer earns the
first real new proofs and validates producer authoring. C2 turns obstruction data
into a backlog so the next producers unblock the *most* facts, not arbitrary
ones. B2 is the general engine that ends the one-producer-per-shape treadmill. B3
is the ceiling-raiser and the reason this architecture exists — but it is only
safe and only useful *after* B2 gives it a search substrate and D gives it a
trustworthy checker.

Blunt version: the plumbing is done and trustworthy; the intelligence that makes
the agent broadly useful is B1→B2→B3, and it is tractable **specifically because**
the kernel makes untrusted proposals safe.

## Groundwork already landed (2026-08-25)

- `scripts/gen-statement-adapters.py` + `14-frontier-reachability.md` — the
  reachability tool and the measured decomposition (Track A1).
- `--skip-unreachable` — the loop no longer spends two model rounds (~26k tokens)
  discovering a fact has no export.
- `--reachable-first` — `--next` surfaces the productive frontier first (Track C3
  seed).
- The mobility summary now names the dominant unevaluable reason, so
  `unevaluable=186` reads as a reachability block, not a tactic gap.
