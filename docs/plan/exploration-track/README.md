# Exploration Track — searched bridge composition, certified evidence, open problems

Status: proposed track (2026-08-01). Not yet accepted; every phase below carries
its own ADR gate. This folder is the plan, not a commitment.

Owner: unassigned. Does **not** preempt the active priorities in root
[PLAN.md](../../../PLAN.md) or the paused CAS lane
([handoff](../cas-parity-handoff-2026-07-22.md)).

## Thesis

Axeyum already composes theory-to-theory reductions to decide queries. It does so
in a fixed, hand-tuned order compiled into `crates/axeyum-solver/src/auto.rs`
(8,616 lines, ~45 route labels, full `RouteTrace` telemetry). This track proposes
to:

1. **Reify** that composition space as a validated data artifact rather than
   control flow;
2. **License** every composed verdict through a machine-checkable soundness
   direction, so novel chains cannot emit wrong answers;
3. **Search** the space with a measured policy instead of a hand-tuned order;
4. **Widen** the space with lateral (cross-mathematical) bridges from the CAS;
5. **Point** the result at open mathematical problems in the regime where search
   plus exact checking genuinely is the method.

The identity sentence is unchanged: **untrusted fast search, trusted small
checking.** This track is an argument that the search half has been hand-written
where it should be searched, and that the checking half is the asset that makes
searching safe.

Root **[PLAN.md](../../../PLAN.md)** is the only current project tracker. This
file and the phase/task files define the proposal and its exit contracts;
[STATUS.md](STATUS.md) is a compatibility pointer to the dependency-correct
current order.

## Read this first

[`00-review-synthesis.md`](00-review-synthesis.md) records what nine independent
branch reviews found — including **five factual corrections to the original
proposal** that change the shape of the work. Do not plan from the thesis above
without reading the corrections; two of them invalidate first-instinct designs.

## Phase map

| Phase | Title | Gate | State |
|---|---|---|---|
| [0](phase-0-catalogue/README.md) | Bridge catalogue as data | Golden-tested artifact reproduces dispatch decisions | proposed |
| [1](phase-1-direction/README.md) | Direction algebra + verdict licensing | Soundness-negative chain fuzz has teeth | proposed |
| [2](phase-2-evaluation/README.md) | Evaluation harness and reward signal | **VBS–SBS gap measured** (go/no-go for phase 3) | proposed |
| [3](phase-3-policy/README.md) | Searched route policy | Policy-v0 ≡ legacy dispatch, then beats it | proposed |
| [4](phase-4-eqsat-walkback/README.md) | Equality saturation + walk-back contract | Chain validation with teeth; measured chain sizes | proposed |
| [5](phase-5-lateral-bridges/README.md) | Lateral bridges from the CAS | pending review | pending |
| [6](phase-6-parallel/README.md) | Parallel search and cube-and-conquer | Verdict-identical across `--jobs`; streaming proof check | proposed |
| [7](phase-7-agentic-loop/README.md) | LLM-in-the-loop proposal layer | Pilot conversion rate per dollar | proposed |
| [8](phase-8-open-problems/README.md) | Open-problem intake and triage | pending review | pending |
| [9](phase-9-lean-evidence/README.md) | Lean evidence ladder and Comparator | pending review | pending |

Cross-cutting registers:

- [`adr-queue.md`](adr-queue.md) — every decision that may not be made silently in code.
- [`risks.md`](risks.md) — consolidated soundness traps, ranked.
- [`sequencing.md`](sequencing.md) — the dependency order and the three measurement gates.

## The three measurement gates

Three phases independently concluded "measure before building." These are the
track's real decision points; everything downstream is contingent on them.

1. **G1 — VBS–SBS gap** (phase 2, task EH-3). If axeyum's routes rarely differ in
   cost on decidable instances, there is no algorithm-selection signal and
   phase 3 is moot. Cheap to measure, must run first.
2. **G2 — explanation chain size** (phase 4, task EQ-6). If congruence-closure
   explanation chains blow up on real shapes, tiers 1–2 of the walk-back ladder
   are unaffordable and the design changes.
3. **G3 — reachable compute band** (phase 6). The open-problem regime is
   10²–10⁴ CPU-hours on one workstation. Target selection must be calibrated to
   that band before any run is scheduled.

## Standing rules inherited

- CLAUDE.md's pre-merge gates apply to every `auto.rs` touch in this track:
  `cargo test --workspace --lib`, `-p axeyum-solver --test corpus_regression`,
  and `--test progress_frontier`. The 829-commit `nia_unsat` bisect is the
  cautionary precedent.
- Every partial/underspecified operator or composed chain gets a fuzz seed-class
  that generates the degenerate case. A corpus sweep plus a fuzz that avoids the
  corner is not a soundness gate.
- Determinism is a public API promise. Phases 3, 6, and 7 each threaten it in a
  different way and each carries an explicit determinism design.
- Multi-agent hygiene: pathspec-only commits, `rustfmt --edition 2024 <file>`
  never `cargo fmt`, one writer per area.
