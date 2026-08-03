# Sequencing, gates, and what to do first

## The dependency order

```
                    ┌─ phase 0 catalogue ─┐
                    │                     ├─→ phase 3 policy ──┐
  phase 1 direction ┘                     │   (gated on G1)    │
        │                                 │                    │
        │                    phase 2 evaluation ──[G1]─────────┘
        │                                 │
        ├─→ phase 4 eqsat/walk-back ──[G2]┤
        ├─→ phase 5 lateral bridges       │
        │                                 │
  phase 6 parallel ──[G3]─────────────────┤
        │                                 │
        └─→ phase 8 open problems ←───────┘
                    │
              phase 9 Lean evidence  (independent; sequence B-first)
                    │
              phase 7 agentic loop   (depends on 0/1 for the DSL only)
```

Phases 1, 6, and 9 have no upstream dependency inside the track and can start
immediately. Phase 3 is the only phase hard-gated on a measurement.

## The three gates

| Gate | Task | Question | Consequence of a negative result |
|---|---|---|---|
| **G1** | T2.3 | Is the VBS–SBS PAR-2 ratio above ~1.1 on decidable instances? | Phase 3 is moot. Redirect that effort to phases 5, 6, and 8, where the payoff does not depend on route-selection signal. |
| **G2** | T4.6 | Do congruence-closure explanation chains stay tractable on real shapes? | Tiers 1–2 of the walk-back ladder are unaffordable; either implement FMCAD-2022 proof minimization first or cap eqsat at Tier 0. |
| **G3** | phase 6 | What sits in the 10²–10⁴ CPU-hour band on one workstation? | Target selection for phase 8 changes; record-chasing is off the table regardless. |

**None of the expensive work starts before its gate reports.** This is the single
most important scheduling rule in the track.

## If you can only do one thing

**T3.5 — policy-v0 ≡ legacy dispatch.** Encode today's fixed dispatch order as data
and prove byte-identical behavior on the full corpus. It is the prerequisite for
every route-search idea, it is the only safe way to touch `auto.rs`, and it has
standalone value: it converts 8,616 lines of implicit ordering into a reviewable
artifact even if no learning ever happens.

Runner-up: **T9.1 — axiom-ledger triage.** 65 rows, all `unclassified`, blocking
every R4+ evidence claim. Cheapest task in the track with the highest ratio of
unblocked downstream work.

## Recommended first slice (roughly one focused month)

1. T0.1 + T0.2 — RouteTrace JSON + route registry. No behavior change.
2. T1.1 + T1.2 — `Direction` monoid and the golden direction ledger. No behavior
   change; produces the machine-readable over/under-approximation labels the repo
   currently carries only as 97 prose mentions.
3. T2.1 + T2.2 + **T2.3 (G1)** — features, episode log, and the gate measurement.
4. T9.1 — axiom-ledger triage, in parallel; independent of everything else.

Nothing in that slice modifies a verdict. Everything in it is either additive
telemetry, a generated artifact, or a measurement. That is deliberate: the track's
riskiest surface is `auto.rs`, and the first month should buy information rather
than spend risk.

## What competes with this track

- The **active QF_BVFP/binary79 focus** (P1.2/P2.8) in STATUS.md.
- The **paused CAS lane** at wave twenty-four, which must resume at its handoff
  checkpoint before anything else touches CAS parity work — note phase 5 touches
  `crates/axeyum-cas` and must coordinate.
- Per CLAUDE.md multi-agent hygiene: `auto.rs` is the hottest file in the repo.
  Keep new code in new modules (`route_registry.rs`, `direction.rs`, `bridge.rs`)
  and make `auto.rs` diffs minimal and additive.

## Effort honesty

| Phase | Rough size | Notes |
|---|---|---|
| 0 catalogue | 3–5 weeks | Mostly mechanical once the registry pattern is set |
| 1 direction | 4–6 weeks | Soundness-critical; the fuzz work is the bulk |
| 2 evaluation | 3–4 weeks to G1 | G1 itself is days |
| 3 policy | 2–4 months | T3.4 (chain executor) dominates and is the risk |
| 4 eqsat | 2–3 months | Three M-tasks hide behind the word "saturation" |
| 5 lateral bridges | 6–10 weeks for B1+B2+B3-lite | B3 full SDP is a separate arc |
| 6 parallel | 2–4 months | T6.3 splitter and T6.5 streaming checker dominate |
| 7 agentic loop | 3–4 weeks to the pilot | Then measured go/no-go |
| 8 open problems | 4–6 weeks to the census | The census is the deliverable, not a record |
| 9 Lean, (B) only | 4–6 weeks | (A) mathlib capstone is 4–8 months, optional |

Total to a coherent v1 of the track, excluding the optional capstone and full SDP:
on the order of **9–15 months part-time**. That is a real number, not a
discouragement — the phases are independently valuable and several ship standalone
capability regardless of whether the searched-policy thesis pans out.
