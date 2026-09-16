# ADR-2133: generation-bounded instance selection was already built; the ladder on the final check is what the sizing indicates

Status: proposed
Date: 2026-09-16
Index-status: proposed
Index-summary: The lane was briefed to build generation- and relevance-bounded instantiation with a per-round cap, on QUANT-INSTANCE-PROBE's finding that UFLIA's block is instance SELECTION. **Every briefed pillar already ships** — `TermGenerations` (`qinst_egraph.rs:4597`), `budget_flood_slice` (`:4256`) ordering the deferred pool by generation then index, `FLOOD_ROUND_ADMISSION_CAP = 256`, `FLOOD_EAGER_GENERATION_MAX = 1` (whose own doc comment names z3's `qi.eager_threshold`), ADR-0112's match-only-new-terms incrementality, and nested-universal discovery ON by default. So the deliverable became the sizing, and the sizing retired the lever. Measured on ADR-2113's 53 reference-minimal UFLIA cores (s6, pinned pairs, 24 s / 8 GiB): the per-round cap **does** engage, on **14 of the 26** cores that print the fixpoint census — but pooled over all 53 its own truncation is `rej_flood = 21,886` of **7,328,804** rejections, **0.30 %**, against `rej_nocontext` **36.06 %** and `rej_poscap` **27.41 %**. Tuning a cap that truncates 0.30 % of candidates cannot move this population, whatever it orders by. Two deeper facts say why: on **22 of the 35** open cores that dump, our ground set **never reaches the generation z3's own refutation needs** (a REACH gap no selection policy closes; 8 of them admit zero instances), and on the 13 that do reach it the median ground set handed to the final check is **516** terms — not a set any ground checker drowns in. Meanwhile z3's `:max-generation` needs generation **>= 3 on 25 of 53**, while our one generation-bounded final check sees only generation **<= 1** (69.5 % of terms) and only above ground 2048, so it does not run at all on **26 of the 37** dumped cores (median ground 1061). The increment that follows is therefore not an admission cap but a **generation LADDER on the final refutation check** — `gen <= 0`, `<= 1`, … ascending, first `unsat` wins, fall through to the unchanged full check otherwise — shipped **OFF** behind `AXEYUM_QINST_GEN_LADDER` / `GenerationLadderGuard`. It is strictly additive (every layer is a subset of the conjunction the full check already takes, so a layer's `unsat` refutes the whole set and a layer's non-`unsat` is discarded), so it has no `sat` path and the brief's suggested soundness-negative has no analogue; the real failure mode — a ladder that swallows the full check — is mutation-killed at exactly one named fixture. Two measurement traps are recorded rather than quietly fixed: `flood_slices` is itself gated on a SECOND variable (`AXEYUM_QPROBE_CENSUS`), so the first arm reported "engaged on 0 of 26" when the answer is 14 of 26; and a join key that kept the capture's `.txt` suffix silently dropped every `ref-cores.tsv` row while every other column still looked right. **The ladder's own A/B is a null, and a real one**: interleaved per file on the 53 cores it is 0 stable gains, 0 stable losses, 0 flips (OFF decides 16, ON 15; the single apparent loss is `unknown` on all six runs of a 3x interleaved recheck). That null is not a coverage hole, because the ladder now prints what it did: it **reached the check on 31 of 53 cores** and ran **1 to 4 layers** across **35 invocations**, with **`refuted_at=none` on all 35**. Not one shallow subset of our accumulated ground set was refutable when the full set was not. Set beside the probe's result that our ground checker refutes 6 of 7 cores when handed z3's OWN instances, that is the sharpest statement of where UFLIA stands: **the refutation is absent from our ground set at every generation, not buried in it** — so no ranking, cap, or layered check over that set can recover it, and the next increment is REACH (`rej_nocontext`, nested activation), not selection. By the brief's own criterion (stop if ON decides < 20 of 53) ON decides 15, so the lane stops at this ADR: no division-level A/B, no held-out draw.

## Context

QUANT-INSTANCE-PROBE separated the two candidate explanations for UFLIA's
plateau. Handed z3's own used instantiations as plain ground assertions, our
existing dispatch ladder refutes **6 of the 7** cores whose instance set
reconstructs completely. So the ground checker is not the block; something
about which instances we build, and how many, is.

This lane was briefed to act on that: build generation- and relevance-bounded
instantiation with a per-round cap, an eager/lazy split, incremental matching,
and registration of nested universals — the z3 `qi_queue.cpp` design.

## Decision

**Do not build the briefed lever.** It exists, and the sizing says its ceiling
on this population is zero cores. Build the generation ladder on the final
refutation check instead, ship it OFF, and record the measurement.

## What already exists, at `file:line`

Verified at this lane's HEAD in `crates/axeyum-solver/src/qinst_egraph.rs`:

| briefed pillar | shipped as |
|---|---|
| per-term generation, cost `weight + generation` | `TermGenerations` `:4597`, `derivation_generation` `:4629` |
| queue in cost order, per-round cap | `budget_flood_slice` `:4256`; `FLOOD_ROUND_ADMISSION_CAP = 256` `:1225` |
| eager/lazy split on the generation axis | `FLOOD_EAGER_GENERATION_MAX = 1` `:1233` |
| engagement floor | `FLOOD_THROTTLE_MIN_GROUND = 2048` `:1242` |
| incremental matching, new terms only | ADR-0112; module doc `:16-22` |
| nested universals registered for matching | `AXEYUM_NESTED_QUANT`, default ON (`config_registry.rs:7045`) |
| generation-bounded final check | `FLOOD_FINAL_SUBSET_MAX_GENERATION = 1` `:5235` |

The reference design the brief cites is the one already implemented. z3's
`qi_queue.cpp` cost `(+ weight generation)` and its `qi.eager_threshold` are
named in `FLOOD_EAGER_GENERATION_MAX`'s own doc comment; `smt_enode.h`'s
per-e-node `m_generation` is what `TermGenerations` mirrors; `mam.cpp`'s
match-only-terms-new-since-the-last-round is ADR-0112. cvc5's `instMaxLevel` is
the same generation ceiling under another name, and `instWhenMode` is the
cadence `interleaved_check_due` already implements.

Three prior lanes (ADR-2120 activation, ADR-2124 incremental ground closure,
ADR-2130 session-hosted arithmetic) each moved one core and none moved the
population. This is the fourth reading of the same wall from a new angle.

## What the sizing measured

53 ADR-2113 reference-minimal UFLIA cores. Release `smtcomp_cli --trace`,
`--timeout-ms 24000`, `ulimit -v 8388608`, s6 (idle), pinned physical core
pairs `1,9` / `3,11` / `5,13` / `6,14`. Two arms, because
`census.flood_slices += usize::from(census.enabled)`: arm 0 `AXEYUM_QPROBE`
only (the historical probe byte for byte, carrying the ground dumps), arm 1
with `AXEYUM_QPROBE_CENSUS` as well.

**The per-round cap acts on 0.30 % of rejected traffic.** Pooled over all 53
cores, 7,328,804 rejections:

| rejection | count | share |
|---|---:|---:|
| `rej_nocontext` | 2,642,864 | **36.06 %** |
| `rej_poscap` | 2,009,088 | 27.41 % |
| `rej_seen` | 1,392,171 | 19.00 % |
| `rej_true` | 1,173,037 | 16.01 % |
| `rej_handoff` | 68,352 | 0.93 % |
| **`rej_flood`** | **21,886** | **0.30 %** |
| `rej_dupother` | 21,406 | 0.29 % |

Seven of thirteen reject kinds nonzero — the positive control that the census
is live. `budget_flood_slice` engaged on 14 of the 26 cores that print the
fixpoint census, so the machinery is not idle; it is simply not where the
instances are lost.

**Reach, not selection, on 22 of 35.** Of the 38 cores we do not decide, 35
leave a ground dump:

| | cores | median ground | terminal reason |
|---|---:|---:|---|
| `ours_maxgen < z3_maxgen` | **22** | 1086 | 16 `timeout-mid-round`, 3 `SHAPE`, 2 `CLOCK`, 1 `ground-ceiling` |
| `ours_maxgen >= z3_maxgen` | **13** | **516** | 7 `timeout-mid-round`, 5 `SHAPE`, 1 `CLOCK` |

Eight of the 22 admit zero instances at all.

**The generation gap.** z3 `:max-generation` per core: `<= 1` on 17/53,
`<= 2` on 28/53, **`>= 3` on 25/53**. Our own ground sets pool to gen0 52.7 %,
gen1 16.8 %, gen2 22.4 %, gen3 7.8 %, gen4 0.3 %. So
`FLOOD_FINAL_SUBSET_MAX_GENERATION = 1` admits 69.5 % of terms — a weak
reduction — and `FLOOD_FINAL_SUBSET_CHECK_MIN_GROUND = 2048` keeps that
pre-check from running at all on 26 of the 37 dumped cores.

## The lever

`GENERATION_LADDER_LEVEL = 0` (`AXEYUM_QINST_GEN_LADDER`, or
`GenerationLadderGuard` in-process). At level 1,
`generation_ladder_check` restricts the accumulated ground set to
generation `<= 0`, then `<= 1`, … ascending to
`GENERATION_LADDER_MAX_GENERATION = 4`, skipping a layer that adds nothing and
never running the full set. It carries **no ground-set floor of its own** —
that is the substantive difference from `FLOOD_FINAL_SUBSET_CHECK_MIN_GROUND =
2048`, whose floor is why the shipped pre-check is absent on the majority of
this population. The whole ladder runs under
`remaining / GENERATION_LADDER_BUDGET_DIVISOR = 4`, split equally across the
layers still to run, so it costs no more before the full check than the shipped
single-layer pre-check already could.

### Why no verdict it produces can be wrong

Every layer is a **subset** of the conjunction the unchanged full check already
takes, and every member of that conjunction is an original assertion or an
admitted instance of an asserted universal. So a layer's `unsat` refutes the
whole set: the ladder is strictly additive, turning an `unknown` into an
`unsat` and nothing else. It never claims `sat` — a layer that does not refute
is discarded rather than believed — and it never replaces the full check:
`generation_ladder_check` returns `Option`, and `None` means only "no layer
refuted".

That shape is why the brief's suggested soundness-negative — a `sat` claimed
before the lazy queue drains — has **no analogue here**: there is no `sat` path
to claim it on. The failure mode this lever really has is a ladder whose
non-refutation swallows the full check, and that is what the fixtures aim at.

## Evidence

- Unit, `qinst_egraph::tests` (generations constructed exactly):
  `the_generation_ladder_refutes_at_the_shallowest_layer_that_can`,
  `a_generation_ladder_that_refutes_nothing_must_not_swallow_the_full_check`,
  `the_generation_ladder_is_off_in_the_shipped_configuration`.
- Integration, `crates/axeyum-solver/tests/quant_generation_ladder.rs`: two
  satisfiable fixtures that must not be refuted at either level, two
  unsatisfiable ones that must still be refuted at both — the second pair being
  simultaneously the positive controls that keep the first pair from passing
  against an engine that decides nothing.
- Mutation, `scripts/tests/mutation_controls.py quant-generation-ladder`,
  baseline 3 tests:
  - "a ladder that refutes nothing must FALL THROUGH to the full check" —
    **killed 1**, exactly `a_generation_ladder_that_refutes_nothing_must_not_swallow_the_full_check`.
  - "a layer admits only terms at or below its OWN generation" — **killed 2**.
  - `--check-anchors`: 159 suites, 1120 anchors, **stale = 0**.

## The A/B, and why its null is a real one

53 cores, ladder OFF vs ON, **interleaved per file** — same core file, same
pinned physical core pair, OFF then ON back to back, so ambient load cancels in
the difference rather than being attributed to an arm. s6, 24 s / 8 GiB.

| | decided | unknown |
|---|---:|---:|
| OFF | 16 | 37 |
| ON | 15 | 38 |

**Gains 0. Flips 0.** The one apparent loss
(`UFLIA_boogie_Cast_Cast.R_System.Object_System.Int32`) was re-run three times
per arm, interleaved, on the same pinned pair: **`unknown` on all six runs**,
so it is the OFF arm getting lucky once and not a stable loss. Stable gains 0,
stable losses 0, flips 0.

**The null is not a coverage hole, and this is the number that says so.** With
`AXEYUM_QPROBE` the ladder now prints what it did, because otherwise "the ladder
changed no verdict" and "the ladder never ran" are the same observation. Over
the 53 cores it **reached `generation_ladder_check` on 31**, and ran layers on
every one of them:

| layers run in one invocation | 1 | 2 | 3 | 4 |
|---|---:|---:|---:|---:|
| invocations | 13 | 11 | 9 | 2 |

35 invocations across 31 cores, 1 to 4 layers each — and **`refuted_at=none`
on all 35**. Not one shallow subset of our accumulated ground set was refutable
when the full set was not.

Put beside QUANT-INSTANCE-PROBE's result — our ground checker refutes 6 of 7
cores when handed z3's OWN instances — that is the sharpest statement of where
UFLIA actually stands: **the refutation is absent from our ground set at every
generation, not buried in it.** A set of 8,019 terms that contains no refutable
subset at any depth is not a volume problem, and no ranking, cap, or
layered check over that set can become one.

By the brief's own criterion — "if ON decides < 20 of 53, stop at the ADR with
the histogram" — ON decides **15**, so this lane stops here. No division-level
A/B was run and no held-out draw was made.

## Measurement traps recorded rather than quietly fixed

- **`flood_slices` is census-gated.** `census_enabled()` reads a SECOND
  variable, `AXEYUM_QPROBE_CENSUS`, on top of `AXEYUM_QPROBE`, and every
  `flood_*` and `rej_*` counter is hard-zero without it. Arm 0 therefore
  reported `flood_slices = 0` on 26 of 26 cores, and "the selection machinery
  never engages" was written down before arm 1 was run. The answer is 14 of 26.
- **A join key that dropped every row.** The sweep writes `cap/<core>.txt` and
  `dump/<core>.dump`; joining `ref-cores.tsv` on the capture filename matched
  nothing and printed `z3_maxgen=?` for all 53 while every other column looked
  right.

## Consequences

- The lever ships **OFF**; nothing about the shipped configuration changes.
- The next increment on this population is **reach**, not selection:
  `rej_nocontext` at 36.06 % and the 22 cores that never reach z3's generation
  are one problem (nested / context-dependent activation, ADR-2113 §4b), and
  it is the same wall the probe found from the reconstruction side.
- `FLOOD_FINAL_SUBSET_CHECK_MIN_GROUND = 2048` is now measured to be the reason
  the shipped shallow pre-check is absent on the majority of this population.
  Lowering it is a separate, cheaper experiment than the ladder.

## Artifacts

`bench-results/quant-instance-select-20260916/` — `README.md`,
`size-report.py`, `sizing.tsv` (one row per core), the two sweep scripts, and
the A/B runner.
