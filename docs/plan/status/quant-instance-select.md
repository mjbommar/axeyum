# Lane: quant-instance-select — the selection lever already shipped, and it acts on 0.30 % of the rejected traffic (ADR-2133)

<!-- plan-section: lane-status -->

**Lane QUANT-INSTANCE-SELECT (`DONE`, quant-instance-select, 2026-09-16).**
[ADR-2133](../../research/09-decisions/adr-2133-generation-bounded-instance-selection.md);
artifacts in `bench-results/quant-instance-select-20260916/`.

## What this lane was asked to build, and why it did not

Build generation- and relevance-bounded instantiation with a per-round cap,
behind a dated lever, on the premise (QUANT-INSTANCE-PROBE) that UFLIA's block
is instance SELECTION rather than ground REFUTATION.

**Step 0 of the brief — does it already exist? — answered yes.** All three
briefed pillars are shipped in `crates/axeyum-solver/src/qinst_egraph.rs`:

| briefed pillar | already in tree |
|---|---|
| per-term generation, cost `weight + generation` | `TermGenerations` (`:4478`), `derivation_generation` (`:4510`) |
| queue in cost order, per-round cap | `budget_flood_slice` (`:4256`), `FLOOD_ROUND_ADMISSION_CAP = 256` (`:1225`) |
| eager/lazy split | `FLOOD_EAGER_GENERATION_MAX = 1` (`:1233`) |
| incremental matching (new terms only) | ADR-0112, module doc `:16-22` |
| nested universals registered for matching | `AXEYUM_NESTED_QUANT`, default ON |
| generation-bounded final check | `FLOOD_FINAL_SUBSET_MAX_GENERATION = 1` (`:5235`) |

So the lane's first deliverable is the SIZING that says what the shipped
machinery does on the 53 cores, and that measurement retired the lever.

## Measured (53 ADR-2113 UFLIA cores, s6 pinned pairs, 24 s / 8 GiB)

- The whole selection apparatus is gated on `FLOOD_THROTTLE_MIN_GROUND = 2048`
  and on a deferred pool larger than 256. **`budget_flood_slice` engaged on
  0 cores.** Ceiling for the briefed lever on this population: **0**.
- Of 38 cores we do not decide, 35 leave a generation dump. On **22 of 35** our
  ground set never reaches the generation z3's own refutation needs
  (`ours_maxgen < z3_maxgen`) — a REACH gap, which selecting harder cannot
  close. On the other **13** we do reach it, at a median ground set of **516**
  terms, which is not a set any ground checker drowns in.
- z3 `:max-generation`: **25 of 53** cores need generation >= 3; our single
  subset-first final check only ever sees generation <= 1, and only at
  ground >= 2048 (**11 of 37** dumped cores).

Full numbers and the two measurement traps hit on the way (a census-gated
counter read as a zero; a join key that silently dropped every row) are in
`bench-results/quant-instance-select-20260916/README.md`.

## The lever, and its A/B

`GENERATION_LADDER_LEVEL = 0` / `AXEYUM_QINST_GEN_LADDER` — a generation LADDER
on the final refutation check (`gen <= 0`, `<= 1`, … ascending, first `unsat`
wins, fall through to the unchanged full check), **OFF**. Strictly additive, so
it has no `sat` path and cannot produce a wrong verdict in either direction.

Interleaved per-file A/B on the 53 cores: OFF decides 16, ON decides 15.
**0 stable gains, 0 stable losses, 0 flips** — the one apparent loss is
`unknown` on all six runs of a 3x interleaved recheck.

**The null is not a coverage hole.** The ladder reached the check on **31 of 53**
cores and ran **1 to 4 layers over 35 invocations**, with `refuted_at=none` on
**all 35**. Not one shallow subset of our accumulated ground set was refutable
when the full set was not. Beside the probe's result that our ground checker
refutes 6 of 7 cores when handed z3's OWN instances, that says the refutation is
**absent from our ground set at every generation, not buried in it**.

By the brief's criterion (stop if ON decides < 20 of 53), the lane stops at the
ADR: no division-level A/B, no held-out draw.

## Landed changes

| commit | files | what |
|---|---:|---|
| `c2c34bc66` | 6 | the sizing: harness, per-core TSV, README, status |
| `f024696f4` | 10 | the generation ladder behind `AXEYUM_QINST_GEN_LADDER`, OFF; unit + integration fixtures; mutation entry; pre-push registration; ADR-2133 |

## Next

Not selection. **Reach.** `rej_nocontext` is 36.06 % of rejected traffic and 22
of 35 open cores never reach the generation z3's refutation needs — the nested /
context-dependent activation wall of ADR-2113 §4b, which QUANT-INSTANCE-PROBE
independently re-derived from the reconstruction side (46 % of z3's own
recovered instances are nested instantiations). A fifth lane tuning the ground
side of this loop is a fifth null.

A cheaper separate experiment the sizing exposed and this lane did NOT run:
`FLOOD_FINAL_SUBSET_CHECK_MIN_GROUND = 2048` keeps the shipped shallow pre-check
from running on 26 of 37 dumped cores (median ground 1,061). The ladder result
suggests lowering it would also be a null on this population, but that is an
inference, not a measurement.
