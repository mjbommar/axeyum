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

## Landed changes

| commit | files | what |
|---|---|---|
| (see ADR-2133) | `bench-results/quant-instance-select-20260916/` | sizing harness, per-core TSV, README |

## Next

The increment the sizing indicates is not a per-round admission cap. It is a
**generation-layered final refutation check** — today one layer at generation
<= 1, gated at ground >= 2048, so it never runs on 31 of 37 dumped cores. A
ladder over generations is strictly additive (a subset `unsat` refutes the
conjunction) and so cannot produce a wrong verdict in either direction.
