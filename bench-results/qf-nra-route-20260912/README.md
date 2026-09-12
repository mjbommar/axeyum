# QF_NRA — census of all 77 winnable files, 2026-09-12

Lane `qf-nra-route`. This directory holds the **population**, the **method**,
and the **raw per-file attribution** behind the QF_NRA row of the
2026-09-11/12 head-to-head board.

## Population — all 77, not a sample

Source: `bench-results/session-20260911-smtlib/head-to-head/QF_NRA.tsv`
(200 files; axeyum 117, z3 187, cvc5 186).

**Winnable** = axeyum's verdict is not in `{sat, unsat}` **and** at least one
reference verdict is. That is 77 of 200, listed in `winnable-77.txt` (absolute
corpus paths, sha256 `4c24f8e982c7a169a232e273aab18a16e86e6214f1c8ad1311f803c7fe3f9955`).

All 77 board basenames resolve to **exactly one** file in the 12,154-file
corpus root — checked, not assumed: 0 missing, 0 ambiguous.

### The population is not one family

Path-sorted lists let one family dominate the head of a census. This one does
not concentrate that way:

| family | files |
|---|---:|
| meti-tarski (sin 12, atan 9, sqrt 8, exp 7, CMOS 3, Chua 2, Nichols-Plot 2, polypaver 2, RL-high-pass 1) | 46 |
| LassoRanker (CooperatingT2 5, Ultimate 4, SV-COMP 3) | 12 |
| 20161105-Sturm-MBO | 5 |
| 20220314-Uncu | 3 |
| 20200911-Pine | 3 |
| 20211101-Geogebra | 2 |
| 20180501-Economics-Mulligan | 2 |
| 2019-ezsmt, UltimateAutomizer, hycomp, kissing | 1 each |

### Ground truth is not in dispute on these 77

Declared `:status` vs the two references:

| declared | z3 | cvc5 | files |
|---|---|---|---:|
| sat | sat | sat | 33 |
| unsat | unsat | unsat | 25 |
| unsat | unknown | unsat | 6 |
| unknown | sat | unknown | 3 |
| unknown | sat | sat | 3 |
| unsat | unsat | unknown | 2 |
| unknown | unsat | unsat | 2 |
| unknown | unsat | unknown | 2 |
| sat | unknown | sat | 1 |

**No row has z3 and cvc5 disagreeing**, and no reference contradicts a declared
`:status`. So any verdict we newly produce on these files has an uncontested
expected answer to be checked against.

### How it overlaps the 2026-09-06 census

`bench-results/parity-losses-20260906/QF_NRA.census.tsv` censused a 77-file
loss set too, but against **cvc5 alone** and before ADR-1751/ADR-1752. 70 of
77 are the same files; 7 are new and 7 dropped out. That census's classes are
therefore **not** re-usable here, and this one re-derives them from scratch.

## Method

Instrument: `smtcomp_cli <file> --timeout-ms 24000 --trace`, one file per
process, release build of this lane's tree.

Two fields are recorded per file, deliberately **not** collapsed into one:

- `give-up kind=… detail=…` — the reason the solver stated when it declined.
- `route bound_by=… last=…` — which route consumed the budget, and which route
  spoke last. The CLI's own docs record that classifying by the **last** route's
  message has been refuted here before (a 403-file census was wrong on 67 of
  70 in two divisions). Both are reported below; they disagree.

**Timeout wall.** A previous census wrapped a 24 s budget in `timeout 32` and
killed 17 processes at load 4–6, manufacturing false "no reason" rows. This one
uses `timeout -k 5 180` — 7.5x the budget — and counts any file that still
produced no reason as its own row rather than dropping it.

**Host.** s4, under concurrent load from other lanes (load average 12–23
throughout, 16 cores). The board itself was measured on s6, idle and pinned.
So the *reasons* here are comparable to the board; the *times* are not, and no
timing claim is made from this census. A structural, pre-budget decline (the
majority here) is load-independent; a watchdog kill is not.
