# Lane: board-tier1 — the seven Tier-1 divisions, at n = 200 instead of n = 24

<!-- plan-section: lane-status -->

**Lane board-tier1 (`DONE`, board-tier1, 2026-09-13).** Seven divisions measured
at 200 full-span files each, with the blockers censused over the whole winnable
set. Pure measurement: **no solver code changed.**

The Tier-1 priority list placed AUFLIRA and UFNIA at #1 and #2 on the strength
of a 24-file probe, not a board. All seven of its divisions are now boarded at
200 full-span files each, three solvers interleaved per file at 24 s / 8 GiB.

Pinned lists committed at **`3320c7136`** BEFORE anything was measured, and
`mklist.py --dry-run` re-derives them so that ordering is checkable rather than
merely asserted.

Artifact: [`bench-results/tier1-divisions-headtohead-20260913/`](../../../bench-results/tier1-divisions-headtohead-20260913/README.md)
· method in [`PROTOCOL.md`](../../../bench-results/tier1-divisions-headtohead-20260913/PROTOCOL.md)

    axeyum 126 / 1400   z3 644 / 1400   cvc5 566 / 1400   winnable 603

| division | files | probe (n=24) | board (n=200) | verdict |
|---|---:|---:|---:|---|
| AUFLIRA | 20,011 | 4 % | **5.0 %** | CONFIRMED |
| UFNIA | 13,464 | 20 % | **26.5 %** | CONFIRMED |
| ABV | 4,975 | 8 % | **2.0 %** | **REFUTED** (lower) |
| ALIA | 3,098 | 0 % | **0.0 %** | CONFIRMED |
| AUFNIRA | 1,480 | 4 % | **1.5 %** | CONFIRMED |
| AUFBV | 1,523 | 4 % | **5.0 %** | CONFIRMED |
| FP | 2,669 | 20 % | **23.0 %** | CONFIRMED |

CONFIRMED = the board rate is inside a **Wilson** 95 % interval around the
probe. Wilson, not the normal approximation: ALIA's probe was 0 of 24, where
the normal interval is the single point 0.0 and every possible board would
"refute" it.

**Six of seven probe rates survive, and AUFLIRA and UFNIA are correctly placed
at #1 and #2.** The one refutation, ABV, is in the least consequential
direction — and its real content is that the division is hard for everyone
(z3 14 of 200, cvc5 4), which a 24-file probe cannot show.

## The headline answer

The `NESTED-ARRAY-IR` lane (ADR-1955) is sizing an IR change against a
**29,564-file** figure. The brief asked to be told loudly if the true share is
much lower. **It is not lower; it is higher, and much more concentrated.**

| division | winnable | nested-array refusal | share |
|---|---:|---:|---:|
| ABV | 17 | 17 | 100 % |
| AUFLIRA | 187 | 185 | 99 % |
| AUFNIRA | 139 | 129 | 93 % |
| ALIA | 36 | 33 | 92 % |
| UFNIA / AUFBV / FP | 224 | **0** | **0 %** |

364 of the 379 winnable rows in the four array divisions — **96 %** — and
exactly zero in the other three. Every one returns in ~0.1 s of a 24 s budget
(median 23,999 ms unspent): the front door refuses the file, so no budget
reaches it.

But 29,564 is a **population**, not a reach — it is exactly the four array
divisions' file counts. The projected **ceiling** is **20,399**, and
**18,510 of that (91 %) is AUFLIRA alone**; ABV, ALIA and AUFNIRA together
project to 1,889. The work is worth doing and it is **one division plus a
remainder**, not four. It is also a ceiling on *reach*, not a forecast of files
gained: parsing a file is not deciding it.

## Soundness

126 verdicts, **0 disagreements**, 0 reference-vs-reference conflicts, 0
reference-vs-`:status` conflicts. `wrapper-killed` is zero for every solver in
every division across all 4,200 runs. Twelve verdicts that nothing checked at
24 s were re-run at 600 s: **0 contradictions**, and two AUFBV rows confirmed by
z3 — which needed 201.5 s and 134.0 s where we took 1.61 s and 4.61 s.

## Decisions and findings

- **[ADR-1957](../../research/09-decisions/adr-1957-a-zero-disagreement-claim-must-publish-its-comparable-denominator.md)**
  — a zero-disagreement claim must publish its comparable denominator and mark
  the line when it is zero. ABV and ALIA both print `DISAGREEMENTS: 0` over
  ZERO comparable verdicts.
- **ADR-1941 is load-bearing here**: the `attempts=`-only rule would discard
  **454 of 603 census rows (75 %)**, where only **19 (3 %)** carry an open
  segment. On AUFLIRA it would empty the census entirely.
- **ADR-1950's falsification mechanism fired on this lane's own table**:
  `e-matching: instantiation time budget exhausted` is named for a clock and
  its median row gives up with 6,565 ms of 24,000 unspent.
- Four findings with repros in
  [`findings/README.md`](../../../bench-results/tier1-divisions-headtohead-20260913/findings/README.md),
  none fixed here: a terminal internal error in AUFNIRA (3 rows, repro
  `AUFNIRA/FFT/smtlib.701996.smt2`); the unconfirmed verdicts; a stride-built
  `parity-lists/FP.txt`; and a core-collision checker that reported green over
  a live fleet while detecting nothing.

## Not this lane

- The nested-array IR change itself — sized here, not built here.
- A model-replay check for the ten verdicts still unconfirmed.
- The AUFNIRA `!int_bv_0` re-declaration defect.
- Any budget or cap change. A cap turns a slow `unknown` into a fast one and
  only an A/B over the pinned winnable population can tell the difference.

### Landed commits

| commit | what |
|---|---|
| `3320c7136` | the seven pinned 200-file lists, committed before any measurement |
| `9afba4c94` | the harness, and the repin the loadframe caught |
| `655605500` | controls for four checkers |
| `8b1a6fa38` | AUFLIRA and ABV boards, AUFLIRA census, the 600 s re-check |
| `d3e6e13ad` | a core-collision check that was green over a fleet and detected nothing |
| `e4bbf0a5e` | ALIA board, and the VACUOUS label on an empty zero |
| `8ca59deb0` | ABV and ALIA censuses |
| `9c0419b9a` | ADR-1957 |
| `332e3ca2b` | the 29,564 figure is a population; 95 % of its reach is one division |
| `d3795fb8b` | derive the reference-frame claim, and make FRAME OK able to say VIOLATED |
| `3db876e7e` | findings, and `mklist.py --dry-run` |
| `4580337e2` | `finish-division.sh` |
| `05c61ea9b` | an empty winnable set is a result, not a missing census |
| `5fdd04df6` | tie the three artifacts together, and prove the tie can break |
| `c1e5bfbc1` | `PROTOCOL.md` |
| `b9a9be905` | one command for every control |
| `09ff53271` | all seven boards |
| `660997e3b` | all seven censuses, and the README |

<!-- plan-section: landed-changes -->

| 2026-09-13 | board-tier1 | First parity rows for AUFLIRA / UFNIA / ABV / ALIA / AUFNIRA / AUFBV / FP (47,220 files): 10 / 53 / 4 / 0 / 3 / 10 / 46 of 200 vs z3 197 / 96 / 14 / 32 / 138 / 30 / 137, **0 disagreements, 0 wrapper kills**; six of seven probe rates CONFIRMED at n=200, ABV REFUTED; the nested-array refusal is 364 of 379 winnable array rows (96 %) but **91 % of its reach is AUFLIRA alone**; ADR-1957; ADR-1941's attempts-only rule would discard 454 of 603 census rows |
