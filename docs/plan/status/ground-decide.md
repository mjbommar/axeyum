# Lane: ground-decide — the ground checker mostly refuses, and the set it refuses is one we had no need to build

<!-- plan-section: lane-status -->

**Lane ground-decide (`DONE`, ground-decide, 2026-09-14).** [ADR-2015] closed
the last loop-side hypothesis for the `UFLIA`/`UFNIA` gap and handed over one
measured observation — 78 held-set replays in which **our own ground checker
declines our own instantiated conjunction** — with the instruction to split them
before sizing anything. This lane sized it. **The census needed a string split
first, the leader changed when it was done, and the lever built against the new
leader moves zero.** Full reasoning in [ADR-2020]; artifacts in
[`bench-results/ground-decide-20260914/`](../../../bench-results/ground-decide-20260914/PREREGISTRATION.md).

## The census needed splitting, and this lane walked into the trap first

The record separator inside the committed census cells is `;QPROBE`, **not** a
bare `;` — the `why=` detail contains `;`. A `why=` may also **wrap** another
reason or **append** one after a stats parenthetical. Peeling those:

| | outer string | binding cause |
|---|---:|---:|
| distinct buckets | 5 | **10** |
| largest | `Timeout｜preprocessed dispatch timeout…` (25) | lazy LIA pre-SAT skeleton boundary (**22**) |

**46 of the 78** had their binding cause behind at least one wrapper, and the
25-row largest outer bucket is **four** causes. [ADR-2015]'s prose led with the
eager Ackermann bound; it is **second** (17). One bucket (`no model within the
bounded integer width 32`, 5) is left **`UNSPLIT`** across its two emit sites
and reported as such.

## The split, and the structure

Denominator 127 still-failing rows. The 78/40 is a **replay** split; at **row**
level it is **58 unknown-only / 31 sat-only / 6 MIXED (not separable) / 2
refute / 2 error**, plus 28 rows that never replayed.

**55 of 78 = 70.5 % `[59.6 %, 79.5 %]` are CHEAP REFUSALS by an admission
bound** — wall median **1,407 ms of a 10,000 ms budget** — not exhausted clocks.
The two populations split by division: `UFLIA` refuses 40:5, `UFNIA` exhausts
18:15.

## The bounds, read rather than assumed

- **`64` is not a unit error.** But it was never calibrated against the eager
  expansion: its own doc places it between the largest decided in-tree instance
  (40 pairs) and the smallest observed hang (117), as a **proxy for an unbounded
  downstream solve**. Unchanged since `6233a7c98`, 2026-06-24.
- **The same constant means two things.** `auto.rs:4068` treats it as a **route
  selector** (falls through to the lazy/CEGAR route); `combined.rs:86` treats it
  as a **hard decline** with no fallback. **17 of 17** of our replays are at the
  hard-decline site.
- **The skeleton envelope is a memory bound with 115x headroom.** Its own
  re-derivation measured peak RSS at **71 MiB** against the 8 GiB ceiling it
  cites and wrote *"above this, nobody has measured."* It refuses at **1.4x**
  that point.
- **`oversized_admission_probe` is not wired into the UF route** at all.
- **The lazy function-consistency lemma batch is uncapped**: `violated_pairs=448`
  adds `lemmas_added=17,750`. Deliberate and regression-tested (`42fc03e6e`),
  but justified at **6–23** pairs.

## Ten seconds on eleven ground terms

`t3_rw899.smt2`, 11 ground terms, 10 s budget: **20,626 LIA calls, 18,678 LP
relaxations, 9,035 simplex solves, 11,401,903 cloned arena nodes**. By `perf`:
27 % CDCL search, ~22 % allocator, 16 % simplex/Gomory, 7 % Tseitin. The width
ladder clones the **whole file's DAG** per rung (14,235 nodes for a set of 11).

## The A/B: a clean negative, shown non-vacuous

`AXEYUM_GROUND_DECIDE_PRESAT_ENVELOPE`, off by default, failing **closed**;
envelope `10,240/16,384` → `40,960/65,536`. Interleaved per-file, one binary,
two env values, shards fixed across arms (s5 `{1,3,5,7}`, s6 `{1,3,5,7}`).

| run | rows | OFF | ON | GAIN | LOSS | FLIP |
|---|---:|---:|---:|---:|---:|---:|
| main `UFLIA`+`UFNIA` | 129 | 0 | 0 | **0** | 0 | 0 |
| control `QF_BV` | 6 | 0 | 0 | 0 | 0 | 0 |
| secondary `QF_LIA` | 27 | 2 | 2 | 0 | 0 | 0 |
| noise floor (same arm) | 129 | 1 | 0 | 0 | **1** | 0 |

Wilson `[0.0 %, 2.9 %]`, wall 1.00x. **The null is non-vacuous**: on
`javafe.ast.MethodDecl.005.smt2` the OFF arm crosses both pre-SAT bounds
(`15500/1024`, `23388/4096`) in the shipped 24 s path and the ON arm crosses
neither. The refusal was measured converting into a **timeout**, as
pre-registered. **The same-arm noise floor moves 1 row, so the lever's effect is
smaller than the band built to detect it. Ships OFF.**

## What redirects the work

cvc5 1.3.4 on the **same 22 files** our skeleton boundary declines: **21
refuted, median `global::totalTime` 70 ms**, **nine with ZERO instantiation
tuples**, and **eight of those nine are files where our held set is at the 8,192
admission cap**. The conjunction we cannot decide is an artifact of
**over-instantiation**. Budget ([ADR-1995]), ceiling ([ADR-1956]), reach
([ADR-2005]) and head ([ADR-2015]) are closed; **selection** is not, and is the
axis this points at.

<!-- plan-section: landed-changes -->

| date | change | commits |
|---|---|---|
| 2026-09-14 | ADR-2020 — pre-registration, binding-cause census, reference measurement, env-gated pre-SAT envelope lever (OFF), A/B + controls + noise floor | `bdcffb3d0`, `a4642ce8d`, `e052b899b`, `ade774075`, `d62972ad7`, `7222e2549` |

[ADR-1956]: ../../research/09-decisions/adr-1956-do-not-raise-the-instantiation-round-ceiling-zero-of-the-177-rows-reach-it.md
[ADR-1995]: ../../research/09-decisions/adr-1995-the-instantiation-loops-verdict-is-not-monotone-in-its-budget.md
[ADR-2005]: ../../research/09-decisions/adr-2005-the-instances-are-e-matchable-and-we-already-build-them.md
[ADR-2015]: ../../research/09-decisions/adr-2015-the-round-head-is-a-symptom-the-ground-checker-is-the-wall.md
[ADR-2020]: ../../research/09-decisions/adr-2020-the-ground-checker-mostly-refuses-and-the-set-it-refuses-is-one-we-had-no-need-to-build.md
