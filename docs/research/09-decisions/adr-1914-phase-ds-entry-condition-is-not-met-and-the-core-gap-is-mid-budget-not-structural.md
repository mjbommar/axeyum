# ADR-1914: Phase D's entry condition is NOT met — the core gap is mid-budget, not structural, and the phase closes unentered

Status: accepted
Index-summary: Phase D of the CDCL consolidation plan is gated on "Phase C has closed AND a conflict-count comparison still shows a material gap on a family we care about". Phase C closed 2026-09-10; this settles the second conjunct by re-running gate (b) on a QUIET box — load average 1.01–1.16 against the 2026-09-05 run's 12–33 with a spike to 111 — and the condition is **not met**. Three engines, byte-identical DIMACS (variable/clause counts match 2026-09-05 on 212 of 213 files), 20 s, pinned, one at a time: p4dfa native **9**/113 (was 6), CaDiCaL **12** (was 10), Kissat **14** (was 11); Noetzli 87/89/90 (was 86/88/89). Zero disagreements over 639 (engine, file) pairs, 54 of 54 `sat` models replayed. EVERY engine gained on a quiet box, so the 2026-09-05 deficit was partly contention on all columns. PAR-2 separates the engines by 2.3–3.7% of the two-timeout ceiling. The decisive measurement is not the count but the DECOMPOSITION. (1) Of the references' extra wins across 213 files, exactly **two** are decided with ≥ 4x budget headroom — and on one of those two, Kissat takes 0.60 s where **CaDiCaL takes 11.05 s**, an 18x spread between the two REFERENCES, so it is where a search fell and not a technique we lack. (2) Re-running the native core at 5x and 15x the budget on the files it misses: **four of six p4dfa files decide at 100 s** (4.2x/4.6x/6.8x/8.5x the reference) — a speed gap of known size — and two do not decide at 300 s. (3) A trap worth the ADR on its own: two Noetzli rows read `unknown` at a 300 s budget with `timed_out = false` at 194.7 s and 243.6 s — they hit `DEFAULT_PROOF_SAT_CONFLICT_LIMIT = 2_000_000` and returned `ResourceOut`, so "unknown at 300 s" there means "> 2M conflicts", not "> 300 s". That cap is reached on ZERO of the 117 undecided files at the gate's 20 s budget, so it does not explain the gap; it binds only above ~195 s. Decision: **Phase D closes unentered.** No core tuning is scheduled. Three pre-registered re-entry conditions replace it, each requiring more files DECIDED rather than fewer conflicts — the Phase C correction that a ratio diagnoses cause but does not predict value. Also recorded: the Phase C note's "QF_SLIA is a one-entry change to `route_solo`" is **wrong** and following it would build a vacuous instrument.
Date: 2026-09-11

## Context

[The CDCL consolidation plan](../../solver-comparison-2026-09/12-cdcl-consolidation-plan.md)
sequences four phases and puts core tuning last, deliberately:

> **Phase D — core tuning, only after A–C.** *Entry condition, not a date:*
> Phase C has closed and a conflict-count comparison still shows a material gap
> on a family we care about.

Phase C closed on 2026-09-10
([note](../03-measurements/theory-interface-completeness-2026-09-10.md)), so the
first conjunct holds. This ADR settles the second.

The measurement is
[the gate (b) re-run note](../03-measurements/gate-b-rerun-and-phase-d-entry-2026-09-10.md);
the artifact is [`bench-results/sat-core-gate-b-20260910/`](../../../bench-results/sat-core-gate-b-20260910/).

### Why a re-run was required rather than a re-reading

The evidence Phase D was written against is the 2026-09-05 gate (b) sweep that
[ADR-1703](adr-1703-the-native-core-is-the-sat-engine-batsat-is-demoted-to-a-differential-oracle.md)
rests on. That artifact carries its own disqualifying caveat: the host "was
heavily loaded by unrelated lanes throughout" — `load average` 12–33, one spike
to 111 — so *ordering* between engines was reliable and absolute seconds were
not. A decision about whether to spend weeks on core tuning cannot rest on a
table whose own author flagged its numbers as noisy.

Two things also changed since: `cadical` 3.0.1 and `kissat` 4.0.4 are now
installed by `scripts/provision-external-sat-referee.sh` (ADR-1910), and
`gate_b_sweep` was ported off the removed BatSat arm to the native core.

## Decision

**Phase D's entry condition is NOT met. The phase closes unentered.** No core
tuning work is scheduled, and no technique is recommended.

Three pre-registered re-entry conditions replace the open-ended gate (§ below).

## The measurement

Three engines, byte-identical DIMACS, 20 s per instance, `taskset -c 0-7`, one
engine at a time, on a box running nothing else (`ps`: one solver at 100% of
one core; load average **1.01–1.16** across all six engine/family sweeps).

| Engine | p4dfa / 113 | 2026-09-05 | PAR-2 (s) | Noetzli / 100 | 2026-09-05 | PAR-2 (s) |
|---|---:|---:|---:|---:|---:|---:|
| native | **9** | 6 | 37.248 | **87** | 86 | 5.203 |
| CaDiCaL 3.0.1 | **12** | 10 | 36.339 | **89** | 88 | 4.646 |
| Kissat 4.0.4 | **14** | 11 | 35.873 | **90** | 89 | 4.116 |

Controls: variable and clause counts match the 2026-09-05 dumps on **212 of
213** files, so the two runs are on the same formulas (the exception,
`bv-term-small-rw_388`, shrank 3,533 → 213 variables from preprocessing
improvements since). **Zero cross-engine verdict disagreements** over 639
(engine, file) pairs; **54 of 54** `sat` models replayed through
`CnfFormula::evaluate`, external arms included.

**Every engine gained on a quiet box.** That is the first thing the re-run had
to establish and it is why the improvement is not all ours to claim: the
2026-09-05 figures were depressed by contention on *all* columns. Net movement
is that the gap to CaDiCaL narrows from 4 files to 3 and the gap to Kissat is
5 files in both runs.

PAR-2 separates the engines by 0.91 s and 1.38 s out of a 40 s two-timeout
ceiling on p4dfa — **2.3% and 3.7%**.

## Why "not met" — three findings, in order of weight

### 1. The references' extra wins are mid-budget, and the far outlier refutes itself

Bucketing every file a reference decides and the native core does not, by the
*reference's own* wall time (a win at 0.2 s of 20 s and one at 19 s of 20 s are
different claims about what an improvement would have to buy):

| | far (≤ 5 s, ≥ 4x headroom) | mid (5–15 s) | near (> 15 s) |
|---|---:|---:|---:|
| p4dfa, CaDiCaL's 3 extra | **0** | 3 | 0 |
| p4dfa, Kissat's 6 extra | **0** | 4 | 2 |
| Noetzli, CaDiCaL's 2 extra | **0** | 2 | 0 |
| Noetzli, Kissat's 3 extra | **2** | 1 | 0 |

**Two files in 213** are decided with real headroom by a reference and missed
by us. And on one of those two — `bv-term-small-rw_524` — Kissat takes 0.60 s
while **CaDiCaL takes 11.05 s**. An 18x spread between two mature *references*
on one instance is not a technique the loser lacks; it is which way a search
fell. A single file's ratio cannot carry a technique argument, and this file is
the counterexample that proves it.

The relation is not containment either: the native core decides
`compose.p3._bit8_na6_nr3_paired` in 798.6 ms, which Kissat does not decide at
all inside 20 s.

### 2. Most of what we miss, we reach at 5x the budget

Re-running the native core on exactly the files a reference decides and it does
not, at 100 s and 300 s:

| file | native at 100 s | best reference | factor |
|---|---|---:|---:|
| `string1x8.3` | **sat, 23.1 s** | Kissat 5.6 s | 4.2x |
| `videoconf_simple` | **sat, 44.4 s** | Kissat 5.2 s | 8.5x |
| `string1x8.6` | **sat, 50.2 s** | Kissat 7.4 s | 6.8x |
| `string1x8.1` | **sat, 80.1 s** | Kissat 17.6 s | 4.6x |
| `string1x8.4` | unknown at 300 s | Kissat 8.3 s | **> 36x** |
| `tcp_open` | unknown at 300 s | Kissat 18.2 s | **> 16x** |

**Four of six are a 4–9x speed gap; two are beyond a 15x budget.** A 4–9x gap
is not what "material" was meant to license a tuning programme for, and the
residue is two files.

(The 300 s arm reproduces the 100 s wall times to within 1% on all four decided
files — a determinism control on the measurement itself.)

### 3. A reading that looks like a timeout and is not

Two Noetzli rows report `unknown` at a **300 s** budget with `timed_out = false`
and wall times of **194.7 s** and **243.6 s**. They did not run out of time:
they hit `DEFAULT_PROOF_SAT_CONFLICT_LIMIT = 2_000_000`
(`crates/axeyum-cnf/src/proof_sat.rs:50`) and returned `ResourceOut`. On those
rows "unknown at 300 s" means **"> 2,000,000 conflicts"**, and their true
time-to-decide is unmeasured.

Recorded as a finding because the two cases are indistinguishable in the verdict
column and one of them overstates the gap.

**The cap does not explain the gate result.** At the 20 s budget, **all 117**
undecided native results across both families carry `timed_out = true`; the cap
is reached on zero of them. It binds only above roughly 195 s — 10x the budget
gate (b) measures at.

## What this ADR deliberately does NOT do

**It recommends no technique.** Phase D named vivification, chronological
backtracking and mode-switching defaults as candidates. Since the entry
condition is not met, none is scheduled, and this ADR does not rank them.

That restraint is the Phase C correction applied: *a conflict-count ratio is a
diagnosis of cause, not a prediction of value.* On QF_IDL, lifting a
propagation cap cut conflicts 1.5–8.1x **and took the division from 8 of 9
decided to 6 of 9**. Any future Phase D must therefore be argued on files
decided, never on conflicts reduced — which is what the re-entry conditions
below require.

## Re-entry conditions

Phase D reopens if any one of these becomes true, and not otherwise:

1. A reference decides **three or more** files in one family with ≥ 4x budget
   headroom that the native core misses, on a quiet box, **with both references
   agreeing within 4x on each such file** — so that a single lucky trajectory
   (finding 1) cannot trigger it.
2. One of the three open Phase C cells is measured and shows a conflict-count
   gap **whose closure is then shown to decide more files**, not merely to
   reduce conflicts.
3. The PAR-2 separation on a family we care about exceeds **10%** of the
   two-timeout ceiling. It is 2.3–3.7% today.

## Consequences

- The plan's ordering claim survives its own test. §2 of the plan argued G4
  (core behind the references) "is the one that looks like the problem and is
  the least valuable to attack first". Measured on a quiet box, that is right.
- **ADR-1703 is not disturbed.** Its gate (b) verdict — a real but modest and
  family-dependent gap — reproduces; the native core remains the SAT engine.
- The 2026-09-05 artifact keeps its numbers. It is a recorded measurement of
  that day and is not edited; this is a second measurement beside it.
- **A stale claim is flagged, not fixed here.** The Phase C note says closing
  the QF_SLIA cell is "a one-entry change" to `route_solo`'s table. It is not:
  `route_solo`'s `Route.run` signature is
  `fn(&mut TermArena, &[TermId], &SolverConfig)` and receives
  `script.assertions`, while the online string route the front door runs
  consumes `Script::word_skeleton` — a separate parallel `Seq`-level view
  (`crates/axeyum-smtlib/src/parse.rs:244`) populated all-or-nothing and empty
  whenever any atom uses `str.len`, `substr`, regex or an extended function.
  A naive entry would measure the raw-assertion decline, producing an empty
  result indistinguishable from a strong negative. The cheap honest census is
  `proof_gap_shape_census`'s existing `word_skeleton_terms` field; **that census
  did not run in this lane.**
- One bias is left uncorrected and runs in the references' favour, so every
  reference advantage above is a lower bound: the native arm starts its clock
  after parsing the DIMACS and an external binary pays parse inside its budget.
  Measured rather than assumed — Kissat's own profiler puts `parse` at **0.04 s,
  1.31%** of a 3.02 s run on the 7.2 MB `compose.s2` DIMACS.
