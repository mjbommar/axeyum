# ADR-1945: a blocked count is not a reachable count, and two sequential caps are not two caps

Status: accepted
Index-summary: Split `ufbv_online`'s atom cap by path — 4_096 on the scalar path, 1_024 kept for arrays — and hold `MAX_INPUT_DAG_NODES` at 16_384 everywhere; measured at +40 QF_UFBV files with 0 of 400 array files changing verdict. A census attributing N files to a cap is an upper bound on what raising it buys: when caps are SEQUENTIAL GATES the count attributed to the earlier one is not reachable through it at all (the node cap bought 0 of its 31 at 2x, 4x and 16x), and a cap shared with another division may be the guard in front of that division's open bug.
Index-status: accepted
Date: 2026-09-13

## Context

The [QF_UFBV blocker
census](../../../bench-results/fpbv-divisions-headtohead-20260912/README.md)
attributed **84 of 87 winnable files** to two literals on adjacent lines of
`crates/axeyum-solver/src/ufbv_online.rs`:

    const MAX_INPUT_DAG_NODES: u64 = 16_384;   // 31 files, 1.00x-14.04x over
    const MAX_THEORY_ATOMS: usize = 1_024;     // 53 files, 1.04x- 5.33x over

The lane that measured that refused to raise them, and its reason was right:
**a cap turns a slow `unknown` into a fast `unknown`.** Removing it does not
make a query decidable — it makes us spend the budget finding that out. The 2
rows in that census that were real budget exhaustion were the warning.

This ADR records what the A/B found, and the two things it found that were not
about these constants at all.

## The measurement

**9,793 axeyum runs** over seven populations, plus 98 reference runs;
`count-runs.py` derives both from the artifacts rather than from arithmetic on
what the sweeps were supposed to have done.

The core sweep is 1,800 of them: the pinned 200-file `QF_UFBV` division at nine
cap settings, 24 s wall and 8 GiB address space, **every arm on one file back to back on one pinned
physical core before any arm starts the next file, with the arm order rotating
by file index**. Six shards, two per box on distinct physical cores of s5/s6/s7.
Plus **800 already-decided control files** from four divisions `ufbv_online`
also serves, at six settings. Full protocol, runners and derivations:
[`bench-results/ufbv-caps-ab-20260912/`](../../../bench-results/ufbv-caps-ab-20260912/README.md).

**The baseline arm decides 89 of 200 — the board row exactly.** A sweep whose
control arm does not reproduce the number it is compared against is measuring
something else.

| cap raised | value | decided of 200 | gain | loss | wall |
|---|---|---:|---:|---:|---:|
| — (baseline) | 1_024 / 16_384 | **89** | — | — | 472.6 s |
| atoms | 2_048 | 120 | +31 | 0 | 776.3 s (1.64x) |
| atoms | 4_096 | 133 | **+44** | 0 | 1070.3 s (2.26x) |
| atoms | 8_192 | 134 | +45 | 0 | 1190.5 s (2.52x) |
| nodes | 32_768 | 89 | **+0** | 0 | 519.9 s (1.10x) |
| nodes | 65_536 | 89 | **+0** | 0 | 520.6 s (1.10x) |
| nodes | 262_144 | 89 | **+0** | 0 | 519.6 s (1.10x) |
| both | 4_096 / 65_536 | 137 | +48 | 0 | 1167.4 s (2.47x) |
| both | 8_192 / 262_144 | 138 | +49 | 0 | 1650.6 s (3.49x) |

## Finding 1: 84 blocked, 49 reachable

**49 of the 87 winnable files decide. 35 do not.** The census named a failure
mode, not a set of fixable files, and the two differ every time anyone measures
both. The nearest comparison is the same date, in the same style, on the same
pinned lists:
[the constructor-argument slice is 10 of 173](../03-measurements/the-constructor-arg-slice-is-10-of-173-files-2026-09-12.md).
Here it is 49 of 84.

The 35 are not hypothetical: with both caps at their most generous, the give-up
histogram over the 111 files the baseline leaves undecided reads

     49  DECIDED
     21  Timeout: preprocessed dispatch timeout after reduced solve
     17  ResourceLimit: online UFBV has N semantic atoms, exceeding the cap of 8192
     12  Timeout: online UFBV canonical CdclT search exhausted its budget
      5  Watchdog / 3 Boolean-variable cap / 2 interface cap / 1 node / 1 ingest

**33 of the 35 non-gainers are now clock-bound**, where the census found 2 of
87 were. That is the previous lane's prediction, measured: a fast `unknown`
became a slow one. It is the *price* of the 49 rather than an argument against
them, and it is why the wall column above belongs beside the gain column.

**17 files still exceed 8_192 atoms.** The census measured 1.04x-5.33x over
1_024, max 5,458 — but it could only measure files that *reached* the atom
check. Once the node cap admits the 39 node-blocked files, they bring atom
counts past 8,192. **A census's over-cap magnitudes are a lower bound on the
population, not a description of it**, whenever an earlier gate hides part of
that population from the measurement.

## Finding 2: two sequential caps are not two caps

**The node cap is worth exactly zero on its own, at 2x, 4x and 16x.** Not a
small gain — not one file, at any value, on 31 files the census attributed to
it.

The mechanism is visible in the histogram and is not a coincidence. The caps are
**sequential gates on one path**: `admit_input` rejects an over-budget DAG
before `build_theory_atoms` ever runs, so a file over the node cap has never had
its atom count measured. Raising the node cap does not decide it; it hands it to
the atom cap. Over the 111 undecided files:

    arm        node-blocked   atom-blocked
    base                 39             64
    n32768               17             84
    n65536                9             92
    n262144               1            100

Every file the node raise admits reappears, undecided, one gate later.

On top of `atoms = 4_096` the node raise does finally buy **4 files** — and
three were over the node cap by **1.00x-1.07x** (16,437 / 16,588 / 17,509
against 16,384). The 14x tail the census measured, the number that made the node
cap look like the bigger problem, bought nothing at all.

The general rule, which is the part of this ADR that outlives these two
constants: **when a census attributes files to a cap, ask what the file would
have hit next.** An attribution to gate *k* is only a reachable-fix count if
gates *k+1 … n* are known to admit it. Otherwise the census has measured where
the dispatch stopped, which is a fact about ORDER as much as about the value.

## Finding 3: both caps also guard a DIFFERENT division's open bug

`ufbv_online` is not QF_UFBV's alone. `admit_input` is the admission gate for
`abv-online-cdclt`, the first route every array query tries, and
`build_theory_atoms` serves both paths. So the control population is **800 files
we already decide** — QF_BV, QF_UFLIA, QF_ABVFP and QF_ABV — and **every arm
loses something**:

| arm | decided of 800 | loss |
|---|---:|---:|
| base | 711 | — |
| atoms 4_096 | 709 | 2 |
| nodes 65_536 / 262_144 | 709 | 2 |
| both 4_096 / 65_536 | 707 | 4 |
| both 8_192 / 262_144 | 708 | 3 |

All four losses are on the **array** path, and re-running each nine times per
arm on an idle box separates them completely:

| file | base | atoms 4_096 | nodes 65_536 |
|---|---|---|---|
| `QF_ABV/…/try3_sameret…` | 9/9 @ 4.5 s | **6/9 @ 22.5 s** | 9/9 @ 4.5 s |
| `QF_ABV/…/try5_small_noof…` | 9/9 @ 5.3 s | **5/9 @ 23.3 s** | 9/9 @ 5.3 s |
| `QF_ABVFP/…/query.435` | 9/9 @ 0.6 s | 9/9 @ 0.6 s | **0/9 @ 25.0 s** |
| `QF_ABVFP/…/query.708` | 9/9 @ 0.4 s | 9/9 @ 0.4 s | **0/9 @ 25.0 s** |

The node raise turns a **0.4-0.6 s `array-fast-path` verdict into a 25 s
`Watchdog`, zero times out of nine**. That is not a budget edge and not noise;
it is a 40x blow-up into `abv-online-cdclt`, the route the QF_ABVFP census
measured completing **zero CEGAR rounds at a 600 s budget**. The atom raise
costs the two QF_ABV files 18 seconds by the same mechanism, deterministically,
whether or not the verdict survives on a given box.

So on the array path these constants are not tuning knobs. They are **the guard
currently standing in front of an open defect**, and the A/B found that out by
running a control population rather than by reading the diff. A cap that was
never justified for the reason it is now load-bearing is still load-bearing.

**The control had to be checked for vacuity separately, and half of it was
vacuous.** `--trace`'s `route-trail` names every attempted route:
`ufbv_online` runs on **344 of the 800** control files and a cap actually fires
on **35** — but on **0 of 400** QF_BV and QF_UFLIA files, which never enter this
route at all. A zero-loss result over a population that cannot reach the cap is
not evidence of safety. `decided_by`/`bound_by` cannot answer this question: a
route that declines in 1 ms is neither, and the final give-up line belongs to
whichever route ran last.

## Decision

**Split the atom cap by path. Raise the scalar one; hold everything else.**

    const MAX_THEORY_ATOMS:        usize = 1_024;   // array path, UNCHANGED
    const MAX_SCALAR_THEORY_ATOMS: usize = 4_096;   // scalar path, NEW
    const MAX_INPUT_DAG_NODES:     u64   = 16_384;  // both paths, UNCHANGED

`theory_atom_cap(admit_arrays)` chooses, and both comparison sites read it —
the static pre-check directly, the dynamic retained-search check from the value
the static check admitted the query under, so a cap cannot disagree with itself
mid-search and decline a query it had already accepted. `admit_arrays` is
`false` for `check_qf_ufbv_online_cdclt` and `true` for
`check_qf_aufbv_online_cdclt`, and is carried on `PreparedAbstraction` so
everything reading the abstraction reads the same answer.

4_096 rather than 8_192 because that is where the curve flattens: +44 against
+45, for 11 % less wall, and 8_192 is the setting under which 17 files reappear
at the atom cap — the population above it is not small, so the next raise would
be asked for too.

Both caps stay levers (`AXEYUM_UFBV_MAX_THEORY_ATOMS`,
`AXEYUM_UFBV_MAX_SCALAR_THEORY_ATOMS`, `AXEYUM_UFBV_MAX_INPUT_DAG_NODES`), so
the next lane re-runs this without a rebuild.

### Measured as shipped, not argued from the diff

One binary, nothing set, against the same binary with
`AXEYUM_UFBV_MAX_SCALAR_THEORY_ATOMS=1024`:

| division | files | pre-ADR | shipped | gain | loss |
|---|---:|---:|---:|---:|---:|
| QF_UFBV | 200 | 89 | **129** | **+40** | **0** |
| QF_ABV | 200 | 186 | 186 | 0 | 0 |
| QF_ABVFP | 200 | 179 | 179 | 0 | 0 |

**0 of the 400 array files differ in verdict**, and their wall totals move by
under 1 %. `QF_ABVFP` at 179 of 200 reproduces its board row exactly.

All 49 files any arm newly decided were re-run against z3 4.13.3, cvc5 1.3.4 and
the declared `:status`: **43 decided at the shipped setting, 0 disagreements**,
43/43 against `:status`, 40/40 against each reference, and **3 files we decide
that neither reference does**. 0 of our runs were wrapper-killed.

**The division goes from 89 to 129 of 200 against z3's 174** — the gap closes
from 85 files to 45 — at 2.23x the division's wall.

## Consequences

**A second number now has to be quoted with the first.** 12 of the 49 gains land
at 15-24 s of a 24 s budget, so the sweep was repeated on a deliberately loaded
box: the atoms-only gain is **+44 on a lightly loaded frame and +33 on a heavily
loaded one**. Both are the result. Quoting +44 alone overstates it and +33 alone
understates it, and a single number for a budget-edge population is exactly what
this repository's frontier-ratchet note warns against. `monotone.py` gives the
same answer without a second run: along every cap ladder, **1 file of 200** is
decided at a lower value and not at a higher one.

**`abv-online-cdclt`'s non-progress is now blocking coverage in two divisions,
not one.** QF_ABVFP's census named it; this lane shows the same route is why the
QF_UFBV node cap cannot be raised and why the array atom cap cannot. Fixing it
would unblock roughly 4 more QF_UFBV files here and 16 on QF_ABVFP, and until it
is fixed `MAX_INPUT_DAG_NODES` should be treated as a guard rather than a knob —
including by anyone who reads the census and sees 31 files behind one constant.

**The next QF_UFBV rung is not these caps.** At the shipped setting the
remaining undecided files are dominated by `preprocessed dispatch timeout` and
`canonical CdclT search exhausted its budget`, with `MAX_BOOLEAN_VARIABLES =
8_192` and `MAX_INTERFACE_ATOMS = 512` appearing behind them. That is a search
problem and a different ladder, and raising the atom cap further would only move
files onto it.

**Two registry entries and one new one are now dated** against this measurement,
so `check-config-registry-staleness.py` will flag them if the code they rest on
moves again. `MAX_INPUT_DAG_NODES`'s previous date rested on a 2026-09-08 note
that this lane's own lever commit invalidated — the gate caught that within the
hour, which is the gate working.

## Alternatives considered

**Raise both to their most generous tested values (8_192 / 262_144).** Buys one
file more than 4_096 / 65_536 for 41 % more wall on the division, and it is the
setting under which 17 files reappear at the atom cap — evidence that the
population above 8_192 is not small, so the next raise would be asked for too.
Rejected as the wrong end of a flattening curve.

**Raise the atom cap globally, accepting 2 losses for +44.** Net +42 across
1,000 files, and it was the obvious reading until the losses were replicated:
both are on the array path, both are the same 18-second regression into
`abv-online-cdclt`, and both are avoidable for free by splitting the constant.
Paying a known cost when the split costs one `bool` is not a trade, it is an
oversight.

**Raise nothing, and keep the levers as a measurement surface.** This is what
[ADR-1921](adr-1921-the-int-blast-width-escalation-is-measured-and-not-shipped.md)
did for the width ladder, and it would be right if the gains were marginal or
the shipped setting cost anything. Neither holds: +40 measured as shipped, with
0 of 400 array files changing verdict. Declining a measured, loss-free +40
because the shape of the finding resembles a previous null would be
cargo-culting a conclusion rather than reading one.

**Delete the caps.** Not measured, and the 33 clock-bound non-gainers say what
would happen: the division's wall would keep climbing for files that do not
decide. A cap that converts a slow `unknown` into a fast one is doing real work
for every query it turns away that would not have been decided anyway; this
measurement shows where that trade stops being worth it, not that it was never
worth anything.
