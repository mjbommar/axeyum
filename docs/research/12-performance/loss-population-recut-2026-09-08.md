# The loss population, re-cut — and the mechanism that stops the next one going stale

Lane `recut-and-clamp`, 2026-09-08. Two jobs. The first was to re-cut the loss
lists every optimisation brief in this repository is written against. The second
was to clamp `dispatch_abv_online`, and **it was already done** — the honest
report of that half is a verification, not a change, and the finding is how the
brief came to name work that had landed.

## 1. Why the re-cut

`bench-results/parity-losses-20260905/<DIV>.txt` is the population a brief means
by "the N files we lose in `<DIV>`". Measured by the `parallel-portfolio` lane
and re-measured here, a large fraction of those 403 files were already decided
by the shipped default. Every lane pointed at those lists was partly pointed at
files the tree wins.

Nothing was wrong with the lists. They were a correct measurement of 2026-09-05,
in a directory whose name says so, and every reader — including the people who
cut them — treated them as current anyway. **A date in a path is a fact a reader
has to decide to act on, and readers reliably do not.**

## 2. The numbers

**480 → 318.** 157 of the files on the 2026-09-05 and 2026-09-06 lists are
already decided by the shipped default, and 5 more are flaky.

| division | 2026-09-05/06 | **2026-09-08** | recovered | flaky |
|---|---:|---:|---:|---:|
| QF_ABV | 19 | **12** | 7 | 0 |
| QF_BV | 6 | **6** | 0 | 0 |
| QF_IDL | 54 | **19** | 35 | 0 |
| QF_LIA | 27 | **22** | 3 | 2 |
| QF_LRA | 54 | **49** | 5 | 0 |
| QF_NIA | 61 | **58** | 3 | 0 |
| QF_NRA | 77 | **75** | 1 | 1 |
| QF_RDL | 47 | **9** | 38 | 0 |
| QF_SLIA | 7 | **7** | 0 | 0 |
| QF_UF | 38 | **6** | 30 | 2 |
| QF_UFLIA | 58 | **23** | 35 | 0 |
| UF | 32 | **32** | 0 | 0 |
| **total** | **480** | **318** | **157** | **5** |

The brief this lane worked from said "141 of 403". On the same 403 (that is,
excluding the QF_NRA set) this sweep finds **156 recovered plus 4 flaky** — the
number moved again in the day between the two measurements, which is the point
rather than a correction.

**Three divisions carry the whole result.** QF_RDL (47 → 9), QF_UF (38 → 6) and
QF_IDL (54 → 19) account for 103 of the 157 recoveries; QF_UFLIA adds 35 more.
Four divisions did not move at all — QF_BV, UF, QF_SLIA, and (by one file)
QF_NRA. A brief aimed at those four is aimed at the same population it always
was; a brief aimed at QF_RDL was aimed at a list five times longer than the
truth.

## 3. What is actually stale, and it is not only the lists

`bench-results/PARITY.md` is the ledger, and it is *fresher* than the lists —
QF_UFLIA, QF_LIA and QF_LRA all carry entries from 2026-09-08. That did not help,
for two reasons worth separating.

**The ledger is behind the tree.** The newest entry of any division was measured
at `f24c61f91`, and there are **72 commits touching `crates/` between that and
HEAD**, including the two that move the most files. So even a same-day ledger
entry can be a measurement of a tree nobody is running.

**One of those entries is measurably wrong about today.** The QF_UFLIA entry of
`2026-09-08T20:27:12Z` records **129/200**. `git merge-base --is-ancestor
26d9d80e3 f24c61f91` fails: the parity run does **not** contain the
interface-caps change, which the `uflia-interface-caps` lane measured at
**151/200** on the same committed 200-file list the same day. Two numbers for
one division on one day, twenty-two files apart, both correctly recorded, and
nothing in either artifact says which tree it describes.

This is exactly the failure `check-parity-freshness.py`'s header warns about —
"an entry stamped with today's date carrying the pre-fix number would be
fresher-looking and more wrong" — and it is live in the tree, not hypothetical.
The handle is the `behind=` line, which is why the new gate prints it too.

## 4. The mechanism: `scripts/check-loss-list-freshness.py`

A dated directory is not a staleness signal, so the gate makes it one. It does
not re-measure; it reads committed files and answers the question a brief-writer
has: **which set do I cite for this division?**

It fails on:

- a set no longer authoritative for one of its divisions whose `README.md`
  carries no `SUPERSEDED-BY:` line — the guard that cannot rot, because the
  moment a lane cuts a new set the gate is red until the old one is marked, and
  the mark lands in the file a reader opens;
- a `SUPERSEDED-BY:` naming nothing, or naming itself;
- a division past a 14-day budget (warning at 10), matching
  `check-parity-freshness.py` and for the reason argued there;
- a missing or incomplete `MANIFEST.json` — without the solver commit, "was fix
  X in this measurement?" is a memory question again;
- an empty scan, because a scan that stopped matching its subject returns the
  same answer as a clean tree.

### Authority is per DIVISION, not per directory

The first version of this gate treated the newest *directory* as the authority.
It was wrong on its first run: `parity-losses-20260906` is a QF_NRA-only census,
an **addition** beside the eleven-division 2026-09-05 set, and a per-set rule
demanded those eleven declare themselves superseded by a sweep that never
measured them. `addition-is-not-supersession` is now a control.

### `behind=` is reported and never fatal

For the three reasons `check-parity-freshness.py` sets out and this gate does not
restate: velocity here is bursty so any fixed ceiling is red-by-construction
during a burst; non-ancestry is legitimate because lanes measure from their own
worktrees; and a sha can vanish from a shared checkout. It is worth having
anyway — the 2026-09-05 set reads **`behind=606`**, which is the number that
would have warned every lane briefed against it.

### The controls

Fifteen cases, twelve guard mutations, all twelve killed; nine kill exactly one
case. The table in the suite's header was **recorded** from
`scripts/tests/loss_list_freshness_mutations.py`, not predicted — and two
predictions were wrong. Emptying `REQUIRED_MANIFEST_FIELDS` does **not** kill
`no-manifest`, because that branch returns before the field list is read, so the
two guards are independent; and the mutation that collapses per-division
authority killed the real-tree case as well.

**Then the tree changed under the table, which is itself the finding.** On the
first run this repository held two loss-list sets, one of them an unmarked
QF_NRA-only addition, and `real-tree` died under both the authority-collapse
and the `DIVISION_RE` mutations. After the re-cut landed — a third set that is
the authority for every division, with both older sets marked — neither
mutation moves `real-tree` any more: with one set on top of everything, "newest
set wins" and "newest set per division" agree.

So `real-tree` is coverage, not a guard, and its sensitivity is a property of
the tree rather than of the checker. It stays, because a fixture-only suite
would remain green if the shipped directories drifted away from what the parser
reads — but it must not be counted as evidence that those two guards are
tested. Their fixtures are. The suite's header now says so.

## 5. Method, and the two ways it can lie

The sweep is byte-identical to the SCORED path of `scripts/parity-run.sh`,
including its 29 s external `timeout`, so a verdict here is comparable to the
census it replaces and reproduces the *shipped* scoring rather than a stricter
one. Whether a file needed the watchdog's grace is a separate `over_budget`
column.

**Pass 1 alone over-counts losses.** A 24 s budget is a wall clock, s4 carried
other lanes throughout (load 11.5 → 27), and a file that misses the budget under
contention may decide on an idle box. So a **confirm** pass re-runs only what
pass 1 left `unsolved`. It is one-sided by construction: it can move a file OFF
the loss list and never onto it, which makes the loss list an upper bound
refined downward and the "already decided" count a lower bound.

**Re-running the old list cannot find new losses.** It answers "which files we
lost do we now win?" and is structurally incapable of the converse. So a
**complement** pass runs the division's parity list minus the 2026-09-05
population.

### The complement pass has no oracle, and the obvious substitute is wrong

Only z3 is installed on s4; these divisions score against cvc5, bitwuzla and
yices. The tempting substitute is the benchmark's own `(set-info :status …)`,
and it does not work: SMT-LIB carries a curated status whether or not any
competition solver decides the file. In the QF_LRA complement, **52 of the 54
unsolved files declare `sat` or `unsat`** — and the ledger's own arithmetic puts
all 49 of that division's reference-only losses on the OLD list, so those 52 are
the division's `neither` set, not losses.

(Commit `21ef9b1a4`'s message quotes this as "37 of 39", which was the count when
QF_LRA's complement pass was two thirds through. 52 of 54 is the finished run.
The conclusion is the same and got stronger; the number is corrected here
because a commit message cannot be.)

What the complement pass can honestly do is reconcile at the count level: the
old-list survivors plus the complement's unsolved files should equal the
ledger's `reference-only` plus `neither`. Where it does, the loss list is exactly
the old-list survivors. Where it does not, the residual is reported.

## 6. What the reconciliation says

`bench-results/parity-losses-20260908/scripts/reconcile.py`, joining the re-cut
to the ledger. `residual = (old-list survivors + complement unsolved) −
(reference-only + neither)`; negative means we decide MORE than the entry
implies, which is the expected direction when the tree has moved.

| division | re-cut | comp unsolved | sum | ledger r-only + neither | residual | ledger entry | behind |
|---|---:|---:|---:|---:|---:|---|---:|
| QF_ABV | 12 | 2 | 14 | 21 | **−7** | 2026-09-05T21:59 | 607 |
| QF_BV | 6 | 8 | 14 | 12 | **+2** | 2026-09-05T21:14 | 607 |
| QF_IDL | 19 | 76 | 95 | 95 | **0** | 2026-09-06T22:21 | 247 |
| QF_LIA | 22 | 60 | 82 | 81 | **+1** | 2026-09-08T20:50 | 73 |
| QF_LRA | 49 | 54 | 103 | 103 | **0** | 2026-09-08T20:39 | 73 |
| QF_NIA | 58 | 101 | 159 | 161 | −2 | 2026-09-06T00:51 | 607 |
| QF_NRA | 75 | 13 | 88 | 90 | −2 | 2026-09-07T01:33 | 218 |
| QF_RDL | 9 | 47 | 56 | 58 | −2 | 2026-09-06T23:10 | 247 |
| QF_SLIA | 7 | 0 | 7 | 7 | **0** | 2026-09-06T01:04 | 607 |
| QF_UF | 6 | 1 | 7 | 4 | **+3** | 2026-09-06T21:10 | 247 |
| QF_UFLIA | 23 | 26 | 49 | 71 | **−22** | 2026-09-08T20:27 | 73 |
| UF | 32 | 84 | 116 | 115 | **+1** | 2026-09-06T22:35 | 247 |

**Three divisions reconcile to zero** (QF_IDL, QF_LRA, QF_SLIA) and four to
within two files. On those, the loss list is exactly the old-list survivors and
the complement's unsolved files are the division's `neither` set — which is also
why the declared-`:status` heuristic would have been wrong about 52 of QF_LRA's
54.

**Two independent reproductions fall out of it.** QF_ABV lands on 14 unsolved of
200, i.e. 186 decided — the `ladder-budget` lane's number. QF_UFLIA lands on 49
unsolved of 200, i.e. **151 decided** — the `uflia-interface-caps` lane's
number, which `PARITY.md`'s own same-day entry does not have, for the reason in
§3.

### Four divisions decide FEWER files than their ledger entry implies

QF_UF **+3**, QF_BV **+2**, QF_LIA **+1**, UF **+1**. Each survived a
`comp-confirm` pass — a second run of the complement's unsolved files, which by
construction can only move the residual toward the ledger — so this sweep's
contention does not explain them.

How big a superset the residual sits in is what decides whether it is
actionable, and it varies by two orders of magnitude:

- **QF_UF: 3 files in a superset of 7.** That division's ledger entry has
  `neither = 0`, so *every* file we do not decide is one the reference does. One
  of the three can be named exactly, because it is not on the 2026-09-05 list at
  all and therefore sat in the ledger's `both` column:
  `QF_UF/QG-classification/qg7/iso_brn_repgen041.smt2`, declared `sat`, timing
  out at 24.2 s in both passes. It is
  `QF_UF.regression-candidates.txt`. The other two are among the six old-list
  survivors and cannot be separated without the reference.
- **QF_BV: 2 files in a superset of 8** (`QF_BV.regression-candidates.txt`); the
  ledger's `neither = 6` accounts for the rest.
- **QF_LIA: 1 in 60. UF: 1 in 84.** No candidate list is emitted for these —
  a "regression candidates" file that is 98% `neither` would be a worse artifact
  than none, and naming it that would be the same over-claim the
  declared-`:status` heuristic makes.

None of these is a confirmed regression. Confirming one needs the division's
reference re-run on the named files, which s4 cannot do — and each ledger entry
it is measured against records its own load average of 1–3 against this sweep's
11–27, so a single-file residual is inside the noise the comparison carries.
The QF_UF row is the one worth acting on.

## 7. `over_budget`: closed on the loss population, open in QF_SLIA

Across the 803 runs of the sweep and confirm passes over the 2026-09-05/06
population: 162 decided, **0 decided past the budget**, 377 unsolved past it.
Not one newly recovered file needed the watchdog's grace period to be counted.
The recoveries are wins inside the budget, which is what survives a hard
external limit, and the grace-dependent class the portfolio lane found in
QF_ABV is closed there.

The **complement** passes are not clean, and the exception is worth naming
because it is the same shape in a different division. Of 1,989 complement runs,
**four** are decided past the budget — all four QF_SLIA, all four in
`20180523-Reynolds/pyex/…/httplib2-entry-disposition/`, at 24,240–25,055 ms
wall. They are `QF_SLIA.grace-wins.txt`. Under a hard external 24 s limit they
are four losses.

**And the route trail cannot say where the time went.** Re-run with `--trace`,
three of the four reproduce, and their trails read:

| file | wall | `bound_by` | `bound_ms` | `total_ms` | `decided_by` |
|---|---:|---|---:|---:|---|
| `…57dd17639` | 24,336 | `fd:parse` | 70 | **158** | `int-blast-ladder` |
| `…ace22aa8a` | 24,339 | `fd:parse` | 75 | **166** | `int-blast-ladder` |
| `…769a661db` | 24,240 | `dl-online` | 18 | **47** | `int-blast-ladder` |

24.1 seconds of a 24.3 second run is attributed to no route attempt at all. It
is not I/O — the files are 49 KB. This is the prefix-sum caveat the
[span-log sweep](ladder-budget-discipline-2026-09-08.md) records ("a route that
never returns leaves its budget on whichever attempt is recorded next, or on no
attempt at all") in its worst form: on this shape the trail accounts for 0.7% of
the wall clock. **Do not attribute QF_SLIA cost from the route trail** until
that is fixed; the fourth file (`…eeaeeba27`) came back at 18.8 s on the
re-run, so it is flaky rather than grace-dependent.

## 8. `dispatch_abv_online` was already clamped — verified, not assumed

The brief asked for a clamp on the one dispatch site passing `config` through
unmodified, and named nine QF_ABV files that are wins only because
`WATCHDOG_GRACE` is 1 s. That change had **already landed** on local `main`
(`3399c0f8b`, lane `budget-discipline`) as
`ABV_ONLINE_LADDER_RESERVE_SHARE = 4` through `LadderSlice::all_but_reserve`.
It was not on `origin/main` when the brief was written, which is the ordinary
lag of a shared push window — the general lesson being the one already in this
repository's notes: **verify a task still exists before doing it, the same way
you verify a blocker still exists before treating it as one.**

So this lane measured it instead. Ten files (the nine named, plus a tenth the
name-matching pulled in), both arms of `AXEYUM_ABV_ONLINE_RESERVE`, one pinned
core per arm, `--trace` read for `bound_ms` / `total_ms`:

| | `off` (historical) | `on` (shipped) |
|---|---|---|
| decided | 9 of 10 | 9 of 10, **same verdicts** |
| `total_ms` range on the nine | **24,031 – 24,333** | **18,027 – 18,339** |
| decided **inside** the 24,000 ms budget | **0 of 9** | **9 of 9** |
| bound by | `abv-online-cdclt` at 24.00 s | `abv-online-cdclt` at 18.01 s |
| decided by | `array-fast-path` | `array-fast-path` |

The `off` arm reproduces the brief's signature exactly (`bound_ms=24003
total_ms=24031` against the reported `24009 / 24029`). **The defect was live and
is now fixed**; nine files that counted as wins only because the harness kills at
29 s are decided at 18 s, which is what survives a hard external limit.

The tenth file, `try5_small_difret_functions_dwp_cat.next_line_num.il.dwp.smt2`,
is `unsolved` in **both** arms at ~3 s, bound by `array-fast-path` — it gives up
early rather than timing out, and it is not a regression: it is already on the
2026-09-05 QF_ABV loss list.

`abv-watchdog-blind.txt` and `abv-reserve-ab.tsv` in
`bench-results/parity-losses-20260908/` are the population and the per-file
data.

The same class is checked across the whole re-cut population in §7.
