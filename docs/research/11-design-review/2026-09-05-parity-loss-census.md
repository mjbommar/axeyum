# Parity loss census, all eleven divisions, 2026-09-05/06 (S3)

> ## CORRECTION, 2026-09-06 — read this before using the `class` column
>
> **This census's `class` column was measured wrong on at least 67 of 70 files
> in two divisions, and the method that produced it is retired.** Two defects,
> both confirmed by re-measurement (lane S11a,
> [status](../../plan/status/s11a-uf-ackermann-cap.md)):
>
> 1. **The class is the LAST route's message, not the route that spent the
>    budget.** On 35 QF_UF files `euf-online` is entered first and consumes
>    23.5 s of a 24 s budget; the eager-Ackermann decline that named the class
>    is a 0.3–15 ms tail *after the budget is already gone*. Raising the cap
>    that class names could have moved at most 3 files, not 70.
> 2. **`explain_corpus` is not the front door.** It runs `check_auto_explained`
>    on the flat assertion view rather than `solve_smtlib`, and is measured to
>    disagree with the shipped front door on **134 of 397** committed
>    benchmarks. All 32 UF rows are an artifact of that difference.
>
> Independently, S1's watched literals then moved QF_UF from 162 to 190 —
> so this note's conclusion that "neither division has a single search-timeout
> file; 2.1's fix lands nothing here" was **false in both halves**.
>
> **What is still good here:** the per-file populations (the `<DIV>.txt` lists),
> the wall times, and the `smtcomp_cli` verdicts. **What is not:** every
> `class` and `last_route` value, in every division, until a front-door
> re-measurement confirms it. Divisions confirmed since: QF_IDL, QF_RDL,
> QF_LRA and QF_UFLIA by the slices that acted on them, and **UF, whose classes
> were re-derived through the front door on 2026-09-06** — re-derived and
> **superseded**, not confirmed: all 32 rows were wrong, and the replacement is
> [the UF front-door census](2026-09-06-uf-front-door-census.md). **QF_ABV was
> re-derived through the front door on 2026-09-08 and is likewise superseded,
> not confirmed** — five of its nineteen files are decided by the current tree,
> and of the fourteen that are not, the route that spent the budget is one the
> trail could not name because it never returned; the replacement is
> [the QF_ABV route attribution](../12-performance/qf-abv-route-attribution-2026-09-08.md).
> Divisions **not** confirmed: QF_LIA, QF_SLIA, QF_BV, QF_NIA.
>
> The general shape, worth carrying beyond this file: **a diagnostic tool with
> partial coverage does not merely fail to find things — it manufactures
> confident false positives in every artifact built on top of it.** The fixed
> method is in the [parity plan](../../plan/smt-parity-plan-2026-09-05.md) §6.
>
> ### Maintaining this block, so it does not become the next frozen wrong thing
>
> The confirmed/not-confirmed lists above **move**, and a correction block whose
> contents go stale is the same defect it was written to fix. So:
>
> - **When a slice re-measures a division through the front door**, move that
>   division from the not-confirmed list to the confirmed list *in the same
>   commit as the slice*. Do not batch it.
> - **A division is "confirmed" only if a front-door measurement re-derived its
>   classes** — not if a slice merely moved its count. A count moving is
>   evidence the lever worked, not evidence the class was right.
> - **Retire this whole block** when the not-confirmed list is empty AND the
>   `class` column has been regenerated through the front door. At that point
>   delete it rather than editing it to say "historical"; the git history keeps
>   what happened.
> - **This block is permanent until then.** Unlike a coverage gap, which stops
>   producing false positives the moment coverage lands, these are frozen
>   measurements: nothing about them improves on its own, so no expiry date
>   applies and none should be written here.
>
> Known to be moving as of 2026-09-06: QF_NRA is being censused through the
> front door as a new division and is not in either list because it is not part
> of this census. (The UF front-door census landed; see the confirmed list.)

Status: **measurement only**. This is the S3 slice of
[`docs/plan/smt-parity-plan-2026-09-05.md`](../../plan/smt-parity-plan-2026-09-05.md):
every reference-only file (reference `sat`/`unsat`, axeyum `unsolved`) across
all eleven divisions, run through `smtcomp_cli --timeout-ms 24000 --trace`
and `explain_corpus --json --timed-trace` at solver commit `9914a1c0e`,
`taskset -c 0-7` on the idle hosts s5/s6/s7, classified into one of
`search-timeout`, `admission-decline(<constant>)`,
`route-decline(unsupported:<shape>)`, `parser-reject(<reason>)`,
`dispatch-overrun`, `other(<text>)` per the plan's §2 rule. Populations are
`bench-results/parity-losses-20260905/<DIV>.txt`; full classifications are
`bench-results/parity-losses-20260905/<DIV>.census.tsv`
(`file, declared, reference_verdict, class, last_route, dominant_stage,
wall_ms, detail`).

## A note on the diagnostic tool

`explain_corpus` is explicitly "DIAGNOSTIC ONLY" (its own banner): it runs
`check_auto_explained` on the flat assertion view, not `solve_smtlib` (the
shipped front door), and is measured to disagree with it on 134 of 397
committed benchmarks. Two further findings from this census, not previously
recorded:

- **Its own worker hangs on some inputs with no external watchdog.** Two
  processes (QF_ABV's `bmc-arrays/bubbleSort.smt2`, QF_LIA's two
  `RwMutex-PT-*/RC-*.smt2` files) were found still running after 1.2 to 2.6
  **hours** against a nominal 24 s budget -- orphaned from an earlier,
  interrupted run of this census. `smtcomp_cli` has an external `recv_timeout`
  watchdog with a grace period and always returns; `explain_corpus`'s
  `--__worker-file` path has only the solver's *internal* soft-stop, and on
  these files it never fires. The rest of this census wraps every
  `explain_corpus` worker invocation in an external `timeout -k 5 45`, which
  is what turned these three into recorded `other(explain-corpus-crash)`
  rows instead of an indefinitely stuck host.
- **A handful of files decide under the flat view but not the front door**
  (`other(explain-corpus-decided:flat-sat)` / `flat-unsat`, 6 files across
  QF_ABV and QF_IDL): exactly the divergence class the tool's own banner
  warns about, not a solver capability finding.

Every `other(explain-corpus-crash)` and `other(explain-corpus-decided:...)`
row is still backed by `smtcomp_cli`'s own verdict and wall time (in
`detail`), which is what the day's parity sweep actually measured.

## Per-division tables

### QF_SLIA -- 7 files (s6)

| class | files |
|---|---:|
| `other(incomplete: no model within the bounded integer width 32)` | 3 |
| `parser-reject(unsupported: str.replace_all over a non-constant operand)` | 2 |
| `other(string-gate-unconfirmed: bounded-unsat-not-certified)` | 1 |
| `other(incomplete: integer constant does not fit the bounded width 32)` | 1 |

Top routes: `int-blast-ladder` (4).

### QF_BV -- 6 files (s5)

| class | files |
|---|---:|
| `search-timeout` | 5 |
| `other(explain-corpus-crash)` | 1 |

Top routes: `qf-bv` (5, all search-timeout).

### UF -- 32 files (s5)

> **SUPERSEDED, 2026-09-06.** Every row in this table is wrong. Re-measured
> through the front door (`solve_smtlib`, `AXEYUM_QTRACE=1`), all 32 files enter
> the *quantified* ladder, where the declared-sort CEGAR bound does not live;
> the string `declared-sort` appears in no trace or verdict of any of the 32.
> The replacement classification, with the stage that spent the budget rather
> than the last route's message, is
> [the UF front-door census](2026-09-06-uf-front-door-census.md) and
> `bench-results/parity-losses-20260906/UF.front-door.census.tsv`: 23
> `route-decline(residual-quantifier)`, 7 `search-timeout`, 2
> `other(instantiation-satisfiable)`.

| class | files |
|---|---:|
| ~~`admission-decline(declared-sort lazy CEGAR refuses N congruence pairs, bound 64)`~~ | ~~32~~ |

Top routes: ~~`ufbv-declared-sort-lazy` (32, all of them)~~ — no front-door trace
of any of the 32 reaches that route.

### QF_ABV -- 19 files (s5)

> **SUPERSEDED 2026-09-08.** Every `class` and `last_route` below is wrong for
> this division, and the population is stale: five of these files are decided
> by the current tree. Read
> [the front-door route attribution](../12-performance/qf-abv-route-attribution-2026-09-08.md)
> instead. The wall times and `smtcomp_cli` verdicts in the TSV remain good.

| class | files |
|---|---:|
| `search-timeout` | 8 |
| `other(explain-corpus-decided:flat-sat)` | 4 |
| `other(explain-corpus-crash)` | 4 |
| `other(incomplete: array shape left undecided by the lazy ROW/extensionality path)` | 3 |

Top routes: `array-fast-path` (12), `qf-abv-array-decline` (3).

### QF_LIA -- 27 files (s7)

| class | files |
|---|---:|
| `admission-decline(lazy linear arithmetic pre-SAT skeleton exceeds the joint resource boundary)` | 15 |
| `search-timeout` | 4 |
| `other(explain-corpus-crash)` | 4 |
| `other(incomplete: QF_LIA branch-and-bound undecided, wall-clock deadline, node cap 20000000)` | 3 |
| `other(incomplete: exact-rational simplex declined, i128 overflow)` | 1 |

Top routes: `lia-dpll` (18), `lia-simplex` (4).

### QF_UF -- 38 files (s5)

| class | files |
|---|---:|
| `admission-decline(combined theories: eager Ackermann elimination would emit N congruence constraints)` | 35 |
| `admission-decline(declared-sort lazy CEGAR refuses N congruence pairs, bound 64)` | 3 |

Top routes: `qf-bv` (35, the Ackermann-to-QF_BV path), `ufbv-declared-sort-lazy` (3).

### QF_RDL -- 47 files (s6)

| class | files |
|---|---:|
| `admission-decline(online CDCL(T) LRA atom cap exceeded, N > 1024)` | 23 |
| `search-timeout` | 22 |
| `other(explain-corpus-crash)` | 1 |
| `admission-decline(Fourier-Motzkin elimination exceeded the wall-clock / size budget)` | 1 |

Top routes: `nra` (46).

### QF_UFLIA -- 58 files (s5/s6/s7)

| class | files |
|---|---:|
| `search-timeout` | 31 |
| `admission-decline(lazy function-consistency CEGAR inconclusive)` | 21 |
| `route-decline(unsupported:ingest:wide-integer-literal)` | 6 |

Top routes: `uf-arith-lazy-overbound` (52), `smtlib-ingest` (6).

### QF_LRA -- 54 files (s6)

| class | files |
|---|---:|
| `search-timeout` | 31 |
| `admission-decline(online CDCL(T) LRA atom cap exceeded, N > 1024)` | 23 |

Top routes: `nra` (54, all of them).

### QF_IDL -- 54 files (s6)

| class | files |
|---|---:|
| `admission-decline(lazy linear arithmetic pre-SAT skeleton exceeds the joint resource boundary)` | 46 |
| `search-timeout` | 6 |
| `other(explain-corpus-decided:flat-unsat)` | 2 |

Top routes: `lia-dpll` (54, all of them) -- but see the dispatch-overrun note
below: `dominant_stage` (the attempt that actually consumed the wall clock)
is `dl-online` for the great majority of the 46 admission-declines, not
`lia-dpll`.

### QF_NIA -- 61 files (s7)

| class | files |
|---|---:|
| `search-timeout` | 30 |
| `admission-decline(estimated N CNF clauses before lowering exceeds budget 64000000)` | 17 |
| `other(incomplete: bounded integer model overflowed at width 32)` | 11 |
| `admission-decline(ingest: distinct with N arguments)` | 1 |
| `other(incomplete: no model / integer constant does not fit the bounded width 32)` | 2 |

Top routes: `int-blast-ladder` (60, all but one).

## Cross-division class totals

| class | files | share |
|---|---:|---:|
| `admission-decline(*)` | 217 | 53.8% |
| `search-timeout` | 137 | 34.0% |
| `other(*)` | 41 | 10.2% |
| `route-decline(unsupported:*)` | 6 | 1.5% |
| `parser-reject(*)` | 2 | 0.5% |
| `dispatch-overrun` | 0 | 0.0% |
| **Total** | **403** | 100% |

No file in any of the 403 landed as a bare `dispatch-overrun` (a process
killed with no stage line at all) once `explain_corpus`'s own hangs were
externally bounded -- every file printed either a full route ladder or a
`smtcomp_cli` wall time close to the 24 s budget. `admission-decline` is the
largest class **by count**, but the QF_IDL finding below shows that a decisive
admission-decline can still be preceded by the real cost sitting in a
different, non-terminal route -- so this table is a census of *terminal*
reasons, not of where the clock went.

## The QF_IDL dispatch-overrun pattern, confirmed at scale

The plan's 2.1 "second cause" (dl-online spends 18-21 s on its own
`past_deadline` wall-clock check, hands off to `lia-dpll`, which then
declines in seconds on `MAX_PRE_SAT_ARITH_ATOMS`) is not an isolated
observation from five traced files -- it is 46 of QF_IDL's 54 losses. In each
one, `last_route` (the decisive decline) is `lia-dpll`, but `dominant_stage`
(the attempt that actually burned the wall clock) is `dl-online` at
consistently 18-21 s before `lia-dpll` declines in under a second on its
pre-SAT admission check. Fixing S1 (propagation in `CdclT::unit_propagate`)
recovers this reserve; S2 (evaluate the admission check before consuming it)
is a smaller, independent win on the same files if S1 lands later.

## Six divisions: which plan slice the losses point at

**QF_UF (38 files).** First entry; the plan had "nothing known except that
the quantifier-free EUF route is the online e-graph on `CdclT`." All 38 are
`admission-decline`, split 35/3 between eager Ackermann elimination refusing
a large congruence-constraint count (route `qf-bv`, the Ackermann-to-QF_BV
path) and the same declared-sort lazy CEGAR congruence-pair bound (64) that
dominates UF. This rules out 2.1's propagation defect as QF_UF's cause and
points squarely at S11: an Ackermann-elimination / CEGAR admission budget,
not a search-timeout problem.

**UF (32 files).** All 32 are the single `declared-sort lazy CEGAR refuses N
congruence pairs (bound 64)` shape, route `ufbv-declared-sort-lazy`. This
matches the 2026-08-21 gap analysis's framing (finite-model-finding
benchmarks, a technique gap) with a specific, uniform target: the S11 bounded
finite-model-finding extension needs to raise or eliminate the 64-pair bound,
not touch propagation or timeouts -- every one of the 32 losses is the same
knob.

**QF_LIA (27 files).** The plan expected "a split between search timeouts
(2.1's fix) and cut-generation limits." The split is real but lopsided: 15 of
27 are `admission-decline` on `lia-dpll`'s pre-SAT skeleton resource boundary
(the same family as QF_IDL's dominant class), only 4 are clean
search-timeout, and 4 more are `other(explain-corpus-crash)` -- files large
enough that the diagnostic tool's own worker hung and had to be externally
killed, though `smtcomp_cli`'s own ~25 s wall time is consistent with a
timeout. One file's `other` is specifically an i128 overflow in the
exact-rational simplex during branch-and-bound reconstruction -- a second,
independent QF_LIA data point for the wide-integer lever (S9 / ADR-1702
slice 2) beyond the QF_UFLIA literal-parsing case. Net: S4/S11 (the
admission-boundary and cut budget) covers more files here than S1.

**QF_ABV (19 files).** First entry at 90.9%. 8 clean search-timeout
(`array-fast-path`), 3 genuine capability gaps -- `array shape left
undecided by the lazy ROW/extensionality path and refused by bo[unds]` -- an
S11 target (the ADR-0084/0085 array-shape boundary the plan named as a
hypothesis, now confirmed present on 3 files), 4 where the flat-view
diagnostic disagrees with the front door (not a capability finding), and 4
`other(explain-corpus-crash)` (the tool's worker hanging on array-heavy
inputs; `smtcomp_cli` itself completed normally on all of these). Net: the
capability half of 2.7's hypothesis is real but small (3 files); the larger
share is S1/S8 (search-timeout and per-conflict throughput).

**QF_SLIA (7 files).** The plan's hoped-for "cheapest division to close."
One file is the exact `refused-string-gate-unconfirmed` shape 2.9 named
(StringGate declining to certify a bounded-string unsat candidate) -- an S11
target as scoped. Four are a different, previously unnamed shape: the
`int-blast-ladder`'s bounded integer width (32 bits) either has no model
within the bound or a literal that does not fit it -- a second, independent
width-ladder finding alongside QF_NIA's (below). Two are
`parser-reject`/`error` on `str.replace_all` over a non-constant operand,
outside the wired string-route surface entirely -- an S9-adjacent parser gap,
not a certification gap. Net: 2.9's unsat-certification hypothesis explains
1 of 7, not the majority; the bounded-width and parser gaps are the larger
share.

**QF_UFLIA (58 files, re-censused after the day's changes).** Confirms the
2.3 diagnosis directly: 31 clean `search-timeout` (route
`uf-arith-lazy-overbound`, the lazy UF/arith CEGAR loop, S1's territory), 21
`admission-decline` on the same CEGAR loop declining `inconclusive` on an
application/function-group count (a distinct S11-shaped admission-budget
target from the timeouts, even though it is the same route family), and 6
`route-decline(unsupported:ingest:wide-integer-literal)` -- files that never
reach the solver because the parser rejects an `Int` literal above the
modeled i128 range, exactly the 2.3 lever named for ADR-1702 slice 2 (S9).
All three levers the plan named for this division (S1, S9, and the CEGAR
admission budget) are present in the fresh count, in that order by size.

## What this changes about the plan's slice ordering

- **S11 has more distinct, independently-confirmed targets than the plan's
  four named ones.** UF and QF_UF's Ackermann/CEGAR congruence bound (67
  files together) is the single largest uniform admission-decline family in
  the whole census outside the two 1,024-atom LRA/RDL caps. QF_ABV's 3-file
  array-shape gap and QF_SLIA's 1-file StringGate case are confirmed but
  small. QF_SLIA and QF_NIA both independently hit the bounded integer-width
  (32-bit) ladder limit -- a shared S11/S12 target that was not previously
  named as one.
- **S9 (wide-integer literals) has a second confirmed instance** beyond
  QF_UFLIA: one QF_LIA file hits an i128 overflow inside the exact-rational
  simplex itself, not at the parser. The lever is the same (ADR-1702 slice
  2's wide-integer path) but the failure site differs, so a fix scoped only
  to the SMT-LIB literal parser will not close this file.
- **The QF_IDL dispatch-overrun pattern (S2) is not a five-file curiosity --
  it is 46 of 54 losses in one division**, all showing the identical
  dl-online-then-lia-dpll signature. This is the strongest single argument in
  this census for prioritizing S1/S2 ahead of the per-division S11 slices:
  fixing propagation recovers the reserve on 46 files in QF_IDL alone, before
  touching admission constants anywhere.
