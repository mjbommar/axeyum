# ADR-2080: the initial-lemma refresh rereads the whole atom set a quarter of a million times, the quadratic loop is not the cost, and the cap everyone looks at has never fired

Status: accepted
Index-summary: [ADR-2075] §7(B) handed over `refresh_initial_lemmas` at **95.98 %** of a row z3 refutes in 107 ms, with the mechanism given as a cap that bounds its OUTPUT (`MAX_INITIAL_BOUND_MUTEX_LEMMAS = 8_192`, tested inside the pair loop) where its sibling bounds its INPUT. **The site is right and the loop is wrong.** An attribution build over the whole committed 208-row census: on `havoc-bench_sum` the refresh runs **293,304 times** — `assert_incremental` calls it once per assertion and it rebuilds from scratch — over an atom set that reaches **7,272**, and `extract_ms=21,395` of `mutex_ms=21,822` is the **LINEAR** per-atom rescan. The quadratic loop everyone looks at is quadratic in the BOUNDS (**90**) and is 427 ms of 21.8 s; on one row of five it is 69 billion iterations, so both halves are real and neither alone explains the population. **The cap in the handoff has never fired**: `cap_hits=0` on **153 of 153** rows with a reading. Both caps were added in **ONE hunk of ONE commit** (`c093fa911`, 2026-06-25) on adjacent lines — one commit applying two disciplines, not two authors across time — and the 2026-09-08 registry sweep could not have caught the gap, because `config_registry_scan.py` derives its population from `const` declarations and **a coverage checker over declarations is structurally blind to an absent one**. The population is **5 of 153** (Wilson `[1.4 %, 7.4 %]`), **3 of them outside** the bucket handed over. One lever built, **ships `Off`**: an incremental refresh (early return on an unchanged atom count, cached extraction over the append-only atom vector, pair loop indexed by the `expr` `conflicting_bounds` already requires), output-preserving by construction. A/B over all 208 census rows: **0 gains / 0 losses / 0 flips / 0 exit-status moves**; 3 passes over 58 rows: **0 unstable** — so pre-registered D2 ships it `Off`. The speed is real and reported as speed only: the five profiled rows are the **five largest speedups on the whole census** (0.552-0.644) against per-row base bands of **1.000-1.275**, while the three largest apparent SLOWDOWNS (1.948, 1.460, 1.218) each sit **inside their own row's band** and are not slowdowns — a "ten largest speedups" table is structurally blind to that half. Mechanism, both paths instrumented: `extract_ms` **22,199 → 5**, and the pair loop **69.1 billion → 327 million at an identical `max_bounds=1,756`** (582x per call). **Three of the five leave [ADR-2075]'s bucket**: `Watchdog` + `; partial route ` + 8 attempts becomes `ResourceLimit` + a complete `; route ` + **20** attempts with a named next blocker — that ADR's own structural recommendation, reached by removing the un-deadlined work rather than by adding a clock, and **not** counted as a verdict. The input cap the brief asked for exists, records its crossing unconditionally where a census can see it, and **ships its decline `Off`**: enforcing it cost 0 of 58 rows, but **exactly ONE** decided control row is a measured crosser (Wilson `[0 %, 79.4 %]`) with 34 more of unknown exposure, it would fire on **103 of 153** rows, and it buys exactly what the output-preserving route buys. **P2 and P6 are both wrong** — the atom count is 7,272 not <512, and the cap cost nothing. A mutation battery **found a real gap**: making the cache re-read from zero, so it doubles every refresh, killed NOTHING until a fourth test was written, because the duplicates land after the originals and `seen` dedups the repeated pairs. Final table M1→3, M2→2, **M3→exactly 1**, **M4→0 and unkillable** (deleting the early return cannot change output by construction; that impossibility is the finding). z3 refutes **all five in 108-309 ms**, so the remaining gap is capability, not budget, and the pass was never the whole cause. **The sharpest open question is left open**: switching the whole pass off changed no verdict on 58 rows and its output cap has never fired on 153, so its cost is measured and its BENEFIT is measured by nobody.
Index-status: accepted
Date: 2026-09-15

## Context

[ADR-2075] §7(B) and §12.4 handed this lane one site and one mechanism:

> `MAX_INITIAL_BOUND_MUTEX_LEMMAS = 8_192` is checked **inside** that loop and
> caps the CONFLICTS FOUND, so a query with few conflicting pairs pays the whole
> quadratic scan every time. Its sibling sixty lines below … caps its **input** …
> This is **95.98 %** of `havoc-bench_sum`, which z3 refutes in **107 ms**.

Branch base: `git merge-base main HEAD` is
`05410406886866fe7897c168f77c052b036a1353`, which **is** local `main`'s HEAD.
Rules, decision rules and predictions were
[pre-registered](../../../bench-results/lemma-input-20260915/PREREGISTRATION.md)
before the lane's first binary finished compiling.

The handoff's *site* is right and its *mechanism is the wrong loop*. Both halves
of that are measured below, and the second one is the finding.

## 1. The population, sized by profile rather than by guess

An attribution build (the instrument is committed as `instrument.py`, applied to
a `lane-snapshot.sh` tree, and is an **attribution binary only** — R2) reports
once a second on stderr, because the rows under study are killed by the watchdog
and a report emitted at return would never exist. A row that finishes inside
that second prints nothing and is recorded `NOREAD`, never as zero.

Run over the whole committed 208-row front-door census at 24 s, 8 pinned cores:

| | n |
|---|---:|
| rows measured | 208 |
| with an `li-stats` reading | 153 |
| `NOREAD` (finished inside 1 s) | 55 |
| **D4 population** (the pass holds ≥ 50 % of the budget) | **5 of 153** |

Wilson 95 % on 5/153 is `[1.4 %, 7.4 %]`.

| row | pass % | calls | mutex_ms | extract_ms | pair_iters | max_atoms | max_bounds | cap_hits |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `vcc-havoc/havoc-bench_sum.1.bar` | **91.0 %** | 293,304 | 21,822 | 21,395 | 519,291,513 | 7,272 | 90 | 0 |
| `vcc-havoc/havoc-bench_dlist_insert_head.12.ua_wcscpy` | 87.9 % | 27,963 | 21,091 | 21,061 | 10,566,990 | 34,954 | 28 | 0 |
| `vcc-havoc/vccp-union1.c.6.reint2` | 86.8 % | 61,008 | 20,827 | 20,610 | 339,448,160 | 34,743 | 106 | 0 |
| `vcc-havoc/havoc-bench_036.1.AddElement` | 69.2 % | 7,212 | 16,594 | 11,412 | 7,149,619,382 | 15,046 | 1,756 | 0 |
| `spec_sharp/textbook-Factorial.dll.1.Factorial.F_System.Int32` | 51.4 % | 17,759 | 12,333 | 12,325 | 108,774 | 36,054 | 34 | 0 |

**So it is not one row, and it is not confined to the bucket that was handed
over.** Two of the five are in [ADR-2075]'s 9 (`havoc-bench_sum`,
`havoc-bench_036.1.AddElement`); **three are not**, and one of those three
(`textbook-Factorial`) is in a different family. Pre-registered **P1** (≥ 2 of
the 9) and **P5** (≥ 1 outside) are both **right**.

The denominator matters and is stated: this is 5 of the 153 census rows that
produced a reading, not 5 of the corpus. Nothing here licenses a corpus rate.

## 2. The quadratic loop is not the cost — the LINEAR rescan is

Read the two time columns against each other. On four of the five rows
`extract_ms` is within 2 % of `mutex_ms`: **21,395 of 21,822**; 21,061 of
21,091; 20,610 of 20,827; 12,325 of 12,333. `extract_ms` is the per-atom
`simple_int_literal_bounds` scan. The pair loop — the O(n²) everyone looks at —
is the *remainder*, and on `havoc-bench_sum` that remainder is 427 ms of 21,822.

The reason is in the shape of the call, not the shape of the loop:

- `euf::check_with_incremental_arith` keeps ONE `IncrementalArithDpll` across
  CEGAR rounds and calls `assert_incremental` once per new assertion;
- `assert_incremental` calls `refresh_initial_lemmas` **once per assertion**;
- the refresh rebuilds everything from scratch.

So on `havoc-bench_sum` the refresh runs **293,304 times** over an atom set
whose high-water mark is **7,272** — the atom vector is read on the order of a
billion times to find at most **90** bounds. The quadratic loop is quadratic in
the BOUNDS (90), not in the atoms (7,272). ADR-2075 read "O(atoms) rescan, then
an O(bounds²) pair loop" correctly and then attributed the cost to the second
one; the measurement says the first.

`havoc-bench_036.1.AddElement` is the one row where the pair loop does cost:
**7.1 billion** iterations against `max_bounds=1756`, and `extract_ms` is only
11,412 of 16,594. So both halves are real, and neither alone explains the
population. Pre-registered **P3** was about the pair loop and is answered in §5.

## 3. `cap_hits=0` on 153 of 153 — the cap in the handoff has never fired

`MAX_INITIAL_BOUND_MUTEX_LEMMAS = 8_192` truncated **nothing**, on every row of
this census that produced a reading. It is not merely the wrong kind of bound
for this cost; on this population it is not a bound at all. Its registry entry
said "Silent truncation of a pre-seeding pass"; the truncation has never
happened here.

That is worth stating as its own finding because a cap with a plausible story
and no measured firing is exactly the shape [ADR-2020] found (a constant that
looked absurd and was a deliberate proxy) and [ADR-2055] found from the other
side (a cap that, once enforced, cost 18 clean exits). **Before changing a cap,
find out whether it has ever bitten.**

## 4. Both caps' history, and why the registry could not see the gap

`git log -S` on `crates/axeyum-solver/src/dpll_lia.rs`:

| constant | introduced | since |
|---|---|---|
| `MAX_INITIAL_BOUND_MUTEX_LEMMAS = 8_192` | `c093fa911`, **2026-06-25** | never changed |
| `MAX_INITIAL_BOUND_IMPLICATION_LEMMAS = 4_096` | `c093fa911`, 2026-06-25 | never changed |
| `MAX_INITIAL_BOUND_IMPLICATION_ATOMS = 256` | `c093fa911`, 2026-06-25 | → `512` in `83098f933`, 2026-06-26 |

**All three landed in ONE hunk of ONE commit, on adjacent lines, on the same
day.** The "sibling sixty lines below knows better" is not two authors
disagreeing across time: it is one commit applying two different disciplines to
two passes written together. The input bound was given to the pass whose input
it was easy to characterise, and the other pass got an output bound.

The only later touch is `e3a7e0d3a` (2026-09-08), the config-registry
attribution sweep, which added the `note_crossed` record to
`MAX_INITIAL_BOUND_IMPLICATION_ATOMS` and registered
`MAX_INITIAL_BOUND_MUTEX_LEMMAS` with `Signal::None`. It registered the OUTPUT
cap and did not notice there was no INPUT cap to register — **and it could not
have.** `scripts/config_registry_scan.py` derives its population by matching
`const NAME: <numeric type> = …` in the source, which is the right way to build
a population of bounds that exist. A bound that does not exist has no `const`
line, so a checker whose subject is "every bound is attributable" is
structurally blind to a missing bound. That is a general shape worth carrying:
**a coverage checker over declarations measures the declarations, and an absent
declaration is the one thing it cannot report.**

## 5. The input distribution, published BEFORE any number is proposed (R17)

Over the 153 rows with a reading:

| quantity | min | p50 | p90 | p99 | max |
|---|---:|---:|---:|---:|---:|
| `max_atoms` (the pass's input) | 2 | 717 | 15,150 | 34,954 | **36,054** |
| `max_bounds` (what it finds) | 0 | 190 | 16,808 | 21,710 | 21,716 |
| `calls` (refresh entries) | 2 | 65 | 2,989 | 61,008 | **293,304** |

**Pre-registered P2 is WRONG**, and wrong in the direction that matters: it
predicted the binding input would be the call count and that `max_atoms` on
`havoc-bench_sum` would sit *below* 512, so a cap in the sibling's shape would
not even fire. It is **7,272**. The cap would fire — and it would fire on
**103 of 153** rows, and on **5 of 5** of the D4 population. So an input cap at
the sibling's value is not a corner-case guard here; it would decline the pass
over two thirds of this census.

Exposure on the half that matters — rows that are exiting cleanly today:

| decided (control) rows | n |
|---|---:|
| in the census | 53 |
| with a reading | 19 |
| **NOREAD — exposure UNKNOWN, not zero** | 34 |
| reading AND crossing 512 atoms | **1** (Wilson `[0.9 %, 24.6 %]`) |

## 6. What was built, and why it is output-preserving by construction

`AXEYUM_LIA_INITIAL_BOUND_INDEX=1`, **off by default**, selects an incremental
refresh. Both paths stay compiled in, which is what lets the A/B run **one
binary under two environment values**. Three changes:

1. **An unchanged atom count returns early.** Both passes are pure functions of
   `ctx.atoms` (the arena only gains hash-consed nodes, so the same atoms yield
   the same clause handles), so a refresh at an unchanged atom count can only
   re-derive clauses `initial_clauses` already holds. On `havoc-bench_sum` that
   is the difference between 293,304 rebuilds and at most 7,272.
2. **The bound extraction is cached** over the append-only atom vector
   (`ArithAbstractor`'s only writer is a `push`), so extending over the new
   suffix yields exactly the vector a full rescan builds.
3. **The pair loop is indexed by `expr`**, which `conflicting_bounds` already
   requires to match before it will return anything. Each group's index vector
   is built in increasing `i` and is therefore sorted, and `partition_point`
   finds the first member above `i`, so the accepted pairs are visited in
   exactly the order the shipped double loop visits them — **including under the
   truncation cap**, which is what makes the two sequences equal rather than
   merely equal as sets. The map is only looked up, never iterated, so no output
   depends on hash order.

**Nothing is dropped.** Unlike an input cap this cannot turn a row that decides
today into a faster `unknown`, which is the failure mode [ADR-2055] measured.

### R12: proved output-preserving, and the tests shown to die

Three tests. `the_indexed_bound_scan_matches_the_quadratic_scan_pair_for_pair`
compares the full conflict SEQUENCE; `the_indexed_refresh_seeds_exactly_the_
clauses_a_full_rebuild_does` drives the whole refresh one assertion at a time
(and calls it twice per assertion, because the no-op repeat is the common case)
and compares lemmas and clause set against a solver driven through the shipped
path; `the_bound_scan_fixture_can_tell_the_two_scans_apart` is the
fixture-validity control and **deliberately does not call the code under test**,
so it survives every mutation of the indexed path — [ADR-2075]'s two tests were
*both* vacuous on their first mutation run because nothing played that role.

The end-to-end test asserts `!initial_bound_index_enabled()` first: it compares
the two paths against each other, so an ambient environment that had already
selected one would make it compare a path with itself and pass.

Four mutations, each applied in a `lane-snapshot.sh` copy under `/data0` (never
the shared worktree — a mutant on disk is every other lane's build), each one
BUILT and each run over a NONZERO test count, because a mutant that fails to
compile and a filter that selects nothing both present as "not clean" and
neither is a measurement:

| mutation | died | which |
|---|---:|---|
| **M1** the index skips one eligible partner (`partition_point(…) + 1`) | 3 | the two output tests and the cache test — though M1 kills by *panicking* on an out-of-range slice, so it is the weakest of the four |
| **M2** the lookup reads a different group than the insert wrote | **2** | the scan differential and the end-to-end refresh |
| **M3** the cache re-reads from zero instead of the suffix | **1** | `the_cached_bound_vector_equals_a_full_rescan` — exactly one, and it is the test written for it |
| **M4** the unchanged-atom-count early return is deleted | **0** | and it **cannot** be killed — see below |

The fixture-validity control survives M1, M2 and M3, which is what it is for.

**M3 is the reason the fourth test exists, and it is the finding of this
battery.** On the first run the suite was three tests and M3 killed **nothing**:
duplicating every bound in the cache on every refresh left the *output*
byte-identical, because the duplicates land after the originals, first-occurrence
order is unchanged, and `seen` dedups the repeated pairs. Three tests passed over
a cache that doubles on each call. A cache's CONTENTS are a claim of their own,
and no test over output can make them.

**M4 is reported rather than patched.** Deleting the early return cannot change
output *by construction* — it skips work whose result the solver already holds —
so no test over output can catch it, and the impossibility is the finding rather
than a gap to paper over. Its evidence is §7: 86.5 % of the arm's refresh calls
on `havoc-bench_sum` are that early return, and the rows it fires on are the
five largest speedups on a 208-row census.

## 7. The A/B: the profile's five rows are the five largest speedups, and nothing decides

Polarity, stated in the runner's own header: BASE is the lever unset — the
shipped full-rebuild refresh; ARM is `AXEYUM_LIA_INITIAL_BOUND_INDEX=1`. One
binary (`a5d126ae7a8adfd4`, freshness by `find -newer` before the run), two
environment values, same file, same pinned core of 0-7, arms back to back, order
alternating with the row's ordinal.

Over the **whole 208-row census** at 24 s, 416 arm-runs:

| | n |
|---|---:|
| GAINS (`unknown` → decided) | **0** |
| LOSSES (decided → `unknown`) | **0** |
| FLIPS (`sat` ↔ `unsat`) | **0** |
| EXIT-STATUS moves (R5, its own channel) | **0** |
| verdicts, base | `sat` 21, `unsat` 38, `unknown` 149 |
| verdicts, arm | `sat` 21, `unsat` 38, `unknown` 149 |

**Zero gains, so by the pre-registered D2 the lever ships `Off`.** Faster and
still `unknown` is not a gain, and saying so after measuring is the point of
measuring. Pre-registered **P4** — that `havoc-bench_sum` would still not decide
with the pass made cheap — is **right**.

What the wall-time column does say is that the change is doing exactly the thing
the profile named, on exactly the rows it named. The arm/base ratio has median
**1.000** over 208 files, and the five largest speedups on the whole census are
the five rows of the D4 population, in a block, ahead of everything else:

| ratio | base | arm | row |
|---:|---:|---:|---|
| **0.552** | 25,051 ms | 13,827 ms | `vcc-havoc/vccp-union1.c.6.reint2` |
| **0.552** | 25,040 ms | 13,825 ms | `vcc-havoc/havoc-bench_dlist_insert_head.12.ua_wcscpy` |
| **0.586** | 25,137 ms | 14,731 ms | `vcc-havoc/havoc-bench_sum.1.bar` |
| **0.588** | 25,045 ms | 14,724 ms | `spec_sharp/textbook-Factorial…F_System.Int32` |
| **0.709** | 25,153 ms | 17,842 ms | `vcc-havoc/havoc-bench_036.1.AddElement` |
| 0.754 | 422 ms | 318 ms | `vcc-havoc/CWindowsCard.c.41.nondet` (the first non-D4 row) |

A profile that picks five rows out of 153 and an A/B that then ranks those same
five first out of 208 is two independent instruments agreeing, and it is the
only reason to believe the mechanism rather than the story.

The slowest row under the arm is a ratio of **1.332**, which is why §7.1 has to
exist before any of this is read as a speed claim.

### 7.1 Three passes, and the band each ratio is read against

58 rows — the D4 five plus all 53 decided `UFNIA` control rows — **3 passes per
arm**, 348 arm-runs:

| | n |
|---|---:|
| GAINS / LOSSES / FLIPS | **0 / 0 / 0** |
| EXIT-STATUS moves | **0** |
| **UNSTABLE across passes** | **0** |
| verdicts per arm (174 runs each) | `sat` 63, `unsat` 96, `unknown` 15 — identical |

The **noise floor** is the same arm repeated: `base`, 3 passes, 58 rows, max/min
per row **median 1.028, p90 1.662, max 6.449**. Quoting that population band
against everything would be wrong in both directions, so every ratio below is
read against **its own row's** base-arm band:

| arm/base | that row's base band | base passes | arm passes | row |
|---:|---:|---|---|---|
| **0.552** | **1.000** | 25,037 / 25,034 / 25,034 | 13,825 / 13,217 / 13,822 | `vccp-union1.c.6.reint2` |
| **0.552** | 1.275 | 25,036 / 19,632 / 25,034 | 13,830 / 13,823 / 13,624 | `dlist_insert_head…ua_wcscpy` |
| **0.566** | **1.000** | 25,140 / 25,137 / 25,138 | 14,425 / 13,720 / 14,225 | `havoc-bench_sum.1.bar` |
| **0.582** | **1.000** | 25,141 / 25,144 / 25,137 | 14,629 / 13,621 / 14,631 | `havoc-bench_036.1.AddElement` |
| **0.644** | 1.096 | 25,046 / 22,845 / 25,042 | 16,238 / 14,623 / 16,137 | `textbook-Factorial…Int32` |

Three of the five have a base band of **exactly 1.000** across three passes, so
their ~0.55 is not inside anything.

**And the same discipline deletes a regression that a speedup table would have
hidden.** The three largest apparent slowdowns are:

| arm/base | that row's base band | verdict |
|---:|---:|---|
| 1.948 | **1.976** | inside its own noise |
| 1.460 | **1.467** | inside its own noise |
| 1.218 | **1.263** | inside its own noise |

Each of the three sits *inside* the band its own base arm produced on the same
three passes (`f2_rw141` base = 212 / 417 / 211 ms). A "ten largest speedups"
table is structurally blind to this half, and a lane that published 0.552 while
leaving 1.948 out would be reporting one tail of a distribution it had measured
both ends of. **17 of 58 rows** fall outside their own band at all, and the five
that matter are the top five of those.

### 7.2 The mechanism, read rather than argued

A second attribution binary instruments **both** paths, so the arm's own numbers
sit beside the base's on the same row (`ref/mechanism-5.tsv`; again attribution
only — it counts an atomic per outer iteration, so no timing claim rests on it):

| row | arm | calls | noop | refresh_ms | extract_ms | pair_iters | max_bounds | max_atoms |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| `havoc-bench_sum` | base | 196,234 | 0 | 22,414 | 22,199 | 446,252,651 | 90 | 12,886 |
| | arm | 879,346 | **760,561** | **6,425** | **5** | 292,264,853 | 2,380 | **358,178** |
| `vccp-union1` | base | 57,340 | 0 | 22,223 | 22,059 | 319,027,466 | 106 | 39,051 |
| | arm | 138,133 | 34,064 | **416** | **4** | 15,091,308 | 106 | 75,963 |
| `dlist_insert_head` | base | 282,923 | 0 | 14,047 | 13,960 | 106,941,870 | 28 | 52,376 |
| | arm | 577,665 | 166,093 | **416** | **17** | 17,285,730 | 28 | **771,384** |
| `havoc-bench_036` | base | 47,372 | 0 | 22,263 | 6,716 | **69,108,254,764** | 1,756 | 12,324 |
| | arm | 332,437 | 202,139 | **6,742** | **5** | 326,723,670 | 1,756 | **391,554** |
| `textbook-Factorial` | base | 51,157 | 0 | 9,922 | 9,907 | 310,266 | 34 | 45,438 |
| | arm | 53,263 | 13,195 | **9** | **1** | 80,442 | 34 | 45,954 |

Three things are legible here that no amount of reading the source would give:

- **The rescan is gone.** `extract_ms` 22,199 → **5**; 22,059 → **4**;
  13,960 → 17; 9,907 → **1**. That is the change the profile asked for.
- **P3 is right, and `havoc-bench_036` measures it at the same scale.** Its
  `max_bounds` is **1,756 under both arms**, so the pair-loop counts are directly
  comparable: **69.1 billion** iterations become **327 million**, and per
  refresh call 1.46 million become 2,508 — **582x**. P3 predicted ≥ 100x.
- **The arm gets much further.** It makes *more* refresh calls (879,346 against
  196,234) over an atom set that reaches **358,178** instead of 12,886 — 28x —
  and 86.5 % of those calls are the early return doing nothing. The pass is no
  longer what the row is spending its budget on; it has been spent on search.

The base numbers differ between the two instrumented runs (`calls` 293,304 then
196,234; `max_atoms` 7,272 then 12,886) because each instrument costs something
different and the row is killed at a wall-clock deadline, so how far it gets
varies. **The shape is what is stable and the shape is the claim**:
`extract_ms` is 99.0 % / 99.3 % / 99.8 % of `refresh_ms` on the extraction-bound
rows in every run.

## 8. The row changes CATEGORY even where the verdict does not

[ADR-2075]'s characterisation of its bucket is not about a theory or a route:

> **These are the rows whose running code checks no deadline.** … a kill records
> no route because a route is recorded on the way OUT.

That is a property with three observable parts — undecided, `give-up
kind=Watchdog`, and no COMPLETE `; route ` line — so all three are read, and
both prefixes are grepped, because grepping only `^; route ` is the exact defect
that ADR is about. Traced under both arms at 24 s on cores the A/B is not pinned
to (`ref/route-line-5.tsv`, raw stdout in `prof/`):

| row | arm | give-up kind | route line | attempts |
|---|---|---|---|---:|
| `havoc-bench_sum.1.bar` | base | **Watchdog** | **PARTIAL** | 8 |
| | arm | ResourceLimit | **COMPLETE** | **20** |
| `vccp-union1.c.6.reint2` | base | **Watchdog** | **PARTIAL** | 8 |
| | arm | ResourceLimit | **COMPLETE** | **20** |
| `havoc-bench_036.1.AddElement` | base | **Watchdog** | **PARTIAL** | 8 |
| | arm | ResourceLimit | **COMPLETE** | **20** |
| `havoc-bench_dlist_insert_head.12.ua_wcscpy` | base | ResourceLimit | COMPLETE | 20 |
| | arm | ResourceLimit | COMPLETE | 20 |
| `textbook-Factorial…F_System.Int32` | base | ResourceLimit | COMPLETE | 20 |
| | arm | Incomplete | COMPLETE | 20 |

**Three of the five leave the bucket.** They stop being killed by the
process-level watchdog and start declining in good order, with a full route
trail, and they get through **20 attempts of the dispatch ladder instead of 8**.
`havoc-bench_sum` was reproduced twice, independently, with the same numbers.

This is the structural recommendation [ADR-2075] §12.5 made —

> give these walks a deadline poll, or at minimum a breadcrumb frame

— reached from the other side: not by teaching the un-deadlined loop to notice
the clock, but by removing the work it was doing without one. And it converts an
unnameable failure into a named one: `havoc-bench_sum` under the arm says
`bound_by=q:mbqi last=fd:bounded-completeness-unsat`, `detail=e-matching:
instantiation time budget exhausted mid-round`. **The next blocker on this row
is now a sentence rather than a silence**, which is what the base arm could not
produce for it.

A near-miss is recorded with it, because it is the same defect class this whole
chain is about: the first run of `route-line-census.sh` reported the
`textbook-Factorial` arm as `NOVERDICT / NONE / ABSENT`. Nothing was wrong with
the run — the census read the file **while the tracing process was still writing
it**. A census over artifacts another process is still producing reports an
absence, and an absence is indistinguishable from a finding. It was caught by
reading the bytes rather than the summary, which is the only thing that ever
catches it.

## 9. What an input cap costs — and why its zero must be read against ONE row

The cap the brief asked for exists and was measured rather than argued about.
`AXEYUM_LIA_INITIAL_BOUND_MUTEX_ATOM_CAP=1` makes the mutex pass decline above
512 atoms; the arm is against the SHIPPED path (the index lever stays off), one
binary `ad3c9e00ad2f8587`, 58 rows = the 53 decided `UFNIA` control plus the D4
five, interleaved, order alternating:

| | n |
|---|---:|
| rows with both arms | 58 |
| **COST** (decided → undecided) | **0** |
| GAIN (undecided → decided) | **0** |
| FLIP | **0** |
| EXIT-STATUS moves | **0** |

**That zero is nearly vacuous, and the denominator is the whole story.** The cap
can only bite where the atom count exceeds 512. Of the 58 rows, **6** are
measured to cross it — and **5 of those 6 are the D4 rows, which are undecided
under every arm.** Among the **53 decided control rows, exactly ONE** is a
measured crosser:

| | n |
|---|---:|
| decided control rows | 53 |
| with a reading AND crossing 512 atoms — where the cap could bite | **1** |
| with a reading and not crossing — the cap is a no-op by construction | 18 |
| `NOREAD`, exposure **UNKNOWN** | 34 |

So the honest statement is: the one decided row where the cap fires
(`2019-Preiner/combined/f2_rw77`) still returns `unsat`, 707 ms → 809 ms.
Wilson 95 % on **0/1** is `[0 %, 79.4 %]`. **This run does not establish that
the cap is safe.** It establishes that it did not cost anything on the single
control row where it could have, and that 34 more rows were never exercised.
Quoting "0 losses on 53 rows" would be quoting a denominator 53 times too large.

And the other half of the ledger is what settles it. On the five rows where the
cap DOES fire, it buys **exactly what the indexed refresh buys**:

| row | base | **cap** arm | **index** arm |
|---|---:|---:|---:|
| `havoc-bench_sum` | 25,133 ms | 14,424 ms | 14,225 ms |
| `vccp-union1` | 24,536 ms | 13,218 ms | 13,822 ms |
| `dlist_insert_head` | 15,821 ms | 13,623 ms | 13,823 ms |
| `havoc-bench_036` | 25,133 ms | 15,435 ms | 14,629 ms |
| `textbook-Factorial` | 23,038 ms | 15,933 ms | 16,137 ms |

Two routes to the same saving, neither converting a verdict — and one of them
declines a pass that produces valid lemmas on **103 of 153** census rows while
the other drops nothing at all. **Pre-registered P6 (the cap costs ≥ 1
currently-decided row) is WRONG**, and it does not matter: D3 asks whether an
output-preserving change removes the cost instead, and it does, for the same
money.

There is a further reading, and it is the uncomfortable one. Switching the whole
pass off above 512 atoms changed **no verdict on 58 rows**, and its output cap
has fired **zero times on 153**. The pass's *cost* is measured; its *benefit*
on this corpus is not measured at all, by anyone, and nothing in this lane
establishes it. That is a question for a later lane and it is named in §13
rather than answered here.

## 10. Verdicts against independent authorities

There are **no new verdicts** to check (§7: 0 gains), so the authority run
answers the other question — whether these rows are hard or whether we are slow.
`z3 -T:24` is SECONDS, `cvc5 --tlimit=24000` is MILLISECONDS; the two flags are
deliberately not written to look alike.

| row | z3 | cvc5 | us, both arms |
|---|---|---|---|
| `havoc-bench_sum.1.bar` | **unsat, 209 ms** | unsat, 409 ms | `unknown`, 24 s |
| `dlist_insert_head…ua_wcscpy` | **unsat, 110 ms** | unsat, 109 ms | `unknown`, 24 s |
| `vccp-union1.c.6.reint2` | **unsat, 108 ms** | unsat, 309 ms | `unknown`, 24 s |
| `havoc-bench_036.1.AddElement` | **unsat, 309 ms** | unsat, 10,720 ms | `unknown`, 24 s |
| `textbook-Factorial…Int32` | **unsat, 109 ms** | no-opinion (26 s) | `unknown`, 24 s |

| | n |
|---|---:|
| rows | 5 |
| z3 decided | **5** |
| cvc5 decided | 4 |
| **both decided — the comparable denominator** | **4** |
| no-opinion (cvc5 only) | 1 |
| disagreements between the authorities | **0 of 4 comparable** |

Every one is `unsat`, and z3 refutes **all five in 108-309 ms** against our
24,000 ms. So the D4 population is not hard, the budget is not the constraint,
and — this is the part that bears on the decision — **the refresh was never the
whole cause on any of them.** Removing 22 seconds of it left every row exactly
as undecided as before.

## 11. The rules and the predictions against what happened

| rule | outcome |
|---|---|
| R1 population derived by script, with a control | `derive-population.sh`; the control prints `undecided=155 decided=53`, both non-empty |
| R2 attribution binary only | two of them; no verdict, wall time or decision in §7 comes from either; freshness by `find -newer` on both |
| R3 every bucket with its denominator; NOT-MEASURED separate | §1 (5 of **153**, not of 208); §5 (34 control rows are `NOREAD`, reported as **exposure unknown**, never as zero) |
| R4 decision RULES pre-registered | D1-D5 fixed before any number existed; D2 is what decides §12 against the lane's own preference |
| R5 exit status its own channel | §7, §7.1, §9 — 0 moves on 416 + 348 + 116 arm-runs |
| R6 interleaved one-binary A/B | §7; polarity in the runner's header; order alternates with the ordinal |
| R7 3 passes; noise floor published | §7.1 — and the floor is what **deletes** the apparent 1.948 regression |
| R8 control shown NON-VACUOUS | §11.1 — established, where [ADR-2075] could not |
| R9 authorities, comparable denominator | §10 — 5/5 z3, 4/5 cvc5, comparable denominator **4**, 1 no-opinion printed |
| R10 Wilson on every proportion | §1 `[1.4 %, 7.4 %]`; §5 `[0.9 %, 24.6 %]` |
| R11 measures THIS branch; post-merge predicted | §12 |
| R12 output-preservation proved, and the test shown to die | §6 — and the battery **found a real gap**, which is why there are four tests |
| R13 no waiter greps a process by a pattern its own command line contains | every waiter here watches an artifact |
| R14 unfinished checks reported as "did not run" | §13 |
| R15 `MEM_LIMIT_GB=16 scripts/mem-run.sh`; peak RSS | every analysis script; peak RSS across the attribution run **1,715,576 KB** |
| R16 fixture suites; the list parsed out of the hook | §12 |
| R17 an input cap only with its distribution and its cost | §5 then §9 — and the distribution is what refutes P2 |

| | predicted | measured |
|---|---|---|
| **P1** | D4 selects ≥ 2 of the [ADR-2075] 9 | **right** — 2 (`havoc-bench_sum`, `havoc-bench_036`) |
| **P2** | the binding input is the CALL COUNT; `max_atoms` on `havoc-bench_sum` sits **below** 512, so a sibling-shaped cap would not fire | **WRONG** — 7,272, and the cap would fire on **103 of 153** rows. The call count *is* the mechanism, but the atom count is not small, and those are different claims |
| **P3** | expression-indexing cuts pair iterations ≥ 100x | **right** — 582x per call on `havoc-bench_036` at an identical `max_bounds=1,756` |
| **P4** | `havoc-bench_sum` still does not decide | **right**, and on all five |
| **P5** | ≥ 1 D4 row outside the [ADR-2075] 9 | **right** — **3 of the 5**, one in a different family |
| **P6** | an enforced 512-atom cap costs ≥ 1 currently-decided row | §9 |

One prediction wrong out of six, and the one that was wrong was the lane's own
favourite theory. P2 was written because the call count is a more interesting
mechanism than a large atom set, and it conflated "the cost is driven by
repetition" (true) with "the input is small" (false). Both are needed to
conclude a cap would not fire, and only one of them held.

### 11.1 R8: the control, shown non-vacuous

[ADR-2075] could not establish this for its own lever and said so: on a decided
row the soft deadline wins, the breadcrumb never prints, and the reading that
would show the changed code executing is unavailable. This lane has a probe that
works there, because its instrument reports on a wall-clock thread rather than
at the watchdog — a decided control row carrying `calls>0` is a row the refresh
RAN on.

| control (decided) rows | n |
|---|---:|
| in the census | 53 |
| with a reading **and `calls>0`** — the refresh ran there | **19** |
| with a reading and `calls==0` | 0 |
| `NOREAD` (finished inside the instrument's 1 s period) — **not established** | 34 |

Nineteen rows, up to 78 refresh calls each, on the route
`euf::check_with_incremental_arith` → `IncrementalArithDpll::{new_within,
assert_incremental}` → `refresh_initial_lemmas`. The control is non-vacuous on
19 of 53 and **silent on the other 34**, which is stated rather than rounded up.

## 12. Decision

1. **The handoff's site is right and its mechanism is the wrong loop.** The cost
   of `refresh_initial_lemmas` is the LINEAR per-atom rescan, run once per
   assertion — `extract_ms` is 99 % of `mutex_ms` on four of the five rows where
   the pass dominates. The quadratic pair loop is over the BOUNDS (90 on the
   headline row), not the atoms (7,272), and on four of five rows it is under
   2 % of the pass. On the fifth it is 69 billion iterations, so both halves are
   real and neither alone explains the population.
2. **`MAX_INITIAL_BOUND_MUTEX_LEMMAS` has never fired here** — `cap_hits=0` on
   153 of 153 rows with a reading. Before changing a cap, find out whether it
   has ever bitten.
3. **The population is 5 of 153, not 1 and not 9**, and **3 of the 5 are outside
   the bucket that was handed over**. The brief's "if it is one row, say so and
   stop" does not apply, and the reason it does not is a measurement rather than
   a hunch.
4. **`AXEYUM_LIA_INITIAL_BOUND_INDEX` ships `Off` and is NOT recommended `On` on
   this evidence.** Pre-registered D2: gains = 0 ships `Off`, whatever the
   ratio, and the ratio here is real (0.552-0.644 against per-row noise bands of
   1.000-1.275) and still buys no verdict. The lever is committed with its four
   tests because the site is real, the change is proved output-preserving, and
   the next lane should not have to re-find any of it.
5. **`MAX_INITIAL_BOUND_MUTEX_ATOMS` ships with its CROSSING recorded and its
   DECLINE `Off`.** The record is unconditional and reaches a census as
   `; config … crossed=` / `; partial config …`; the decline is a capability
   change that would fire on 103 of 153 rows and buys exactly what the
   output-preserving route buys. D3 says no cap is proposed when an
   output-preserving change removes the cost instead, and that is the outcome.
6. **Three of the five rows leave [ADR-2075]'s bucket under the arm** —
   `Watchdog` + `; partial route ` + 8 attempts becomes `ResourceLimit` +
   `; route ` + 20 attempts — which is that ADR's own structural recommendation
   reached by removing the un-deadlined work rather than by teaching it the
   clock. **This is not a verdict and is not counted as one.**
7. **The next lane's target is not this pass.** z3 refutes all five in
   108-309 ms; removing 22 seconds of refresh left all five exactly as
   undecided. Under the arm the rows now name their own next blocker —
   `bound_by=q:mbqi`, `e-matching: instantiation time budget exhausted
   mid-round` — which is a sentence the base arm could not produce.

**Predicted post-merge value: no division total moves.** Both levers ship `Off`;
the only unconditional behaviour change in `crates/` is one `note_crossed` call
on queries above 512 arithmetic atoms under `--trace`. R16's fixture suites are
run anyway, because route behaviour is selectable here even though the default
path is byte-identical.

### 12.1 Gates, with their counts, all on this branch

| gate | result |
|---|---|
| `check-clippy-complete.sh` (under `cargo-serialized --batch`) | **890 of 890** workspace targets across **27 of 27** crates, **0 diagnostics** |
| `cargo fmt --all --check` | exit 0 |
| `cargo check --workspace --all-targets` | finished, 1m 04s |
| `cargo check -p axeyum-solver --all-targets` (**default features**) | finished, 16.59s; no diagnostic from `dpll_lia.rs` or `config_registry.rs` |
| `RUSTDOCFLAGS="-D warnings" cargo doc --workspace --all-features --no-deps` | finished; 41 crates generated |
| `corpus_regression` | `test result: ok. 2 passed; 0 failed` |
| `-p axeyum-solver --lib --features full -- --test-threads=4` | `test result: ok. **1789 passed**; 0 failed` — the 1,785 baseline plus this lane's four |
| `progress_frontier --features full -- --test-threads=1` | `test result: ok. 12 passed; 0 failed` |
| `run-dispatch-reason-suites.sh` (R16) | **19 suites**, `ALL dispatch/reason SUITES GREEN`, every count nonzero (7, 10, 20, 11, 12, 3, …, 13, 2, 20) |
| `check-merge-hygiene.sh` | `MERGE_HYGIENE\|markers=0\|adr_index=ok\|generated=current\|…\|PASS` |
| `check-suite-gating.py` | `SUITE_GATING\|suites=340\|gated=40\|excused=302\|PASS` — this lane adds no integration suite file (its tests are in the `dpll_lia` unit module) |

`progress_frontier` rewrites its own machine record; the five
`bench-results/frontier/*.json` it touched were **reverted, not committed**.

**One gate is red and it is red without this branch.**
`check-config-registry-staleness.py` exits 1 with **11 stale dated
justifications**. None of them is this lane's — both entries added here are
`undated`, which the checker does not examine — and the commits it cites
(`b47972ab9`, `f6303ee7a`, `ee36e0421`, …, all 2026-09-13/14) are other lanes'.
It is not in `hooks/pre-push`. It is reported here rather than left out, because
a gate this lane ran and did not mention would be a gate this lane hid. **The
first run of it inside the battery script was itself wrong**: the step was
written `python3 … | tail -4 || rc=1`, and under a pipe `||` reads `tail`'s exit
status, not python's, so a red gate contributed `rc=0`. It was re-run
unpiped to read its real status.

## 13. Not measured here, reported as "did not run"

- **Whether the mutex pass is worth running at all.** Switching it off above 512
  atoms changed no verdict on 58 rows, and its output cap has never truncated
  anything on 153. The pass's cost is measured; its BENEFIT on this corpus is
  measured by nobody, including this lane. That is the sharpest open question
  here and it is not answered.
- **The cap arm's zero rests on ONE exposed decided row** (§9). Wilson `[0 %,
  79.4 %]`. Thirty-four control rows have unknown exposure because they finish
  inside the instrument's one-second reporting period.
- **The control's non-vacuity is established on 19 of 53** decided rows and
  **not** on the other 34 (§11.1).
- **Nothing outside the committed 208-row census was measured.** The D4 rate is
  5/153 of that census; R1 forbids transferring it to the corpus.
- **`havoc-bench_036`'s 69-billion-iteration pair loop is not separately
  levered.** It is the one row where the index rather than the cache is the
  dominant saving, and the two are behind one lever, so their contributions are
  not separated on it.
- **No `perf` profile was taken by this lane.** The attribution is from
  instrumented counters, which name a function and a call count but not a caller
  chain; ADR-2075's `perf` work is not repeated or re-checked here.
- **The `; partial config … crossed=` line was read on a traced arm run but the
  new key's appearance was not separately regression-tested.** The mechanism
  (`note_crossed` → `live_config_trace_line` → `partial_line`) is the one the
  sibling bound already uses and was read in `smtcomp_cli.rs`, but no test pins
  that `MAX_INITIAL_BOUND_MUTEX_ATOMS` specifically appears there.

[ADR-2020]: adr-2020-the-ground-checker-mostly-refuses-and-the-set-it-refuses-is-one-we-had-no-need-to-build.md
[ADR-2055]: adr-2055-the-tableau-is-the-memory-and-capping-it-costs-eighteen-clean-exits.md
[ADR-2075]: adr-2075-the-silent-hang-is-not-silent-it-is-the-inventory-of-code-that-polls-no-deadline.md
