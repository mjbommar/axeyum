# Post-merge board, DT-EXACTNESS — the first lane whose arm survived the merge intact

**2026-09-13, on `76f4f22c6`** (merge of lane DT-EXACTNESS, ADR-1980). Five
divisions, 200 files each, re-measured on **merged `main`** with a binary built
after the merge: one arm, 24 s wall, 8 GiB `ulimit -v`, one pinned physical core
per shard, divisions run **serially** within a shard.

This exists because of the practice committed in `c2fb0ade4`: *after merging a
lane, re-measure the affected division on `main` before the number goes
anywhere.* That practice was written because nine lanes' arms were recorded as
board values and the total was overstated by 38.

## Result

| division | board (pre-merge) | lane's branch A/B arm | **merged `main`** | vs arm |
|---|---:|---:|---:|---:|
| UFDTLIRA | 105 | 143 | **143** | 0 |
| UFDT | 31 | 50 | **50** | 0 |
| AUFDTLIRA | 96 | 118 | **118** | 0 |
| **affected total** | **232** | **311** | **311** | **0** |
| UF (control) | 90 | 90 | **90** | 0 |
| UFNIA (unrelated) | 53 | — | **53** | — |

**+79, landing exactly. Every row matched its branch arm to the file.**

## The check that makes "landed exactly" mean something

Equal totals are not the same claim as equal files: two different sets can sum
to 311. Row by row, against the lane's own A/B base and arm columns:

| division | lane gains | of those, decided on merged `main` | decided on `main` but in neither base nor gains | base-decided, lost on `main` |
|---|---:|---:|---:|---:|
| UFDTLIRA | 38 | **38 / 38** | 0 | 0 |
| UFDT | 19 | **19 / 19** | 0 | 0 |
| AUFDTLIRA | 24 | **24 / 24** | 0 | **2** |

The 2 losses are exactly the 2 the lane reported. There is no substitution
anywhere: nothing decided on `main` that was neither already decided nor one of
the 81 predicted gains. **+79 = 81 gains − 2 losses, on the named files.**

## Why this one landed and ADR-1966's `+22` became `+6`

The mechanism is drift between the branch point and `main`, and there was none:
the lane branched from `c2fb0ade4`, which **was** `main`'s HEAD, so its `base`
arm and the published board were the same tree. The lane predicted this in its
report and named what could still have reduced it — another lane landing on the
same exactness-refused rows, since the board is a max and not a sum. Nothing
else landed in that window.

The generalisable form: **a lane's A/B arm transfers to `main` exactly when its
merge-base is `main`'s HEAD and nothing lands in between.** That is checkable
before the measurement, not only after it — `git merge-base` against `main` is
the whole test. It is not a property of how careful the lane was.

## UFNIA: 53, and the 47 was load

The `c2fb0ade4` board recorded UFNIA at **47** and I explicitly declined to call
that a regression, because that sweep ran single-arm at load ~10 with 12
concurrent solvers. On the quiet box — load 4 per host, one runnable process per
pinned core — it is **53**, which is exactly its own board value and exactly
what its committed census (`bench-results/ufnia-uflia-census-20260913/`) reports
as decided. **There was no regression; there was a measurement at load.**

The lesson is not "re-run when suspicious". It is that the earlier sweep's own
caveat said the small deltas were consistent with load alone, and UFNIA's −6 was
inside that band the whole time.

## Soundness

**Zero disagreements, on real coverage.** Of 1,000 rows, 573 declare a comparable
`:status` (543 `unsat`, 30 `sat`); 427 declare `unknown`. Of the 454 rows we
decided, **408 have a comparable declared status and all 408 agree**.

That coverage line is the part that matters, and it is the check ADR-1966's
verifier could not perform: its `:status` extraction piped `(set-info :status
unsat)` into `grep -oE '(sat|unsat|unknown)$'`, whose `$` anchor never matches a
string ending in `)`. It returned empty on every file, and empty was skipped, so
one of its three authorities silently contributed nothing. **A disagreement
count is meaningless without the comparable count beside it.**

25 of our 51 `sat` verdicts are on files whose declared status is `unknown` —
decided where the benchmark author left it open. Those rest on front-door model
replay against the original assertions, not on a reference.

## Cost

| division | mean wall/row | rows > 20 s |
|---|---:|---:|
| UFDTLIRA | 1.5 s | 6 / 200 |
| AUFDTLIRA | 7.8 s | 53 / 200 |
| UFDT | 8.7 s | 40 / 200 |
| UF | 11.5 s | 50 / 200 |
| UFNIA | 15.3 s | 95 / 200 |

The lane measured the conversion's cost at +0.55 s/row on UFDTLIRA and
+2.5 s/row on UFDT, *almost entirely on rows that did not move* — thirteen rungs
running on queries none of them can decide. UFDTLIRA's 1.5 s mean shows where
that lands: the division that gained most is also the cheapest, because the rows
that convert convert fast and the rows that do not are the ones paying.

## Method notes for whoever runs the next board

- **Divisions must run serially within a shard.** The first launch of this sweep
  started all five divisions concurrently on each pinned core pair, a 5x
  oversubscription that would have biased every number DOWN. Caught before any
  row was recorded; the run was discarded and relaunched.
- The waiter that watched this run **exited on its own bash arithmetic error**
  (`$(ssh … grep -c …)` returning an empty line, giving `live + 0\n0`) rather
  than on the completion condition. The banned-idiom list already carries this
  shape twice. It cost nothing here only because the row counts are on disk and
  were re-read directly — which is the actual rule: **watch the artifact, not
  the waiter.**
