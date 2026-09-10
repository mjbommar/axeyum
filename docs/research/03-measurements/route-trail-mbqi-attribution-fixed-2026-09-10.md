# The route trail now charges MBQI its own seconds — what moved, and which published numbers move with it

Measured 2026-09-10 on `s4`, `taskset -c 0-7`, 4-wide, budget 24 000 ms, both
arms run back to back from the same script on the same box. Implementation:
ADR-1906, commits `43cfae068` (decision) and `72a5adf6f` (fix). Population: the
32 files in
[`bench-results/parity-losses-20260908/UF.txt`](../../../bench-results/parity-losses-20260908/UF.txt).
The NAS mount was live; nothing here reproduces without it.

**In one line: the defect moved 16.8 points of clock from `q:mbqi` onto
`q:uf-fmf-full`, and the three-rung total is byte-for-byte the same before and
after — 55.2% in both arms — so the fix redistributed and did not create.**

## What the defect was

`RouteTrace` charges a segment to whoever records **next**. The quantified
ladder's terminal arm records the full MBQI pass **last**, deliberately, so MBQI
owns the trail's final word instead of a declined finite-model probe. The
deferral therefore deferred the cost as well: `q:uf-fmf-full`'s segment spanned
MBQI's entire pass, and `q:mbqi` read ~5 **microseconds** on every file.
`bound_by=q:uf-fmf-full` meant "MBQI plus the finder", never the finder alone.

Why it was not a one-line fix, and the design that resolves it, are in
[ADR-1906](../09-decisions/adr-1906-a-route-trace-segment-cost-is-movable-a-rung-verdict-is-not.md).

## The measurement

Both arms, same 32 files, same script, minutes apart. The denominator is the sum
of every recorded attempt's `elapsed_ns`, stated rather than implied.

| | pre-fix | post-fix |
|---|---:|---:|
| `q:egraph` | 169 981 ms · 38.3% | 174 970 ms · 38.4% |
| `q:uf-fmf-probe` | 118 595 ms · 26.8% | 121 759 ms · 26.7% |
| **`q:uf-fmf-full`** | **126 142 ms · 28.5%** | **53 176 ms · 11.7%** |
| **`q:mbqi`** | **0 ms · 0.0%** | **76 566 ms · 16.8%** |
| `q:mbqi-quick` | 27 232 ms · 6.1% | 26 847 ms · 5.9% |
| `q:forall-exists-witness` | 1 166 ms · 0.3% | 1 662 ms · 0.4% |
| denominator | 443 342 ms | 455 266 ms |

### The total is the check, and it holds to one decimal place

`q:uf-fmf-probe + q:uf-fmf-full + q:mbqi` reads **55.2% in both arms**. The three
rungs' combined share did not move; 16.8 points moved *within* it, from the
finder to MBQI. That is the strongest available evidence that the take/re-attach
pair is a **move** and not a copy — the failure mode a per-rung reading cannot
see is double-counting, and double-counting would have inflated this total.

### Coverage against an independent denominator

Lane U1 correctly called instrument A's self-coverage figure vacuous: the route
summary's `total_ms` **is** `RouteTrace::total_elapsed()`, so checking one
against the other cannot fail. The check below is not that. The denominator is
the **process wall clock measured by the shell**, outside the binary:

| | pre-fix | post-fix |
|---|---:|---:|
| trail total | 443 342 ms | 455 266 ms |
| process wall, the 24 files that emit a trail | 444 851 ms | 458 254 ms |
| **coverage** | **99.7%** | **99.3%** |

The trail accounts for essentially the whole solve on any file that finishes far
enough to print one, before and after. Nothing was lost by taking a segment and
nothing was created by giving it back.

(8 of the 32 are killed by the watchdog before the `; route-trail` line is
printed and contribute wall with no trail. Against all 32 files' wall the ratio
is 68.4% pre-fix and 68.9% post-fix — that gap is the watchdog, not the
instrument, and it is why the 24-file denominator is the one to read.)

### Verdict invariance — confirmed, not asserted

**3 of 32 decided in both arms, and the same three: `f05`, `f26`, `f27`.** That
matches what `main` decides after the deferred-pool release (`c35941f9b`). This
was an instrument change; the ladder is untouched.

### `bound_by` — the field this fixes

| `bound_by` | pre-fix | post-fix |
|---|---:|---:|
| `q:egraph` | 10 | 11 |
| `q:uf-fmf-probe` | 8 | 8 |
| `q:uf-fmf-full` | **6** | **2** |
| `q:mbqi` | **0** | **3** |

On three files the binding route was MBQI all along and the trail named the
finder. `bound_by` is the field an undecided file is read by.

## Ground truth for the split, established three ways

The A/B above shows a quantity moving between two labels. It does not by itself
say which label is right. Three independent readings on the nine committed
`uflia_induction` files that reach this arm — small enough to run in a test
suite, and the same population the new guards use:

| file | pre-fix `q:mbqi` | pre-fix `q:uf-fmf-full` | post-fix `q:mbqi` | post-fix `q:uf-fmf-full` | `AXEYUM_QTRACE` mbqi |
|---|---:|---:|---:|---:|---:|
| `guarded_false_base` | 0 ms | 50 ms | 46 ms | 0 ms | 46 ms |
| `guarded_false_step` | 0 ms | 31 ms | 31 ms | 0 ms | 31 ms |
| `guarded_linear_closed_form` | 0 ms | 341 ms | 344 ms | 0 ms | 337 ms |
| `guarded_linear_nonneg` | 0 ms | 352 ms | 359 ms | 0 ms | 350 ms |
| `guarded_monotone_step` | 0 ms | 239 ms | 241 ms | 0 ms | 233 ms |
| `guarded_parity_range` | 0 ms | 251 ms | 254 ms | 0 ms | 252 ms |
| `guarded_wrong_slope` | 0 ms | 31 ms | 31 ms | 0 ms | 31 ms |
| `unguarded_int_even_or_odd` | 0 ms | 453 ms | 455 ms | 0 ms | 435 ms |
| `unguarded_recurrence_nonneg` | 0 ms | 189 ms | 190 ms | 0 ms | 183 ms |

The last column is a **genuinely separate instrument**: `AXEYUM_QTRACE`
checkpoint stamps on stderr, differenced consecutively, with no `RouteTrace`
involvement. It agrees with the post-fix `q:mbqi` column to within a few percent
on every file, and it equals the pre-fix `q:uf-fmf-full` column. So the quantity
that used to be labelled `q:uf-fmf-full` was entirely MBQI's, and the fix put it
where the independent instrument already said it belonged. Verdicts were
identical in both arms on all nine.

## The guards, and the mutations that kill them

Two integration guards in
`crates/axeyum-solver/tests/quantified_route_trace.rs`, plus two unit tests on
the primitive in `route_trace.rs`. Both integration guards assert a **minimum
population first**, so a shrunken corpus fails instead of quietly passing.

Two mutations were run, each the realistic wrong implementation, each on a
committed tree and reverted afterwards. **Each kills exactly one test, and they
kill different ones:**

| mutation | what it models | dies | survives |
|---|---|---|---|
| keep the take, record MBQI through the plain sink | the old ordering | `the_full_mbqi_rung_is_charged_its_own_wall_clock` | the other 5 |
| caller-measured `Instant`, **no** take | the obvious half-fix, which double-counts | `the_finder_keeps_only_its_own_segment` (overcharged by 152–2 639 ms on 8 files) | the other 5 |

The second is the one worth having. A fix that hands MBQI an explicit duration
without taking it off the running clock passes every per-rung assertion and
silently inflates `total_ms` — the denominator every published share divides by.
That failure is invisible per rung and visible only in the total.

## Which published numbers move

The full sweep of the tree is in the ADR's consequences section; the outcome is
that **four documents publish instrument-A quantified-ladder clock, and two
numbers were live and wrong.** Both are corrected in this commit.

### The 56.2%

[`instantiation-strategy-gap-2026-09-10.md`](instantiation-strategy-gap-2026-09-10.md)
Finding 5 published **56.2%** as "the share of the UF budget going to SAT-side
rungs that cannot produce `unsat`", computed as `q:uf-fmf-probe + q:uf-fmf-full`
off the pre-fix trail. That row of the same document's own Method section states
the defect, 120 lines above the number.

Re-derived here on the **same instrument and the same population**, so the
comparison is like for like:

| | pre-fix instrument A | post-fix instrument A |
|---|---:|---:|
| `q:uf-fmf-probe + q:uf-fmf-full` | **55.2%** | **38.4%** |

55.2% reproduces the published 56.2% to within a point (different day, different
load), and the corrected reading is **38.4%**. The 16.8-point difference is
exactly `q:mbqi`'s share.

### Why this is not "52.4% was also wrong"

Lane U1's [`where-the-uf-clock-goes-2026-09-10.md`](where-the-uf-clock-goes-2026-09-10.md)
corrected 56.2% to **52.4%** using instrument **B** (`AXEYUM_QTRACE`
differences), which already separated MBQI and was therefore never contaminated
by this defect. 52.4% is a valid figure for the run it was taken on. It differs
from the 38.4% here mostly in the **probe** term (42.4% there, 26.7% here) — a
rung this fix does not touch at all — so the gap is between-run and
between-denominator variation, not a second error. **Do not present 38.4% as a
correction of 52.4%.** The claim this note supports is narrower and stronger:
on one instrument, one population, one afternoon, the finite-model share reads
55.2% before the fix and 38.4% after.

Both figures now carry the same caveat, which is the real lesson: **a rung share
is only meaningful against a stated denominator and a stated run.** Three
numbers (56.2, 52.4, 38.4) that look like successive corrections of one quantity
are three measurements of three slightly different quantities.

## What did NOT get verified — reported as "did not run"

ADR-1906 also fixes a second defect at the same site: the `q:uf-fmf-full`
decline record sat outside the `matches!(other, Unknown)` guard, so an MBQI
`unsat` — which reaches the same arm and skips the finder entirely — still
emitted a `q:uf-fmf-full declined` entry for a rung that never executed.

**That path is unexercised by every population available here.** Across the
32-file post-fix sweep, `q:mbqi` is recorded `declined` on all 18 occurrences and
`decided` on none; the positive control is `q:mbqi-quick` in the same logs, which
shows 3 `decided` and 29 `declined`, so the query does match `decided` when it
occurs. The nine `uflia_induction` files are the same. The terminal MBQI rung
never refutes on anything reachable, so the fix is argued from the source and
**not** confirmed by measurement, and no guard is written for it — a guard that
cannot fail on any input we have is worse than none.

## Still open

`q:egraph` records `DeclineReason::NotApplicable` rather than the instantiation
loop's own `UnknownReason`, so the trail cannot distinguish "the e-graph was not
applicable" from "the e-graph saturated". That is the second of the two
recording defects named in `instantiation-strategy-gap-2026-09-10.md`'s
recommendations. It is a decline-*vocabulary* question, it moves no clock share,
and it is untouched here.

## Reproducing

```sh
scripts/cargo-serialized.sh build --release -p axeyum-bench \
  --example smtcomp_cli --features axeyum-solver/full
# per file, 4-wide, pinned:
AXEYUM_TRACE=1 taskset -c 0-7 target/release/examples/smtcomp_cli \
  "$f" --timeout-ms 24000 --trace
```

The per-rung aggregate is the sum of `elapsed_ns` per `route` over the
`; route-trail` JSON line; `bound_by` / `total_ms` come from the `; route` line
above it. The independent cross-check is `AXEYUM_QTRACE=1` with consecutive
differencing — and note that `qtrace`'s top-level rungs stamp **cumulative**
seconds from one `t0`, while `mbqi-quick` and `nat-induction` carry their own
`Instant` and are also inside the next cumulative difference. Mixing the two
conventions is what made an earlier parser read 247% coverage.

Gates run for this change, each with a nonzero count confirmed:
`--test quantified_route_trace` 6, `--test route_attribution` 8,
`--test route_trace` 12, `--test quant_skolem_egraph_routing` 1,
`--test corpus_regression` 2, `--lib --features full` 1 695,
workspace `clippy --all-targets --all-features -D warnings` exit 0,
`cargo fmt --all --check` exit 0.
