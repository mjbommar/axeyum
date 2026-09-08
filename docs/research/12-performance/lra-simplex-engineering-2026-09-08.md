# The QF_LRA simplex: what the counters said, and what they said no to

Lane `lra-simplex-engineering`, 2026-09-08. Companion to
[the theory-side diary](lra-theory-side-2026-09-07.md), which is the previous
turn on this division and whose method — **wire the counter, then look** — this
lane inherited and had to apply to itself twice.

The lane was briefed with three candidate changes, ranked by a source-level
survey of Yices and Z3: (A) a sparse cross-linked tableau, (B) a
fill-in-minimising pivot rule, (C) row-based bound propagation. It was told to
answer one diagnostic question first, because a cheap fix might make the rest
unnecessary.

The diagnostic came back **zero**. The ranking came back **inverted**. Both are
below with their numbers.

---

## 0. The short version

| question | answer |
|---|---|
| Do the `farkas` decline paths fire on the files we lose? | **No. Zero times, against 247,991 verified certificates.** The cheapest candidate fix is worth nothing here. |
| Was that measurable when the lane started? | **No** — the counter had read `n/a` on every QF_LRA file since 2026-09-07, and `n/a` looked like a stale tool rather than a dropped field. |
| Is the tableau dense enough to justify a sparse representation? | **It is 1.4% dense** — but the pivot's *operation count* was already sparse. What was dense was the scanning and the allocation, which are fixed without changing the representation. |
| Does the fill-in pivot rule help? | **Yes, and it is the whole win.** 3.45x fewer cells written per pivot; two files move `unknown` → `unsat`. |

---

## 1. The step-1 diagnostic, and the instrumentation defect under it

`Tableau::farkas` declines in three places. A decline returns an empty
certificate, which makes `rows_to_core` widen the theory's conflict core to the
**entire asserted set** — sound, and maximally coarse. If that fired often it
would produce lemmas that exclude one total assignment each, which on a search
reaching final check tens of thousands of times would look exactly like "the
simplex is slow".

`final_check_core_widenings` counts the consequence. The brief asked for it over
the QF_LRA miss population.

**It was not available.** `smtcomp_cli --trace` printed
`final_check_core_widenings=n/a` on every QF_LRA file — and had done since
`ea85c9813` (2026-09-07) moved the shipped QF_LRA route from `CdclT` to the
native proof-producing core. `native_cdclt::theory_layer_stats` ended in
`..Default::default()` under a comment saying it "does not measure" those
counters. It measures none of them, true — and it does not have to: all seven
arrive inside its own `engine: Option<TheoryEngineCounters>` argument, already
filled by `LraTheory::engine_counters`. The constructor was discarding values it
held in hand.

Why this was expensive rather than cosmetic: the eight fields *above* the gap
printed real numbers, so the line looked healthy. `n/a` is honest in the small —
it says "not measured", never "zero" — and misleading in the large, because the
day before, the same counters had real values on the same files. **An absent
number where a number stood yesterday reads as a stale tool, not as a dropped
field.** The previous lane's H2 result ("refuted, widenings = 0 on all eleven
traced files") was measured on a route QF_LRA no longer takes, and nothing in
the output said so.

The guard added with the fix is
`every_engine_counter_reaches_the_trace_line`: it destructures
`TheoryEngineCounters` with **no `..` rest**, so the field list is the struct's
and not the maintainer's memory of it, and adding a counter breaks the test at
compile time. It did — twice in this lane, exactly as intended. Mutation-checked:
forcing one field back to `None` kills that test and only that test (1,499
passed, 1 failed).

### The answer

Over the 33-file QF_LRA miss population
(`bench-results/adr-1701-slice-1-20260905/qf_lra_population.tsv`), both pivot
arms, 24 s / 8 GiB per file:

| counter | Bland arm | fill-in arm |
|---|---:|---:|
| `farkas_certificates` | 88,280 | 159,711 |
| `farkas_declined_basic_not_slack` | **0** | **0** |
| `farkas_declined_nonbasic_problem_var` | **0** | **0** |
| `farkas_declined_self_check` | **0** | **0** |
| `final_check_core_widenings` | **0** | **0** |

Every refutation on this population carries a self-verified Farkas certificate.
The three decline arms — which this lane split apart so they could be told from
one another, where before only their shared consequence was visible — fire zero
times between them.

**Do not spend effort on the `farkas` decline paths for QF_LRA.** They are
correct, and they are not reached.

### The half of the population the question cannot be asked about

22 of the 33 miss files print **no `; theory-layer` line at all**. The trace says
`watchdog fired before the worker thread returned (no CDCL(T) search on this
query completed before the deadline)`. The whole `sc/` family (11 files), the
whole `sal/` family (7), and 3 of 4 `spider_benchmarks` are in this class.

So the "simplex is slow" framing applies to **11 of 33** losses. For the other
22 the CDCL(T) search does not return inside the budget and its counters are
unreadable — the counters live inside the worker thread the watchdog abandons.
This is the same third census class the previous lane flagged as "the most
valuable thing on the board for whoever takes this next", now with a mechanism
attached: **it is not that those files are hard, it is that we cannot see inside
them.** Making the worker publish its counters on abandonment is a small change
and is the next thing worth doing on this division.

---

## 2. The pivot rule (candidate B) — the whole win

We used Bland's rule unconditionally for the entering variable. It terminates
and it pivots badly: it is indifferent to how much fill-in the pivot creates,
and fill-in sets the cost of every later pivot.

`EnteringRule::MinimiseFillIn` scores each usable candidate by its column's
nonzero count — lowest wins, ties broken by a seeded reservoir sample. That is
Z3's secondary criterion (`lp_primal_core_solver.h:183-228`, whose own comment
gives the motivation: "a short row produces short infeasibility explanation");
Yices scores by *non-free basic* variables in the column
(`simplex.c:3880-3925`) and we do not, because the plain nonzero count is
maintained in `O(1)` per written cell while the non-free count needs a column
walk per candidate per pivot.

Termination is recovered as both references recover it: a per-call count of
**repeated leaving variables**, and a switch to Bland for the rest of the call
past a threshold both independently set to 1,000, reset at the top of every
call.

### `blending/1`, one binary, arm selected by `AXEYUM_SIMPLEX_PIVOT`

| | Bland | MinimiseFillIn |
|---|---:|---:|
| verdict | unknown (24 s) | **unsat (8.6 s)** |
| `final_checks` | 1,631 | 19,050 |
| `simplex_pivots` | 24,881 | 31,226 |
| `pivot_cells_written` | 119,556,256 | 43,476,902 |
| **cells per pivot** | **4,805** | **1,392** |
| rows combined per pivot | 72.8 | 39.6 |
| cells per combined row | 66.0 | 35.2 |
| mean tableau nonzeros | 2,354 | 2,097 |

The mechanism is measured, not argued. The rule cuts the pivot's real work
**3.45x**, pays for it with more entering-scan cells (an index read against an
exact-rational multiply-add), and buys 11.7x more final checks in a third of the
time.

**Note what it does not do.** Mean fill-in barely moves — 2,354 → 2,097, 11%.
The win is *not* a sparser tableau; it is picking a pivot row that is short **at
the moment of the pivot**. That distinction is the reason section 3 reaches the
conclusion it does, and it would have been invisible without the fill-in
counter: the obvious story ("the fill-in rule reduces fill-in") is 11% true and
the actual mechanism is 3.45x.

### Miss population, 33 files

| | Bland | MinimiseFillIn |
|---|---:|---:|
| decided | 6 | **8** |
| gains | — | 2 |
| **losses** | — | **0** |
| **sat/unsat flips** | — | **0** |

Gains: `2019-ezsmt/blending/1` and `blending/5`, both unknown → **unsat**.

`bland_fallbacks` was **1** across the whole population — the terminating
fallback is live but rare, which is what a guard should look like.

One honest negative: on `miplib/pp08a-1000` cells-per-pivot went the wrong way
(4,135 → 4,388) and mean nonzeros rose (7,010 → 7,761). That file is the one the
previous lane found spends 75% of its budget in theory *propagation* offering
zero literals; the pivot rule is not its problem and did not become one.

---

## 3. The sparse cross-linked tableau (candidate A) — reframed, not refuted

The brief ranked this first, on our own source's record of a 350 x 425 tableau at
1.41 ms per pivot. The counters say the diagnosis was right and the **remedy was
aimed at the wrong half**.

The tableau is **1.4% dense**: 2,097 nonzeros in 148,750 cells, about 6 nonzeros
per row. But the pivot's inner loop already visited only the pivot row's nonzero
columns (`base_nz`), so its *operation count* was already sparse — 1,392
multiply-adds per pivot, not 148,750. What was dense was everything around it:

| dense cost, per pivot | before | fixed by |
|---|---|---|
| entering scan over all `n` columns | 425–684 cell reads | a sorted per-row nonzero index |
| `base_nz` filter over all `n` columns | 425 | the same index |
| `new_row = vec![zero; n]` allocate + zero-fill | 13.6 KB | rewriting the row in place |
| `self.row[r].clone()` | 13.6 KB | copying ~35 values by index |

None of these needed a representation change. `row_nz[i]` — the sorted column
indices where row `i` is nonzero — is a sparse **index over dense storage**:
`row[i][v]` stays an `O(1)` random access, which `farkas`, the value repair and
every existing test rely on, so it has no soundness surface at all.

Measured on `clock_synchro/clocksynchro_2clocks`, a file that **decides** (so the
counters are not a function of how much budget elapsed):

| counter | before | after |
|---|---:|---:|
| `simplex_pivots` | 65 | 65 |
| `final_checks` | 30 | 30 |
| `pivot_cells_written` | 6,239 | 6,239 |
| `leaving_scan_rows` | 8,184 | 8,184 |
| `fill_nnz_sum` | 26,652 | 26,652 |
| **`entering_scan_cells`** | **22,842** | **604** |

Every counter byte-identical except the one the change targets, which falls
37.8x. On `blending/1` the same identity holds (19,050 final checks, 31,226
pivots, 43,476,902 cells written in both arms) with `entering_scan_cells` down
11.1x and `theory_final_check_ms` 7,945 → 4,722.

**What is left for a real sparse representation**, and it is a smaller and
better-defined thing than the brief assumed: the row *storage* is still
350 x 425 x 32 B = 4.76 MB where the live data is ~50 KB, so a pivot's scattered
reads across 13.6 KB rows are a cache argument, not an operation-count one. That
is worth doing and worth measuring, but it is not the 40x the density ratio
naively suggests, because the operations were never dense. Anyone picking this
up should predict a cache effect and be ready to measure a small one.

Also still open, and independent: the **violated-basic priority heap**
(§4.3 of the survey). `leaving_scan_rows` is unchanged by anything here and the
main loop still rescans from row 0 every iteration. The counter is now in the
trace line, so it is a measurement away from being costed.

---

## 4. Cumulative

`QF_LRA/2019-ezsmt/blending/1.smt2`: **unknown at 24 s → unsat in 5.1 s.**

Across three commits, with every arm run from one binary under the
`AXEYUM_SIMPLEX_PIVOT` lever so no comparison is confounded by a rebuild.

## 5. What was built, and where the knobs are

- `PivotPolicy` (`simplex.rs`) — every constant a named documented field
  carrying the reference it came from; `PivotPolicy::bland()` keeps the previous
  behaviour runnable, because a baseline you cannot still run is a remembered
  number. `Incremental::with_policy` is the A/B seam.
- `AXEYUM_SIMPLEX_PIVOT=bland|<threshold>` — read once into a `OnceLock` (the
  `nra.rs` precedent), so an A/B is one binary and two runs.
- `TableauCounters` — eleven clock-free counters, every one derived from a
  quantity the pivot already computes (a vector length, a loop bound, a branch
  it already took), so they cost at most one integer add per **row** and can be
  on in the shipped build. Instrumentation behind a feature flag is not there at
  the moment somebody needs it.

### The soundness argument, in one sentence

Both entering rules draw from one candidate-set predicate
(`entering_is_usable`) and a rule may only *order* that set — which matters
because `run` reads `select_entering(..) == None` as "this row is unrepairable"
and hands the row to `farkas`, so a rule that returned `None` with a usable
candidate available would manufacture a wrong `unsat`.
`every_rule_agrees_on_whether_a_row_can_be_repaired` pins it over 400 random
systems and asserts coverage in three directions: repairable rows reached,
unrepairable rows reached, and the two rules actually **choosing differently**
somewhere — without that last assertion the test would pass against a rule that
is secretly Bland's.
