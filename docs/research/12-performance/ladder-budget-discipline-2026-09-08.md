# Which routes spend a ladder's clock without deciding, and which of them cost a file

Lane `budget-discipline`, 2026-09-08. Three separate measurements that day found
the same shape by accident — a route consumes its whole slice, decides nothing,
and the file is then decided in milliseconds by something underneath it. This
note enumerates the rest deliberately, says which are wasteful and which are
earning their keep, and records the one reusable fix.

## 1. The enumeration

**Source: the committed span-log sweep**
([span-log-sweep-2026-09-08.md](span-log-sweep-2026-09-08.md)), 300 files — the
first 50 of each committed parity list in `bench-results/parity-lists/` for
`QF_ABV`, `QF_BV`, `QF_IDL`, `QF_LIA`, `QF_LRA`, `QF_NIA` — at solver commit
`049afd423`, 24 s and 8 GiB per file, one process at a time on s6 and s7. Shards:
`~/projects/personal/axeyum.com/public/data/spans/<division>.json`.

Every `route_attempt` span carries the route, its wall time, and its outcome, so
"what fraction of its slice did it take, how often did it decide, and what ran
after it" is answerable from the artifact rather than from a new sweep.

**Two caveats that change how the table reads.** A route attempt's wall clock is
a *prefix sum* — time is attributed to the next route that records — so a route
that never returns leaves its budget on whichever attempt is recorded next, or on
no attempt at all. And the sweep predates two changes landed later the same day
(the `QF_UFLIA` ladder reserve and the `QF_ABV` congruence-scan fix), so
`QF_UFLIA` is absent and two `QF_ABV` rows are now decided.

Routes that spent more than 100 ms across the sweep without deciding, ordered by
that wasted time. `recov` is the count of non-deciding attempts on files where a
LATER route did decide — the only column that says whether a reservation could
buy anything at all.

| division | route | n | decided | wasted (s) | median % of the 24 s budget | > 10% of budget | recov | after it, median |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| QF_NIA | `nia-linearize` | 50 | 2 | 487.8 | 44.6% | 47 | **1** | 1.7 s |
| QF_IDL | `dl-online` | 50 | 25 | 421.9 | 87.5% | 25 | **0** | — |
| QF_LRA | `nra` | 29 | 4 | 270.1 | 12.2% | 13 | **0** | — |
| QF_NIA | `int-blast-ladder` | 48 | 1 | 154.6 | 4.4% | 21 | **0** | — |
| **QF_ABV** | **`abv-online-cdclt`** | 47 | 24 | 121.2 | 0.0% | 5 | **18** | **168 ms** |
| QF_LIA | `lia-simplex` | 42 | 19 | 97.2 | 0.0% | 4 | 17 | 1.6 ms |
| QF_BV | `qf-bv` | 48 | 44 | 95.9 | 100.3% | 4 | 0 | — |
| QF_ABV | `array-fast-path` | 22 | 18 | 72.2 | 96.0% | 3 | 0 | — |
| QF_LRA | `dl-online` | 47 | 17 | 40.9 | 1.0% | 3 | 4 | 3.1 s |
| QF_LIA | `lia-dpll` | 18 | 17 | 24.0 | 100.0% | 1 | 0 | — |
| QF_IDL | `lia-dpll` | 14 | 0 | 12.9 | 1.9% | 1 | 0 | — |
| QF_BV | `dl-online` | 50 | 0 | 12.2 | 0.1% | 1 | 44 | 17 ms |

Plus one route with no row at all in this sweep, measured separately the same day
([nia-refinement-round-2026-09-08.md](nia-refinement-round-2026-09-08.md)):
`int-real-relax` holds **188.5 s of the `QF_NIA` population's 762.6 s (24.7%)**
and refutes **zero of 50** files, at a fixed `budget / 6` per file.

### What the `recov` column decides

**A route that never decides is not automatically wrong, and four of these are
not.** The reservation this lane builds is worth nothing unless something below
the route would have decided the file:

- **`QF_LRA/nra`** (270 s, 4 decisions of 29): nothing runs after it. Every
  route recorded below it in the trail is a string-front-door gate that declines
  in microseconds. A reserve here would be pure loss — it would shorten the only
  route with a chance.
- **`QF_IDL/dl-online`** (421.9 s, 25 decisions of 50): it **already reserves**
  `min(t/4, 6 s)` for the ladder, and on this population the ladder decides
  **zero** of the files it declines. The reserve's entire justification is one
  file outside this sample (`QF_IDL/sal/lpsat/lpsat-goal-18`, undated). Recorded
  as a finding against `DL_LADDER_RESERVE_SHARE`; **not changed**, because
  removing a reserve on the strength of a 50-file sample that does not contain
  the file it was built for is the same error in the other direction.
- **`QF_NIA/nia-linearize`** (487.8 s, 2 decisions of 50): the routes after it
  decide **one** file in the whole sweep. A reserve would cost the route that is
  doing the work to feed routes that are not. The `QF_NIA` lever is the one
  `nia-refinement-round-2026-09-08.md` names — the linearizer builds a relaxation
  its own consumer refuses on size — not a budget split.
- **`QF_NIA/int-blast-ladder`**, **`QF_BV/qf-bv`**, **`QF_LIA/lia-dpll`**,
  **`QF_ABV/array-fast-path`**: last rungs. Nothing runs after them by
  construction.
- **`QF_LIA/lia-simplex`** has 17 recoverable attempts but they carry **0.1 s**
  of the 97.2 s between them: it declines instantly on the shapes `lia-dpll`
  decides, and burns its time on files nothing else decides either. Not a
  reservation case.

**`QF_ABV/abv-online-cdclt` is the one route in six divisions where the pattern
is real and costly**, and it is the instance that was found by accident.

### The `QF_ABV` case, per file

`abv-online-cdclt` runs first on every array query and took `config.timeout` in
**full**. From the shard:

| | |
|---|---:|
| files it decided | 24 of 47 |
| its **slowest** decision | **5.723 s** |
| decisions over 1 s | 8 of 24 |
| files it spent the whole 24 s on | 5 |
| ...of those, decided by `array-fast-path` immediately after | **4** |
| that ladder's decision time on those four | **0.007 – 0.174 s** |
| slowest `array-fast-path` decision anywhere in the sweep | 2.898 s |

Those four files are `sat` today only because the harness watchdog's grace period
outlasts the budget: 24 s spent above plus a **fresh** 24 s budget below is 48 s
of a 24 s promise. Under a hard external limit they are losses.

## 2. The fix: one policy, not a fourth divisor

The tree had grown four hand-rolled copies of this arithmetic before it had a
name for it (`dl_probe_budget`, `extended_dl_probe_timeout`, `cegar_probe_budget`,
`int_real_relax_budget`), plus three more inside dispatch bodies
(`probe_budget`, `mbqi_first_refusal_budget`, `pre_lia_uf_probe_budget`, and a
bare `timeout / 2` in the quantifier retry). Each had to be found by measuring a
division.

`LadderSlice` (`crates/axeyum-solver/src/auto.rs`) is now the single policy. Two
shapes, and the distinction is the one the `QF_UFLIA` measurement paid four files
to learn ([uf-arith-overbound-2026-09-08.md](uf-arith-overbound-2026-09-08.md)):

- **`AllButReserve`** — the route keeps everything except `1/N` (optionally
  capped at a flat ceiling). For a route that decides most of what it is given.
- **`Fraction`** — the route takes `1/N` (optionally capped). For speculative
  insurance ahead of the routes that do the work.

Halving a budget is the worst of both: it starves the deciding route without
buying the ladder anything it needed.

Every share is now a named `const` with a `config_registry` entry, so "why does
this route get 18 s of a 24 s budget" is answerable by name. Nine constants were
named in the process; seven of them were literals inside an expression that no
name-keyed registry could see.

### Two policy inversions closed

`int_real_relax_budget` returned the caller's config **unchanged** — the full,
unshrunk timeout — whenever `timeout / 6` rounded to zero. So a route asked for a
sixth of the clock got all of it, at exactly the small-budget end where
starvation matters most. This was recorded as a FINDING against
`INT_REAL_RELAX_BUDGET_SHARE` in the config registry and not acted on.

Looking for a second instance of it found one: `pre_lia_uf_probe_budget` had the
identical inversion at `timeout / 10`. Both now clamp to `MIN_LADDER_SLICE`
(1 ms), which differs from the old behaviour only under 6 ms and 10 ms
respectively. That is the argument for writing a finding down rather than fixing
one site quietly.

### The ratchet

`every_route_budget_in_this_file_goes_through_the_slice_policy` derives its
population from `auto.rs`'s own source: every site that sets a route's `timeout`
must be one of the three helpers that narrow a config to the **remaining** clock,
or `LadderSlice::apply`. A fifth hand-rolled divisor fails the test at the moment
it is written, which is the only moment it is cheap to notice. The test asserts a
non-zero site count first, so a scan that stopped matching the source fails
rather than passes.

### `ABV_ONLINE_LADDER_RESERVE_SHARE = 4`

Chosen against **both** bounds the sweep gives, which is why it is neither the
largest nor the smallest defensible value:

- it leaves the online route **18 s of a 24 s budget, above every decision it
  made** in the sweep (slowest 5.723 s of 24 decisions);
- it gives the ladder **6 s, twice the slowest ladder decision** observed
  (2.898 s) and 35x its median (168 ms).

A route needing 99% of the clock is not recoverable by any reserve. `QF_UFLIA`
had one such file (`hash_uns_05_20`, 23.7 s of 24 s) and paid it as the named
cost of the same change; nothing in this `QF_ABV` population does, and
`AXEYUM_ABV_ONLINE_RESERVE=off` is the arm that measures whether one exists
outside it.

The array ladder also now runs on the **same clock**: `dispatch_array_fast_paths`
receives what is left of the dispatcher's entry deadline instead of a fresh copy
of the caller's full timeout. That is the half of the change that removes the
reliance on watchdog grace.

## 3. The A/B

Three arms over the **whole committed 200-file `QF_ABV` division list**, run
**concurrently on s6** (16 cores, otherwise idle) so contention is common-mode,
one pinned binary (`sha256 83d0e50b43fb…`), 24 s and 8 GiB per file, matching
`scripts/parity-run.sh`. Artifacts: `bench-results/ladder-budget-20260908/`.

`off` is a faithful control, not merely the reserve disabled: under it the array
ladder also keeps the caller's original config rather than the remaining
deadline. An arm that gave the online route the whole budget **and** handed the
ladder what was left of it would leave the ladder zero milliseconds — strictly
worse than the code it is a control for, which is a measurement of nothing.

### Same-binary control first

| | |
|---|---|
| decided set, `off-a` vs `off-b` | **identical**, 186 of 200 both |
| verdict disagreements | 0 |
| total wall | 714 s vs 710 s (0.6%) |

### The three arms

| arm | decided | sat | unsat | unknown | total wall |
|---|---:|---:|---:|---:|---:|
| `off-a` | 186 | 129 | 57 | 14 | 714 s |
| `off-b` | 186 | 129 | 57 | 14 | 710 s |
| **`on` (shipped)** | **186** | 129 | 57 | 14 | **627 s** |

**+0 / −0, zero disagreements.** The reserve neither gains nor loses a file on
this division, which is the safety half of the result and the half a reservation
most often fails.

### What it did change, and it is the thing the reserve was for

| | `off-a` | `off-b` | `on` |
|---|---:|---:|---:|
| runs exceeding the 24 s budget | 24 | 24 | **10** |
| ...of those, **decided** | **14** | 14 | **0** |

**Fourteen files were decided only PAST the budget they were given, and all
fourteen are now decided inside it** — each about six seconds faster, 24.2 s →
18.2 s, which is the reserve exactly: the online route stops at 18 s and
`array-fast-path` decides in milliseconds. Under the reserve **no decided file
exceeds the budget at all**; the ten runs that still do are every one of them
`unknown`, i.e. genuine search timeouts the watchdog ends.

The fourteen (all `sat`, all `dwp_formulas`/`flanagansaxe`/`wp` family except
the last):

`try3_noof_functions_dwp_md5sum.set_char_quoting`, `…dwp_ptx.bkm_scale`,
`…dwp_sum.set_char_quoting`, `try4_difret_functions_disjunctions_vdir.strmode`,
`…flanagansaxe_chroot.get_quoting_style`,
`…flanagansaxe_id.close_stdout_set_file_name`,
`…flanagansaxe_printf.get_quoting_style`, `…flanagansaxe_yes.get_quoting_style`,
`…wp_dd.advance_input_offset`, `…wp_mkdir.set_char_quoting`,
`…wp_seq.set_char_quoting`, `…dwp_env.set_char_quoting`,
`…flanagansaxe_cat.next_line_num`, `copy_array11.c`.

Under the parity protocol's 24 s wall these were counted as solved because the
harness kills at 40 s. Under a hard external limit — which is what a competition
or a CI budget is — they were losses.

**The claim this A/B does NOT support:** the reserve does not decide anything new
here. It converts "decided by grace" into "decided by budget". Whether a `QF_ABV`
file exists that the online route needs more than 18 s for is unmeasured; the
`off` arm is what would find it.

The binary used for this A/B predates the `MIN_LADDER_SLICE` correction below,
which changes only slices under a millisecond and therefore cannot touch a 24 s
run.

## 4. Two guards that could not fail, and how they were found

**The mutation discipline is the reason this section exists.** Three mutations,
each applied in an isolated worktree with a restoring trap and an anchor
assertion (so a green run cannot come from a mutation that never applied), each
run against the **whole** `--lib --features full` suite (1,609 tests, baseline
green):

| mutation | tests that died |
|---|---|
| `ABV_ONLINE_SLICE` stops reserving | **exactly 1** — `abv_online_probe_keeps_all_but_the_array_ladder_reserve` |
| a fifth hand-rolled divisor is added to the file | **exactly 1** — `every_route_budget_in_this_file_goes_through_the_slice_policy` |
| the old `share.is_zero() → return the whole budget` branch is restored | **ZERO** |

The third result is the finding. Two things were wrong, and neither would have
been visible from reading the code:

1. **The registered FINDING overstates its own reach.** It says the sharing
   policy is "bypassed silently at exactly the small-budget end where starvation
   matters most". `Duration` division is in **nanoseconds**:
   `Duration::from_millis(5) / 6` is 833 µs, not zero. `is_zero()` there needs a
   budget under **six nanoseconds**, so the band the old branch inverted on is
   six nanoseconds wide and no caller has ever been in it. The defect was
   structural, not behavioural. This lane repeated the FINDING's framing in a
   commit message before measuring it, which is the same error one level up.
2. **The first version of the fix recreated the inversion a hundred thousand
   times wider.** `want.clamp(MIN_LADDER_SLICE.min(remaining), remaining)`
   resolves, for any `remaining` under a millisecond, to
   `clamp(want, remaining, remaining)` — the route gets the entire clock and the
   ladder nothing. The floor is now capped at **half** the remaining budget, and
   the guard is written in nanoseconds, where the band it is guarding actually
   lives. Re-run: the third mutation now kills exactly one test.

A guard for a six-nanosecond band written in milliseconds is a guard that cannot
fail, and it passed review, passed clippy, and passed its own name.

## 5. The unchecked cell bound in `simplex::feasible`

`simplex::MAX_TABLEAU_CELLS` (4,000,000) is checked only in
`Incremental::new`. `feasible` — the constructor `lra::simplex_fallback` calls —
consults no cell bound at all, and was reported reaching **360 million cells** on
one file. Closing that changes default admission, so the population it would
refuse was measured first.

**Method:** an instrumented build (`AXEYUM_LRA_CELLS=1`, printing
`cells=<rows × (nvars + rows)> outcome=<…>` at every `feasible` call), the
committed 200-file `QF_LRA` list on **s7**, 24 s and 8 GiB per file. Artifact:
`bench-results/ladder-budget-20260908/cells-QF_LRA200.tsv`.

| | |
|---|---:|
| files reaching `lra::simplex_fallback` | 36 of 200 |
| total `feasible` calls | 3,129 |
| **largest tableau built** | **8,797,712 cells** (282 MB) |
| files where some call is over the 4 M cap | **7** |
| ...whose final verdict is a decision | **0** |

**One caveat, stated because it is checkable in the artifact's own header.** s7
was carrying another lane's two-process portfolio sweep throughout (`loadavg`
3.05 at start), so the seven files' `unknown` is a verdict taken under
contention, and a quieter host might decide one of them. The cell counts are
not affected — they are deterministic counts of what the program allocates, not
timings — so "seven files build a tableau over the cap" is exact and "all seven
are undecided" is the weaker of the two claims. Both point the same way here,
and the stronger one is the one the decision rests on: **a fixed 4 M cell cap
and an 8 GiB memory gate are 67x apart on the same allocation**, whatever those
seven files decide.

**Not added, and the measurement says why twice.**

- Adding the cap would refuse seven files that decide nothing today, and would
  buy nothing: nothing runs after `lra` on them, so the freed budget has no
  consumer. A completeness bound that costs seven files' worth of search and
  returns no verdict is not obviously better than the search.
- The 360-million-cell reading no longer describes this tree. `lra::simplex_admission`
  (landed 2026-09-08, same day) prices that exact allocation against
  `memory_limit_mb` **before** `feasible` is called, so the catastrophic case is
  already refused; the worst case with a limit set is 282 MB. At 8 GiB that gate
  admits 268 M cells while this constant admits 4 M — **two gates on one
  allocation, 67x apart, in different units**, which is the defect the config
  registry exists to surface rather than to paper over with a third number.

The residual gap is real and named: a caller that sets **no** `memory_limit_mb`
has nothing bounding this allocation. That is an admission-policy question with
its own ADR, not a line in a lane's diff. The measurement is recorded on the
`MAX_TABLEAU_CELLS` registry entry so the next lane starts from it.

## 6. Reproducing

```sh
# the enumeration, from the committed span shards
python3 scripts/analyze-ladder-slices.py

# the A/B: three arms, ONE host, concurrently, from one pinned binary
cargo build --release -p axeyum-bench --example smtcomp_cli
cp target/release/examples/smtcomp_cli /tmp/smtcomp_cli.pinned
for arm in off-a:off off-b:off on:on; do
  bench-results/ladder-budget-20260908/sweep.sh \
    bench-results/parity-lists/QF_ABV.txt /tmp/smtcomp_cli.pinned \
    "${arm%%:*}-QF_ABV200.tsv" "${arm##*:}" &
done; wait
python3 bench-results/ladder-budget-20260908/analyze.py off-a-*.tsv off-b-*.tsv on-*.tsv
python3 bench-results/ladder-budget-20260908/overrun.py off-a-*.tsv off-b-*.tsv on-*.tsv

# the guards, against their own removal (isolated worktree, restoring trap)
bench-results/ladder-budget-20260908/mutate.sh reserve
bench-results/ladder-budget-20260908/mutate.sh handroll
bench-results/ladder-budget-20260908/mutate.sh inversion
```

The tableau-cell sweep needs the instrumented build described in §5; the
`AXEYUM_LRA_CELLS` `eprintln!` is a two-line diff to `lra::simplex_fallback`
recorded in `bench-results/ladder-budget-20260908/lra-cells.patch` rather than
carried in the shipped source, because a permanent counter for a bound this lane
recommends NOT adding would be instrumentation for a decision already made.
