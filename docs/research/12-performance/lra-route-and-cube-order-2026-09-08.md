# The extra rounds bought almost nothing, and 97% of the budget went to an elimination that never once succeeded

**Date:** 2026-09-08 · **Population:** the 22 `QF_LRA` files bound by the
lazy-SMT route (`bench-results/watchdog-blind-files-20260908/qf_lra_blind22/`)
· **Machine:** s5 (idle, 16 cores, `taskset -c 0-7`), 24 s budget, serial
· **Artifacts:** `bench-results/lra-route-encoder-20260908/`

The Farkas fix removed the second LP per round and bought 1.63x the refinement
rounds in the same wall clock. Three files decided; nineteen still exhausted
24 s. This is what the extra rounds bought, and why the loop does not converge.

## The step-1 reading

Instruments added for this: `cube_flips` / `cube_identical` (Hamming distance
between consecutive cubes), `cube_collect_ms` / `cube_fm_ms` /
`cube_fm_declines` / `cube_simplex_ms` / `cube_simplex_calls` (the conjunctive
decider split into the stages it actually has), and `online_probe` (which of
seven declines put the file on this route at all). All opt-in; off, each site is
one thread-local `bool` read.

`scripts/lra-lazy-report.py bench-results/lra-route-encoder-20260908/instr_legacy_a`
prints the table. Three readings, in the order they change what to do:

### 1. Every one of the 22 is on this route because of ONE missing encoder arm

`online_probe=skeleton-unsupported` on 22 of 22. Not the admission screen, not
memory, not the atom count. The online CDCL(T) engine — the one with an
incremental simplex in lockstep with the search, theory propagation and
conflict-driven learning — declined the whole query before building anything,
because `lra_online::Encoder::encode_app` had no arm for **Boolean equality**
(`(= p q)` at `Sort::Bool`), and these are `sc/`, `sal/` and
`spider_benchmarks/` files translated from CVC where `iff` is everywhere.

The offline abstractor in `dpll_t.rs` has covered that shape since it was
written (`Op::Eq if arena.sort_of(args[0]) == Sort::Bool`). **The two halves of
one route disagreed about the input language**, and the weaker half silently
took every query the stronger half could not parse.

`dl_online` hit the same gap on the `fischer` family and worked around it
locally — `bool_eq_gates`, a post-order pre-pass whose comment reads "The
skeleton encoder has no `Eq` case, so these carry their own `XNOR` gate rather
than making the query fall through". The workaround was written; the encoder was
not fixed; `QF_LRA` had no workaround.

### 2. The rounds are not exploring — successive cubes differ in 1 to 4 literals

| | atoms | mean `cube_flips` |
|---|---|---|
| `tgc_io-safe-20` | 1,409 | 1.6 |
| `sc-25.base.cvc` | 1,736 | 1.3 |
| `pursuit-safety-16` | 1,444 | 4.2 |
| `gasburner-prop3-9` | 300 | 2.7 |

`cube_identical` is 0 everywhere, so no clause failed to reach the skeleton
solve. But round *n+1* differs from round *n* in **one to four of up to 1,736
atoms**, and the loop pays a complete cold conjunctive decision for that
one-literal step. The mean learned core is 2.0–2.3 literals on 13 of 19 files
and `cores_full_assignment` is 0 everywhere, so the lemmas are as strong as a
non-unit lemma gets — the loop is learning binary theory clauses. It is learning
them at 2 to 20 per second against a state space of 2^1736.

So the answer to "is the blocking clause too weak, is the same region being
re-explored, or is the theory conflict not minimal" is **none of the three**.
The cores are minimal, the clauses are binary, and the region moves — by one
atom per 250 ms to 3 s.

### 3. Fourier–Motzkin consumed 96–99.9% of the budget and decided 0 of 2,745 cubes

The stage split is the finding:

| file | rounds | `theory_ms` | `cube_fm_ms` | `cube_simplex_ms` | FM declines | simplex calls |
|---|---|---|---|---|---|---|
| `tgc_io-safe-20` | 8 | 23,679 | **23,442** | 138 | 8 | 8 |
| `sc-25.base.cvc` | 33 | 23,681 | **23,047** | 373 | 33 | 33 |
| `sc-5.base.cvc` | 253 | 23,312 | **22,923** | 270 | 253 | 253 |
| `gasburner-prop3-12` | 404 | 22,360 | **21,464** | 696 | 404 | 404 |
| `tgc_io-nosafe-4` | 93 | 23,734 | **23,666** | 43 | 93 | 93 |

`cube_fm_declines == cube_simplex_calls == rounds` on **every file**. The
conjunctive decider (`lra::decide_within`) runs Fourier–Motzkin first and the
exact-rational simplex only as its fallback. Across the whole population that is
**2,745 eliminations, 2,745 declines, a 0% success rate** — each one spending
250 ms to 3 s of exact-rational cross products before reaching
`MAX_FM_CONSTRAINTS` — and the simplex then decided every one of those same
cubes in 43 to 696 ms *in total per file*.

This is a larger waste than the Farkas double-solve it sits behind: that was
48.6% of the budget, this is 96–99.9% of what remained.

## The three changes

All three are fields of `lra_route::LraRoutePolicy` with a
`LraRoutePolicy::legacy()` arm reproducing the pre-2026-09-08 behaviour exactly,
selected by `AXEYUM_LRA_ROUTE`, so an A/B is one binary and two runs.

1. **`SkeletonEncoding::bool_eq`** — the online skeleton encoder covers Boolean
   equality. `SkeletonEncoding::legacy()` does not.
2. **`fall_through_on_cheap_decline`** — a probe decline that consumed none of
   the budget falls through to the offline loop instead of ending the query.
   Without this, widening the encoder would send the eight files above the
   1,024-atom admission screen from "24 s of offline search" to "instant
   `unknown`" — a wall-clock improvement that is a capability loss.
3. **`simplex_first_at_constraints`** (`SIMPLEX_FIRST_AT_CONSTRAINTS = 256`) —
   at or above 256 collected constraints the simplex decides the cube first and
   Fourier–Motzkin becomes its fallback. `usize::MAX` is the old order.

### Why the third is a threshold and not a swap

Both engines are sound and each declines on cases the other decides, so whichever
runs first the other gets the identical system, and the order cannot change a
verdict. It can change the *certificate*: elimination is exact, so on a small
system it produces the tightest refutation. Setting the threshold to 0 moved
`nra_handelman_cert`'s pinned residual from `−31/400` — a number the test's
comment derives by hand — to `−31/1580`. The bound therefore sits at the bottom
of the measured range: 265 is the smallest system in the population where FM was
observed to fail, and **nothing has measured its success rate below that**.

## The A/B

Base is `AXEYUM_LRA_ROUTE=legacy` through the same binary, so the arms differ in
the policy and in nothing else.

Four arms through **one** binary, s5 idle, `taskset -c 0-7`, 24 s, serial.
`arm_legacy` is the same-binary control and reproduces the base run exactly —
3 `unsat` / 19 `unknown`, the same three files.

| arm (`AXEYUM_LRA_ROUTE`) | decided | total wall |
|---|---|---|
| `legacy` — the whole pre-2026-09-08 behaviour | 3/22 | 476,303 ms |
| `cube-order-only` — simplex first, nothing else changed | 7/22 | 376,588 ms |
| `fm-first` — encoder + fall-through, old cube order | 8/22 | 306,136 ms |
| default — all three | **9/22** | 300,421 ms |

Per file, wall clock in ms (`u` = `unknown`):

| file | legacy | cube-order | route | all |
|---|---|---|---|---|
| `Carpark2-ausgabe-8` | u 24,230 | u 13,819 | u 208 | u 207 |
| `gasburner-prop3-12` | u 24,129 | u 24,127 | **unsat 6,011** | **unsat 6,412** |
| `gasburner-prop3-9` | u 24,128 | u 24,125 | **unsat 506** | **unsat 507** |
| `pursuit-safety-16` | u 24,331 | u 24,128 | u 24,330 | u 24,129 |
| `pursuit-safety-5` | u 24,130 | **unsat 4,810** | **unsat 207** | **unsat 207** |
| `tgc_io-nosafe-4` | u 24,130 | **unsat 907** | **unsat 106** | **unsat 107** |
| `tgc_io-safe-20` | u 24,429 | u 24,129 | u 5,011 | u 6,112 |
| `sc-5.base.cvc` | u 24,129 | **unsat 11,817** | u 24,130 | **unsat 17,523** |
| `sc-7` … `sc-25` (9 files) | u ~24,130 | u ~24,100 | u ~24,150 | u ~24,100 |
| `frame_prop.base` | unsat 3,810 | unsat 1,208 | unsat 1,208 | unsat 1,308 |
| `fs_not_sc_seen.base` | unsat 3,009 | unsat 1,310 | unsat 1,308 | unsat 1,409 |
| `no_op_accs.base` | unsat 10,016 | unsat 1,508 | unsat 1,307 | unsat 1,408 |
| `reint_to_least.base` | u 24,130 | **unsat 4,010** | **unsat 207** | **unsat 207** |

**Zero disagreements.** No file is decided differently by any two arms, and
every one of the nine decided verdicts matches the benchmark's own
`(set-info :status unsat)`. The three files that already decided are 2.9-7.6x
faster.

The two changes are largely independent, because they act on different halves:
the routing moves a file onto the online CDCL(T) engine, and the cube order
makes the offline loop 20-50x faster for the files that stay on it. Four files
from the order alone, five from the routing alone, six together.

### Where the budget goes now

Same instrument, default arm. `cube_fm_ms` is **0** on every file that still
runs the offline loop, and `theory_ms` has gone from 96-99% of the budget to
16-58% of it, with the propositional half now the larger share on the smaller
files:

| file | rounds (legacy → all) | `theory_ms` | `cube_fm_ms` | `cube_simplex_ms` | `skeleton_ms` |
|---|---|---|---|---|---|
| `sc-7` | 255 → **1,447** | 4,633 | 0 | 3,718 | 19,031 |
| `sc-13` | 86 → **1,027** | 9,614 | 0 | 7,808 | 12,881 |
| `sc-19` | 49 → **764** | 14,060 | 0 | 11,730 | 9,206 |
| `sc-25` | 33 → **328** | 11,358 | 0 | 9,689 | 3,623 |
| `pursuit-safety-16` | 29 → **394** | 13,602 | 0 | 12,170 | 3,422 |

5.7x to 13.6x the refinement rounds, and the mean learned core width rises with
them (2.2 → 3.3-32.1), so the extra rounds are buying wider lemmas rather than
repeating the narrow ones.

### The next lever, named by the instrument rather than inferred

Twelve of the thirteen files that still lose print
`online_probe=model-did-not-replay`. The online CDCL(T) engine now **parses
these files, searches them, and reaches a satisfying Boolean assignment** — and
then `LraTheory::real_model()`'s reconstruction fails to replay against the
original assertions, so it declines a decision it had in hand and hands the
query back to the offline loop. That is a different defect from either of the
two this lane fixed, and it is where the whole `sc/` family now sits.

`Carpark2-ausgabe-8` and `tgc_io-safe-20` are not that shape: both are mixed
`{real,int}` files on the `coercion-relax` route, whose verifier rejects the
relaxed candidate against the original int↔real coupling. Their verdict is
`unknown` in every arm; what changed is that the relaxation now produces a
candidate in 80 ms instead of never producing one in 24 s.

## Composed with the memory-watchdog lane

This branch and the `--memory-limit-mb` lane (`f833198a3`, `79a7c5297`,
`8cfe1fd6e`) both rewrote `lra::decide_within`, and the merge is worth reading
because the resolution is better than either side.

That lane found three `QF_LRA` files reaching **26.6 GB under an 8 GiB flag**
and named the cause: `decide_within` tags every collected constraint with a
dense unit multiplier vector before Fourier–Motzkin runs — an `n x n` matrix of
`Rational`, `32*n^2` bytes — which `MAX_FM_CONSTRAINTS` never bounded because it
prices the *derived* system inside `eliminate`, i.e. after the runaway. Their
fix prices it up front (`fm_admission`) and refuses.

This lane found that the elimination that matrix exists for decides **nothing**
on this population.

Put together, the `simplex_first` check goes **above both** `fm_admission` and
the tagging loop. When it fires, the largest allocation on the route is not
merely priced — it is never made. Neither lane wrote that ordering; it falls out
of the two together. Their gate still guards the path that does run, and
`simplex_admission` is checked before the simplex-first arm for exactly the
reason their second commit exists (the simplex's own dense
`n x (nvars + n)` tableau was the *second* unpriced matrix).

Three details the merge had to get right, none of them textual:

1. **No double solve.** With the simplex-first arm above it, the
   `fm_admission`-refusal branch and the `Feasibility::TimedOut` arm would each
   call `simplex_fallback` a second time on the identical system. Both are now
   guarded on `stages.simplex.is_none()` — the same shape as the 48.6%-of-budget
   double solve removed from `dpll_t` earlier the same day.
2. **`Feasibility::OutOfMemory` is untouched**, including its comment on why the
   simplex retry is deliberately not attempted after a memory decline. It is
   also not an FM *decline* in the counter's sense: it hands the cube to nobody.
3. **A `MemoryLimit` decline does not fall through.** This lane's
   `fall_through_on_cheap_decline` sends a probe decline that spent none of the
   budget to the offline loop. A memory decline is sticky and means the *process*
   is over budget, so falling through would start a second full search with
   nothing left to spend — the same reasoning as their `OutOfMemory` arm.
   `dpll_t` now ends the query on `UnknownKind::MemoryLimit` whatever the policy
   arm says.

### Re-measured after the merge, on the merged tree

The A/B above was taken before the merge, so it is a statement about a tree
nobody will run. Both decisive arms were re-run through a binary built from the
merge commit — s5, `taskset -c 0-7`, 24 s, serial, load 4.1-5.0 (**not** the
idle host the first run had; the wall-clock totals are therefore not comparable
to it, and the decided counts are what this run is for).

| run | decided | total wall |
|---|---|---|
| `arm_legacy` (pre-merge control, idle) | 3/22 | 476,303 ms |
| `merged_legacy` (post-merge control, load ~4.5) | 3/22 | 477,430 ms |
| `arm_all` (pre-merge default, idle) | 9/22 | 300,421 ms |
| `merged_all` (post-merge default, load ~4.5) | **9/22** | 295,615 ms |

The two legacy controls land 0.24% apart on wall clock and decide the same three
files, so the merge moved nothing on the baseline. The default arm decides the
same nine, and **no file's verdict changed between the pre- and post-merge
runs**. Still zero disagreements across all four runs, and every decided verdict
still matches the benchmark's own `(set-info :status unsat)`.

The memory lane's `fm_admission` and `simplex_admission` gates therefore do not
refuse anything on this population at the default budget — which is the result
that had to be checked, since a gate that refused here would have taken the gain
back without changing a single verdict.

### The ordering is pinned by a test, not by a comment

`lra::cube_order_tests` asserts on the counters, because the verdict cannot see
the difference: moving the simplex-first arm below the tagging leaves the answer
identical *and* leaves the elimination unrun, so `cube_fm_ms` alone does not
catch it. `cube_matrices` — incremented at the tagging loop itself — does.

**Mutation control, run:** moving the arm below the tagging took the
`-p axeyum-solver --lib --features full` sweep from `1622 passed; 0 failed` to
`1621 passed; 1 failed`, and the one failure is
`a_large_system_is_decided_without_entering_fourier_motzkin` on its
`cube_matrices` assertion. The below-threshold test is the positive control: it
requires `cube_matrices == 1`, so the pair cannot both pass by counting nothing.

## Reproducing

```sh
scripts/cargo-serialized.sh build --release -p axeyum-bench --example smtcomp_cli
AXEYUM_SWEEP_BIN=<binary> AXEYUM_LRA_ROUTE=legacy \
  scripts/trace-sweep.sh <file-list> <out-dir> 24
scripts/lra-lazy-report.py <out-dir>
```
