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

<!-- A/B RESULTS -->

## Reproducing

```sh
scripts/cargo-serialized.sh build --release -p axeyum-bench --example smtcomp_cli
AXEYUM_SWEEP_BIN=<binary> AXEYUM_LRA_ROUTE=legacy \
  scripts/trace-sweep.sh <file-list> <out-dir> 24
scripts/lra-lazy-report.py <out-dir>
```
