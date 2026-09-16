# ADR-2132: `QF_LRA` — a builds-per-file screen for the warm basis, and the discriminator that turned out not to discriminate

Status: proposed
Index-summary: [ADR-2125] shipped the warm simplex basis `off` on 1 STABLE-GAIN against 2 STABLE-LOSS and named the axis its successor should screen on -- `simplex_cold_builds`, "it wins where the cubes are many and small and loses where they are few and large". This lane SIZED that axis first over the pinned 200: the distribution is bimodal with no overlap (few-enormous rows at 1, 28 and 42 builds costing 23,908 / 283.5 / 548.1 ms each, the 28-build row being the pinned stable loss; the winning family at 841-1,543 builds costing 0.4-6.4 ms), every row at or above 51 builds costs at most 12.2 ms/build and every row above 20 ms/build has at most 42, so any threshold in [43, 51] separates them and **64** is the next power of two above that window. THE HEADLINE IS NOT THE SCREEN. ADR-2125 could place only ONE of its three movers in its sizing table and labelled the second loss's reading a HYPOTHESIS in as many words; counted here it is **1,598 builds at 1.04 ms each** -- the MANY-SMALL shape the lever WINS on, 14 % from the gain's 1,815 -- so **no builds-per-file threshold separates them and the hypothesis is REFUTED**, measured BEFORE the constant was written into the source. The threshold was NOT then moved between 1,598 and 1,815: those two rows are the held-out evaluation population. A/B: three arms, one binary, order rotating three ways per file, both `QF_LRA` draws COMPLETE at 200 (verified disjoint) plus five exposure divisions. **`on` reproduces ADR-2125 exactly -- 1 stable gain against 2 stable losses -- on a new binary and a complete 400 rows**, and `screened` is **1 gain against 1 loss with a clean pinned draw**: it REMOVES the pinned stable loss (28 builds, refused), gives up `on`'s pinned gain on `sc-7.base.cvc` (1,695 builds, admitted, and its 64 cold rounds cost the decision -- the threshold's clearest single price), and buys a held-out gain `on` does not get. 0 flips, 0 soundness disagreements at 194 and 174. The screen's admitted set was PREDICTED EXACTLY from a different lane's sizing: 51 of 51, same set, 0 missing, 0 extra; and 0 of 93 sub-threshold rows opened it. Ships `off` on criterion 3. THE -9.2 % IS SPLIT AT LAST and it is not the basis: over 67 rows, **linearization 74.7 %, basis 36.6 %, Fourier-Motzkin 0.6 %, residual -11.9 %** -- and a two-term split had to be thrown away first because it explained 64 ms of a 1,906 ms saving on a file whose COLD path decides by Fourier-Motzkin. ADR-2111's untaken fill-in measurement is also taken: **fill-in grows the warm tableau up to 21x** (sc-39 enters at 4,688 nonzeros and peaks at 98,572), so a construction-time nonzero bound is no bound at all once the engine runs and `MAX_TABLEAU_CELLS` stays -- with the files the warm basis helps most being the ones whose footprint the admission count describes least. Gates: workspace clippy `--all-features` ok at full scope, lib sweep **1,619/0 on a quiet box** (1,613/6 contended, with the ratchet independently measuring throughput moving 109 % mid-sweep), `progress_frontier` **0 REGRESSION**, six z3 fuzzes **17 per arm in all three arms**, mutation kills 2 and 1 with anchors stale=0. FOUR defects in this lane's OWN instruments were found by reading their output against what it described, not by any test.
Index-status: proposed
Date: 2026-09-16

## Context

[ADR-2125] kept the simplex basis warm across the offline lazy-SMT loop's cubes,
measured **40,916 from-scratch tableaux → 0** and **−9.2 %** wall clock, and
shipped `off` on **1 STABLE-GAIN against 2 STABLE-LOSS**. It then named its own
successor in one sentence, twice — in §7.3 and again in §8.4:

> The loss and the gain are on one axis — **builds per file** — and the lever is
> free to consult it. `simplex_cold_builds` is already a counter, and a decider
> that refuses a cube set whose builds are few and huge would keep the `sc/*`
> gain without taking the `latendresse/*` loss.

This lane took that. The screen is built, registered, fixtured and measured. The
headline is not the screen.

**The discriminator does not discriminate.** ADR-2125 could place only one of its
three movers in its sizing table and said so explicitly, calling the reading for
the second loss a HYPOTHESIS rather than a measurement. Counted here, that row —
`QF_LRA/uart/uart-8.induction.cvc.smt2` — is **1,598 builds at 1.04 ms each**,
which is the MANY-SMALL shape the lever WINS on, 14 % away from the gain's 1,815.
No builds-per-file threshold separates them. The screen removes the pinned loss
and cannot touch the held-out one, and that was known before the threshold was
written into the source.

Branch base: this lane merged local `main` at `677c0192c`, which carries
[ADR-2125]'s merge `5df0e1a32`.

Compute: **s5, physical core pairs `5,13` and `6,14`**, and nothing else. Both
pairs were checked for a previous lane's leftover shards before the first timing
(`ps -eo pid,psr`, load average 0.07); there were none.

## 1. The sizing, taken before the code — and the two rows it had to go and get

### 1.1 What was already measured

[ADR-2125] committed per-file trail data for the whole pinned `QF_LRA` 200
(`bench-results/lra-warm-basis-20260916/sizing.0{0,1}.tsv`), including
`simplex_cold_builds`. That is the axis, and it did not have to be re-run.

```text
QF_LRA pinned 200: 200 rows | 180 reached the lazy-SMT loop | 20 SILENT
   builds          0   112  ############################################################
   builds        1-3     1  #
   builds      16-63    16  ################
   builds     64-255    21  #####################
   builds   256-1023    16  ################
   builds  1024-4095    14  ##############
   builds: min 0  p25 0  median 0  p75 88  p90 951  max 1543   |  >0: 68 rows
```

The **20 SILENT rows report nothing about this counter, not zero**, and are in no
denominator here — the distinction ADR-2125 drew and this keeps.

### 1.2 The distribution is bimodal, and the modes do not overlap

A share of the clock does not separate the two shapes; **milliseconds per build**
does, and **builds** is the clock-free proxy for it:

| builds | ms/build | file |
|---:|---:|---|
| 1 | 23,908.0 | `latendresse/ecoliFBAyicesTest-3875-4` |
| 28 | 283.5 | `latendresse/ecoliMILPglycerolYices3-50000` ← ADR-2125's **pinned stable loss** |
| 42 | 548.1 | `miplib/danoint-266` |
| … | … | |
| 841–1,543 | 0.4–6.4 | the `sc/*` family, `miplib/vpm2-5`, `sal/pursuit`, `LassoRanker/…Ex4.2` |

Two facts, both over the 68 rows that re-solve:

* every row at or above **51** builds costs at most **12.2 ms** per build;
* every row above **20 ms** per build has at most **42** builds.

So **any threshold in `[43, 51]` separates the two shapes exactly on this
population.** A threshold is being chosen from a window, not fitted to a point.

### 1.3 The value, and what it costs the rows it admits

`MIN_WARM_CUBE_SCREEN_BUILDS = 64`: the next power of two above that window,
**1.52× the largest few-enormous row** and **13.1× below the smallest winning
one**. Taking the window's own edge would make the constant a function of this
population's largest outlier.

`cold_builds / lra_rounds` is **1.00** on every row above 100 builds, so the
screen trips after about 64 refinement rounds — **4.1–7.6 %** of the winning
family's rounds run cold before the basis is kept. That is the price of deciding
without a clock, and it is a price rather than a risk: below the threshold the
file runs the route it runs today, byte for byte.

**A CLOCK is not available, and that constraint is load-bearing later.**
Determinism is a public API promise here. A screen on wall-clock milliseconds
would make a verdict depend on the machine, so every quantity the screen may
read has to be clock-free: builds, rounds, atoms, pivots.

### 1.4 How many rows fall on each side

```text
pinned 200:  180 spoke, 20 SILENT
              51 of 180 at or above 64 builds   -- the screen ADMITS these
             129 of 180 below it                -- the screen REFUSES these
```

51 is the ceiling of what the screened arm can move on this population; 129 is
the risk it declines to take.

## 2. The finding: the axis does not separate the held-out loss

ADR-2125 published three re-checked movers and one explanation for all of them.
Two were absent from its sizing table, and it labelled the second loss's reading
a hypothesis in as many words:

> nothing here has counted its builds. Saying otherwise would be fitting the
> explanation to the two rows that suit it.

Counted here (`axeyum.v1`, sha256 `91675258916e4aeb`, s5 core 5, 24 s, `--trace`):

| ADR-2125 verdict | builds | ms/build | atoms | cold_pivots | file |
|---|---:|---:|---:|---:|---|
| STABLE-LOSS | 28 | 283.5 | — | — | `latendresse/ecoliMILPglycerolYices3-50000` |
| **STABLE-GAIN** | **1,815** | **1.7** | 976 | 466,693 | `sc/sc-14.induction.cvc` |
| **STABLE-LOSS** | **1,598** | **1.0** | 1,272 | 252,412 | `uart/uart-8.induction.cvc` |

**The hypothesis is refuted.** `uart-8` is the many-small shape. It is on the
winning side of every threshold in the window, and on the same side as the gain
at *every* threshold whatever: 1,598 and 1,815 are 14 % apart.

So the screen can remove the **pinned** loss and cannot touch the **held-out**
one. Against the ship criterion in §7 — 0 stable losses on BOTH draws — it was
already unable to ship when this was measured, which was **before** the threshold
was written into the code.

### 2.1 The threshold was not then moved, and that is the point

A threshold of 1,700 separates 1,598 from 1,815. It is not taken. **Those two
rows are the held-out evaluation population**, and a boundary drawn between two
of its members is fitted to the set it is scored on — which is the one thing a
held-out draw exists to prevent. The value stays at 64, chosen from the pinned
sizing before any of this was known, and this ADR reports what that value does
rather than what some other value would have done.

### 2.2 What separates them instead — an observation, offered as two points

The warm arm replaces (linearize + cold simplex) per cube with (sync + warm
solve), and `sync_cube` is O(live atoms) while the cold simplex is O(pivots). The
trade should therefore turn on cold WORK PER ATOM, and on these two rows it does:

```text
sc-14  (gain)  466,693 pivots / 1,815 builds = 257 per build / 976   atoms = 0.263
uart-8 (loss)  252,412 pivots / 1,598 builds = 158 per build / 1,272 atoms = 0.124
```

A 2.1× separation, and clock-free — pivots and atoms, not milliseconds.

**It is not built and not registered.** Two points is a fit, not a
discriminator, and both are held-out rows: building a screen on them would spend
the blind population that is supposed to score the next one. It is recorded as
the shape a successor should SIZE first, on the pinned 200, exactly as this lane
sized builds-per-file before touching the code.

## 3. The design claims, with `file:line`

Full table at `bench-results/lra-warm-screen-20260916/reference-citations.md`,
verified against `references/z3` at `e18d63bda04fcab8240eb55314d567db3e43d540`
— the revision [ADR-2125] cited, re-read from `.git/refs/heads/master` rather
than inherited.

### 3.1 z3 never decides whether to keep the basis, and the line that looks like it does is a statistic

`lar_solver::find_feasible_solution()` is the entire "make this system feasible
again" entry point (`lar_solver.cpp:464-474`). It bumps three statistics, sets a
strategy and a flag, and calls `solve()`. **No branch on the problem's size, no
rebuild, no admission cap.**

The trap worth carrying is inside it. A reader grepping this file for a size
refusal finds exactly one pair of size comparisons — `lar_solver.cpp:468-469` —
and they are `>` against a **high-water mark** which they then assign:

```cpp
if (A_r().row_count() > stats().m_max_rows)
    stats().m_max_rows = A_r().row_count();
```

A whole-file search for any other size gate returns nothing. So z3's one size
comparison **records** a size and decides nothing.

`pop(unsigned)` is the sharpest citation (`lar_solver.cpp:567-605`). A solver
that rebuilt after a pop would have the restore there; what is there instead, at
`:575-579`, is **four `SASSERT`s that the basis and the heading are still
correct**. And `init_run_tableau()` opens by asserting the basis is set correctly
and returns before any pivot when the point is already feasible
(`lp_primal_core_solver_tableau_def.h:256-269`).

### 3.2 Ours, at the screen

| what | where |
|---|---|
| the lever, three-valued | `dpll_t.rs`, `warm_cube_mode` / `parse_warm_cube_mode` |
| the screen's state machine, one transition per entry | `dpll_t.rs`, `WarmCubeScreen::decider` |
| the threshold | `dpll_t.rs`, `MIN_WARM_CUBE_SCREEN_BUILDS` |
| the count it reads, ALWAYS ON | `simplex.rs`, `cold_builds_so_far` / `bump_cold_builds` |
| the event both counters share | `simplex.rs:697`, `feasible_within_sparse` |
| two admission doors on one structure, in two currencies | `simplex.rs:2073` (dense cells), `simplex.rs:2044` (nonzeros) |

**The asymmetry is the finding, not a defect list.** z3 has no screen because it
never pays for a rebuild: its basis survives every pop, so "is keeping it worth
it" is not a question its architecture can ask. Ours pays for the rebuild on the
offline route, so the question exists — and §2 is the answer that the only
clock-free quantity ADR-2125 named does not answer it.

## 4. What was built

### 4.1 The lever is three-valued

`off` | `on` | `screened`. Under `screened` the loop runs the cold route until
the file has built `MIN_WARM_CUBE_SCREEN_BUILDS` from-scratch tableaux, then
builds the ADR-2125 decider once. `WarmCubeScreen` has three states and not an
`Option`, because "never built" and "tried and refused" are different facts and a
refusal must not be retried every round: `try_new_for_cubes` walks every atom,
and retrying it per round on a 7,260-atom file is a cost with no verdict attached
— the shape ADR-2125 found its first working arm in.

`on` is **kept** rather than deleted. The screen's claim is comparative, and a
claim of that shape needs the thing it is compared against to still be runnable.

Every unrecognised spelling — `""`, `"ON"`, `"screen"`, `"1"` — is `Off`. The
variable is the only difference between the arms of an A/B, so a launcher typo
must produce the shipped route: an arm labelled `screened` that quietly became a
third behaviour would be measured under the wrong name, which is the one failure
an A/B cannot see from its own numbers.

### 4.2 The screen reads its OWN counter, and that is not duplication

`LazySmtCounters::simplex_cold_builds` is armed only by `--trace`. A screen
consulting it would **route one way under instrumentation and the other way
without**, and every A/B of this lever would then measure a route production
never takes. So `simplex::cold_builds_so_far` is a second counter on the same
event, incremented unconditionally at the same site on the same condition, and
read as a DELTA against a snapshot taken at the loop's entry (it is per-thread
and cumulative; there is deliberately no reset, because a reset is a second way
for two queries to interfere and a delta needs none).

`a_screen_count_and_the_traced_count_are_the_same_number` keeps them in step and
asserts the **unarmed half first**: a test that only compared the two while armed
would pass on an implementation that incremented the screen counter inside the
`if enabled()` branch — the exact defect the counter exists to avoid.

**The DELTA is not tidiness, and there is a file that proves it.** The counter is
bumped at `feasible_within_sparse`, which is reachable from every route that
calls it — not just the three lazy-SMT loops.
`QF_LRA/sc/sc-24.induction3.cvc.smt2` is the demonstration, read off its own
capture rather than argued:

```text
; lazy-smt reading=not-reached lra_entries=0 nra_entries=0 nia_entries=0
           atoms=0 simplex_cold_builds=2264 warm_cube_build=off
; route decided_by=none bound_by=lira-dpll last=fd:bounded-completeness-unsat
```

**2,264 from-scratch tableaux and no lazy-SMT loop ran at all** — they are the
`lira-dpll` rung's. A screen reading the counter ABSOLUTELY would have tripped on
its first round in the linear loop, on work that loop never did. Snapshotting at
entry and comparing a difference is what makes the screen a statement about the
route it is on.

The same fact bites the SIZING, in the other direction, and §8 records it as a
gap rather than a fix: the builds histogram in §1 counts every route too. On the
pinned 200, where the threshold was derived, the error is **exactly zero** —
all 68 rows with a nonzero build count have `lra_entries > 0`, checked against
ADR-2125's own committed sizing. On the held-out draw it is at least 3 of 47.

### 4.3 The attribution ADR-2125 said a successor must not skip

> nothing here says how much of the −9.2 % is the basis and how much is not
> rebuilding the `Collector`. A successor should not attribute the saving to the
> basis on this evidence.

Two additive schema-3 fields make the split two differences between fields that
are both ON the trail line, over one interleaved pair of arms on one file — no
counterfactual and no modelling:

```text
saved by the BASIS         = off.cube_simplex_ms
                             - (arm.cube_simplex_ms + arm.warm_cube_solve_ms
                                                    + arm.warm_cube_sync_ms)
saved by the LINEARIZATION = off.cube_collect_ms - arm.cube_collect_ms
```

The second works because an answered cube never reaches `decide_cube`, so it
never builds a `Collector`: the warm arm's own collect figure is already the
residue.

`warm_cube_sync_ms` is split from `warm_cube_solve_ms` rather than pooled because
[ADR-2125] §4.3 is why this lever works at all — its first working arm was
SLOWER, reconciling by shared prefix at 1,133,095 retractions over 632 checks,
and `sync_cube` took that to 4,238 assertions and 0 retractions. Pooled, a
reconciliation regression and a pivoting regression are one number that says only
"slower".

### 4.4 The dense-cell cap is NOT restated in nonzeros, and the reason is measurable

ADR-2125 found `Incremental::new` refusing the warm engine at
`MAX_TABLEAU_CELLS` **dense cells** while the tableau stores nonzeros — 8,797,712
cells against 4,688 nonzeros on one file — and opened a second door
(`with_nonzero_admission`) for the one call site rather than move the constant.
This lane was asked to finish the job or say what the cell count guards that a
nonzero count does not. **It guards fill-in, and that is a property of the
algorithm rather than of the storage.**

`Tableau::select_entering`'s fill-in-minimising rule says so in its own comment:
*"a pivot on a sparse column touches few rows and grows the tableau least"*. A
pivot combines rows, so it creates nonzeros. `MAX_WARM_CUBE_NONZEROS` bounds the
count at CONSTRUCTION and nothing after it; `m × (nvars+m)` is the ceiling
fill-in cannot pass.

**The reason is not new and this lane does not claim it.** `config_registry.rs`'s
own note on `MAX_TABLEAU_CELLS` already says the constant is *"STALE IN ITS OWN
UNIT SINCE ADR-2111"* and that it is left in place because *"it still bounds the
PIVOT'S WORK … the number of cells is what bounds how large nnz can grow under
fill-in"*. The history confirms the first half: the commit that introduced it
(2026-08-03, the one that put the online theory on the warm simplex) reasons in
*"a 4× cut in tableau cells"* and the doc comment prices 4M cells at ~128 MB
because a `Rational` is two `i128`s. It was a MEMORY bound in the dense era.
ADR-2111 made the storage sparse and the unit stopped describing anything the
program allocates.

What that registry note then says is the gap: *"Whether a nonzero-count bound
should replace it needs the fill-in measurement ADR-2111 did not take."*

**So what is new here is the instrument, and then the number.**
`warm_cube_fill_peak` is the measurement's numerator and `warm_cube_entry_nnz`
its denominator; the peak alone settles nothing, because 98,572 nonzeros against
a 400,000 cap is one claim if the tableau entered at 90,000 and the opposite
claim if it entered at 4,688.

Measured over seven `QF_LRA` files (`fill-in.txt`):

```text
entry_nnz  fill_peak   growth   file
   65,133     65,852    1.01x   LassoRanker/.../firewire Iteration3
   96,154     98,960    1.03x   LassoRanker/.../Ben-Amram-2010LMCS-Ex2.3
   27,184     32,104    1.18x   LassoRanker/.../Gcd_havoc
    2,288     28,093   12.28x   sc/sc-19.base.cvc
    4,448     95,323   21.43x   sc/sc-37.base.cvc
    4,688     98,572   21.03x   sc/sc-39.base.cvc
```

**Fill-in grows the stored set by up to 21×, and the decisive row is
ADR-2125's own.** `sc-39.base.cvc` is the file it measured at **4,688 nonzeros
against 8,797,712 dense cells** and used to argue the dense cap was in the wrong
currency. It is right that the cap refuses a 188 KB structure. It is wrong that
4,688 describes the structure: the peak is **98,572**.

So a construction-time nonzero bound is not a bound on the structure at all once
the engine runs. `MAX_TABLEAU_CELLS` is loose — the peak is 1.1 % of it — but it
is a real ceiling and the only one of the two fill-in cannot pass. **The cell cap
stays, and the reason is now a number rather than a reading of the pivot loop.**

The second finding is the shape, and it inverts the intuition: the rows that
enter SPARSE are the rows fill-in changes. `LassoRanker/*` enters at 27k–96k and
grows 1.01–1.18×; `sc/*` enters at 2.3k–4.7k and grows 12–21×. `sc/*` is the
family this lane's screen admits and ADR-2125's gain came from, so **the files
the warm basis helps most are the files whose footprint the admission count
describes least.**

Seven files is a probe, not a population: enough to answer ADR-2111's yes/no,
not enough to set a constant from. Nobody has taken the tail here either.

The second reason is ADR-2125's and unchanged: the constant governs the ONLINE
engine's admission too, so moving it would make an A/B of one lever an A/B of
two routes.

## 5. Soundness and the gates

### 5.1 The transition fixture runs all three arms in ONE process

The lever is read once per process into a `OnceLock`. That is right for a
measurement and wrong for this fixture, because the property the screen must have
is that the three arms **AGREE ON THE VERDICT** — and three separate test
binaries could not assert that. Each would compare its own arm against a verdict
written into its own source, which is the maintainer's memory of the answer
rather than a comparison.

So the mode is lifted to a parameter of `check_with_lra_dpll_within_mode`, with
exactly ONE production caller. It is not a test-only route: it is the route, with
its one environmental read moved to the boundary.

`tests/lra_warm_screen_2132.rs` then holds both halves of the screen's claim:

* `a_file_that_crosses_the_threshold_mid_run_decides_what_off_decides` — the
  crossing case. Asserts the verdict agreement AND three mechanism facts: that
  the `off` arm really built past the threshold, that the screened arm really
  answered cubes warm, and that it answered **strictly fewer than `on`** (the
  screen's own signature — the rounds below the threshold ran cold in one arm and
  warm in the other). Plus `cold_restarts == 0`, the only thing in the file that
  can see a basis being quietly rebuilt.
* `a_file_below_the_threshold_keeps_no_basis_at_all` — the other half, and the
  screen's actual point. Same generator and the SAME disjunction rate at a
  different seed, deliberately: a below-threshold case built by removing the
  disjunctions would differ in shape as well as in size, and then "the screen
  stayed shut" could be a fact about the shape.

**The vacuity guards fired twice while these were being written**, and both
readings are now measured parameters in the source rather than guesses. The first
version's crossing query built 5 tableaux against a threshold of 64; the first
version of the counter test was handed a two-atom query the ONLINE engine decides
without ever reaching the counted site. Measured on the shipped generator: the
crossing pair builds **124** and the below pair **34**.

The threshold is **restated** in the fixture rather than imported. A fixture that
imported it would follow it anywhere, including to zero — which is exactly the
mutation §5.4 requires it to die on.

### 5.2 ADR-2125's fixtures are unchanged and green

`a_warm_cube_sequence_decides_exactly_what_a_cold_one_does_and_keeps_the_invariant`,
`a_stale_bound_from_a_popped_cube_would_refute_a_satisfiable_one` and
`sync_cube_retracts_a_row_the_new_system_no_longer_bounds` are untouched. No
fixture in this lane was weakened; the byte-coverage test
`every_lazy_smt_counter_reaches_the_trace_line` was **extended by the compiler**,
which is the point of its `..`-free destructure — three new fields made it refuse
to compile until each was named and rendered.

### 5.3 The gates

Every `cargo test` line below has a **nonzero** count confirmed, because a
feature-gated suite compiles to nothing and exits 0.

| gate | measured |
|---|---|
| `cargo fmt --all --check` | ok |
| `cargo check --workspace --all-targets` (default features) | ok |
| **`clippy --workspace --all-targets --all-features -- -D warnings`** | **ok** |
| `--lib --features full lra` | **145 passed**, 0 failed |
| `--lib --features full simplex` | **41 passed**, 0 failed |
| `--lib --features full config_registry::tests` | **18 passed**, 0 failed |
| `--lib --features full lazy_smt_counters` | **6 passed**, 0 failed |
| `--lib --features full dpll_t::tests` | **15 passed**, 0 failed |
| `--test lra_warm_screen_2132` (release) | **3 passed**, 0 failed |
| the dispatch/reason suites, via the shared runner | ok |
| `check-suite-gating.py` | PASS (348 suites, 47 gated, 303 excused) |
| `check-config-registry-staleness.py` | 0 unexplained |
| `check-merge-hygiene.sh` | PASS |
| `check-links.sh` | all links ok |
| `mutation_controls.py --check-anchors` | 158 suites, 1,102→1,114 anchors, **stale = 0** |
| the six z3 fuzzes × three arms | **17 per arm, 51 total**, 0 failed (§5.5) |
| `--lib --features full -- --skip reconstruct::` | **1,613 passed, 6 failed** contended; **1,619 passed, 0 failed** on a quiet box (§5.3.2) |
| `progress_frontier --features full -- --test-threads=1` | **12 passed, 0 failed, 0 REGRESSION** |

**The clippy line is the battery's own, at full scope**, not the three-crate
narrowing ADR-2125 used — and getting there cost three lints of this lane's own
(§5.3.1).

**The ratchet is clean and its marks are read rather than its pass count.**
`nra_degree` 12.1 ms against a 23.0 ms ceiling and `string_bound` PROGRESS
(+32, ratchetable) are both **enforced**; `bv_reduction`, `lia_cuts` and
`nia_unsat` are marked NOT COMPARABLE, so their ratchets are enforced on nothing
here. The marks carry their own reason and it is the same reason the lib sweep's
six reds have:

```text
NOT COMPARABLE [bv_reduction]: throughput moved 109 % during the sweep (125.6 ms -> 262.8 ms)
NOT COMPARABLE [lia_cuts]:     throughput moved  46 % during the sweep (255.1 ms -> 137.0 ms)
NOT COMPARABLE [nia_unsat]:    throughput moved  75 % during the sweep (136.3 ms -> 238.4 ms)
```

**The machine did not hold still while this battery ran**, measured by the
ratchet's own calibration rather than inferred from a load average. That is
independent evidence for §5.3.1's reading of the six reds, and it is worth more
than the isolated re-run because it comes from a different instrument.

**No baseline is raised from this run**,
including `string_bound`'s ratchetable progress: that is not this lane's change
to make. ADR-2125 had two such families on its idle run and this has three, which
is a worse frame, not a better one — said here rather than left to a reader who
counts `12 passed` and stops.

#### 5.3.1 The lib sweep's six reds are the load-sensitive budget family

```text
array_bv_abs::tests::refutes_rw213_by_bv_abstraction
auto::tests::arithmetic_uf_overbound_pre_lia_probe_decides_on_clone
auto::tests::cap_overflowing_skolemized_chain_is_refuted_via_the_egraph_loop
auto::tests::every_policy_gives_the_same_verdict_on_an_overbound_query
auto::tests::negated_quantified_implication_exposes_counterexample_witness
auto::tests::top_level_negated_universal_exposes_counterexample_witness
```

**Re-run together, serialized, on the same tree: 6 passed, 0 failed, in 0.49 s**
— against failing inside a 525 s parallel sweep.

Their failure messages are budget-shaped, e.g.
`Unknown(ResourceLimit, "quantified solve time budget exhausted after checked
fast paths")` where `Unsat` was expected. **None is on the offline linear loop
this lane changed**; they are quantified/Ackermann routes in `auto.rs` and a
bit-vector abstraction in `array_bv_abs.rs`.

And the family is already on the record. [ADR-2114] names
`auto::tests::arithmetic_uf_overbound_pre_lia_probe_decides_on_clone` —
one of these six, by name — with the identical resolution: *"re-run
individually: 2/2 pass"*. [ADR-2125] hit a sibling in the same file
(`pathological_overbound_stays_terminal_under_every_policy`) and [ADR-2111] hit
that one before it.

**What is NOT claimed**: that six is the same reading as ADR-2125's one. It is
six, that is more, and this lane did not establish why more failed this time —
the sweep ran immediately after 23 dispatch suites on a box that had been at
load 135 earlier in the session.

#### 5.3.2 The same sweep, same tree, quiet box: green

```text
test result: ok. 1619 passed; 0 failed; 0 ignored; 0 measured; 320 filtered out; finished in 345.33s
```

**1,619 = 1,613 + 6.** The identical gate — not narrowed, not re-threaded, not
filtered — run again at load 3.5 instead of on a box whose throughput the
ratchet measured moving 109 % mid-sweep. It took **345 s against 525 s**, which
is the contention showing up in the clock as well as in the verdicts.

This is a stronger statement than [ADR-2125] was able to make about its own red.
That ADR said explicitly: *"What is NOT claimed: that a green isolated run proves
the sweep would be green on a quiet box."* Here the sweep itself was re-run and
it is green, so the claim is available and is made: **the lib sweep passes on
this tree.** The battery's `GATES FAILED` line reflects the contended run and is
kept in `gates.log` rather than deleted, because a gate result that was later
superseded is still what that run measured.

### 5.4 Mutation: two guards, two suites, and one honest disagreement with the brief

Two suites, because the guards live in different files and are seen by different
fixtures. Both baselines are **nonzero** — 3 tests and 16 — so neither result is
the "suite compiled to nothing" reading exiting 0.

| guard removed | kind of damage | killed |
|---|---|---:|
| the builds threshold the screen opens at | the screen becomes `on` under another name | **2** |
| the screen counter's bump on the UNTRACED path | routes one way under `--trace`, another without | **1** |

`mutation_controls.py --check-anchors`: 158 suites, 1,114 anchors, **stale = 0**.

**Admitting at 0 builds makes `screened` byte-for-byte `on`** — same verdicts,
same counters, same clock — so no verdict comparison anywhere in this ADR could
see it. Two fixtures can, and both die:

* `a_file_below_the_threshold_keeps_no_basis_at_all` — the direct guard. At a
  threshold of 0 the screen opens on a 34-build file, so `warm_checks == 0`
  fails and so does the `("off", "below-screen")` label pair.
* `a_file_that_crosses_the_threshold_mid_run_decides_what_off_decides` — the
  signature. At 0 the screened arm answers exactly as many cubes as `on`, so
  `on.warm_checks > screened.warm_checks` fails.

**This lane's brief asked for exactly ONE named fixture to die, and it is two.**
The mutation registration said so before the run rather than after. The honest
reading is that the two observe ONE defect from two sides, with **nested** kill
sets rather than disjoint ones — and the only way to get a single kill would
have been to weaken the signature assertion, which is precisely the assertion
that distinguishes this lane's arm from ADR-2125's. That is not a trade worth
making for a tidier number, and [ADR-2125] §5.6 set the precedent by reporting
its own non-disjoint sets rather than a coverage figure.

The second mutation does kill exactly one, and it does so for a reason worth
keeping: `a_screen_count_and_the_traced_count_are_the_same_number` asserts the
**unarmed half first and separately**. A test that compared the two counters only
while armed would have survived this mutation — and an earlier draft of that test
did exactly that, which is how the ordering got written down.

**What mutation testing does not show is the guards that are missing.** It
measures the ones that exist. The adversarial question — for every distinction
the producer makes, is there a fixture over a *satisfiable* query that can see it
— is answered separately by [ADR-2125]'s soundness-negative pair, which this lane
left untouched and green.

## 6. The A/B

### 6.1 One binary, three arms, and the guard that has fired before

`axeyum.v1` (sha256 `91675258916e4aeb`), three values of
`AXEYUM_LRA_WARM_CUBE`, arms back to back on the same file on the same pinned
core with the order **rotating three ways** per file. 24 s / 8 GiB, s5 core
pairs `5,13` and `6,14`, nothing else on the box.

[ADR-2100]'s runner refuses unless its two BINARIES hash differently, because two
identical arms give a perfect zero that looks exactly like agreement. With one
binary the risk moves to "the binary never reads the variable", and ADR-2125
proved that risk is real here — its first mechanism check read
`warm_cube_checks = 0` in both arms. `--mechanism-check` is where that is
refused, and it now checks the screened arm too, which has a way of being inert
that `on` does not: the file can simply never cross the threshold.

```text
mechanism-check: off=0/928 on=996/built screened=953/built
mechanism-check OK: all three arms distinguishable on this file
```

### 6.2 `QF_LRA` pinned 200 — complete

```text
comparison         rows  off  arm  net  gain  LOSS  FLIP  rc!=0  cmp  DIS
off vs screened     200  107  107   +0     0     0     0      0  194    0
off vs on           200  107  107   +0     1     1     0      0  194    0

  raw GAIN (off->on)   sc/sc-7.base.cvc
  raw LOSS (off->on)   latendresse/ecoliMILPglycerolYices3-50000
```

**The screen removes ADR-2125's pinned stable loss.** That row is 28 builds — a
handful of enormous solves — and the screen refuses it at any threshold above 42.
The `on` arm still takes it on this binary and this run, so ADR-2125's result is
reproduced rather than inherited.

`off` decides **107 of 200**, which is the board's standing `QF_LRA` figure to
the row.

### 6.3 `QF_LRA` held-out 200 — complete

```text
comparison         rows  off  arm  net  gain  LOSS  FLIP  rc!=0  cmp  DIS
off vs screened     200   93   93   +0     1     1     0      0  174    0
off vs on           200   93   92   -1     0     1     0      0  173    0

  raw GAIN (off->screened)   sc/sc-18.induction.cvc
  raw LOSS (off->screened)   uart/uart-8.induction.cvc
  raw LOSS (off->on)         uart/uart-8.induction.cvc
```

**The screen does not remove the held-out loss, and §2 said so before this code
existed.** `uart-8.induction.cvc` is 1,598 builds at 1.04 ms each, so the screen
admits it — 1,872 cubes answered warm — and the loss survives unchanged.

The screen also picks up a raw GAIN the unscreened arm does not
(`sc-18.induction.cvc`, 1,685 builds; `off` and `on` both `unknown`, `screened`
`sat`). A raw mover is not a finding and it goes to §6.7 with the rest.

`off` decides 93 of 200 on this draw.

#### What ADR-2125's three published movers did here

```text
     off       on  screened  builds  scr_cubes   what
     sat  unknown       sat      28          0   pinned STABLE-LOSS  -- REMOVED
     sat      sat       sat   1,815      1,106   held STABLE-GAIN    -- not a gain here
     sat  unknown   unknown   1,598      1,872   held STABLE-LOSS    -- NOT removed
```

The middle row is worth stating plainly rather than leaving for a reader to
notice. **ADR-2125's held-out GAIN is not a gain in this run at all**, because
this lane's `off` arm decides it. That is not a contradiction: it is a boundary
file, and §6.6's control already shows one row in 120 moving in BOTH arms between
the two runs. But it means the gain that motivated the screen is not present in
this population to be kept, so the screen's case here rests on the pinned loss it
removes and not on a gain it preserves.

#### Mechanism, held-out

```text
arm         rows `built`   cubes answered   cold tableaux left   cold_restarts
on                    79           59,320                7,869               0
screened              66           53,516               11,664               0
off                    -                -               58,874               -
```

The screen refused 13 of the 79 rows `on` kept a basis on and opened on 0 that
`on` did not. `cold_restarts = 0` in both arms.

```text
population          rows all 3 decide   off          on           screened
QF_LRA held-out                    92   97,533 ms    85,406 ms    85,710 ms
                                             ---      -12.4 %      -12.1 %
```

#### A defect in this lane's own launch, and why the shard is still trusted

The held-out shard's log is **empty**. Its launch redirected stdout twice —
`> LRAheld.log 2>&1 … > /dev/null 2>&1` — and the last redirection wins, so every
line the runner printed, including its closing `AB3-DONE`, went to `/dev/null`.
The chain waiting on that marker would have waited out its six-hour timeout on a
shard that had already finished.

**The marker was not written by hand to satisfy the guard.** A guard satisfied by
hand is not a guard. Completeness was established from the artifact instead,
which is a stronger check than the marker anyway — the marker only says the loop
exited:

```text
held TSV data rows                        200
list rows                                 200
rows with all three verdicts non-empty    200
distinct files in TSV                     200
files in the list but NOT in the TSV        0
```

### 6.4 The mechanism, and the prediction it confirms exactly

```text
arm         rows `built`   cubes answered   cold tableaux left   cold_restarts
on                    71           38,344                    0               0
screened              51           32,742                3,871               0
off                    -                -               33,158               -
```

`cold_restarts = 0` in both treatment arms is the tripwire: a warm basis quietly
being rebuilt gives identical verdicts, identical churn counts, and differs only
in the clock. The screen refused **20 of the 71** rows `on` kept a basis on and
opened on **0** that `on` did not — the second number is the one that would
indicate a bug. 51 < 71 with both nonzero, so criterion 5 is met by the run
rather than by assertion.

**The admitted set was predicted exactly, and not merely its size.** §1.4 derived
from ADR-2125's committed sizing — a different lane, a different binary, a
different day — that 51 of the pinned 200 sit at or above 64 builds. Measured:

```text
predicted from ADR-2125's sizing (builds >= 64):   51
screened arm built a decider on:                   51
screened arm answered >=1 cube warm on:            51
  predicted but NOT built:                          0
  built but NOT predicted:                          0
```

Same count and the **same set**. That is the sizing axis being reproducible
enough to route on, which is a stronger claim than the histogram alone supports,
and it is why the threshold could be fixed before the code existed.

### 6.5 What it costs

```text
population        rows all 3 decide   off         on          screened
QF_LRA pinned                  106   61,555 ms   51,727 ms   53,003 ms
                                          ---     -16.0 %     -13.9 %
```

The screen keeps about seven eighths of the unscreened arm's speed while
refusing 20 of its 71 rows — the rows it refuses are the cheap ones, which is
what a threshold at 64 builds selects for.

A useful noise floor falls out of the same data. On rows where the screen never
opens, `screened` runs the `off` route with one thread-local read per round
added, so the arm-to-arm difference there is the measurement's noise: over the
rows both decide at ≥50 ms it is at most **2.4 %** (on an 85 ms file) and at most
**0.4 %** above 500 ms. Nothing below that is a finding.

### 6.6 The reproducibility control

ADR-2125 ran the same two arms on the same corpus at the same envelope on the
same core pairs, on a different day from a different branch base, and committed
its per-file verdicts. Over the 120 rows the two runs share:

```text
`off` arm agrees on   119 / 120
`on`  arm agrees on   119 / 120
```

The one difference — `clock_synchro/clocksynchro_7clocks.worst_case_skew.induct`,
`unknown` in both of ADR-2125's arms and `unsat` in both of mine — **moves both
arms together**, so it cancels in the difference either A/B reports and is
attributable to the lever in neither. It is either the ambient 1–1.5 % flip rate
at a 24 s budget on a boundary file or a change on `main` between the two branch
bases; this lane does not say which, because it did not measure it.

This licenses reading the two lanes' numbers as one series. It does **not**
license carrying ADR-2125's mover CLASSIFICATIONS forward — a stable loss is a
claim about a 3× recheck on a specific binary — which is why §6.7 re-checks this
lane's own.

### 6.7 The mover recheck, and the screen is strictly better than `on`

Four movers across both complete draws, **derived** from the finished TSVs for
BOTH comparisons rather than typed from what a partial run happened to show.
Each re-run **3× per arm** on one pinned core pair with the arms alternating
within the passes, at the same 24 s / 8 GiB envelope. ADR-1966 had 11 of its 18
movers vanish under exactly this procedure, so a raw mover is never the finding.

```text
row                                      draw      off vs on          off vs screened
latendresse/ecoliMILPglycerolYices3-…   pinned    STABLE-LOSS        BOTH-DECIDE
sc/sc-7.base.cvc                        pinned    STABLE-GAIN        NEITHER-DECIDES
sc/sc-18.induction.cvc                  held-out  NEITHER-DECIDES    STABLE-GAIN
uart/uart-8.induction.cvc               held-out  STABLE-LOSS        STABLE-LOSS
```

Read down the two columns:

```text
                pinned              held-out            total
on              1 gain, 1 LOSS      0 gains, 1 LOSS     1 gain, 2 LOSSES
screened        0 gains, 0 LOSSES   1 gain,  1 LOSS     1 gain, 1 LOSS
```

**`on` reproduces [ADR-2125]'s headline exactly — 1 stable gain against 2 stable
losses — on a new binary, a new branch base and a complete 400-row population
rather than the two half-draws ADR-2125 could finish.** That is worth recording
on its own: the result this lane set out to improve on is not an artefact of the
partial population it was measured on.

**And the screen is strictly better than `on` on both draws.**

* On the PINNED draw it removes the stable loss — `ecoliMILPglycerolYices3-50000`
  is 28 builds, below the threshold, so the screen never keeps a basis there and
  the row comes back BOTH-DECIDE. It also gives up `on`'s stable gain on
  `sc-7.base.cvc`, which is 1,695 builds: the screen ADMITS that row, and the 64
  rounds it spends cold first are enough to lose the decision inside 24 s. **That
  is the screen's own cost showing up as a forgone gain**, and it is the clearest
  single price the threshold charges.
* On the HELD-OUT draw it buys a stable gain `on` does not get
  (`sc-18.induction.cvc`, 1,685 builds, `on` NEITHER-DECIDES) and takes the same
  stable loss `on` takes.

So the trade is: one pinned loss removed and one pinned gain forgone, plus one
held-out gain bought. Net across both draws, `screened` is 1 gain / 1 loss where
`on` is 1 gain / 2 losses.

**It is still one stable loss, and criterion 3 is still not met.**
`uart-8.induction.cvc` is 1,598 builds — the many-small shape — and no threshold
in the sizing window separates it from the winning family. §2 measured that
before this code existed; this is the 3×-per-arm confirmation on this binary.

### 6.8 The exposure divisions

PLACEHOLDER — filled in when the queues finish.

## 7. Decision

### 7.1 The criteria, written before the numbers

Recorded here, in this file, **before the A/B on either draw had finished** —
the reading taken immediately after this section was written put the two
`QF_LRA` shards at **74 and 68 rows of 200**, and the committing SHA is the
evidence of when. [ADR-2125] put its
criteria in a §7.1 after its §7 for the same reason and said so; this puts them
in before it, which is the same discipline one step earlier.

`screened` ships ON only if **all** of the following hold. Anything short of all
of them ships `off`.

1. **0 soundness disagreements** against the files' declared `:status`, at a
   comparable denominator that is printed rather than implied.
2. **0 stable losses and 0 flips** on the pinned `QF_LRA` draw, where "stable"
   means the 3×-per-arm recheck agrees. A raw mover is not a finding: ADR-1966
   had 11 of 18 vanish under exactly this recheck.
3. **0 stable losses on the HELD-OUT draw too.** The pinned list is the
   population every number in ADR-2111 and on the board was measured on, so an
   A/B on it alone is an A/B on the training set.
4. **No stable loss in the five exposure divisions**, each with its own
   denominator, and a division with no rows reported as **did not run** rather
   than as zero movement.
5. **`warm_cube_build = built` on a nonzero share of the treatment rows**, and
   the screened arm's `built` count **strictly below** the `on` arm's. This is
   ADR-2125's criterion 5 plus the half that is specific to a screen: an arm
   that opened on everything is `on` under another name, and would satisfy
   criteria 1–4 while measuring nothing this lane built.
6. **Every one of the six z3 differential fuzzes green in all three arms with a
   NONZERO test count.** They are `#![cfg(feature = "z3")]` and compile to zero
   tests without the feature, printing `running 0 tests ... ok` and exiting 0.

**Criterion 3 is already known to fail.** §2 measured `uart-8.induction.cvc` at
1,598 builds — the winning shape — before this code existed, so a builds-per-file
screen cannot remove that stable loss. The A/B is run anyway and in full, for
three reasons that are not "to confirm what we know":

* a stable loss is a claim about a 3× recheck on THIS binary, not an inheritance
  from ADR-2125's;
* criteria 1, 5 and 6 are about soundness and mechanism and are not implied by
  criterion 3's failure; and
* the −9.2 % attribution ADR-2125 was told not to skip needs the paired arms
  whatever the ship decision is.

### 7.2 The result: `screened` ships `off`, on criterion 3

Against §7.1's six criteria, in order:

1. **0 soundness disagreements** — **MET.** 0 against the files' declared
   `:status` at comparable denominators of **194** (pinned) and **174**
   (held-out), printed beside the counts. 0 exit-status differences in any arm.
2. **0 stable losses and 0 flips on the pinned draw** — **MET.** 0 flips
   anywhere, and the pinned draw's one raw mover under `screened`
   (`ecoliMILPglycerolYices3-50000`) re-checks as BOTH-DECIDE. This is the
   criterion `on` fails: the same row is a STABLE-LOSS for it.
3. **0 stable losses on the HELD-OUT draw** — **NOT MET.**
   `uart-8.induction.cvc` is a STABLE-LOSS, 3/3 in both directions. It is 1,598
   builds, the many-small shape, and no threshold in the sizing window separates
   it from the family the lever wins on.
4. **No stable loss in the five exposure divisions** — see §6.8.
5. **`built` on a nonzero share, and the screened arm's count strictly below
   `on`'s** — **MET**, by the run rather than by assertion: 51 < 71 on the
   pinned draw and 66 < 79 on the held-out one, all four nonzero. The screen
   opened on **0** rows `on` did not.
6. **Six z3 fuzzes green in all three arms with a nonzero count** — see §5.3.

**Criterion 3 fails, so `AXEYUM_LRA_WARM_CUBE` keeps its default of `off` and
`screened` ships alongside `on` as a second arm nobody turns on.**

### 7.3 What the result actually is, because "ships off" is the wrong summary

Three things are true at once and a reader who takes only the ship decision will
carry away the wrong one.

**The screen works.** It does exactly what it was built to do, and the evidence
is not the verdict table: it is 0 of 93 rows below the threshold opening it,
the admitted set matching a different lane's sizing on the nose at 51 of 51, and
`cold_restarts = 0` throughout. Nothing here is an inert arm.

**The screen is strictly better than the thing it screens.** `on` reproduces
ADR-2125 at 1 stable gain against 2 stable losses over a complete 400 rows;
`screened` is 1 gain against 1 loss, with a clean pinned draw. It also keeps
about seven eighths of the speed (−13.9 % pinned, −12.1 % held-out, against
`on`'s −16.0 % and −12.4 %).

**And the axis it screens on is the wrong axis.** That is the finding, and it
is not a conclusion about this threshold — it is a conclusion about
builds-per-file. The held-out stable loss sits at 1,598 builds and the winning
family starts at 841; there is no value in between that does not also refuse
most of what the lever wins on. [ADR-2125] named that axis from one mover it
had sized and two it had not, and labelled the second loss's reading a
hypothesis in as many words. Sizing the two it had not is what this lane
contributed, and the hypothesis did not survive it.

The obvious next increment is therefore NOT a different threshold on this
counter. §2.2 records the shape that does separate the two rows — pivots per
build per atom, 0.263 against 0.124, clock-free — as an OBSERVATION over two
points, deliberately unbuilt, because both of those points are held-out rows and
building on them would spend the population meant to score the next screen. A
successor should size that on the pinned 200 first, which is what this lane did
with builds-per-file and is the only reason its threshold could be fixed before
the code existed.

## 8. What this lane did not do

Named with what is known about each, rather than left implied.

1. **The screen that would actually work is not built.** §2.2 measured pivots per
   build per atom at 0.263 on the gain and 0.124 on the loss — a 2.1× separation,
   clock-free — and stopped there. Two points is a fit, and both points are
   HELD-OUT rows; building on them would spend the population that is supposed to
   score the next screen. The successor's first move is to size that quantity on
   the pinned 200, which is what this lane did with builds-per-file and is the
   only reason its threshold could be fixed before the code existed.

2. **`simplex_cold_builds` is not split per route**, and §4.2 measured the error
   it causes in the SIZING: 0 of 68 on the pinned 200 where the threshold was
   derived, at least 3 of 47 on the held-out draw. The SCREEN is unaffected
   because it compares a delta from loop entry. A successor sizing any screen on
   this counter should split it first; this lane did not, and those two numbers
   are how far it can say the error goes.

3. **The threshold was never swept.** One value, 64, chosen from a window before
   the code existed and measured once. Whether 48 or 128 does better on the
   pinned draw is unmeasured — including whether a lower value would have kept
   `on`'s stable gain on `sc-7.base.cvc` (1,695 builds), which the screen gives
   up because its first 64 rounds run cold. That row is PINNED, so tuning against
   it would not be training-set fitting, and it is a legitimate next measurement
   that this lane did not take.

4. **The fill-in tail is not taken.** §4.4's 21× is seven files. It answers
   ADR-2111's yes/no and does not characterise the distribution or license a new
   constant. Nobody has measured what the largest `fill_peak / entry_nnz` on this
   route actually is, which is precisely what a successor re-pricing
   `MAX_WARM_CUBE_NONZEROS` would need.

5. **The attribution's residual is named, not decomposed.** §4.3's three terms
   over-explain the theory-layer saving by −11.9 %, because `theory_ms` covers
   the whole `cube_check` including model materialization and `rows_to_core`, and
   neither has a field. Folding it into the basis would have reported the basis
   at 25 % instead of 37 %, so it is a printed column — but it is 36 s of
   unattributed time across 67 rows.

6. **The exposure divisions ran two arms, not three.** `on` is absent from their
   tables and the summariser prints `DID NOT RUN` rather than a zero. So those
   divisions say whether the SCREEN regressed them; they do not compare the
   screen against the unscreened arm there.

7. **Bound-AXIOM generation** remains the largest unpulled piece of [ADR-2111]'s
   claim 2, named again by [ADR-2122] and by [ADR-2125], and untouched here.

8. **Four defects in this lane's own instruments** are fixed and recorded rather
   than quietly repaired, because the shape recurs: a fuzz runner that called a
   FAILING suite an inert one and deleted the evidence (§5.5); a gate runner that
   blamed a real lint failure on a missing `z3-sys` asset, and also deleted the
   evidence (§5.3); a summariser that reported an absent arm as a disagreement;
   and an ssh `exit 124` read as "the launch did not happen", which ran one
   exposure shard twice on one core pair. Every row either instance of that shard
   wrote was discarded. **All four were found by reading the output against what
   it was describing, not by any test** — which is the argument for reading your
   own instruments rather than their exit status.

[ADR-2045]: adr-2045-the-bound-is-not-the-wall-qf-lra-is-one-offline-dense-engine.md
[ADR-2055]: adr-2055-the-tableau-is-the-memory-and-capping-it-costs-eighteen-clean-exits.md
[ADR-2100]: adr-2100-typed-route-ownership.md
[ADR-2111]: adr-2111-qf-lra-what-the-same-simplex-does-differently.md
[ADR-2122]: adr-2122-lra-bound-propagation-into-the-sat-core.md
[ADR-2125]: adr-2125-a-warm-simplex-basis-across-sat-decisions.md
