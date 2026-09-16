# ADR-2132: `QF_LRA` — a builds-per-file screen for the warm basis, and the discriminator that turned out not to discriminate

Status: proposed
Index-summary: [ADR-2125] shipped the warm simplex basis `off` on 1 STABLE-GAIN against 2 STABLE-LOSS and named the axis its successor should screen on -- `simplex_cold_builds`, "it wins where the cubes are many and small and loses where they are few and large". This lane SIZED that axis first over the pinned 200 and the distribution is bimodal with no overlap: the few-enormous rows are at 1, 28 and 42 builds (23,908 / 283.5 / 548.1 ms each, and the 28-build row IS the pinned stable loss) while the winning family runs 841-1,543 builds at 0.4-6.4 ms. Every row at or above 51 builds costs at most 12.2 ms/build and every row above 20 ms/build has at most 42, so any threshold in [43, 51] separates them; 64 is the next power of two above that window. THEN THE HEADLINE, and it is not the screen: ADR-2125 could place only ONE of its three movers in its sizing table and labelled the second loss's reading a HYPOTHESIS in as many words. Counted here it is **1,598 builds at 1.04 ms each** -- the MANY-SMALL shape the lever WINS on, 14 % from the gain's 1,815 -- so **no builds-per-file threshold separates them and the hypothesis is REFUTED**. The threshold was NOT then moved between 1,598 and 1,815: those two rows are the held-out evaluation population. IN PROGRESS.
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

**So what is new here is the instrument, not the argument.**
`warm_cube_fill_peak` is that measurement's numerator — the largest nonzero
count the warm tableau has held over its life — reported in §6 against the count
the engine was admitted on. Until this counter existed, "fill-in is why the cell
cap stays" was a reading of the algorithm with no number under it.

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

PLACEHOLDER — filled in at the end of the lane.

### 5.4 Mutation

PLACEHOLDER — filled in at the end of the lane.

## 6. The A/B

PLACEHOLDER — filled in at the end of the lane.

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

### 7.2 The result

PLACEHOLDER — filled in at the end of the lane.

## 8. What this lane did not do

PLACEHOLDER — filled in at the end of the lane.

[ADR-2045]: adr-2045-the-bound-is-not-the-wall-qf-lra-is-one-offline-dense-engine.md
[ADR-2055]: adr-2055-the-tableau-is-the-memory-and-capping-it-costs-eighteen-clean-exits.md
[ADR-2100]: adr-2100-typed-route-ownership.md
[ADR-2111]: adr-2111-qf-lra-what-the-same-simplex-does-differently.md
[ADR-2122]: adr-2122-lra-bound-propagation-into-the-sat-core.md
[ADR-2125]: adr-2125-a-warm-simplex-basis-across-sat-decisions.md
