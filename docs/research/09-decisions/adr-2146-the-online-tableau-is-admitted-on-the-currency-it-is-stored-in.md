# ADR-2146: the online engine's tableau is admitted on the currency it is stored in

Status: proposed
Index-summary: The LRA-MODEL-REPLAY census's largest bucket -- **27 of 47** undecided `QF_LRA` rows at the census screen -- had NO warm tableau: `LraTheory::try_new_with_budget` admits the online CDCL(T) engine's tableau on `TableauAdmission::DenseCells`, `m x (nvars+m)` against `MAX_TABLEAU_CELLS`, a count over storage ADR-2111 made sparse, so the witness fell to `solve_values` (a full Fourier-Motzkin elimination keeping a clone of the whole system per variable) and declined with the clock still available. ADR-2125 already asks the nonzero question for the offline cube decider; the online route's own doc said it does not. Sized at head: 27 / 27 still stop there at 16x -- and **27 / 27 stop at the ATOM SCREEN at the shipped multiplier**, because every one has more than the 1,024 atoms `AXEYUM_LRA_ATOM_SCREEN=1` admits (`sc-27` at 1,036 is the smallest), so at the shipped screen this lever can touch none of the census population and its own A/B measures the files under the screen whose dense count crosses the cap. `AXEYUM_LRA_ADMIT_NONZEROS=1` routes construction through `Incremental::with_online_admission`: entry nonzeros against `MAX_ONLINE_TABLEAU_NONZEROS` (400,000, ADR-2125's figure, deliberately the same), rows against `MAX_ONLINE_TABLEAU_ROWS` (65,536; the dense cap bounded rows implicitly at 2,000 and a nonzero count does not), and -- the half an entry count cannot supply -- a RUN-TIME fill-in cap `MAX_TABLEAU_FILL_NONZEROS` (4,000,000, the dense number in the sparse currency) that `Tableau::run` checks BEFORE a pivot whose worst-case fill-in (`col_nnz[entering] x nnz(pivot row)`) would cross it, because ADR-2132 measured fill-in growing a warm tableau 21x. `Tableau::fill_cap` is `None` for every other constructor, so the OFF arm runs the identical pivot loop. Smoke at 16x with the lever: `Gcd_havoc` and `_sanfoundry_10_ground` go from a model decline at the FIRST complete check to 445 and 100 complete checks in the budget -- the wall is removed and the search does not finish. A/B and decision: see the tables.
Index-status: proposed
Date: 2026-09-17

## Context

The LRA-MODEL-REPLAY census
([`bench-results/lra-model-replay-20260916/`](../../../bench-results/lra-model-replay-20260916/README.md))
split "online CDCL(T) LRA model did not replay (arithmetic outside the
incremental engine)" into three mechanisms over the 47 pinned `QF_LRA` files
that end there. The largest, 27 files, is not arithmetic and not a construct:
the warm simplex engine **did not exist**. `simplex_rows=n/a` in the route
trace; `LraTheory::model` took its `else` branch into `solve_values`, a full
Fourier–Motzkin elimination of every variable that keeps a clone of the whole
system per variable, and that declined on its own budget with the deadline
still available.

Why the engine was absent is the sharp part, and
[ADR-2125](adr-2125-a-warm-simplex-basis-across-sat-decisions.md) had
already measured it from the other side: the online route builds its tableau
with `TableauAdmission::DenseCells`, which refuses when
`m × (nvars+m) > MAX_TABLEAU_CELLS` (`simplex.rs::Incremental::new`) — a
dense-cell count over storage
[ADR-2111](adr-2111-qf-lra-what-the-same-simplex-does-differently.md) made
sparse, disagreeing with the real cost by three orders of magnitude on one
file (8,797,712 cells against 4,688 nonzeros, 188 KB). ADR-2125 opened a
second door for the offline cube decider (`MAX_WARM_CUBE_NONZEROS`) and left
the online route's door alone, and the route's own doc said so: "The online
route keeps `TableauAdmission::DenseCells` byte for byte; only the warm cube
decider asks the other question."

## Sizing at head, and the fact that reframes the lever

Re-run on the 27 with the shipped binary at `43f1e0f90`, both screens
([`sizing-summary.txt`](../../../bench-results/lra-admission-diseq-20260917/sizing-summary.txt)):

| screen | where the 27 stop |
|---|---|
| shipped (`AXEYUM_LRA_ATOM_SCREEN` unset) | **27 / 27** `online_probe=admission-screen` — refused before the tableau question is asked |
| census (`=16`) | **27 / 27** `fm-fallback-declined` + `no-model-reconstructed` |

The mechanism is where the census left it. But the first row is the one that
sizes the lever: **every one of the 27 has more than the 1,024 atoms the
shipped screen admits** (`sc-27` at 1,036 is the smallest, the LassoRanker
rows run to 15,647; census `per-file.tsv`, column `atoms`). The census
population was measured at 16× because that is the screen at which it
exists. So at the shipped screen this lever touches none of the 27, by
arithmetic and not by measurement; what its own A/B measures is the
population at or under the screen whose dense count crosses the cap — a file
with 1,000 equality atoms is 2,000 rows over 3,000 columns, 6,000,000 cells,
and refused today — and the composition with the screen is a second,
separate measurement.

## What each side does today, at `file:line`

| | admission | where |
|---|---|---|
| **axeyum, online route** | `m × (nvars+m) ≤ MAX_TABLEAU_CELLS = 4,000,000`, checked in `Incremental::with_policy` (via `Incremental::new`) | `simplex.rs`, `TableauAdmission::DenseCells` at `lra_online.rs::try_new_with_budget` |
| **axeyum, offline cube decider** | `Σ nnz ≤ MAX_WARM_CUBE_NONZEROS = 400,000` | `simplex.rs::with_nonzero_admission`, ADR-2125 |
| **z3** | none at construction: `static_matrix` stores rows and columns as sparse vectors (`static_matrix.h:88-89`) and the tableau grows with the terms | ADR-2111 §references |
| **cvc5** | none at construction: `Matrix<T>` is sparse row/column lists (`matrix.h:56-196`); the tableau is built as constraints arrive | ADR-2111 §references |

Neither reference bounds the tableau by a cell count; both bound WORK (pivot
budgets, effort levels) and let the representation cost what the nonzeros
cost. ADR-2132 then measured the thing an entry count cannot see: fill-in
grows a warm tableau **21×** in this engine (`sc-39` enters at 4,688 nonzeros
and peaks at 98,572), so "a construction-time nonzero bound is no bound at
all once the engine runs". That measurement is why the lever has a run-time
half.

## The change

Behind `AXEYUM_LRA_ADMIT_NONZEROS` (`1` | `on`; anything else OFF), read once,
also passable as a value (`LraOnlineLevers`).

1. **`TableauAdmission::OnlineNonzeros`** → `Incremental::with_online_admission`
   (`simplex.rs`), three questions where `Incremental::new` asks one:
   * entry nonzeros ≤ **`MAX_ONLINE_TABLEAU_NONZEROS = 400_000`** — the same
     figure as `MAX_WARM_CUBE_NONZEROS`, deliberately: two doors onto one
     structure should agree about what it costs, and both are ADR-2111's
     `TableauReserve::Sparse` figure (11.6× ADR-2055's measured median on the
     route, 2.7× its extreme). A separate constant because the two call sites
     are separate levers with separate A/Bs.
   * rows ≤ **`MAX_ONLINE_TABLEAU_ROWS = 65_536`** — the dense cap bounded
     rows implicitly (`m² ≤ 4,000,000` ⇒ `m ≤ 2,000` even with no problem
     variables) and a nonzero count does not; a row costs its nonzeros in
     storage but a whole slot in every per-row scan (the leaving-variable
     scan, `row_bounded`, the bound vectors). 32× the implicit maximum, about
     2× the largest row count the census population would reach; it refuses
     the absurd, not the measured.
   * **`Tableau::fill_cap = Some(MAX_TABLEAU_FILL_NONZEROS = 4_000_000)`** —
     the dense number restated in the currency the tableau is stored in
     (~190 MiB with the column index, the same order as the 128 MiB the dense
     cap meant). `Tableau::run` refuses BEFORE a pivot whose worst-case
     fill-in `col_nnz[entering] × nnz(pivot row)` would carry the live count
     past it, and answers `RunOutcome::Unknown`, which every caller treats as
     a sound don't-know. Under the dense admission `nnz ≤ cells ≤ 4,000,000`
     held by construction; under a nonzero admission it does not, so the
     bound moves to where the growth happens. `fill_cap` is `None` for every
     other constructor: the OFF arm runs the identical loop, and the
     `fill_cap_declines` counter is 0 there by construction.
2. The live nonzero count the cap reads (`Tableau::nnz_live`) is maintained
   at the single cell-mutation point and by the recount, and checked against
   a full recount after every pivot over the same random population as the
   column-count check.
3. The harness's `ulimit -v 8G` is invisible to the process (ADR-2045) and
   the memory watchdog installs only under `memory_limit_mb`, so this cap and
   not the watchdog is what stands between a nonzero-admitted tableau and an
   `rc=134` abort. The A/B counts aborts per arm; a new one is a loss.

## The controls

* `the_nonzero_admission_builds_the_tableau_the_dense_cap_refuses` — 1,500
  atoms `xᵢ ≥ 0` over their own variables: 4,500,000 dense cells against
  1,500 nonzeros; the dense arm's `uses_simplex` is false and the sparse
  arm's true, with the arithmetic asserted from the constants in `const`
  blocks so a moved cap fails the build.
* `the_two_admissions_agree_on_a_satisfiable_and_an_infeasible_system` —
  both arms, both verdict sides, the witness replayed, the core naming both
  crossing atoms (the dense arm decides by Fourier–Motzkin, the sparse by the
  tableau; a wrong tableau disagrees here).
* `the_admission_arms_agree_through_the_route_on_a_query_the_dense_cap_refuses`
  — 1,000 equalities through `check_qf_lra_online_cdclt_with_levers`, sat
  and its infeasible neighbour, both arms.
* `the_online_admission_refuses_on_rows_alone`,
  `the_online_admission_refuses_on_nonzeros_alone` — each ceiling straddled
  by one unit with the other under its cap.
* `the_fill_cap_declines_before_the_pivot_that_would_cross_it` — the same
  random system decided uncapped and `Unknown` under a cap at its entry
  count, `fill_cap_declines = 1`, the live count held at or under the cap
  (refused BEFORE the pivot); a seed that never grows is skipped and at least
  one must not be.
* `the_live_nonzero_count_matches_the_recount_after_every_pivot`.

Fuzz seed class: `qf_lra_differential_fuzz::boundary_tableaux_agree_with_z3`
— 12 wide-shallow seeds of 1,000 single-variable atoms (equalities at two
thirds so the row count crosses the cap) plus 16 linking atoms and a
disjunctive spine, each seed asserted to cross `MAX_TABLEAU_CELLS` by a
solver-free companion test, compared against z3 in whichever arm the
environment selects; the gate runs the file under all four arms.

Mutation controls: `lra-admit-nonzeros-lever` (the lever selects
`DenseCells` whatever the arm — the inert-arm shape),
`lra-admit-nonzeros-row-cap`, `lra-admit-nonzeros-nnz-cap`,
`lra-admit-nonzeros-fill-cap`, `lra-admit-nonzeros-live-count`; one test per
suite.

## The measurement

<!-- A/B tables: filled in from bench-results/lra-admission-diseq-20260917 -->

_Pending: the A/B tables (QF_LRA pinned 200, QF_UFLRA pinned 200 — the
`uflra_online` route constructs the same theory through `new_with_deadline`,
so this lever reaches it; QF_RDL and QF_IDL controls; QF_LRA held-out 200),
the composition with `AXEYUM_LRA_ATOM_SCREEN=16` on the pinned 200, the 3×
rechecks, and the ship decision are appended when the sweeps on s5/s6
complete._

## Gates run

_Pending: filled in with counts._

## Consequences

* The online route asks the same question about its tableau that the cube
  decider asks, and the doc that said it did not is corrected.
* `MAX_TABLEAU_CELLS` is not changed; it stays the OFF arm's admission and the
  cube decider's untouched neighbour.
* The trace carries `fill_cap_declines`, so a run that hit the cap is
  distinguishable from one that timed out.
* `AXEYUM_LRA_ATOM_SCREEN` is unchanged. The lever that reaches the census
  population is the COMPOSITION of this one with the screen, and that is
  measured, not assumed.
