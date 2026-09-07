# ADR-1752: the online LRA admission cap becomes budget-relative, and the memory behind it gets bounded where it is spent

Status: accepted
Index-summary: `MAX_ONLINE_LRA_ATOMS = 1_024` accounted for 23 of 54 censused QF_LRA losses and, per the QF_NRA lane's 2026-09-07 A/B, is the real gate behind 62 QF_NRA losses too. It gets two things wrong. A COUNT is the wrong currency — the footprint is `atoms x coefficients-per-atom`, so 23,385 atoms over a handful of variables cost less than 1,492 over 700 and the count refused both identically — and the 8 GiB abort it rested on was measured on 2026-08-03, three days BEFORE `MAX_LRA_CACHED_COEFFICIENTS` bounded the very cost it named, and was never re-taken. So the cap is replaced by a byte budget, derived into the existing coefficient ceilings through a measured `BYTES_PER_LRA_COEFFICIENT`, enforced deterministically from the builder's own counters rather than from a resident-set probe (determinism is a public API promise), and reporting refusals as "projected N MiB > budget M MiB at K atoms over V variables". The count itself SURVIVES as an outer, conservative screen, and that is the honest part: three replacement cost models were built and each was falsified by the corpus (retained coefficients — 7.8 GB abort; the dense tableau — refused a file Fourier-Motzkin decides in 0.18 s; Fourier-Motzkin's own allocations bounded in place — still 7.8 GB on `miplib/danoint-266`). With no `#[global_allocator]` hook nothing here can attribute an allocation it did not make, so a fourth guess would be guessing against a corpus that has said no three times. The screen is calibrated to reproduce `1_024` EXACTLY at the default budget, so the shipped build cannot regress; what changed is that it now moves with `memory_limit_mb` (8 GiB buys 13,107 atoms, where before no amount of memory bought one past 1,024), that refusals say what to do, that the unbounded Fourier-Motzkin fallback is bounded in bytes for the first time, and that the three dead ends are recorded with their file names and numbers.
Index-status: accepted
Date: 2026-09-07

## Context

`crates/axeyum-solver/src/lra_theory.rs` refused any query carrying more than
1,024 distinct linear-real atoms, **before** normalization:

```rust
const MAX_ONLINE_LRA_ATOMS: usize = 1_024;
…
if atom_terms.len() > MAX_ONLINE_LRA_ATOMS { /* Unknown(ResourceLimit) */ }
```

That constant is expensive in two divisions at once.

- **QF_LRA.** The 2026-09-05 loss census attributes **23 of 54** losses to it,
  with no other cause: a clean two-way split against 31 search timeouts. On the
  33-file scoring population, 22 files print no `; theory-layer` line at all —
  no CDCL(T) route ever ran on them.
- **QF_NRA.** The `qf-nra` lane established on 2026-09-07, by an A/B on one
  binary differing only by an environment lever, that the cross-product
  admission bound it had been sent to raise is **not** the binding gate. Lifting
  it hands the query straight to this one, which refuses immediately: the decline
  message changes from "771 cross-products exceed the deterministic admission
  bound of 2" to "online CDCL(T) LRA atom cap exceeded (23385 > 1024)", at the
  same 0.83 s and the same 101 MB peak. **62 QF_NRA losses** sit behind it.

The cap's own doc comment recorded the measurement it rested on: raising it to
16,384 changed the verdict on **none** of the 64 files of the 200-file parity
list that carry more than 1,024 atoms, cost one file 24 s of budget it used to
decline in 0.12 s, and made `QF_LRA/sc/sc-39.base.cvc.smt2` (1,492 atoms) abort
at the 8 GiB memory cap. It named the cost: `AtomBuilder` normalization, a dense
`LinExpr` per atom polarity over ~700 variables.

So "just raise it" is already a refuted move, and this ADR does not propose it.

## Two things the constant gets wrong

**1. A count is the wrong currency.** The construction's footprint is
`atoms × coefficients-per-atom`. 23,385 atoms over a handful of variables cost
less than 1,492 atoms over 700 — and the count refused both, identically. There
is no atom number that separates a query that fits from one that does not,
because the atom number is not what the memory is a function of.

**2. The measurement behind it is stale, and nothing said so.** The cap's
justification was taken on **2026-08-03** (`e62086742`, the warm-simplex
rewiring). The bound that caps exactly the cost it names —
`MAX_LRA_CACHED_COEFFICIENTS`, on the linearization memo — landed on
**2026-08-06** (`96ff85930`, "Enforce shared arithmetic resource bounds"),
**three days later**. The 8 GiB abort was therefore measured in a tree where the
thing the cap was protecting against was unbounded, and it was never re-taken.
Between them, the construction is today bounded by four separate deterministic
ceilings (`MAX_LRA_NORMALIZATION_NODES`, `MAX_LRA_COEFFICIENT_WORK`,
`MAX_LRA_CACHED_COEFFICIENTS`, `simplex::MAX_TABLEAU_CELLS`), of which the atom
count is a redundant fifth.

This is the failure mode CLAUDE.md names under *Gotchas*: **verify a blocker
still exists before treating it as one — a file that records obstacles
accumulates stale ones by construction, and its authority is what makes them
expensive.** The cap's doc was authoritative, specific and numerate, and that is
precisely why nobody re-measured it for a month.

## Decision

**The atom count becomes budget-relative and reportable, and the memory it was
standing in for is bounded where it is spent.** Four parts.

1. `DEFAULT_ONLINE_LRA_BUDGET_BYTES` is the budget when the caller sets no
   `SolverConfig::memory_limit_mb`; when it sets one, that is the budget. Both
   the `CdclT` route (`check_qf_lra_online_cdclt`) and the self-contained
   `DPLL(T)` route (`check_qf_lra_online`) take it, and `smtcomp_cli` gains
   `--memory-limit-mb` so it can be set and reproduced from a command line.
2. `NormalizationLimits::for_budget` **derives** the two coefficient ceilings
   from the budget through `BYTES_PER_LRA_COEFFICIENT`, after spending the dense
   tableau's own ceiling out of it. The node ceiling is left alone: it is a
   *work* bound, not a memory one.
3. The **Fourier–Motzkin fallback is bounded in bytes**, at its entry
   (`n² × size_of::<Rational>()`, in `solve`) and per elimination step
   (`produced × n × size_of::<Rational>()`, in `eliminate`, checked *before* the
   partition loop that clones a length-`n` multiplier vector per row).
   `MAX_FM_CONSTRAINTS` capped a COUNT whose bytes had no bound at all; this is a
   real fix independent of everything else here.
4. The **atom count survives as the outer, conservative screen**, at
   `BYTES_PER_ADMITTED_ATOM = DEFAULT_ONLINE_LRA_BUDGET_BYTES / 1_024`. That
   constant is chosen for exactly one property: at the default budget the screen
   reproduces the shipped `1_024` **exactly**, so the default build's admission
   behaviour is byte-identical and cannot regress. Refusals state their numbers
   and what to do about them.

Enforcement everywhere is **deterministic**, from counters, not from a
resident-set probe: the same query must be admitted or refused identically on a
loaded host and an idle one, which the determinism promise requires and which a
`/proc/self/status` read would break.

### Why the count survives — three cost models, three refutations

The original intent was to delete the count outright. Three replacements were
built, and each was falsified by the corpus rather than by review:

| model | what it was | how it failed |
|---|---|---|
| 1 | retained coefficients | passed `2017-Heizmann-…/_sanfoundry_10_ground.i_6_3_3.bpl_13.smt2`, which then **aborted at 7.8 GB / 5.3 s** where it had declined in 0.82 s at 121 MB. Those bytes are not coefficients. |
| 2 | the dense tableau's size | caught that file and also refused `TM/p5-driverlogNumeric_s9.smt2`, which Fourier–Motzkin decides `unsat` in 0.18 s at 41 MB. Net on 200 files: 97 → 97, one gain, one loss. |
| 3 | Fourier–Motzkin's own allocations, bounded where they are made | correct as far as it goes, and it still did not stop `miplib/danoint-266.smt2`: **7.8 GB, 11 s**, previously a 0.04 s decline at 15 MB, with `simplex_rows=n/a` and `final_checks=1`. |

`crates/axeyum-solver/src/memory_budget.rs` already states why a faithful answer
is ADR-sized: with no `#[global_allocator]` hook, nothing here can attribute an
allocation it did not itself make. Three refutations in one lane is enough
evidence that a per-atom cost model is not available at this altitude, and a
fourth guess would be guessing against a corpus that has already said no three
times.

So what this ADR delivers is **not a looser gate**. It is that the gate moves
with the budget, that a refusal is actionable, that the unbounded engine behind
it is bounded, and that the three dead ends are written down with their file
names and numbers — so the next attempt starts from "where do `danoint-266`'s
7.8 GB go" rather than from a fresh guess.

## Consequences

- The gate moves with the budget.
  `a_wide_shallow_atom_set_is_admitted_where_the_count_cap_refused_it` pins both
  halves of that: 1,025 atoms are still refused at the **default** budget —
  byte-identically to the constant, and the refusal must name the screen and say
  "raise `SolverConfig::memory_limit_mb`" — while a 4 GiB budget admits them.
  Before this, no amount of memory bought a single atom past 1,024.
- A refusal is actionable by a caller and by a sibling division: it names the
  projection, the budget, and the shape that produced them, so "raise
  `memory_limit_mb` to X" is a decision someone can make from the message.
- `a_construction_over_its_memory_budget_refuses_and_names_the_numbers` drives
  the **theory constructor** at a 1 MiB budget — deliberately not the route,
  whose outer screen fires first at any budget small enough to starve the
  coefficient ceiling, so a front-door test would exercise the screen twice and
  this ceiling never. It requires both that it refuses with a projection that
  genuinely exceeds the budget **and** that the same query at 4 GiB is built.
- `the_fourier_motzkin_fallback_declines_on_bytes_instead_of_allocating` drives
  `solve` and `eliminate` directly at three budgets: one that must DECIDE the
  system, one that starves the entry allocation, and one that starves a single
  elimination step while leaving entry affordable. Deleting the byte ceiling
  kills exactly this test and nothing else.
- `the_tableau_cap_and_the_construction_budget_stay_commensurable` pins the two
  halves of the footprint against each other in **both** directions, so the
  tableau cap and the coefficient budget cannot silently drift until one of them
  stops binding. That drift is the exact mechanism that made this ADR necessary.
- `BYTES_PER_LRA_COEFFICIENT` is a **structural accounting** — the four places
  one semantic coefficient is stored, summed, rounded up — and deliberately not a
  measured peak RSS divided by a coefficient count. That division was attempted
  and abandoned: `QF_LRA/sc/sc-11.base.cvc.smt2` is at **617 MiB resident at
  backend entry**, before the LRA route runs at all, so a peak-RSS quotient would
  be a confident number about the wrong thing. The rounding is deliberately in
  the over-estimating direction, because over-estimating refuses a query that
  would have fitted (a lost decide) while under-estimating admits one that will
  not (an abort). The honest bound on the pure-Rust path still stops exactly
  where `crates/axeyum-solver/src/memory_budget.rs` says it stops, at the absence
  of a `#[global_allocator]` hook.
- **Not claimed:** that lifting the cap decides more files. Admission is
  necessary, not sufficient — the earlier sweep found that raising the count to
  16,384 changed no verdict, and nothing here contradicts that. What changed is
  that queries are now refused for a reason that is true, with a number, instead
  of for a count that stopped corresponding to a cost a month ago.

## Alternatives rejected

- **Raise the constant.** Already measured, twice: no verdict changes, one file
  loses 24 s it used to decline in 0.12 s, one file aborts. Raising a wrong
  currency does not make it the right one.
- **Delete the cap with nothing in its place.** Measured at 0 new decides and 54
  memory aborts. The cap is load-bearing; what it is not is *well-shaped*.
- **A resident-set probe instead of a counter.** `MemoryBudget::exceeded` exists
  and is the right instrument for growth an estimate cannot predict, but it is
  9,395 ns per sample and, worse here, it makes admission depend on what else the
  host is doing. Determinism is a public API promise.
