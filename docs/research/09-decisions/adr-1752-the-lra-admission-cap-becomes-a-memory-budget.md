# ADR-1752: the online LRA admission cap becomes a memory budget, in bytes

Status: accepted
Index-summary: `MAX_ONLINE_LRA_ATOMS = 1_024` accounted for 23 of 54 censused QF_LRA losses and, per the QF_NRA lane's 2026-09-07 A/B, is the real gate behind 62 QF_NRA losses too. It gets two things wrong. A COUNT is the wrong currency — the footprint is `atoms x coefficients-per-atom`, so 23,385 atoms over a handful of variables cost less than 1,492 over 700 and the count refused both identically — and the 8 GiB abort it rested on was measured on 2026-08-03, three days BEFORE `MAX_LRA_CACHED_COEFFICIENTS` bounded the very cost it named, and was never re-taken. So the cap is replaced by a byte budget, derived into the existing coefficient ceilings through a measured `BYTES_PER_LRA_COEFFICIENT`, enforced deterministically from the builder's own counters rather than from a resident-set probe (determinism is a public API promise), and reporting refusals as "projected N MiB > budget M MiB at K atoms over V variables". The budget keeps the derived ceilings close to the ones already in force: this is a change of currency and reporting, not a loosening, and it does NOT claim to decide more files — admission is necessary, not sufficient.
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

**Replace the atom-count admission cap with a memory budget in bytes**, charged
incrementally from the builder's own deterministic counters.

1. `DEFAULT_ONLINE_LRA_BUDGET_BYTES` is the budget when the caller sets no
   `SolverConfig::memory_limit_mb`; when it sets one, that is the budget. Both
   the `CdclT` route (`check_qf_lra_online_cdclt`) and the self-contained
   `DPLL(T)` route (`check_qf_lra_online`) take it.
2. `NormalizationLimits::for_budget` **derives** the two coefficient ceilings
   from the budget through a measured `BYTES_PER_LRA_COEFFICIENT`. The node
   ceiling is left alone: it is a *work* bound, not a memory one — a term graph
   can be walked without retaining anything — and it keeps reporting the
   undifferentiated `ResourceLimit` so a reader can tell "too big to walk" from
   "would not fit".
3. The refusal **states the numbers**:
   `online CDCL(T) LRA memory budget exceeded: projected N MiB > budget M MiB at
   K atoms over V variables`. The constant's message was `1493 > 1024`, which is
   why nobody could tell for a month whether it was still load-bearing.
4. Enforcement is **deterministic**, from counters, not from a resident-set
   probe. The same query is admitted or refused identically on a loaded host and
   an idle one, which the determinism promise requires and which a
   `/proc/self/status` read would break.

The budget is set so the derived ceilings sit close to the ones already in force,
so this is a change of *currency and reporting*, not a loosening. What it buys is
that a **wide-and-shallow** query — many atoms, few coefficients each, which is
exactly the QF_NRA cross-product shape — is now admitted on its actual cost.

## Consequences

- A query is judged on what it will cost rather than on how many atoms it has.
  `a_wide_shallow_atom_set_is_admitted_where_the_count_cap_refused_it` pins the
  case the count got wrong: 1,025 atoms of the form `xᵢ ≥ 0`, one coefficient
  each, which the constant refused and the budget admits.
- A refusal is actionable by a caller and by a sibling division: it names the
  projection, the budget, and the shape that produced them, so "raise
  `memory_limit_mb` to X" is a decision someone can make from the message.
- `a_construction_over_its_memory_budget_refuses_and_names_the_numbers` drives
  the route at a 1 MiB budget and requires both that it refuses **and** that the
  same query under a generous budget does not — a budget that cannot refuse, and
  a budget that refuses everything, both fail it.
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
