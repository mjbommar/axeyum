# 353 — nursery draw 7

<!-- plan-section: lane-status -->

**Status: IN PROGRESS (early commit — incomplete).**

Authoring the draw that ADR-0645 and ADR-0653 declined twice. Both blockers
named by ADR-0653 are cleared on this tree: `Nat.nth` was banked by the draw-6b
lane, and `Nat.fermatNumber` landed on main
(`crates/axeyum-lean-kernel/src/nat_prelude/fermat_number.rs`).

## Measured so far

Probe from [`../notes/351-nursery-draw-6b.md`](../notes/351-nursery-draw-6b.md),
run unchanged against this tree. It imports the real generator and calls the
generator's own screens, so nothing is reimplemented.

    env declarations       = 2383        (ADR-0653 measured 2374; do not carry)
    inventory rows         = 9729
    admissible constants   = 2455
    ready un-owned modules at the PER_FAMILY floor = 11

The two candidate held-out families, by the generator's own yield:

| module | generator rows | R9 first-10 | R9 whole module |
| --- | --- | --- | --- |
| `Mathlib.NumberTheory.Fermat` | 13 | **0/10** | 0/13 |
| `Mathlib.Data.Nat.Nth` | 11 | **0/10** | 0/11 |

`Mathlib.Data.Nat.Dist` is 18 rows at **R9 2/10** — contaminated exactly as
ADR-0653 measured, and it stays off held-out.

Remaining work: partition cycle, the guard dry-run, the write, and the gates.

## Landed changes

_None yet._
