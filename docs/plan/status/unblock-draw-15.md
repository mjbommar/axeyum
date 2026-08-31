# Lane: unblock-draw-15

Status: IN PROGRESS — index-3 candidate found and screened; building the two
definitions.

Context: ADR-1095 / ADR-1100 / ADR-1115. Four consecutive honest declines.
The constraint is positional: `assign_partitions` assigns held-out at cycle
indices 0 and 3, and index 3 needs a late-sorting, topically fresh,
R9/R11/R12-clean family.

## Measured (fresh `shape_search --release`, 2623 declarations)

Screened nine late-sorting candidates against the REAL
`select()`/`assign_partitions()`/`screen_family()`/`is_closed_evaluation`,
with the candidate's constructions simulated into the environment:

| candidate | constructions | pool | R12 | R11 |
| --- | --- | --- | --- | --- |
| `Mathlib.Data.Nat.Find` | `DecidablePred` + `Nat.findGreatest` | 15 | PASS | clean |
| `Mathlib.Data.Nat.Factorization.Root` | `Nat.ceilRoot`+`floorRoot` | 18 | PASS | clean |
| `Mathlib.Data.Nat.MaxPowDiv` | `Nat.divMaxPow`+`padicValNat` | 10 | PASS | clean |
| `Mathlib.Data.Nat.Factorization.LCM` | 2 factorization products | 10 | PASS | clean |
| `Mathlib.Data.Nat.Choose.Central` | `Nat.centralBinom` | 14 | FAIL | refused (topic `Choose`) |
| `Mathlib.Data.Int.Bitwise` | `Int.bit`/`bodd`/`bitwise` | 10 | FAIL | refused (topic `Bitwise`) |
| `Mathlib.NumberTheory.PrimeCounting` | `Nat.primeCounting`(`'`) | 12 | FAIL | clean |
| `Mathlib.Data.Nat.Fib.Zeckendorf` | `Nat.greatestFib` | 11 | PASS | refused (topic `Fib`, vocab 6/10) |
| `Mathlib.Data.Nat.Count` | `Nat.count`+`DecidablePred` | 22 | PASS | clean, but R11 shape-2 contaminated (ADR-1100) |

Chosen: `Mathlib.Data.Nat.Find` with `DecidablePred` + `Nat.findGreatest`.

## Landed changes

(pending)
