# Lane `queue-unblock-four-families`

**Status:** screening complete, declarations not yet started. First commit is the
screening table, before any Rust, as ADR-1420 and ADR-0653 require.

Base: `46bc65cc4` (`git merge main` -> Already up to date).

## What this lane was sent to do

Open four fresh nursery families so a refill draw becomes authorable. ADR-1420
proved a draw is refused today: R5 needs two NEW held-out families, `_with_cycle`
gives `ceil(n/3)` held-out so `n >= 4`, and at most one held-out-safe family was
constructible from the modules unowned at that time.

## Screen A -- the criterion, run with the real machinery

`select()`'s row screen, `check-holdout-adjacency.screen_family` (R11),
`check-holdout-closed-evaluation.is_closed_evaluation` (R12) and the environment
snapshot (R9), with the candidate constructions **simulated** into the
environment rather than declared. Environment 2,711 + 7 simulated; 58 published
families, 40 development/train.

| candidate family | modules | new decls | pool | R9 | R12 | R11 |
| --- | --- | --- | ---: | ---: | ---: | --- |
| `natural-counting-predicate` | `Mathlib.Data.Nat.Count` | `Nat.count` | **22** | 0 | 0 | **clean**, vocab 0/10 |
| `natural-factorization-lcm` | `Mathlib.Data.Nat.Factorization.LCM` | `Nat.factorizationLCMLeft`, `Nat.factorizationLCMRight` | **10** | 0 | 0 | **clean** |
| `natural-factorisation-properties` | `Mathlib.NumberTheory.FactorisationProperties` | none | 15 | 0 | **2** | clean, vocab 4/10 |
| `natural-logarithm-base` | `Mathlib.Data.Nat.Log` | none | 17 | 0 | 0 | refused -- topic `Log`, vocab 10/10 |
| `natural-prime-counting` | `Bertrand` + `PowModTotient` + `PrimeCounting` | `Nat.primeCounting`, `Nat.primeCounting'` | 17 | 0 | 0 | refused -- vocab 8/10 |
| `natural-factorization-lcm` **bundled with** `Factorization.Basic` | 2 modules | same 2 | 15 | 0 | 0 | refused -- vocab 6/10 |
| `natural-binary-recursion` | `Mathlib.Data.Nat.BinaryRec` | `Nat.bitCasesOn` | 8 | **3** | 0 | refused -- vocab 8/8, and SHORT |
| `natural-max-pow-div` | `Mathlib.Data.Nat.MaxPowDiv` | `Nat.divMaxPow` | 7 | 0 | 0 | clean, but SHORT |

`PER_FAMILY` is 10, so anything under 10 makes `select()` raise.

Two families are **held-out-safe**: `Mathlib.Data.Nat.Count` behind one
declaration, and `Mathlib.Data.Nat.Factorization.LCM` behind two. Four families
in total are usable, the other two as development/train.

## Correction to ADR-1420

ADR-1420 concluded, exhaustively over `2^18` subsets, that
`Mathlib.Tactic.IntervalCases` is in every viable held-out subset and that no
two disjoint viable families exist. That was correct **for the modules statable
at the time**. Enlarging the universe by the 63 plain `Nat.*` / `Int.*` names
that a lane can honestly declare as kernel `Definition`s turns 18 topic-clean
modules into 33, and the exhaustive search over that universe finds **1,132**
viable held-out subsets (<= 3 modules, <= 3 declarations) and two disjoint
families at a total cost of **one** declaration. The blocker ADR-1420 measured
is a supply problem in the *statable* dimension, and the ADR's own Route 1 --
declare a construction -- is exactly what moves it.

## Pre-existing red, unrelated to this lane

`python3 scripts/gen-autogenesis-nursery-refill.py --check` **exits 1 on `main`
at `46bc65cc4`**:

    autogenesis-nursery-refill: family 'natural-find-greatest' yields 0 screened
    candidates, fewer than the 10 the refill takes

`Mathlib.Data.Nat.Find`'s 32 rows now screen as 17 blocked on `Nat.find` and
**15 blocked by the divergence registry**, which commit `a3da5621c`
(ADR-1415's module-doc sweep) widened. ADR-1420 recorded this same command
exiting 0 with `entries=460` on `a6c531eab`, so it went red between those two
commits. It blocks any draw regardless of what families exist, and it also
blocks using `--check` as the zero-diff instrument.

## Files

Probe scripts live in `.lane-scratch/` and are not committed as tooling; they
load the real generator and screens by path and write nothing.
