# Lane: queue-unblock-four-families — open four nursery families so a draw becomes authorable

<!-- plan-section: lane-status -->

**Status:** complete. `Nat.count` and `Nat.divMaxPow` declared (definitions and
evaluation tests only, ADR-0653); a four-family draw now passes R5 / R9 /
R11-topic / R11-vocabulary / R12 with only the two disclosure reviews
outstanding. Full reasoning in ADR-1430.

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

## What landed

Two constructions in `crates/axeyum-lean-kernel/src/nat_prelude/count_and_div_max_pow.rs`,
definitions and evaluation tests only:

* `Nat.count (dec : Nat -> Bool) (n : Nat) := Nat.countRange dec n` -- opens
  `Mathlib.Data.Nat.Count`, pool 22, R11 vocabulary 0 of 10. Definitionally
  `countRange`; Mathlib's is a `List.countP` fold over a `DecidablePred`, so
  every mirror stays `open`.
* `Nat.divMaxPowAux` / `Nat.divMaxPow n base` -- opens
  `Mathlib.Data.Nat.MaxPowDiv`, pool 7 alone and 11 bundled with
  `Mathlib.NumberTheory.Bertrand`, R11 vocabulary 0 of 7. Genuinely new.

`cargo test -p axeyum-lean-kernel --lib nat_prelude::` -> **324 passed, 0
failed**. `every_nat_declaration_is_checked_and_axiom_free` fired on the first
run naming all three, and they are registered in `definition_names`.

## Re-screen AFTER declaring, against the kernel (2,829 declarations)

    Mathlib.Data.Nat.Count                natural-counting-predicate   -> held-out
    Mathlib.Data.Nat.Factorization.Basic  natural-prime-factorization  -> development
    Mathlib.Data.Nat.Log                  natural-logarithm-base       -> train
    Mathlib.Data.Nat.MaxPowDiv            natural-max-power-dividing   -> held-out

    select OK: 470 entries
    GUARD REFUSED: R11 ... disclosure ... no review is recorded in
                   holdout-adjacency-review-v1.json

Only the disclosure remains, which ADR-1420 itself classes as not a structural
block. `natural-counting-predicate`'s is substantive: `Nat.count` is
definitionally `countRange`, about which the kernel already carries 19 lemmas,
and the reviewer should decide from that whether the family is blind enough for
held-out.

## Zero-diff over the already-drawn rows

    committed snapshot 2711 declarations; freshly read 2829; new 118, gone 0
    re-derived entries: before 430, after 430
      added 0  removed 0  changed 0
    committed nursery-v2-extension.json publishes 460 rows
      partitions: {'held-out': 170, 'development': 170, 'train': 120}

Zero rows move. The 31 published rows absent from the re-derivation are the
three zero-yield families of the pre-existing red below, and they are absent
from the BEFORE derivation as well.

## Did not run

* `just check` / `scripts/check.sh` -- the coordinator re-runs the full gate
  before merging, so a narrow re-run here gates nothing.
* `scripts/check-shape-duplicates.py` -- `Nat.count` shares a type shape with
  `Nat.countRange`. `shape_search --duplicates` reports ten groups today, six
  of them deliberate aliases already on the allowlist, so if this one is
  reported it needs an allowlist entry with a reason.
* `python3 scripts/gen-autogenesis-nursery-refill.py --check` -- run, and it is
  RED for a pre-existing reason (below), so it could not serve as the zero-diff
  instrument.
