# Lane: nursery-draw-17 — author nursery refill draw 17 and clear the dispatchable floor

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, nursery-draw-17, 2026-09-01).** Baseline re-measured;
the `Nat.count` blindness review is written below and it is a REFUSAL.

## Baseline at `b558d9b5a` (this worktree == `origin/main`, clean)

| gate | exit | headline |
| --- | ---: | --- |
| `gen-autogenesis-nursery-refill.py --check` | **0** | `entries=460 ... env=2829 development=170 held-out=170 train=120 screen_drift=31` |
| `check-autogenesis-holdout-isolation.py` | **0** | `held_out=186 files_scanned=1110 verdict=PASS` |
| `check-holdout-adjacency.py` | **0** | 18 held-out families, 0 refused, 4 undisclosed (advisory) |
| `check-dispatchable-frontier.py` | **1** | G7 queue-below-floor, **2** dispatchable, floor 10 |
| `validate-facts.py` | **0** | — |
| `check-autogenesis-nursery.py` | **1** | pre-existing cross-population `depends_on` component |

Corrections to the briefed numbers, re-derived not inherited:

- Dispatchable frontier is **2**, not 3 (ADR-1420 measured 3 at `a6c531eab`).
- `gen-autogenesis-nursery-refill.py --check` is **green**; ADR-1430 recorded it
  red at `46bc65cc4`, and ADR-1445's membership freeze returned it to green.
- ADR-1430's four-family draw **does not run as stated**: with single-module
  families `select()` raises — `Mathlib.Data.Nat.MaxPowDiv` yields **7** and
  `Mathlib.Data.Nat.Factorization.Basic` yields **5**, against `PER_FAMILY` 10.
  Both of its "fillers" have to be bundles, which its own table does not say.

## The draw IS authorable, mechanically

`bench-results/local/nd17/arrA.json` through the real `select()`/`guard()`:

    [0] Mathlib.Data.Nat.Count              natural-counting-predicate   -> held-out
    [1] Mathlib.Data.Nat.Factorization.Basic natural-prime-factorization -> development
    [2] Mathlib.Data.Nat.Log                natural-logarithm-base       -> train
    [3] Mathlib.Data.Nat.MaxPowDiv          natural-max-power-dividing   -> held-out
    select OK: 500 entries, 40 new;  R9 CLEAN, R12 CLEAN, R11 topic/vocab clean,
    CHURN over already-drawn families: NONE
    only refusal: R11 disclosure, both new held-out families

## `Nat.count` is NOT blind. The review refuses it.

Two independent reasons, both measured (detail in the ADR).

**1. Five of the ten drawn rows are already decided here.** Our `Nat.count dec n
:= Nat.countRange dec n` is a definitional alias, and the kernel carries **22**
`countRange` lemmas (the module doc says 19; re-counted from
`kernel-environment-snapshot-v1.json`). Four drawn rows are the same proposition
term-for-term and a fifth is entailed by a strictly stronger declared equation.

**2. Worse — by the divergence registry's own standard the family is
unclosable.** Mathlib's `Nat.count : (ℕ → Prop) → [DecidablePred p] → ℕ → ℕ`;
ours is `(Nat → Bool) → Nat → Nat`. That is the *same* divergence the registry
records for `Nat.nth` and a *larger* one than `Nat.findGreatest`'s.

**And the assignment cannot be repaired.** Moving Count off cycle index 0 needs a
held-out-safe family whose primary module sorts before `Mathlib.Data.Nat.Count`.
Exhaustive over all subsets of the 10 such unowned modules: **902 subsets reach
the ten-row floor, 0 are viable.**

Next: the exhaustive screen over the post-Count region, then the decision.
