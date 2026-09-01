# Lane: nursery-draw-18

## Status (2026-09-01, in progress)

Task: author nursery refill draw 18 -- a four-family draw filling
`gen-autogenesis-nursery-refill.py`'s `FAMILY_MODULES`/`FAMILY_ROUTES` so
`check-dispatchable-frontier.py` clears its floor of 10.

### Re-measurement at 683884197 (== origin/main, no merge needed)

| gate | exit | headline |
| --- | ---: | --- |
| `gen-autogenesis-nursery-refill.py --check` | 0 | `entries=460 env=2838` |
| `check-autogenesis-nursery.py` | 0 | now GREEN (was red per ADR-1450; the cross-population component is fixed) |
| `check-autogenesis-holdout-isolation.py` | 0 | `held_out=186 verdict=PASS` |
| `check-holdout-adjacency.py` | 0 | 18 held-out families, 0 refused, 4 undisclosed (advisory) |
| `check-dispatchable-frontier.py` | **1** | G7, **2** dispatchable, floor 10 |
| `validate-facts.py` | 0 | 2536 facts, 0 errors |

### Inherited state

- ADR-1430 declared `Nat.count`/`Nat.divMaxPow`. ADR-1450 (draw 17) refused
  `Nat.count` as held-out (definitional alias of `Nat.countRange`, 22 existing
  lemmas cover 4-5 of its 10 drawn rows) and named the unblock: declare a
  construction opening a module sorting before `MaxPowDiv`, leaving room for
  two more families in the window.
- Commit `36f85826f` (this session, before this lane started) declared
  `Nat.factorizationLCMLeft`/`Right`, opening
  `Mathlib.Data.Nat.Factorization.LCM` (pool 10), screened clean as a fresh
  held-out candidate, with its R11 disclosure review already written into
  `holdout-adjacency-review-v1.json` (`natural-factorization-lcm`). It
  re-derived the LCM->MaxPowDiv window: `Factorization.PrimePow` (2),
  `Factors` (2), `Fib.Zeckendorf` (0), `GCD.BigOperators` (0), `Lattice` (0),
  `Log` (17) -- 21 rows across six modules, enough for two more families:
  `Log` alone (17 rows) as one, and
  `PrimePow + Factors + Factorization.Basic (5) + Factorization.Induction (1)`
  (exactly 10) as the other, topically coherent "prime-power factorization"
  bundle.
- Remaining work per that commit's own note: MaxPowDiv's own disclosure
  review, and authoring the draw.

Work in progress -- will update on completion.
