# Lane: unblock-draw-16

Status: IN PROGRESS (started 2026-08-31)

## Goal

Make draw 16 possible: find or build what lets a fifth family sit at cycle
index 3 (a held-out slot), and re-screen with the real
`select()`/`assign_partitions()`/`guard()`/`screen_family()` machinery.
Do not author the draw.

## Inherited state (to be re-measured, not trusted)

- Draw 15 landed (ADR-1175): entries 380 -> 420, held-out 146 -> 166.
- Two lanes then closed 22 mirrors (Nat min/max 12, Stirling 10).
- `G7 queue-below-floor` red again: 4 dispatchable against a floor of 10.
- ADR-1160 pre-screened three remaining index-3 candidates:
  `Factorization.Root` (18 rows), `MaxPowDiv` (10), `Factorization.LCM` (10).
  All three draw boundary equations their construction would settle by
  reduction, so all three need the ADR-1160 reading before use.

## Progress

- Merged local `main` (7e993bb24). Read ADR-1160 and ADR-1175.
