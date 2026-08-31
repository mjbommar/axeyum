# Lane: unblock-four-families

Status: IN PROGRESS (opened 2026-08-31)

## Task

Draw 13 (ADR-1095) declined mechanically: `assign_partitions` cycles
`held-out, development, train` over the fresh family set, so `n` fresh
families yield `ceil(n/3)` held-out ones, and guard R5 needs 2. A draw
therefore needs >= 4 fresh families. Every unblock lane so far delivered one
or two constructions, hence one or two families.

This lane's job: make FOUR families available for draw 14, by declaring only
the constructions (ADR-0653: definition + evaluation test, no theorems).

## Progress

- Merged local `main` (f1703204f).
- Reading the real `select()` / `admissible()` screen rather than
  `propose-nursery-refill.py`'s hygiene screen, which overcounts.
