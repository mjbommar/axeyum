# Clean `Int.fib_add_two` V4 result and V5 plan

Date: 2026-08-21

V4 did not reach elaboration of the final normalization because the minimal
natural-Fibonacci import does not expose the `abel` tactic. No export or
submission occurred, and the mathematical frontier remains exactly the two
additive-group identities isolated by V3.

V5 changes only the import surface by adding `Mathlib.Tactic.Abel`; the proof
body is frozen unchanged. A successful compile is insufficient: the exact
root must export and independently import twice with an empty footprint. If
the tactic-generated proof retains assumptions, the route falls back to
target-owned additive lemmas.
