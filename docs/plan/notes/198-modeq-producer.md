# Notes: 198-modeq-producer

Detail moved out of [`../status/198-modeq-producer.md`](../status/198-modeq-producer.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

1. **The entire Lean 4.30 `Int` API is `propext`-dependent** — `Int.add_comm`
   and `Int.sub_self` included, not just the `emod` lemmas. The
   empty-axiom-footprint import route therefore cannot reach ANY `Int` target
   without rebuilding `Int` arithmetic from constructors, which is why the Int
   `ModEq` family was closed by the kernel-authored route and why this lane
   closed its train member the same way.
2. **`Nat.ModEq.gcd_eq` (`F:ml430-nat-modeq-gcd-eq-5167ff4f`) is the one
   sibling this route cannot reach**, and the reason is measured, not guessed:
   `Nat.gcd.eq_def` carries `Quot.sound` (`Nat.gcd_zero_left`, `Nat.gcd_succ`
   likewise), so no axiom-free candidate can unfold `Nat.gcd`. The mathematics
   is easy — `gcd a m = gcd (a % m) m = gcd (b % m) m = gcd b m` — and the
   blocker is entirely `Nat.gcd`'s well-founded recursion.

**Pre-existing red this lane did NOT cause, and did not fix:**
`check-development-partition.py` was already failing on `main` for
`authoritative-mathlib-nat-modeq-remainder-family-v1` (a development-only
operation with no train reference); it still is. `clippy -D warnings` on
`axeyum-lean-import` is red on `statement_goal_record.rs:131`
(`format_push_string`), untouched by this lane.
