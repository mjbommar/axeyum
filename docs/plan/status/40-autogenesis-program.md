# Lane: autogenesis-program

<!-- plan-section: lane-status -->

**Status:** Exact Mathlib 4.30 `Nat.fib_gcd`, `Nat.fib_dvd`, `Int.fib_natCast`, `Int.fib_add_two`, both recurrence corollaries, `Int.fib_neg`, `Int.gcd_fib`, `Int.fib_dvd`, `Int.fib_of_nonneg`, `Nat.fib_pos`, `Nat.fib_eq_zero`, and now `Int.fib_eq_zero` are durably proved with empty kernel footprints. An isolated clean replay independently reproduced `Int.fib_eq_zero` selection, certified execution, exit-75 recovery, exactly one ledger write, its proved fact, and the preregistered empty readiness delta.

**Next:** preregister exact `Int.fib_add` specialization over sealed recurrence uniqueness, exact constructive induction, admitted `Int.fib_add_two`, and the smallest clean algebra/base-value supports.

Detail and older landed rows moved to [`../notes/40-autogenesis-program.md`](../notes/40-autogenesis-program.md).

<!-- plan-section: landed-changes -->

| 2026-08-22 | (pending) | Corrected-checker `Nat.fib_eq_zero` transaction is frozen from clean commit `39b408e619f2` before one crash-safe intent fault and one recovery |
| 2026-08-22 | (pending) | Exit-75 intent fault leaves `Nat.fib_eq_zero` unchanged; recovery performs exactly one ledger write, the registered checker passes, and the measured readiness delta is empty as preregistered |
| 2026-08-22 | (pending) | Replay preflight declines before mutation because current checker-text gate scanning differs from the retained frontier; exact registration commit reproduces the retained frontier byte-for-byte and is frozen as the V2 replay source |
| 2026-08-22 | (pending) | Historical-source preflight correctly rejects its still-open fact; V3 freezes the exact detached transition child, which preserves the registration gate surface and recovered post-state required by replay verification |
| 2026-08-22 | (pending) | Isolated replay `b63854f8…bfaa0` independently repeats `Nat.fib_eq_zero` selection, certified execution, exit-75 recovery, one write, and the exact empty readiness delta |
