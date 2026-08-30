# Carrier replay overclaim — correcting `F:lean-kernel-accepts-the-whole-constructed-real-carrier`

<!-- plan-section: lane-status -->

Lane: `carrier-replay-overclaim`. IN PROGRESS — this is the mandated early
commit and records only the starting point, not a result.

## Status

Started. The fact claims Lean's kernel accepts EVERY declaration of the
constructed-real carrier. L0/S4's census measured 48 declarations Lean's kernel
refuses as theorems (type not a `Prop`) plus 25 blocked behind them, and the
fact's own suite reached a verdict for the first time only after S4 wrapped it
in `on_a_deep_stack` — before that it SIGABRTed, and the crash read as absence.

Work not yet done at this commit.
