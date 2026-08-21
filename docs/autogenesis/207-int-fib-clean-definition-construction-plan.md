# Clean target-owned `Int.fib` construction plan

Date: 2026-08-21

The absent-aware partition shows a 2,537-declaration official closure. Eight
blocked assumptions are present and all share `Int.instDecidablePredEven` as
the nearest rootward carrier; `Quot.ind` is external to the definition.

Rather than clone that closure, the new target-owned `Int.fib` matches the two
integer constructors directly and decides negative-index parity with `Nat.mod`.
Its nonnegative branch is definitionally `Nat.fib`, so exact `Int.fib_natCast`
is proved by `rfl`. One compile, one root export, and two imports are allowed.
Only an empty footprint with identical observations succeeds; admission remains
separate.
