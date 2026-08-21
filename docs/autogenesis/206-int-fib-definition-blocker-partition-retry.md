# Absent-aware `Int.fib` blocker partition retry

Date: 2026-08-21

The strict V1 path audit stopped when `Quot.ind`, present in the reflexive
theorem footprint, was absent from `Int.fib`'s own declaration closure. This is
evidence that theorem-level and representation-level contamination differ, but
it produced no complete partition and received no credit.

V2 changes the reusable auditor to emit an explicit absent row rather than
abort. One newly preregistered read will partition all nine blockers into those
carried by `Int.fib` and those introduced elsewhere, without rendering bodies.
