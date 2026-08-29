# Lane: int-two-sided-induction — two-sided induction over ℤ, and `Int.fib_add`

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, int-two-sided-induction, 2026-08-29).** Building
`Int.induction_on` (`crates/axeyum-lean-kernel/src/int_prelude/two_sided_induction.rs`),
the first combinator in `int_prelude/` that actually inducts over `ℤ` rather
than case-splitting with `Int.rec`. First commit is deliberately early and
unverified; the kernel gate had not run when it was made.

<!-- plan-section: landed-changes -->

| 2026-08-29 | int-two-sided-induction | `Int.induction_on`: two-sided induction over ℤ (WIP) |
