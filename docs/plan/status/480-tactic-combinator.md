# Lane: tactic-combinator — `decide` and a `Then`/`First` tactic combinator over `linarith`/`ring`/`simp`

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, tactic-combinator, 2026-09-03).** Building
`crates/axeyum-lean-kernel/src/decide.rs` (the fourth producer, closed-goal
kernel reduction) and `crates/axeyum-lean-kernel/src/tactic.rs` (the
`Tactic::{Decide,Linarith,Ring,Simp,Then,First}` combinator gluing `simp`'s
normal form into `linarith`/`ring` via `Eq.trans`/transport). In progress.

<!-- plan-section: landed-changes -->

| 2026-09-03 | tactic-combinator | status stub opened |
