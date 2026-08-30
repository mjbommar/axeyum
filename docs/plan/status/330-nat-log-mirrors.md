# Lane: nat-log-mirrors — `Nat.log`/`Nat.clog` order mirrors

<!-- plan-section: lane-status -->

**Your lane's block (`DONE (9 of 14 dispatchable log/clog mirrors closed;
5 remain open with a scoped handoff below -- log_le_clog is the cheapest
next target, its whole proof sketch is written out; the two AntitoneOn
facts are NOT blocked by a missing Set type the way this task's brief
assumed, they are blocked by a genuinely new monotonicity-in-the-base
lemma nobody has built)`, nat-log-mirrors, 2026-08-30).**

## Closed: 9 of 14

Four already existed as admitted kernel theorems before this lane started
(built by the `log.rs`/`clog.rs` lane on 2026-08-28, never flipped as `ml430`
mirrors): `Nat.log_one_left`, `Nat.log_one_right`, `Nat.clog_one_left`,
`Nat.clog_one_right`. No new proof work for these four — verified the
rendered kernel type against `formal.statement` character-by-character via
`nat_theorem_inventory --release` and flipped status.

Five are new kernel constructions, all in the new
`crates/axeyum-lean-kernel/src/nat_prelude/log_clog_order.rs`:

Detail moved to [`../notes/330-nat-log-mirrors.md`](../notes/330-nat-log-mirrors.md).

