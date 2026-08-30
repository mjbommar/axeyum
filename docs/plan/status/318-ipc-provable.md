# Lane: ipc-provable — slice 2 of `F:excluded-middle-not-intuitionistic`: the `Provable` relation

<!-- plan-section: lane-status -->

**Your lane's block (`DONE for this slice`, ipc-provable, 2026-08-30).**
Task was slice 2 of `docs/plan/status/273-logic-excluded-middle.md`'s
decomposition: an inductive `Provable` relation for IPC natural deduction,
over the `Formula` AST slice 1 already landed in `ipc_heyting.rs`. Landed in
a new sibling file, `crates/axeyum-lean-kernel/src/ipc_provable.rs`.

**The relation's shape.** `FormulaList` (`nil | cons (head : Formula) (tail :
FormulaList)`) is the context type, built the same way `Formula` and `Str`
were — `Kernel::add_recursive_datatype_family` with `Formula` itself as the
(non-recursive) carrier sort. `Provable : FormulaList -> Formula -> Prop` is
a genuinely INDEXED `Prop`-valued inductive (`num_params = 0`, both arguments
are indices — unlike `Nat.le`'s fixed `n` or `Acc`'s fixed `(α, r)`, nothing
in `Provable` stays literally the same variable across a whole derivation,
since `weaken`/`or_elim`/`imp_intro` all change the context), built directly
via the general `Kernel::add_inductive` — the trusted gate that already
admits `Nat.le` (`nat_prelude/order.rs`) and `Acc` (`prelude.rs`), both
consulted as templates for "a hypothesis field that is a recursive
application of the family at a DIFFERENT index than the conclusion."

Eleven constructors, the standard IPC natural-deduction rules: `ax_head` +
`weaken` (together generating exactly "the goal occurs somewhere in the
context," since the kernel has no separate `Mem` relation either),
`and_intro`, `and_elim1`, `and_elim2`, `or_intro1`, `or_intro2`, `or_elim`,
`imp_intro`, `imp_elim`, `bot_elim`.

**What can be derived with it (kernel-checked, not asserted).** Two closed
theorems, each a genuine ND proof term through the trusted gate:
`ipc_provable_imp_self : Provable nil (imp p p)` (`imp_intro (ax_head)`) and
`ipc_provable_and_elim1_example : Provable nil (imp (and_ p q) p)`
(`imp_intro (and_elim1 (ax_head))`). Both admit on the first attempt and are
axiom-free (`Kernel::axiom_footprint` checked empty in-test).

Detail moved to [`../notes/318-ipc-provable.md`](../notes/318-ipc-provable.md).

<!-- plan-section: landed-changes -->

| 2026-08-30 | ipc-provable | Slice 2: `FormulaList` + `Provable` (11-constructor IPC natural-deduction inductive) over `ipc_heyting.rs`'s `Formula`, plus two kernel-checked example derivations and a non-kernel finite-search non-vacuity check; `F:excluded-middle-not-intuitionistic` stays open, needing slices 3 (generic `eval`) and 4 (soundness) |
