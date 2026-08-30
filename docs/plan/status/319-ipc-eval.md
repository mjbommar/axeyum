# Lane: ipc-eval — slice 3 of `F:excluded-middle-not-intuitionistic`: the generic evaluator

<!-- plan-section: lane-status -->

**Your lane's block (`DONE for this slice`, ipc-eval, 2026-08-30).**
Task was slice 3 of `docs/plan/status/273-logic-excluded-middle.md`'s
decomposition (handed off in `docs/plan/status/318-ipc-provable.md`): a
generic `eval : Formula -> (Nat -> Nat) -> Nat` over `ipc_heyting.rs`'s
`Formula` AST, built as a genuine `Formula.rec` recursor application rather
than the one-off direct-`Nat` computation `ipc_heyting.rs` uses for its
single closed `pem_instance` countermodel check. Landed in a new sibling
file, `crates/axeyum-lean-kernel/src/ipc_eval.rs`. Depends only on slice 1
(`ipc_heyting.rs`); nothing from slice 2 (`ipc_provable.rs`, the `Provable`
relation) was needed, confirming the prior handoff's claim.

**The recursor application.** `Formula.rec.{1} motive m_var m_bot m_and_
m_or_ m_imp`, with motive `fun (_ : Formula) => (Nat -> Nat) -> Nat`
(non-dependent — constant in the `Formula` argument). One minor premise per
constructor, in declaration order:

- `m_var : Nat -> (Nat -> Nat) -> Nat := fun i v => v i`.
- `m_bot : (Nat -> Nat) -> Nat := fun v => 0`.
- `m_and_`/`m_or_`/`m_imp` : `Formula -> Formula -> motive_cod -> motive_cod
  -> motive_cod := fun a b ih_a ih_b v => op (ih_a v) (ih_b v)`, with `op`
  one of `meet3`/`join3`/`himp3` (already declared in `ipc_heyting.rs`).

`eval := fun (f : Formula) => Formula.rec.{1} motive … f`, a plain
`Definition`, admitted through the trusted `Kernel::add_declaration` gate.

Detail moved to [`../notes/319-ipc-eval.md`](../notes/319-ipc-eval.md).

<!-- plan-section: landed-changes -->

| 2026-08-30 | ipc-eval | Slice 3: generic `eval : Formula -> (Nat -> Nat) -> Nat` as a genuine `Formula.rec` application over `ipc_heyting.rs`'s connectives, with a discriminating evaluation test suite (not merely admission) pinning its meaning; cross-checked against the existing countermodel theorem; `F:excluded-middle-not-intuitionistic` stays open, needing slice 4 (soundness) |
