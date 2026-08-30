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

**What cannot be derived with it, and why that is checked rather than
asserted.** Proving `Not (Provable nil pem_instance)` needs soundness
(slice 4), which is not built here. As a non-vacuity sanity check on the
RULE SET's encoding — the standing "the trusted gate cannot tell you a
`Definition`/relation is wrong, only evaluation can" gotcha applies to an
inductive relation exactly as it does to a computed function — this lane
also wrote a **non-kernel, Rust-level** finite forward-chaining decision
procedure (`ipc_provable::tests::saturate`) mirroring the same eleven
constructors one for one over a small fixed formula universe. It derives
`p -> p` and `(p and q) -> p` from the empty context (matching the two
kernel theorems) and does **not** derive `p or not p`. This is justified by
the subformula property of normal intuitionistic natural-deduction
derivations (the universe is exactly the subformula closure the three
queries need), documented explicitly in the module doc and test comments as
a meta/non-kernel check, NOT a formalized soundness or completeness
theorem — that formalization is exactly slice 4's job.

**What slices 3 and 4 now need.**

- **Slice 3** (`eval : Formula -> (Nat -> Nat) -> Nat` via `Formula.rec`):
  `Formula.rec` already exists (`family.rec` from slice 1's
  `add_recursive_datatype_family` call, exposed as
  `IpcHeytingPrelude`'s implicit family — re-derive it the same way
  `formula_list_rec` is exposed here) and needs no new infrastructure; it is
  a motive `fun _ => (Nat -> Nat) -> Nat` recursor application over the five
  `Formula` constructors, using `ipc_heyting.rs`'s `meet3`/`join3`/`himp3`/
  `not3` chain ops as the `and_`/`or_`/`imp` cases and constant `0`/`2` for
  `bot`/`var`. This slice is now unblocked and does not depend on anything
  new from slice 2.
- **Slice 4** (soundness: `Provable ctx phi -> (every valuation satisfying
  ctx satisfies phi)`) is genuine new mathematical content: an induction on
  the DERIVATION, i.e. an eliminator application over `Provable`'s own
  generated recursor (`Provable.rec`, produced automatically by
  `add_inductive` — not yet used anywhere in this lane). The eleven cases
  correspond one-to-one to the eleven constructors; the hardest cases are
  `or_elim` and `imp_intro`/`imp_elim` (needing a `sat : FormulaList ->
  (Nat -> Nat) -> Prop` context-satisfaction notion, itself built the same
  way `eval` is — via `FormulaList.rec`). Once slice 4 lands, combining it
  with `ipc_heyting.rs`'s countermodel (`ipc_heyting_join_not_ne_top`) at
  the valuation `p := 1` gives `Not (Provable nil pem_instance)` by
  contraposition, closing `F:excluded-middle-not-intuitionistic`. **Do not
  attempt slices 3 and 4 in one sitting** — slice 3 alone is a clean,
  small, mechanical piece; slice 4 is the real remaining research/
  engineering content and deserves its own lane.

**Files**: `crates/axeyum-lean-kernel/src/ipc_provable.rs` (new, 700 lines
incl. tests and module docs), `crates/axeyum-lean-kernel/src/lib.rs` (2-line
registration: `mod ipc_provable;` + one `pub use`). Did not touch
`nat_prelude/`, `int_prelude/`, `rat_prelude/`, or `ipc_heyting.rs` itself.

**Checks run**: `scripts/cargo-serialized.sh test -p axeyum-lean-kernel --lib
ipc_` — 11 passed (7 `ipc_heyting::` unaffected, 4 new `ipc_provable::`),
`cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` clean
(needed `#![allow(clippy::similar_names)]` on the module — `phi`/`psi`
collide, matching `int_prelude.rs`/`string_prelude.rs`/`complex.rs`'s same
allow — and one `#[allow(clippy::too_many_lines)]` on `saturate`), `cargo
fmt --all --check` clean, `python3 scripts/validate-facts.py` 0 errors over
2155 facts (unrelated to this change — no fact was touched; the fact stays
`open`, per the standing "do not weaken the fact's statement" rule).

**Commits**: `f92ec06aa` (the `Provable` relation + `FormulaList` + the two
example theorems), `86d4a6928` (the test module: presence checks,
axiom-footprint checks, and the non-kernel finite-search non-vacuity
check).

<!-- plan-section: landed-changes -->

| 2026-08-30 | ipc-provable | Slice 2: `FormulaList` + `Provable` (11-constructor IPC natural-deduction inductive) over `ipc_heyting.rs`'s `Formula`, plus two kernel-checked example derivations and a non-kernel finite-search non-vacuity check; `F:excluded-middle-not-intuitionistic` stays open, needing slices 3 (generic `eval`) and 4 (soundness) |
