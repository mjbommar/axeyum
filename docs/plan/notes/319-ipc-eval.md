# Notes: 319-ipc-eval

Detail moved out of [`../status/319-ipc-eval.md`](../status/319-ipc-eval.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**The one real bug, and how it was found.** The first draft typed the two
induction-hypothesis binders `ih_a`/`ih_b` (in the shared `and_`/`or_`/`imp`
minor builder) as `val_ty` (`Nat -> Nat`, the valuation's own type) instead
of `motive_codomain` (`(Nat -> Nat) -> Nat`, what `Formula.rec`'s induction
hypothesis for a direct recursive field actually carries — per
`inductive.rs`'s recursor schema, `ih_j : motive f_j` for a telescope-free
recursive field `f_j`). `add_declaration` failed with an opaque
`TypeMismatch { expected: ExprId(732378), got: ExprId(5776) }` naming
neither binder. Isolated with a temporary debug probe (`Kernel::infer` on
each minor premise in isolation before assembling the recursor application)
rather than bisecting: `m_and`'s OWN inferred type failed with `TypeMismatch
{ expected: ExprId(3), .. }` — a single-digit `expected`, this workspace's
own tell for "the kernel wanted a Sort" — which pinpointed the binder-type
bug directly. The probe was removed before the final commit; the fix and
what it caught are recorded in `binop_minor`'s doc comment so the next
reader does not repeat it.

**Non-negotiable evaluation testing (this is a `Definition`, not a
`Theorem` — admission proves nothing about what it computes).** Eight
tests, each hand-computed in a doc comment before the assertion, against
`ipc_heyting.rs`'s own `meet3 = min`/`join3 = max`/`himp3 a b = if a<=b then
2 else b`:

- Presence (`eval` is a real declaration) and structural type check
  (`Formula -> (Nat -> Nat) -> Nat`, via `infer` + `def_eq`, not assumed).
- `eval(bot, v) = 0` for an arbitrary valuation.
- `eval(var i, v) = v i`, checked at the SAME formula (`var 0`) under TWO
  DIFFERENT valuations (`const 0` vs `const 1`) — this is what proves `eval`
  actually consumes its `v` argument rather than ignoring it.
- **Discriminating check**: at `(v(0), v(1)) = (0, 1)`, `meet3(0,1)=0`,
  `join3(0,1)=1`, `himp3(0,1)=2` are all three DIFFERENT, and `eval` applied
  to `and_`/`or_`/`imp` of `(var 0, var 1)` reproduces exactly those three
  distinct values — a copy-paste error between the three connective minors
  would fail loudly here rather than pass silently.
- **Nested formula**: `eval(imp (var 0) (or_ (var 0) bot), const 1) = 2`
  (`p -> (p or bot)` is IPC-valid, evaluates to top), exercising the
  recursor past depth 1.
- **Cross-check against the existing countermodel**: `eval(pem_instance,
  const 1) = 1`, matching `ipc_heyting_join_not_ne_top`'s already-proven
  `join3 1 (not3 1) = 1` — ties the new generic recursor path back to the
  existing direct-`Nat` computation of the SAME formula, rather than
  introducing an independent unchecked claim about it.
- `axiom_footprint(eval)` is empty.

**Checks run**: `scripts/cargo-serialized.sh test -p axeyum-lean-kernel
--lib ipc_` — 19 passed (7 `ipc_heyting::` + 4 `ipc_provable::` unaffected,
8 new `ipc_eval::`), `cargo clippy -p axeyum-lean-kernel --all-targets --
-D warnings` clean (needed the same `#![allow(clippy::similar_names)]`
`ipc_provable.rs` already carries, here for `iha`/`ihb`), `cargo fmt --all
--check` clean. Did not run `cargo test --workspace` or `./scripts/check.sh`
per lane instructions — the coordinator re-verifies before merging.

**Files**: `crates/axeyum-lean-kernel/src/ipc_eval.rs` (new, ~430 lines
incl. tests and module docs), `crates/axeyum-lean-kernel/src/lib.rs`
(2-line registration: `mod ipc_eval;` + one `pub use`). Did not touch
`nat_prelude/`, `int_prelude/`, `rat_prelude/`, `creal/`, `ipc_heyting.rs`,
or `ipc_provable.rs`.

**Commits**: `b4f8f016c` (early WIP commit, uncompiled draft per lane
protocol), `18cc2267f` (the `binop_minor` fix — motive_codomain, not
val_ty — landing a fully working, tested, clippy-clean `eval`).

**What slice 4 now needs.** Unchanged from `318-ipc-provable.md`'s
description: soundness, `Provable ctx phi -> (every valuation satisfying
ctx satisfies phi)`, i.e. `forall rho, sat ctx rho -> eval phi rho = 2`, by
induction on `Provable`'s own generated recursor (`Provable.rec`, not yet
used anywhere). The eleven cases correspond one-to-one to `Provable`'s
eleven constructors; the hardest are `or_elim` and `imp_intro`/`imp_elim`
(needing a `sat : FormulaList -> (Nat -> Nat) -> Prop` context-satisfaction
notion, built the same way `eval` is here — via `FormulaList.rec`). Once
slice 4 lands, combining it with `ipc_heyting.rs`'s countermodel
(`ipc_heyting_join_not_ne_top`) at the valuation `p := 1` gives `Not
(Provable nil pem_instance)` by contraposition, closing
`F:excluded-middle-not-intuitionistic`. Slice 4 is genuine new mathematical
content and, per the prior handoff's advice (borne out again here — slice 3
really was "clean, small, mechanical" once the one binder-type bug was
found), deserves its own lane rather than being combined with anything
else.
