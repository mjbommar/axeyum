# Lane: ipc-soundness — slice 4 closes `F:excluded-middle-not-intuitionistic`

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, ipc-soundness, 2026-08-30).** Slice 4 of the
decomposition in `docs/plan/status/273-logic-excluded-middle.md`: soundness of
the `Provable` natural-deduction relation over the 3-element Heyting chain, and
the contraposition that closes the fact. All eleven cases check. **The fact is
closed** — `epistemic_status` open → proved, `proof_route` kernel-lean,
`axiom_footprint` `[]`, open since 2026-08-14.

Landed in `crates/axeyum-lean-kernel/src/ipc_soundness.rs` (+ `tests.rs`), with
a new checker example `crates/axeyum-lean-kernel/examples/ipc_soundness_inventory.rs`.

## The one finding that reshaped the slice

**The brief's soundness statement — `Provable ctx phi -> sat ctx v ->
eval phi v = top` — is not a statement an induction on the derivation can
carry, and `imp_intro` is the obstruction.** Its induction hypothesis is about
the *extended* context, so it says only *if `eval phi v = 2` then
`eval psi v = 2`*. The goal is `himp3 (eval phi v) (eval psi v) = 2`, i.e.
`eval phi v <= eval psi v`, and nothing in that hypothesis constrains the case
where `eval phi v` is the chain's **middle** element. The hypothesis is silent
exactly where the goal needs information — which is the whole reason the chain
has three elements rather than two.

The statement that does carry it is the standard algebraic one, over the meet
of the context:

    ipc_ctx_meet nil        v = 2
    ipc_ctx_meet (cons a l) v = meet3 (ipc_eval a v) (ipc_ctx_meet l v)

    ipc_soundness : forall ctx phi, Provable ctx phi
                  -> forall v, Le (ipc_ctx_meet ctx v) (ipc_eval phi v)

Read semantically: *the value of the context is below the value of anything
derivable from it*. `imp_intro` goes through by residuation, `or_elim` by the
chain's linearity.

**Nothing is lost.** `ipc_sat` is built as the brief asked (via
`FormulaList.rec`, `True` at `nil`, `And (Eq (eval a v) 2) …` at `cons`) and
bridged onto the meet — `ipc_sat_le_ctx_meet : ipc_sat l v -> Le 2
(ipc_ctx_meet l v)` — giving the sat-shaped corollary `ipc_soundness_sat`.

Detail moved to [`../notes/324-ipc-soundness.md`](../notes/324-ipc-soundness.md).

<!-- plan-section: landed-changes -->

| 2026-08-30 | ipc-soundness | Slice 4: `ipc_ctx_meet` + `ipc_sat` (both `FormulaList.rec`), nine chain lemmas, and `ipc_soundness` by an eleven-case `Provable.rec` induction — the first use of that recursor — closing `F:excluded-middle-not-intuitionistic` (open since 2026-08-14) with `ipc_excluded_middle_not_provable`, axiom-free, plus a fail-on-absence checker example. Soundness runs on the context MEET, not on `sat`: the sat-shaped statement does not carry the induction through `imp_intro`. |
