# Lane: nat-rule-placement — the literal-`Nat` rule was in the wrong loop

<!-- plan-section: lane-status -->

**`Kernel::reduce_nat_binop` now sits where Lean calls `reduce_nat` — in the δ
loop and in lazy-delta, never in the δ-free step — under Lean's `has_fvar`
guard. `build_creal_prelude` 12.99 s → 6.79 s, and nothing stopped admitting**
(`DONE`, agent-nat-rule-placement, 2026-08-20).

ADR-0459 described the placement as "tried after `whnf_core` and before δ". The
code called it from inside `whnf_no_unfolding_uncached`, and that function *is*
Lean's `whnf_core` — one layer too deep, with no `has_fvar` guard anywhere. In
the pinned reference (`v4.30.0`, `d024af09`) `reduce_nat` is called from
`type_checker::whnf` at `:670` and from `lazy_delta_reduction` at `:978`, the
second under `!has_fvar(t_n) && !has_fvar(s_n)`. Both are now ported; the
`whnf_core` site also carries the guard, which is stricter than Lean and is the
decision ADR-0536 records.

Detail moved to [`../notes/113-nat-rule-placement.md`](../notes/113-nat-rule-placement.md).

<!-- plan-section: landed-changes -->

| 2026-08-20 | (pending) | `Kernel::reduce_nat_binop` moves out of the δ-free normaliser to Lean's two call sites — `whnf_core`'s δ loop (Lean `whnf`, `type_checker.cpp:670`) and `lazy_delta_step` (Lean `lazy_delta_reduction`, `:978`) — both under Lean's `!has_fvar` guard. `build_creal_prelude` 12.99 s → 6.79 s (median of three interleaved rounds), against 8.71 s before the acceleration was ever switched on. Measured separately: Lean's placement *without* the guard is 12.12 s, so the guard is the entire win and the placement is faithfulness, not speed. Identification unmoved — kernel lib 399/0; full kernel crate 609 passed / 1 failed, the one (`real_lean_wellfounded_elaborator_divergence`) failing byte-identically on an unmodified `HEAD` and being a real-Lean *elaborator* rejection rather than ours; solver `reconstruct::` 312/0; clippy 618/618 targets 0 diagnostics; prelude-reuse differential `compared=8 failures=0`; axiom ledger `axreal=30` and all others 0. Three new tests in `tests/nat_literal_arithmetic.rs` pin both call sites and both guards on an environment where the accelerated answer and the declared body disagree; each guard mutation kills exactly one. ADR-0536. |
