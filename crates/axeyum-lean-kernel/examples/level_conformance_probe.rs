//! Re-measure this kernel's universe-level equality on the shapes where it is
//! known to diverge from Lean 4, and print each answer rather than assert one.
//!
//! Two shapes, both recorded in `docs/plan/lean-divergences.md`:
//!
//! - **Probe 5** of `docs/plan/lean-kernel-requirements-2026-08-13.md` §2.6:
//!   Carneiro's example `imax u (imax v w)` versus `imax (max u v) w`, which
//!   *"leanchecker rejects and trepplein accepts"*. Lean 4 decides level
//!   equality by normalization and those rules are provably incomplete;
//!   trepplein and the thesis case-split and are more complete. ADR-0036 ports
//!   `leq_core` from nanoda, which is in the trepplein lineage.
//! - The `level.max-kind:1322:max-to-imax` mutant of ADR-1600 §4: `max u 1`
//!   versus `imax u 1`. These are equal for every `u` because the right operand
//!   is a successor, but Lean's C++ `normalize` sorts one spelling and not the
//!   other, so its `is_equivalent` answers no **on the wire** while both
//!   kernels accept the equivalent written in source.
//!
//! Neither is a soundness defect: deciding *more* equalities cannot admit
//! `False`. Both invert the claim people care about -- "axeyum checked it" does
//! not imply "Lean would check it" -- which is why they are ledger entries and
//! not footnotes.
//!
//! The upstream corpus agrees that the second shape is a legitimate difference:
//! `tests/corner-cases/imax-right-successor.yaml` in `leanprover/lean-kernel-arena`
//! carries `outcome: either`, with the note that a checker *"may reject these
//! hand-crafted exports using a more conservative normalization, or accept them
//! by recognizing that the right operand is nonzero."*
//!
//! ```text
//! cargo run --release -p axeyum-lean-kernel --example level_conformance_probe
//! ```

use axeyum_lean_kernel::Kernel;

fn main() {
    let mut kernel = Kernel::new();
    let anon = kernel.anon();
    let u = kernel.name_str(anon, "u");
    let v = kernel.name_str(anon, "v");
    let w = kernel.name_str(anon, "w");
    let lu = kernel.level_param(u);
    let lv = kernel.level_param(v);
    let lw = kernel.level_param(w);

    // Probe 5: imax u (imax v w) == imax (max u v) w
    let inner = kernel.level_imax(lv, lw);
    let left = kernel.level_imax(lu, inner);
    let outer = kernel.level_max(lu, lv);
    let right = kernel.level_imax(outer, lw);
    let probe5 = kernel.level_is_equiv(left, right);
    println!(
        "LEVEL-PROBE name=probe5-imax-assoc lhs=imax(u,imax(v,w)) rhs=imax(max(u,v),w) \
         axeyum={probe5} lean=false verdict={}",
        verdict(probe5, false)
    );

    // ADR-1600 §4: max u 1 == imax u 1 (the `max-to-imax` mutant's shape).
    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);
    let max_u_1 = kernel.level_max(lu, one);
    let imax_u_1 = kernel.level_imax(lu, one);
    let mutant = kernel.level_is_equiv(max_u_1, imax_u_1);
    println!(
        "LEVEL-PROBE name=max-to-imax lhs=max(u,1) rhs=imax(u,1) axeyum={mutant} \
         lean=false verdict={}",
        verdict(mutant, false)
    );

    // A NEGATIVE CONTROL, and it is not optional: both probes above report
    // `true`, so a `level_is_equiv` that had degenerated into `|_, _| true`
    // would print exactly the two lines above. This pair is NOT equal -- at
    // `v = 0`, `imax 0 v` is `0` and its successor is `1` -- and it is the same
    // shape the arena's `level-imax-normalization` case exploits to derive
    // `False`. If this prints `true`, the two findings above mean nothing and
    // the kernel has a soundness bug.
    let imax_0_v = kernel.level_imax(zero, lv);
    let succ_imax_0_v = kernel.level_succ(imax_0_v);
    let control = kernel.level_is_equiv(imax_0_v, succ_imax_0_v);
    println!(
        "LEVEL-PROBE name=negative-control lhs=imax(0,v) rhs=succ(imax(0,v)) \
         axeyum={control} lean=false verdict={}",
        verdict(control, false)
    );

    // A POSITIVE CONTROL: a plain commutativity both kernels decide `true`, so
    // a `level_is_equiv` degenerated into `|_, _| false` is visible too.
    let max_uv = kernel.level_max(lu, lv);
    let max_vu = kernel.level_max(lv, lu);
    let positive = kernel.level_is_equiv(max_uv, max_vu);
    println!(
        "LEVEL-PROBE name=positive-control lhs=max(u,v) rhs=max(v,u) axeyum={positive} \
         lean=true verdict={}",
        verdict(positive, true)
    );
}

fn verdict(ours: bool, lean: bool) -> &'static str {
    if ours == lean {
        "agree"
    } else if ours {
        "more-complete-than-lean"
    } else {
        "less-complete-than-lean"
    }
}
