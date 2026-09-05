//! ADR-1616: the bridge's own controls.
//!
//! `every_intspace_declaration_is_axiom_free` and
//! `every_live_intspace_declaration_is_listed` (in `intspace_tests`) already
//! cover the two new names once they are listed — and the second of them
//! caught the omission when they were not, which is the evidence that it is
//! not vacuous. What those do NOT cover is whether the bridge's *statement*
//! is the one it claims. That is what this file is for: the index bound is
//! re-declared one `Nat.succ` away and the kernel must refuse, with a
//! positive twin in the same test so the refusal cannot be an artefact of
//! the harness.

use super::{INTEGRAL, IntSpacePrelude, req, rmul, rty};
use crate::build_intspace_prelude;
use crate::env::Declaration;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::{Kernel, on_a_deep_stack};

fn built() -> (Kernel, IntSpacePrelude) {
    on_a_deep_stack(|| {
        let mut kernel = Kernel::new();
        let prelude = build_intspace_prelude(&mut kernel).expect("IntSpace prelude must build");
        (kernel, prelude)
    })
}

/// Rebuild `IntSpace.crealFinite_expectation`'s statement with the index
/// bound set to `Nat.rec`-depth `bump` above `m`, and the SAME proof term
/// the real declaration uses, then hand it to the kernel under a scratch
/// name. `bump == 1` is the true statement; anything else must be refused.
fn redeclare_at_bound(
    kernel: &mut Kernel,
    p: IntSpacePrelude,
    bump: usize,
    label: &str,
) -> Result<(), crate::KernelError> {
    let c = p.creal;
    let mut d = IntDev::new(kernel, c.rat.int);
    let r = rty(&mut d, c);
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, r);
    let triv_ty = d.kernel().const_(p.triv, vec![]);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let mut n = m;
    for _ in 0..bump {
        n = d.succ(n);
    }

    let weighted = {
        let k_fv = d.fresh_fvar();
        let kv = d.kernel().fvar(k_fv);
        let xk = d.apply(x, &[kv]);
        let pk = d.apply(pf, &[kv]);
        let body = rmul(&mut d, c, xk, pk);
        d.lam_fv(k_fv, nat, body)
    };
    let lhs = {
        let s = d.const_app(p.creal_finite, &[m]);
        let sel = d.kernel().const_(p.record.sel(INTEGRAL), vec![]);
        let head = d.apply(sel, &[s]);
        d.apply(head, &[weighted, t])
    };
    let rhs = {
        let record = d.kernel().const_(c.ordered_ring_s, vec![]);
        let name = c.rat.probability_s.expectation;
        d.const_app(name, &[record, x, pf, n])
    };
    let value = d.const_app(p.creal_finite_integral, &[weighted, m, t]);

    let ty = {
        let concl = req(&mut d, c, lhs, rhs);
        let t2 = d.pi_fv(t_fv, triv_ty, concl);
        let t2 = d.pi_fv(m_fv, nat, t2);
        let t2 = d.pi_fv(pf_fv, fn_ty, t2);
        d.pi_fv(x_fv, fn_ty, t2)
    };
    let value = {
        let t2 = d.lam_fv(t_fv, triv_ty, value);
        let t2 = d.lam_fv(m_fv, nat, t2);
        let t2 = d.lam_fv(pf_fv, fn_ty, t2);
        d.lam_fv(x_fv, fn_ty, t2)
    };
    let name = {
        let anon = d.kernel().anon();
        d.kernel().name_str(anon, label)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })
}

/// **The bridge's index bound is load-bearing.** `crealFinite m` integrates
/// over `Nat.succ m` points; a statement claiming it equals the expectation
/// over `Nat.succ (Nat.succ m)` points must be refused, and the same
/// construction at the true bound must be accepted in the same test — so the
/// refusal is the statement's, not the harness's.
#[test]
fn the_finite_bridge_is_sensitive_to_its_index_bound() {
    on_a_deep_stack(|| {
        let (mut kernel, p) = built();
        redeclare_at_bound(&mut kernel, p, 1, "BridgeControl.true_bound")
            .expect("the bridge at succ m must be accepted — the positive twin");
        let wrong = redeclare_at_bound(&mut kernel, p, 2, "BridgeControl.wrong_bound");
        assert!(
            wrong.is_err(),
            "the bridge at succ (succ m) must be REFUSED: crealFinite m integrates \
             over succ m points, not succ (succ m)"
        );
    });
}

/// The two bridge theorems are DIFFERENT statements: the ℝ-valued one has no
/// `CReal.ofRat` in it and the rational one does. Without this, both names
/// could point at the same theorem and every other check would still pass.
#[test]
fn the_two_bridge_statements_are_distinct() {
    on_a_deep_stack(|| {
        let (mut kernel, p) = built();
        let a = kernel.const_(p.creal_finite_expectation, vec![]);
        let b = kernel.const_(p.rat_expectation_integral, vec![]);
        let ta = kernel
            .infer(a)
            .expect("crealFinite_expectation must type-check");
        let tb = kernel
            .infer(b)
            .expect("ratExpectation_integral must type-check");
        assert!(
            !kernel.def_eq(ta, tb),
            "the ℝ-valued bridge and the rational one must be different statements"
        );
        let shown_a = kernel.render_lean(ta);
        let shown_b = kernel.render_lean(tb);
        assert!(
            !shown_a.contains("CReal.ofRat"),
            "the ℝ-valued bridge must not mention the embedding: {shown_a}"
        );
        assert!(
            shown_b.contains("CReal.ofRat") && shown_b.contains("Rat.expectation"),
            "the rational bridge must carry BOTH the embedding and Rat.expectation: {shown_b}"
        );
    });
}
