//! L2 phase G4, pilot 1 (category 1: high-degree missing substrate).
//!
//! Bounded probe for `docs/plan/status/l2-g4-pilot-clusters.md`: infrastructure
//! frontier row `IF-LANG-dce29ad3f7` (`Semigroup`/`mul_assoc`, over population
//! `mathlib-group-defs-v1`) argues this kernel cannot STATE a carrier-generic
//! associativity proposition because it has no bundled `Structure`/typeclass
//! mechanism. That is true for the bundled form, but the roadmap's own
//! priority tier 2 is a "missing definition/datatype/operation", and this
//! probe asks the narrower, session-sized question underneath it: can a
//! RAW, non-bundled, universe-quantified statement --
//!
//!   `forall (alpha : Sort 1) (op : alpha -> alpha -> alpha),
//!      (forall a b c, Eq alpha (op (op a b) c) (op a (op b c)))
//!      -> forall a b c, Eq alpha (op (op a b) c) (op a (op b c))`
//!
//! -- be built and admitted by `Kernel::add_declaration` at all, using only
//! the public `Kernel` API (no bundled record, no typeclass, no `NatOps`
//! carrier-specific scaffolding)? The content is deliberately trivial (the
//! conclusion is syntactically identical to the hypothesis, so the proof is
//! literally the identity `fun alpha op h => h`) -- this probes STATABILITY
//! and kernel acceptance of a `Sort`-quantified statement, not new
//! mathematics. `quotient.rs` already builds `Sort u`-binding Pi types
//! internally (e.g. `expected_eq_type`); this probe checks whether the same
//! capability is reachable from ordinary example/library code, not only from
//! inside the quotient module.
//!
//! TEMPORARY, in the style of `probe_add_structure.rs`: this is pilot
//! evidence, not a library contribution. See the status file for the
//! preregistered metric and verdict.

use axeyum_lean_kernel::{BinderInfo, Declaration, Kernel, build_logic_prelude};
use axeyum_lean_kernel::{ExprId, LevelId};

fn pi_over(kernel: &mut Kernel, fv: u64, ty: ExprId, body: ExprId) -> ExprId {
    let b = kernel.abstract_fvars(body, &[fv]);
    let anon = kernel.anon();
    kernel.pi(anon, ty, b, BinderInfo::Default)
}

fn lam_over(kernel: &mut Kernel, fv: u64, ty: ExprId, body: ExprId) -> ExprId {
    let b = kernel.abstract_fvars(body, &[fv]);
    let anon = kernel.anon();
    kernel.lam(anon, ty, b, BinderInfo::Default)
}

fn app2(kernel: &mut Kernel, f: ExprId, x: ExprId, y: ExprId) -> ExprId {
    let fx = kernel.app(f, x);
    kernel.app(fx, y)
}

fn eq_of(
    kernel: &mut Kernel,
    eq_name: axeyum_lean_kernel::NameId,
    level: LevelId,
    ty: ExprId,
    lhs: ExprId,
    rhs: ExprId,
) -> ExprId {
    let eq_c = kernel.const_(eq_name, vec![level]);
    let e1 = kernel.app(eq_c, ty);
    let e2 = kernel.app(e1, lhs);
    kernel.app(e2, rhs)
}

fn main() {
    let mut kernel = Kernel::new();
    let logic = build_logic_prelude(&mut kernel).expect("logic prelude must build");

    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);

    // Fixed fvar ids: this is a fresh, isolated kernel building exactly one
    // closed term, so any never-reused ids are fine.
    let alpha_fv = 9_001_u64;
    let op_fv = 9_002_u64;
    let h_fv = 9_003_u64;
    let a_fv = 9_004_u64;
    let b_fv = 9_005_u64;
    let c_fv = 9_006_u64;

    let alpha = kernel.fvar(alpha_fv);
    let sort1 = kernel.sort(one);

    // op : alpha -> alpha -> alpha  (non-dependent codomain, so no abstraction
    // step needed -- mirrors `NatOps::arrow`'s own construction).
    let op_ty = {
        let anon = kernel.anon();
        let arrow1 = kernel.pi(anon, alpha, alpha, BinderInfo::Default);
        kernel.pi(anon, alpha, arrow1, BinderInfo::Default)
    };

    let op = kernel.fvar(op_fv);
    let a = kernel.fvar(a_fv);
    let b = kernel.fvar(b_fv);
    let c = kernel.fvar(c_fv);

    let op_ab = app2(&mut kernel, op, a, b);
    let lhs = app2(&mut kernel, op, op_ab, c);
    let op_bc = app2(&mut kernel, op, b, c);
    let rhs = app2(&mut kernel, op, a, op_bc);
    let assoc_prop = eq_of(&mut kernel, logic.eq, one, alpha, lhs, rhs);

    let mut quantified_assoc = pi_over(&mut kernel, c_fv, alpha, assoc_prop);
    quantified_assoc = pi_over(&mut kernel, b_fv, alpha, quantified_assoc);
    quantified_assoc = pi_over(&mut kernel, a_fv, alpha, quantified_assoc);

    // h : quantified_assoc  |-  quantified_assoc  (hypothesis == conclusion,
    // by construction -- the probe is about STATABILITY, not proof content).
    let h_ty = quantified_assoc;
    let body_after_h = quantified_assoc;

    let full_ty = {
        let t = pi_over(&mut kernel, h_fv, h_ty, body_after_h);
        let t = pi_over(&mut kernel, op_fv, op_ty, t);
        pi_over(&mut kernel, alpha_fv, sort1, t)
    };

    let h_expr = kernel.fvar(h_fv);
    let full_val = {
        let v = lam_over(&mut kernel, h_fv, h_ty, h_expr);
        let v = lam_over(&mut kernel, op_fv, op_ty, v);
        lam_over(&mut kernel, alpha_fv, sort1, v)
    };

    let root = kernel.anon();
    let ns = kernel.name_str(root, "G4Pilot1Probe");
    let name = kernel.name_str(ns, "genericAssocStatable");

    println!("-- G4 pilot 1 probe: carrier-generic associativity statement --");
    println!("type:  {}", kernel.render_lean(full_ty));

    match kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty: full_ty,
        value: full_val,
    }) {
        Ok(()) => {
            println!("RESULT: PASS -- kernel accepted a Sort-quantified, non-bundled");
            println!("        associativity-shaped statement with no Structure/typeclass.");
        }
        Err(e) => {
            println!("RESULT: FAIL -- {e:?}");
            std::process::exit(1);
        }
    }

    // Negative control: the SAME identity-shaped proof term against a
    // DIFFERENT (commutativity-shaped, not entailed by an associativity
    // hypothesis) conclusion must be REFUSED. Without this, "PASS" above
    // would not distinguish a real check from a vacuous one.
    let comm_goal = {
        let op2 = kernel.fvar(op_fv);
        let a2 = kernel.fvar(a_fv);
        let b2 = kernel.fvar(b_fv);
        let lhs2 = app2(&mut kernel, op2, a2, b2);
        let rhs2 = app2(&mut kernel, op2, b2, a2);
        let prop = eq_of(&mut kernel, logic.eq, one, alpha, lhs2, rhs2);
        let inner = pi_over(&mut kernel, b_fv, alpha, prop);
        pi_over(&mut kernel, a_fv, alpha, inner)
    };
    let bad_ty = {
        let t = pi_over(&mut kernel, h_fv, h_ty, comm_goal);
        let t = pi_over(&mut kernel, op_fv, op_ty, t);
        pi_over(&mut kernel, alpha_fv, sort1, t)
    };
    let root2 = kernel.anon();
    let ns2 = kernel.name_str(root2, "G4Pilot1Probe");
    let bad_name = kernel.name_str(ns2, "genericCommWronglyClaimed");
    match kernel.add_declaration(Declaration::Theorem {
        name: bad_name,
        uparams: vec![],
        ty: bad_ty,
        value: full_val,
    }) {
        Ok(()) => {
            println!(
                "NEGATIVE CONTROL FAILED: kernel wrongly accepted commutativity from an associativity hypothesis"
            );
            std::process::exit(2);
        }
        Err(_) => {
            println!(
                "NEGATIVE CONTROL: PASS -- kernel correctly refused the mismatched (comm-from-assoc) claim"
            );
        }
    }
}
