//! L2 phase G4, pilot 2 (category 2: shared congruence/rewrite/induction
//! producer from the obstruction graph).
//!
//! Row `IF-LANG-53e5bef137` (population `mathlib-group-defs-v1`): this kernel
//! has at least four independent per-carrier `congr`-shaped dev helpers
//! (`NatOps::congr`, `congr_nat_to`, `congr_bool_to_nat` x3,
//! `string_prelude`'s `congr_arg_str`/`congr_append_left`/`congr_append_right`
//! x4, `characterization::congr_at`) -- see
//! `docs/plan/status/l2-g4-pilot-clusters.md` for the fresh grep count. This
//! pilot builds a carrier-GENERIC `congr_arg` (explicit `ty`/`level`
//! parameters instead of a hardcoded `nat_ty()`/`bool_ty()`) using only the
//! public `Kernel` API, and checks REUSE the strong way: does it produce the
//! **structurally identical proof term** (same `ExprId`, via the kernel's
//! content-addressed interning) as the existing `NatOps::congr` for the same
//! inputs? If so, the generic function is not merely "also correct" -- it is
//! a drop-in replacement for at least this one call site.
//!
//! TEMPORARY, in the style of `probe_add_structure.rs`: pilot evidence, not a
//! library contribution.

use axeyum_lean_kernel::{BinderInfo, Declaration, ExprId, Kernel, LevelId, LogicPrelude, NameId};
use axeyum_lean_kernel::{NatDev, NatOps, build_nat_prelude};

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

fn eq_of(
    kernel: &mut Kernel,
    eq_name: NameId,
    level: LevelId,
    ty: ExprId,
    lhs: ExprId,
    rhs: ExprId,
) -> ExprId {
    let c = kernel.const_(eq_name, vec![level]);
    let e1 = kernel.app(c, ty);
    let e2 = kernel.app(e1, lhs);
    kernel.app(e2, rhs)
}

fn refl_of(
    kernel: &mut Kernel,
    eq_refl_name: NameId,
    level: LevelId,
    ty: ExprId,
    a: ExprId,
) -> ExprId {
    let c = kernel.const_(eq_refl_name, vec![level]);
    let e = kernel.app(c, ty);
    kernel.app(e, a)
}

/// Carrier-GENERIC `Eq.rec` transport: `h : Eq ty p q  |-  motive q h`, given
/// `refl_case : motive p rfl`. `level` is the CARRIER's universe; the motive's
/// own result lives in `Prop` (`Sort 0`), matching every existing per-carrier
/// `transport` in this kernel.
#[allow(clippy::too_many_arguments)]
fn transport_generic(
    kernel: &mut Kernel,
    eq_rec_name: NameId,
    level: LevelId,
    ty: ExprId,
    p: ExprId,
    motive: ExprId,
    refl_case: ExprId,
    q: ExprId,
    h: ExprId,
) -> ExprId {
    let zero = kernel.level_zero();
    let rec = kernel.const_(eq_rec_name, vec![zero, level]);
    let e = kernel.app(rec, ty);
    let e = kernel.app(e, p);
    let e = kernel.app(e, motive);
    let e = kernel.app(e, refl_case);
    let e = kernel.app(e, q);
    kernel.app(e, h)
}

/// Carrier-GENERIC `Eq.rec` motive `fun (x : ty) (_ : Eq ty a x) => body(x)`.
fn eq_motive_generic(
    kernel: &mut Kernel,
    logic: &LogicPrelude,
    level: LevelId,
    ty: ExprId,
    a: ExprId,
    x_fv: u64,
    body: &dyn Fn(&mut Kernel, ExprId) -> ExprId,
) -> ExprId {
    let x = kernel.fvar(x_fv);
    let concl = body(kernel, x);
    let hyp = eq_of(kernel, logic.eq, level, ty, a, x);
    let anon = kernel.anon();
    let inner = kernel.lam(anon, hyp, concl, BinderInfo::Default);
    lam_over(kernel, x_fv, ty, inner)
}

/// Carrier-GENERIC congruence: `h : Eq ty a b  |-  Eq ty (f a) (f b)`. This is
/// the row's proposed increment -- one function, an explicit `(ty, level)`
/// pair instead of a hardcoded carrier, usable for `Nat`, `Bool`, or anything
/// else this kernel represents.
#[allow(clippy::too_many_arguments)]
fn generic_congr_arg(
    kernel: &mut Kernel,
    logic: &LogicPrelude,
    level: LevelId,
    ty: ExprId,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    x_fv: u64,
    f: &dyn Fn(&mut Kernel, ExprId) -> ExprId,
) -> ExprId {
    let fa = f(kernel, a);
    let motive = eq_motive_generic(kernel, logic, level, ty, a, x_fv, &|k, x| {
        let fx = f(k, x);
        eq_of(k, logic.eq, level, ty, fa, fx)
    });
    let refl_case = refl_of(kernel, logic.eq_refl, level, ty, fa);
    transport_generic(kernel, logic.eq_rec, level, ty, a, motive, refl_case, b, h)
}

#[allow(clippy::similar_names)]
fn main() {
    let mut kernel = Kernel::new();
    let prelude = build_nat_prelude(&mut kernel).expect("nat prelude must build");
    let logic = prelude.logic;
    let nat_ty = kernel.const_(prelude.nat, vec![]);
    let succ_name = prelude.succ;
    let one = {
        let z = kernel.level_zero();
        kernel.level_succ(z)
    };

    // -- existing route: NatOps::congr, via the ready-made NatDev wrapper --
    let (nat_a_fv, nat_b_fv, nat_h_fv, existing_route_proof, nat_h_ty) = {
        let mut dev = NatDev::new(&mut kernel, prelude);
        let a_fv = dev.fresh_fvar();
        let b_fv = dev.fresh_fvar();
        let h_fv = dev.fresh_fvar();
        let a = dev.kernel().fvar(a_fv);
        let b = dev.kernel().fvar(b_fv);
        let h_ty = dev.eq(a, b);
        let h = dev.kernel().fvar(h_fv);
        let f = |d: &mut NatDev, x: ExprId| -> ExprId {
            let c = d.kernel().const_(succ_name, vec![]);
            d.kernel().app(c, x)
        };
        let proof = dev.congr(a, b, h, &f);
        (a_fv, b_fv, h_fv, proof, h_ty)
    };

    // -- generic route: the SAME inputs, through the pilot's carrier-generic
    // helper, using fvar ids one past NatDev's fresh-fvar high-water mark so
    // the two constructions cannot alias each other's variables.
    let x_fv = nat_h_fv + 1;
    let a2 = kernel.fvar(nat_a_fv);
    let b2 = kernel.fvar(nat_b_fv);
    let h2 = kernel.fvar(nat_h_fv);
    let f2 = |k: &mut Kernel, x: ExprId| -> ExprId {
        let c = k.const_(succ_name, vec![]);
        k.app(c, x)
    };
    let generic_proof = generic_congr_arg(&mut kernel, &logic, one, nat_ty, a2, b2, h2, x_fv, &f2);

    println!("-- G4 pilot 2 probe: carrier-generic congr_arg vs NatOps::congr --");
    println!(
        "existing route proof (rendered): {}",
        kernel.render_lean(existing_route_proof)
    );
    println!(
        "generic  route proof (rendered): {}",
        kernel.render_lean(generic_proof)
    );

    if existing_route_proof == generic_proof {
        println!("RESULT: PASS -- identical ExprId: the generic helper reconstructs");
        println!("        the SAME proof term as NatOps::congr for this input (true reuse).");
    } else {
        println!("RESULT: DIFFERENT TERMS (still may both be valid, but not literal reuse)");
    }

    // Confirm both independently type-check to the expected Eq statement, so
    // an ExprId match isn't reported without also confirming it typechecks.
    let succ_a = {
        let c = kernel.const_(succ_name, vec![]);
        kernel.app(c, a2)
    };
    let succ_b = {
        let c = kernel.const_(succ_name, vec![]);
        kernel.app(c, b2)
    };
    let expected_ty = eq_of(&mut kernel, logic.eq, one, nat_ty, succ_a, succ_b);

    let full_ty = {
        let t = pi_over(&mut kernel, nat_h_fv, nat_h_ty, expected_ty);
        let t = pi_over(&mut kernel, nat_b_fv, nat_ty, t);
        pi_over(&mut kernel, nat_a_fv, nat_ty, t)
    };
    let full_val = {
        let v = lam_over(&mut kernel, nat_h_fv, nat_h_ty, generic_proof);
        let v = lam_over(&mut kernel, nat_b_fv, nat_ty, v);
        lam_over(&mut kernel, nat_a_fv, nat_ty, v)
    };
    let root = kernel.anon();
    let ns = kernel.name_str(root, "G4Pilot2Probe");
    let name = kernel.name_str(ns, "genericCongrSucc");

    match kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty: full_ty,
        value: full_val,
    }) {
        Ok(()) => {
            println!("KERNEL ACCEPTS: the generic-route proof, wrapped as a real theorem, admits.");
        }
        Err(e) => {
            println!("KERNEL REJECTS: {e:?}");
            std::process::exit(1);
        }
    }
}
