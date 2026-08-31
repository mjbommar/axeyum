//! Audit instrument: **is the constructive IVT/EVT repertoire non-vacuous, and
//! is the missing EVT "row 1" actually missing?** (lane `ivt-evt-dominance-audit`.)
//!
//! `docs/formalized-math-2026-08/08-ivt-and-evt-measured-against-mathlib.md` §2
//! records that EVT has *no* general constructive statement — only a boundary
//! refutation — and §5 item 2 names the statement that would fill the hole:
//!
//! ```text
//! CReal.evt_approx_max : ∀ n, ∃ x ∈ [a,b], ∀ y ∈ [a,b], F y ≤ F x + 1/(n+1)
//! ```
//!
//! Since that was written, `CReal.supOn_ub` and `CReal.supOn_approx_lub` have
//! both landed. This probe asks the trusted gate two questions the ledger and
//! the prose cannot answer:
//!
//! 1. **Is `evt_approx_max` derivable from what is landed today?** The probe
//!    builds the proof term (`supOn_ub` + `supOn_approx_lub` + `le_trans`,
//!    eliminated through `Exists.rec`) and hands it to
//!    `Kernel::add_declaration`. Nothing here is asserted: if the kernel
//!    refuses, the probe exits non-zero.
//! 2. **Is any of it non-vacuous?** A theorem whose hypotheses no function
//!    satisfies proves nothing. The probe instantiates BOTH `CReal.ivt_approx`
//!    and the composed `evt_approx_max` at a **concrete function family whose
//!    hypotheses are themselves kernel theorems** — `CReal.ivtPlateau` for IVT
//!    (all three of `ivtPlateau_nonpos_at_zero`, `ivtPlateau_nonneg_at_one`,
//!    `ivtPlateau_uniformly_continuous`) and `CReal.evtLinear` for EVT
//!    (`evtLinear_uniformly_continuous`) — and admits each instantiation as its
//!    own declaration, so the instantiated *statement* is what the kernel
//!    prints, not what this file claims.
//!
//! # The finding the exit status depends on
//!
//! Every declaration added here must be admitted AND have an empty
//! `Kernel::axiom_footprint`. A probe that could not report "refused" or "costs
//! an axiom" would be worthless, so both are checked and either exits 1.
//!
//! The negative control is in the same run: `Control.evt_exact_max` states the
//! *exact* attained maximum (`F y ≤ F x`, no `+ 1/(n+1)`) with the identical
//! proof term. The kernel must **refuse** it. If it does not, the composition
//! above is not proving what this file says it proves, and the probe exits 1.
//!
//! ```sh
//! cargo run --release -p axeyum-lean-kernel --example ivt_evt_vacuity_probe
//! ```

#![allow(clippy::many_single_char_names)]
// ^ This probe reasons about `CReal` functions on `[a,b]` and points `x`/`y`.
// Those ARE the mathematical names; renaming them to satisfy the lint would
// make the probe harder to check against the statements it audits.
#![allow(clippy::similar_names, clippy::too_many_lines)]

use axeyum_lean_kernel::{
    BinderInfo, CRealPrelude, Declaration, ExprId, ExprNode, Kernel, LevelNode, NameId,
    build_creal_prelude, on_a_deep_stack,
};

/// Left-to-right application spine.
fn app_n(k: &mut Kernel, head: ExprId, args: &[ExprId]) -> ExprId {
    let mut acc = head;
    for &a in args {
        acc = k.app(acc, a);
    }
    acc
}

/// `c args…` for a non-universe-polymorphic constant.
fn capp(k: &mut Kernel, name: NameId, args: &[ExprId]) -> ExprId {
    let c = k.const_(name, vec![]);
    app_n(k, c, args)
}

/// `c.{lvl} args…`.
fn capp_u(
    k: &mut Kernel,
    name: NameId,
    lvl: axeyum_lean_kernel::LevelId,
    args: &[ExprId],
) -> ExprId {
    let c = k.const_(name, vec![lvl]);
    app_n(k, c, args)
}

/// The last two arguments of a two-or-more-argument application spine.
///
/// `f x y` ↦ `(x, y)`. Panics on anything else — a panic here means the
/// kernel's rendered shape is not what this probe assumed, which is a finding,
/// not something to paper over.
fn args2(k: &Kernel, e: ExprId) -> (ExprId, ExprId) {
    let ExprNode::App(f, y) = *k.expr_node(e) else {
        panic!("expected an application spine");
    };
    let ExprNode::App(_, x) = *k.expr_node(f) else {
        panic!("expected a two-argument application spine");
    };
    (x, y)
}

/// `fun (fv : ty) => body`, closing `fv`.
fn lam1(k: &mut Kernel, nm: NameId, ty: ExprId, fv: u64, body: ExprId) -> ExprId {
    let b = k.abstract_fvars(body, &[fv]);
    k.lam(nm, ty, b, BinderInfo::Default)
}

/// `∀ (fv : ty), body`, closing `fv`.
fn pi1(k: &mut Kernel, nm: NameId, ty: ExprId, fv: u64, body: ExprId) -> ExprId {
    let b = k.abstract_fvars(body, &[fv]);
    k.pi(nm, ty, b, BinderInfo::Default)
}

/// The declared type of `name`, read from the environment.
fn decl_ty(k: &Kernel, name: NameId) -> ExprId {
    k.environment()
        .get(name)
        .unwrap_or_else(|| panic!("declaration must exist"))
        .ty()
}

/// Instantiate a Pi-telescope at `args`, returning the residual type.
fn apply_ty(k: &mut Kernel, mut ty: ExprId, args: &[ExprId]) -> ExprId {
    for &a in args {
        let body = k
            .pi_body(ty)
            .expect("telescope is shorter than the argument list");
        ty = k.instantiate(body, &[a]);
    }
    ty
}

struct Probe {
    kernel: Kernel,
    p: CRealPrelude,
    anon: NameId,
    creal_ty: ExprId,
    nat_ty: ExprId,
    lvl1: axeyum_lean_kernel::LevelId,
    and_: NameId,
    and_intro: NameId,
    and_left: NameId,
    and_right: NameId,
    exists_: NameId,
    exists_intro: NameId,
    exists_rec: NameId,
    audit_ns: NameId,
    failures: Vec<String>,
    next_fvar: u64,
}

impl Probe {
    fn fresh(&mut self) -> u64 {
        self.next_fvar += 1;
        self.next_fvar
    }

    /// Admit `name : ty := value`, requiring acceptance and an empty footprint.
    fn admit(&mut self, name: NameId, ty: ExprId, value: ExprId, label: &str) -> bool {
        let decl = Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        };
        match self.kernel.add_declaration(decl) {
            Ok(()) => {
                let footprint = self.kernel.axiom_footprint(name);
                if footprint.is_empty() {
                    println!("ADMITTED  {label}  axioms=0");
                    println!("  {}", self.kernel.render_lean(ty).replace('\n', " "));
                    true
                } else {
                    let names: Vec<String> = footprint
                        .iter()
                        .map(|n| self.kernel.display_name(*n).to_string())
                        .collect();
                    self.failures
                        .push(format!("{label}: admitted but carries axioms {names:?}"));
                    false
                }
            }
            Err(e) => {
                self.failures
                    .push(format!("{label}: kernel REFUSED the proof term: {e:?}"));
                println!("REFUSED   {label}  {e:?}");
                false
            }
        }
    }
}

fn run() -> i32 {
    let mut kernel = Kernel::new();
    let p = match build_creal_prelude(&mut kernel) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("the creal prelude must build: {e:?}");
            return 1;
        }
    };
    let anon = kernel.anon();
    let creal_ty = kernel.const_(p.creal, vec![]);
    let nat_name = kernel.name_str(anon, "Nat");
    let nat_ty = kernel.const_(nat_name, vec![]);
    let lvl1 = {
        let z = kernel.level_zero();
        kernel.level_succ(z)
    };
    let and_ = kernel.name_str(anon, "And");
    let and_intro = kernel.name_str(and_, "intro");
    let and_left = kernel.name_str(and_, "left");
    let and_right = kernel.name_str(and_, "right");
    let exists_ = kernel.name_str(anon, "Exists");
    let exists_intro = kernel.name_str(exists_, "intro");
    let exists_rec = kernel.name_str(exists_, "rec");
    let audit_ns = kernel.name_str(anon, "EvtAudit");

    let mut s = Probe {
        kernel,
        p,
        anon,
        creal_ty,
        nat_ty,
        lvl1,
        and_,
        and_intro,
        and_left,
        and_right,
        exists_,
        exists_intro,
        exists_rec,
        audit_ns,
        failures: Vec::new(),
        next_fvar: 900_000,
    };

    // ================================================================
    // Part 1 -- EVT row 1, composed from what is landed today.
    // ================================================================
    let (evt_name, evt_ty) = build_evt_approx_max(&mut s);

    // ================================================================
    // Part 2 -- negative control: the EXACT attained maximum must be
    //           refused by the same proof term.
    // ================================================================
    build_exact_control(&mut s);

    // ================================================================
    // Part 3 -- non-vacuity: instantiate at concrete function families
    //           whose hypotheses are themselves kernel theorems.
    // ================================================================
    instantiate_evt_at_evt_linear(&mut s, evt_name, evt_ty);
    instantiate_ivt_at_plateau(&mut s);

    // ================================================================
    // Part 4 -- `CReal.supOn` is indexed by the uniform-continuity
    //           WITNESS, which is DATA (`Sort 1`, not `Prop`) because it
    //           carries the modulus. So "the supremum of F on [a,b]" is a
    //           modulus-indexed family unless independence is proved.
    //           Nothing in the environment proves it. This does.
    // ================================================================
    build_modulus_independence(&mut s);

    // ================================================================
    // Part 5 -- does official Lean's own kernel cover these? The
    //           `F:lean-kernel-accepts-the-whole-constructed-real-carrier`
    //           replay covers exactly the REPRESENTABLE declarations, and
    //           73 of the carrier's 2,058 are excluded. Classify the IVT
    //           and EVT subjects by that fact's own predicate, so the
    //           answer is not inherited from a headline count.
    // ================================================================
    report_representability(&mut s);

    if s.failures.is_empty() {
        println!(
            "\nPROBE PASSED -- every declaration admitted, axiom-free; the exact control was refused"
        );
        0
    } else {
        println!("\nPROBE FAILED");
        for f in &s.failures {
            println!("  !! {f}");
        }
        1
    }
}

/// Build and admit
/// `EvtAudit.evt_approx_max : ∀ F a b (hab : le a b) (huc : UC F a b) (n : Nat),
///    ∃ x, le a x ∧ (le x b ∧ ∀ y, le a y → le y b → le (F y) (add (F x) (1/(n+1))))`
///
/// from `supOn_approx_lub`, `supOn_ub` and `le_trans` alone.
fn build_evt_approx_max(s: &mut Probe) -> (NameId, ExprId) {
    let p = s.p;
    let anon = s.anon;
    let creal_ty = s.creal_ty;
    let nat_ty = s.nat_ty;

    // --- outer telescope, as free variables -----------------------------
    let fn_ty = s.kernel.pi(anon, creal_ty, creal_ty, BinderInfo::Default);
    let f_id = s.fresh();
    let f = s.kernel.fvar(f_id);
    let a_id = s.fresh();
    let a = s.kernel.fvar(a_id);
    let b_id = s.fresh();
    let b = s.kernel.fvar(b_id);
    let hab_ty = capp(&mut s.kernel, p.le, &[a, b]);
    let hab_id = s.fresh();
    let hab = s.kernel.fvar(hab_id);
    let huc_ty = capp(&mut s.kernel, p.uniformly_continuous_on, &[f, a, b]);
    let huc_id = s.fresh();
    let huc = s.kernel.fvar(huc_id);
    let n_id = s.fresh();
    let n = s.kernel.fvar(n_id);

    // --- the two landed laws --------------------------------------------
    let lub = capp(&mut s.kernel, p.sup_on_approx_lub, &[f, a, b, hab, huc, n]);
    let lub_decl_ty = decl_ty(&s.kernel, p.sup_on_approx_lub);
    let lub_ty = apply_ty(&mut s.kernel, lub_decl_ty, &[f, a, b, hab, huc, n]);
    // lub_ty = Exists.{1} CReal pred
    let (_carrier, pred) = args2(&s.kernel, lub_ty);

    let sup = capp(&mut s.kernel, p.sup_on, &[f, a, b, hab, huc]);

    // --- Exists.rec's intro branch: open the witness ---------------------
    let x_id = s.fresh();
    let x = s.kernel.fvar(x_id);
    let pred_body = s
        .kernel
        .lam_body(pred)
        .expect("the predicate must be a lambda");
    let px = s.kernel.instantiate(pred_body, &[x]);
    // px = And (le a x) (And (le x b) (le sup (add (F x) eps)))
    let (a1, r1) = args2(&s.kernel, px);
    let (a2, a3) = args2(&s.kernel, r1);
    // a3 = le sup rhs
    let (_sup_side, rhs) = args2(&s.kernel, a3);

    let hx_id = s.fresh();
    let hx = s.kernel.fvar(hx_id);
    let ha = capp(&mut s.kernel, s.and_left, &[a1, r1, hx]);
    let hr = capp(&mut s.kernel, s.and_right, &[a1, r1, hx]);
    let hxb = capp(&mut s.kernel, s.and_left, &[a2, a3, hr]);
    let hsup = capp(&mut s.kernel, s.and_right, &[a2, a3, hr]);

    // --- inner: ∀ y, le a y → le y b → le (F y) rhs ----------------------
    let y_id = s.fresh();
    let y = s.kernel.fvar(y_id);
    let hay_ty = capp(&mut s.kernel, p.le, &[a, y]);
    let hay_id = s.fresh();
    let hay = s.kernel.fvar(hay_id);
    let hyb_ty = capp(&mut s.kernel, p.le, &[y, b]);
    let hyb_id = s.fresh();
    let hyb = s.kernel.fvar(hyb_id);

    let fy = s.kernel.app(f, y);
    let ub = capp(
        &mut s.kernel,
        p.sup_on_ub,
        &[f, a, b, hab, huc, y, hay, hyb],
    );
    let chain = capp(&mut s.kernel, p.le_trans, &[fy, sup, rhs, ub, hsup]);

    let inner = {
        let l3 = lam1(&mut s.kernel, anon, hyb_ty, hyb_id, chain);
        let l2 = lam1(&mut s.kernel, anon, hay_ty, hay_id, l3);
        lam1(&mut s.kernel, anon, creal_ty, y_id, l2)
    };
    let inner_ty = {
        let concl = capp(&mut s.kernel, p.le, &[fy, rhs]);
        let t3 = pi1(&mut s.kernel, anon, hyb_ty, hyb_id, concl);
        let t2 = pi1(&mut s.kernel, anon, hay_ty, hay_id, t3);
        pi1(&mut s.kernel, anon, creal_ty, y_id, t2)
    };

    // --- reassemble the conjunction and re-introduce the existential -----
    let new_r1 = capp(&mut s.kernel, s.and_, &[a2, inner_ty]);
    let h_new_r1 = capp(&mut s.kernel, s.and_intro, &[a2, inner_ty, hxb, inner]);
    let tgt_x = capp(&mut s.kernel, s.and_, &[a1, new_r1]);
    let h_tgt_x = capp(&mut s.kernel, s.and_intro, &[a1, new_r1, ha, h_new_r1]);

    let q = {
        let body = s.kernel.abstract_fvars(tgt_x, &[x_id]);
        s.kernel.lam(anon, creal_ty, body, BinderInfo::Default)
    };
    let target = capp_u(&mut s.kernel, s.exists_, s.lvl1, &[creal_ty, q]);
    let h_ex = capp_u(
        &mut s.kernel,
        s.exists_intro,
        s.lvl1,
        &[creal_ty, q, x, h_tgt_x],
    );

    let intro_branch = {
        let l2 = lam1(&mut s.kernel, anon, px, hx_id, h_ex);
        lam1(&mut s.kernel, anon, creal_ty, x_id, l2)
    };
    let motive = s.kernel.lam(anon, lub_ty, target, BinderInfo::Default);
    let proof = capp_u(
        &mut s.kernel,
        s.exists_rec,
        s.lvl1,
        &[creal_ty, pred, motive, intro_branch, lub],
    );

    // --- close the outer telescope --------------------------------------
    let value = {
        let v6 = lam1(&mut s.kernel, anon, nat_ty, n_id, proof);
        let v5 = lam1(&mut s.kernel, anon, huc_ty, huc_id, v6);
        let v4 = lam1(&mut s.kernel, anon, hab_ty, hab_id, v5);
        let v3 = lam1(&mut s.kernel, anon, creal_ty, b_id, v4);
        let v2 = lam1(&mut s.kernel, anon, creal_ty, a_id, v3);
        lam1(&mut s.kernel, anon, fn_ty, f_id, v2)
    };
    let ty = {
        let t6 = pi1(&mut s.kernel, anon, nat_ty, n_id, target);
        let t5 = pi1(&mut s.kernel, anon, huc_ty, huc_id, t6);
        let t4 = pi1(&mut s.kernel, anon, hab_ty, hab_id, t5);
        let t3 = pi1(&mut s.kernel, anon, creal_ty, b_id, t4);
        let t2 = pi1(&mut s.kernel, anon, creal_ty, a_id, t3);
        pi1(&mut s.kernel, anon, fn_ty, f_id, t2)
    };

    let name = s.kernel.name_str(s.audit_ns, "evt_approx_max");
    s.admit(name, ty, value, "EvtAudit.evt_approx_max");
    (name, ty)
}

/// Negative control. Identical construction, except the inner conclusion drops
/// the `+ 1/(n+1)` slack: `∀ y ∈ [a,b], F y ≤ F x`. That is the EXACT attained
/// maximum, which `CReal.evt_attained_max_decides_sign` proves is not available
/// constructively, so the kernel must REFUSE this proof term.
fn build_exact_control(s: &mut Probe) {
    let p = s.p;
    let anon = s.anon;
    let creal_ty = s.creal_ty;
    let nat_ty = s.nat_ty;

    let fn_ty = s.kernel.pi(anon, creal_ty, creal_ty, BinderInfo::Default);
    let f_id = s.fresh();
    let f = s.kernel.fvar(f_id);
    let a_id = s.fresh();
    let a = s.kernel.fvar(a_id);
    let b_id = s.fresh();
    let b = s.kernel.fvar(b_id);
    let hab_ty = capp(&mut s.kernel, p.le, &[a, b]);
    let hab_id = s.fresh();
    let hab = s.kernel.fvar(hab_id);
    let huc_ty = capp(&mut s.kernel, p.uniformly_continuous_on, &[f, a, b]);
    let huc_id = s.fresh();
    let huc = s.kernel.fvar(huc_id);
    let n_id = s.fresh();
    let n = s.kernel.fvar(n_id);

    let lub = capp(&mut s.kernel, p.sup_on_approx_lub, &[f, a, b, hab, huc, n]);
    let lub_decl_ty = decl_ty(&s.kernel, p.sup_on_approx_lub);
    let lub_ty = apply_ty(&mut s.kernel, lub_decl_ty, &[f, a, b, hab, huc, n]);
    let (_carrier, pred) = args2(&s.kernel, lub_ty);
    let sup = capp(&mut s.kernel, p.sup_on, &[f, a, b, hab, huc]);

    let x_id = s.fresh();
    let x = s.kernel.fvar(x_id);
    let pred_body = s
        .kernel
        .lam_body(pred)
        .expect("the predicate must be a lambda");
    let px = s.kernel.instantiate(pred_body, &[x]);
    let (a1, r1) = args2(&s.kernel, px);
    let (a2, a3) = args2(&s.kernel, r1);
    let (_sup_side, rhs) = args2(&s.kernel, a3);

    let hx_id = s.fresh();
    let hx = s.kernel.fvar(hx_id);
    let ha = capp(&mut s.kernel, s.and_left, &[a1, r1, hx]);
    let hr = capp(&mut s.kernel, s.and_right, &[a1, r1, hx]);
    let hxb = capp(&mut s.kernel, s.and_left, &[a2, a3, hr]);
    let hsup = capp(&mut s.kernel, s.and_right, &[a2, a3, hr]);

    let y_id = s.fresh();
    let y = s.kernel.fvar(y_id);
    let hay_ty = capp(&mut s.kernel, p.le, &[a, y]);
    let hay_id = s.fresh();
    let hay = s.kernel.fvar(hay_id);
    let hyb_ty = capp(&mut s.kernel, p.le, &[y, b]);
    let hyb_id = s.fresh();
    let hyb = s.kernel.fvar(hyb_id);

    let fy = s.kernel.app(f, y);
    let fx = s.kernel.app(f, x);
    let ub = capp(
        &mut s.kernel,
        p.sup_on_ub,
        &[f, a, b, hab, huc, y, hay, hyb],
    );
    let chain = capp(&mut s.kernel, p.le_trans, &[fy, sup, rhs, ub, hsup]);

    let inner = {
        let l3 = lam1(&mut s.kernel, anon, hyb_ty, hyb_id, chain);
        let l2 = lam1(&mut s.kernel, anon, hay_ty, hay_id, l3);
        lam1(&mut s.kernel, anon, creal_ty, y_id, l2)
    };
    // THE ONLY DIFFERENCE: `le (F y) (F x)` in place of `le (F y) (F x + eps)`.
    let inner_ty = {
        let concl = capp(&mut s.kernel, p.le, &[fy, fx]);
        let t3 = pi1(&mut s.kernel, anon, hyb_ty, hyb_id, concl);
        let t2 = pi1(&mut s.kernel, anon, hay_ty, hay_id, t3);
        pi1(&mut s.kernel, anon, creal_ty, y_id, t2)
    };

    let new_r1 = capp(&mut s.kernel, s.and_, &[a2, inner_ty]);
    let h_new_r1 = capp(&mut s.kernel, s.and_intro, &[a2, inner_ty, hxb, inner]);
    let tgt_x = capp(&mut s.kernel, s.and_, &[a1, new_r1]);
    let h_tgt_x = capp(&mut s.kernel, s.and_intro, &[a1, new_r1, ha, h_new_r1]);

    let q = {
        let body = s.kernel.abstract_fvars(tgt_x, &[x_id]);
        s.kernel.lam(anon, creal_ty, body, BinderInfo::Default)
    };
    let target = capp_u(&mut s.kernel, s.exists_, s.lvl1, &[creal_ty, q]);
    let h_ex = capp_u(
        &mut s.kernel,
        s.exists_intro,
        s.lvl1,
        &[creal_ty, q, x, h_tgt_x],
    );
    let intro_branch = {
        let l2 = lam1(&mut s.kernel, anon, px, hx_id, h_ex);
        lam1(&mut s.kernel, anon, creal_ty, x_id, l2)
    };
    let motive = s.kernel.lam(anon, lub_ty, target, BinderInfo::Default);
    let proof = capp_u(
        &mut s.kernel,
        s.exists_rec,
        s.lvl1,
        &[creal_ty, pred, motive, intro_branch, lub],
    );

    let value = {
        let v6 = lam1(&mut s.kernel, anon, nat_ty, n_id, proof);
        let v5 = lam1(&mut s.kernel, anon, huc_ty, huc_id, v6);
        let v4 = lam1(&mut s.kernel, anon, hab_ty, hab_id, v5);
        let v3 = lam1(&mut s.kernel, anon, creal_ty, b_id, v4);
        let v2 = lam1(&mut s.kernel, anon, creal_ty, a_id, v3);
        lam1(&mut s.kernel, anon, fn_ty, f_id, v2)
    };
    let ty = {
        let t6 = pi1(&mut s.kernel, anon, nat_ty, n_id, target);
        let t5 = pi1(&mut s.kernel, anon, huc_ty, huc_id, t6);
        let t4 = pi1(&mut s.kernel, anon, hab_ty, hab_id, t5);
        let t3 = pi1(&mut s.kernel, anon, creal_ty, b_id, t4);
        let t2 = pi1(&mut s.kernel, anon, creal_ty, a_id, t3);
        pi1(&mut s.kernel, anon, fn_ty, f_id, t2)
    };

    let control_ns = s.kernel.name_str(s.anon, "Control");
    let name = s.kernel.name_str(control_ns, "evt_exact_max");
    let decl = Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    };
    match s.kernel.add_declaration(decl) {
        Ok(()) => {
            s.failures.push(String::from(
                "Control.evt_exact_max: the kernel ACCEPTED an exact attained maximum -- \
                 the approximate composition is not proving what it claims",
            ));
            println!("CONTROL FAILED  Control.evt_exact_max was ADMITTED");
        }
        Err(e) => {
            println!("CONTROL OK  Control.evt_exact_max refused: {e:?}");
        }
    }
}

/// Non-vacuity for EVT: instantiate the composed statement at `CReal.evtLinear`,
/// whose uniform continuity on `[0,1]` is the kernel theorem
/// `CReal.evtLinear_uniformly_continuous`.
fn instantiate_evt_at_evt_linear(s: &mut Probe, evt_name: NameId, evt_ty: ExprId) {
    let p = s.p;
    let anon = s.anon;
    let creal_ty = s.creal_ty;
    let nat_ty = s.nat_ty;

    let v_id = s.fresh();
    let v = s.kernel.fvar(v_id);
    let n_id = s.fresh();
    let n = s.kernel.fvar(n_id);

    let zero = s.kernel.const_(p.zero, vec![]);
    let one = s.kernel.const_(p.one, vec![]);
    let zlo = s.kernel.const_(p.zero_lt_one, vec![]);
    let hab = capp(&mut s.kernel, p.le_of_lt, &[zero, one, zlo]);
    let big_f = capp(&mut s.kernel, p.evt_linear, &[v]);
    let huc = capp(&mut s.kernel, p.evt_linear_uniformly_continuous, &[v]);

    let args = [big_f, zero, one, hab, huc, n];
    let body = capp(&mut s.kernel, evt_name, &args);
    let body_ty = apply_ty(&mut s.kernel, evt_ty, &args);

    let value = {
        let l2 = lam1(&mut s.kernel, anon, nat_ty, n_id, body);
        lam1(&mut s.kernel, anon, creal_ty, v_id, l2)
    };
    let ty = {
        let t2 = pi1(&mut s.kernel, anon, nat_ty, n_id, body_ty);
        pi1(&mut s.kernel, anon, creal_ty, v_id, t2)
    };
    let name = s.kernel.name_str(s.audit_ns, "evt_approx_max_at_evtLinear");
    s.admit(name, ty, value, "EvtAudit.evt_approx_max_at_evtLinear");
}

/// Non-vacuity for IVT: instantiate `CReal.ivt_approx` at `CReal.ivtPlateau`,
/// whose three hypotheses are all kernel theorems.
fn instantiate_ivt_at_plateau(s: &mut Probe) {
    let p = s.p;
    let anon = s.anon;
    let creal_ty = s.creal_ty;
    let nat_ty = s.nat_ty;

    let v_id = s.fresh();
    let v = s.kernel.fvar(v_id);
    let n_id = s.fresh();
    let n = s.kernel.fvar(n_id);

    let zero = s.kernel.const_(p.zero, vec![]);
    let one = s.kernel.const_(p.one, vec![]);
    let zlo = s.kernel.const_(p.zero_lt_one, vec![]);
    let hab = capp(&mut s.kernel, p.le_of_lt, &[zero, one, zlo]);
    let big_f = capp(&mut s.kernel, p.ivt_plateau, &[v]);
    let huc = capp(&mut s.kernel, p.ivt_plateau_uniformly_continuous, &[v]);
    let hfa = capp(&mut s.kernel, p.ivt_plateau_nonpos_at_zero, &[v]);
    let hfb = capp(&mut s.kernel, p.ivt_plateau_nonneg_at_one, &[v]);

    let args = [big_f, zero, one, huc, hab, hfa, hfb, n];
    let body = capp(&mut s.kernel, p.ivt_approx, &args);
    let ivt_decl_ty = decl_ty(&s.kernel, p.ivt_approx);
    let body_ty = apply_ty(&mut s.kernel, ivt_decl_ty, &args);

    let value = {
        let l2 = lam1(&mut s.kernel, anon, nat_ty, n_id, body);
        lam1(&mut s.kernel, anon, creal_ty, v_id, l2)
    };
    let ty = {
        let t2 = pi1(&mut s.kernel, anon, nat_ty, n_id, body_ty);
        pi1(&mut s.kernel, anon, creal_ty, v_id, t2)
    };
    let name = s.kernel.name_str(s.audit_ns, "ivt_approx_at_ivtPlateau");
    s.admit(name, ty, value, "EvtAudit.ivt_approx_at_ivtPlateau");
}

/// `EvtAudit.supOn_le_supOn_of_two_moduli` and
/// `EvtAudit.supOn_modulus_independent`.
///
/// `CReal.supOn F a b hab huc` takes the uniform-continuity witness as an
/// argument, and `CReal.UniformlyContinuousOn` is an inductive in `Sort 1`
/// (`Type 0`), **not** a `Prop` — it carries the modulus, so it is data and is
/// not proof-irrelevant. `hab : CReal.le a b` IS a `Prop` and does not have
/// this problem. Consequently two different moduli for the same `F` give two
/// `supOn` terms the kernel does not identify, and nothing in the environment
/// relates them.
///
/// They are nonetheless equal up to `CReal.Equiv`, from the two characterizing
/// laws plus `CReal.le_of_forall_le_add_small`. This builds that proof.
fn build_modulus_independence(s: &mut Probe) {
    let p = s.p;
    let anon = s.anon;
    let creal_ty = s.creal_ty;
    let nat_ty = s.nat_ty;

    let fn_ty = s.kernel.pi(anon, creal_ty, creal_ty, BinderInfo::Default);
    let f_id = s.fresh();
    let f = s.kernel.fvar(f_id);
    let a_id = s.fresh();
    let a = s.kernel.fvar(a_id);
    let b_id = s.fresh();
    let b = s.kernel.fvar(b_id);
    let hab_ty = capp(&mut s.kernel, p.le, &[a, b]);
    let hab_id = s.fresh();
    let hab = s.kernel.fvar(hab_id);
    let huc_ty = capp(&mut s.kernel, p.uniformly_continuous_on, &[f, a, b]);
    let u1_id = s.fresh();
    let u1 = s.kernel.fvar(u1_id);
    let u2_id = s.fresh();
    let u2 = s.kernel.fvar(u2_id);

    // One direction, as a closure over the two witnesses in either order.
    let one_way = |s: &mut Probe, ua: ExprId, ub_w: ExprId| -> (ExprId, ExprId) {
        let sup_a = capp(&mut s.kernel, p.sup_on, &[f, a, b, hab, ua]);
        let sup_b = capp(&mut s.kernel, p.sup_on, &[f, a, b, hab, ub_w]);

        let n_id = s.fresh();
        let n = s.kernel.fvar(n_id);
        let lub = capp(&mut s.kernel, p.sup_on_approx_lub, &[f, a, b, hab, ua, n]);
        let lub_decl_ty = decl_ty(&s.kernel, p.sup_on_approx_lub);
        let lub_ty = apply_ty(&mut s.kernel, lub_decl_ty, &[f, a, b, hab, ua, n]);
        let (_carrier, pred) = args2(&s.kernel, lub_ty);

        let x_id = s.fresh();
        let x = s.kernel.fvar(x_id);
        let pred_body = s.kernel.lam_body(pred).expect("predicate must be a lambda");
        let px = s.kernel.instantiate(pred_body, &[x]);
        let (a1, r1) = args2(&s.kernel, px);
        let (a2, a3) = args2(&s.kernel, r1);
        // a3 = le sup_a (add (F x) eps)
        let (_lhs, rhs) = args2(&s.kernel, a3);
        let (fx, eps) = args2(&s.kernel, rhs);

        let hx_id = s.fresh();
        let hx = s.kernel.fvar(hx_id);
        let ha = capp(&mut s.kernel, s.and_left, &[a1, r1, hx]);
        let hr = capp(&mut s.kernel, s.and_right, &[a1, r1, hx]);
        let hxb = capp(&mut s.kernel, s.and_left, &[a2, a3, hr]);
        let hsup = capp(&mut s.kernel, s.and_right, &[a2, a3, hr]);

        // `F x ≤ sup_b` from the OTHER witness's upper-bound law.
        let hub = capp(
            &mut s.kernel,
            p.sup_on_ub,
            &[f, a, b, hab, ub_w, x, ha, hxb],
        );
        let eps_refl = capp(&mut s.kernel, p.le_refl, &[eps]);
        let step = capp(
            &mut s.kernel,
            p.add_le_add,
            &[fx, sup_b, eps, eps, hub, eps_refl],
        );
        let sup_b_plus = capp(&mut s.kernel, p.add, &[sup_b, eps]);
        let chained = capp(
            &mut s.kernel,
            p.le_trans,
            &[sup_a, rhs, sup_b_plus, hsup, step],
        );

        let motive_body = capp(&mut s.kernel, p.le, &[sup_a, sup_b_plus]);
        let motive = s.kernel.lam(anon, lub_ty, motive_body, BinderInfo::Default);
        let intro_branch = {
            let l2 = lam1(&mut s.kernel, anon, px, hx_id, chained);
            lam1(&mut s.kernel, anon, creal_ty, x_id, l2)
        };
        let at_n = capp_u(
            &mut s.kernel,
            s.exists_rec,
            s.lvl1,
            &[creal_ty, pred, motive, intro_branch, lub],
        );
        let forall_n = lam1(&mut s.kernel, anon, nat_ty, n_id, at_n);
        let le_ab = capp(
            &mut s.kernel,
            p.le_of_forall_le_add_small,
            &[sup_a, sup_b, forall_n],
        );
        let ty = capp(&mut s.kernel, p.le, &[sup_a, sup_b]);
        (le_ab, ty)
    };

    let (fwd, fwd_ty) = one_way(s, u1, u2);
    let (bwd, _bwd_ty) = one_way(s, u2, u1);

    let sup1 = capp(&mut s.kernel, p.sup_on, &[f, a, b, hab, u1]);
    let sup2 = capp(&mut s.kernel, p.sup_on, &[f, a, b, hab, u2]);
    let equiv = capp(&mut s.kernel, p.equiv_of_le_le, &[sup1, sup2, fwd, bwd]);
    let equiv_ty = capp(&mut s.kernel, p.equiv, &[sup1, sup2]);

    let close_value = |s: &mut Probe, v: ExprId| -> ExprId {
        let v5 = lam1(&mut s.kernel, anon, huc_ty, u2_id, v);
        let v4 = lam1(&mut s.kernel, anon, huc_ty, u1_id, v5);
        let v3 = lam1(&mut s.kernel, anon, hab_ty, hab_id, v4);
        let v2 = lam1(&mut s.kernel, anon, creal_ty, b_id, v3);
        let v1 = lam1(&mut s.kernel, anon, creal_ty, a_id, v2);
        lam1(&mut s.kernel, anon, fn_ty, f_id, v1)
    };
    let close_ty = |s: &mut Probe, t: ExprId| -> ExprId {
        let t5 = pi1(&mut s.kernel, anon, huc_ty, u2_id, t);
        let t4 = pi1(&mut s.kernel, anon, huc_ty, u1_id, t5);
        let t3 = pi1(&mut s.kernel, anon, hab_ty, hab_id, t4);
        let t2 = pi1(&mut s.kernel, anon, creal_ty, b_id, t3);
        let t1 = pi1(&mut s.kernel, anon, creal_ty, a_id, t2);
        pi1(&mut s.kernel, anon, fn_ty, f_id, t1)
    };

    let half_value = close_value(s, fwd);
    let half_ty = close_ty(s, fwd_ty);
    let half_name = s
        .kernel
        .name_str(s.audit_ns, "supOn_le_supOn_of_two_moduli");
    s.admit(
        half_name,
        half_ty,
        half_value,
        "EvtAudit.supOn_le_supOn_of_two_moduli",
    );

    let eq_value = close_value(s, equiv);
    let eq_ty = close_ty(s, equiv_ty);
    let eq_name = s.kernel.name_str(s.audit_ns, "supOn_modulus_independent");
    s.admit(
        eq_name,
        eq_ty,
        eq_value,
        "EvtAudit.supOn_modulus_independent",
    );
}

/// Does `ty` live in `Prop`? Read by inference, never from a name.
///
/// Mirrors `tests/support/creal_representability.rs::is_a_proposition`, which
/// is what `F:lean-kernel-accepts-the-whole-constructed-real-carrier` uses to
/// decide which declarations its Lean replay covers.
fn is_a_proposition(kernel: &mut Kernel, ty: ExprId) -> bool {
    let Ok(sort) = kernel.infer(ty) else {
        return false;
    };
    let sort = kernel.whnf(sort);
    let ExprNode::Sort(level) = *kernel.expr_node(sort) else {
        return false;
    };
    matches!(kernel.level_node(level), LevelNode::Zero)
}

/// Classify each IVT/EVT subject as REPRESENTABLE (covered by the Lean-kernel
/// replay), NOT-PROP, or BLOCKED-BY a non-`Prop` `Theorem` in its closure.
fn report_representability(s: &mut Probe) {
    let p = s.p;
    let subjects: Vec<(&str, NameId)> = vec![
        ("CReal.ivt_approx", p.ivt_approx),
        ("CReal.ivt_exact_root", p.ivt_exact_root),
        (
            "CReal.ivt_exact_root_decides_sign",
            p.ivt_exact_root_decides_sign,
        ),
        (
            "CReal.evt_attained_max_decides_sign",
            p.evt_attained_max_decides_sign,
        ),
        ("CReal.supOn", p.sup_on),
        ("CReal.supOn_ub", p.sup_on_ub),
        ("CReal.supOn_approx_lub", p.sup_on_approx_lub),
        // Positive control of the OPPOSITE verdict: the fact names this one as
        // residue, so a run in which everything is representable is broken.
        ("CReal.weierstrassMTest", p.weierstrass_m_test),
    ];

    println!("\nLean-kernel replay coverage (the fact's own representability predicate):");
    let mut any_residue = false;
    for (label, name) in subjects {
        let Some(decl) = s.kernel.environment().get(name).cloned() else {
            s.failures
                .push(format!("{label}: absent from the environment"));
            continue;
        };
        let mut verdict = String::from("representable");
        if let Declaration::Theorem { ty, .. } = decl
            && !is_a_proposition(&mut s.kernel, ty)
        {
            verdict = String::from("NOT-PROP (outside the replay)");
        }
        if verdict == "representable" {
            let closure = s.kernel.declaration_dependency_closure(name);
            for dep in closure {
                let Some(d) = s.kernel.environment().get(dep).cloned() else {
                    continue;
                };
                if let Declaration::Theorem { ty, .. } = d
                    && !is_a_proposition(&mut s.kernel, ty)
                {
                    verdict = format!(
                        "BLOCKED-BY {} (outside the replay)",
                        s.kernel.display_name(dep)
                    );
                    break;
                }
            }
        }
        if verdict != "representable" {
            any_residue = true;
        }
        println!("  {label:38}  {verdict}");
    }
    if !any_residue {
        s.failures.push(String::from(
            "representability: EVERY subject came back representable, including the \
             control CReal.weierstrassMTest, which the carrier fact names as residue -- \
             the classifier is not discriminating",
        ));
    }
}

fn main() {
    let code = on_a_deep_stack(run);
    std::process::exit(code);
}
