#![allow(clippy::many_single_char_names, clippy::too_many_lines)]

//! **Follow-up probe for ADR-1495: is the constructor-argument universe
//! constraint enforced?**
//!
//! `bundled_structure_probe.rs`'s universe CONTROL did not fire: the same
//! seventeen-field bundle carrying a `Sort 1` carrier was accepted at result
//! universe `Sort 1` as well as at `Sort 2`. Lean's kernel rejects that
//! (`inductive.cpp`, `check_constructor`: "universe level of the field's type is
//! too big for the corresponding inductive datatype"). This probe isolates the
//! question to the smallest possible shape and asks what the acceptance buys.
//!
//! Stages:
//!
//! 1. `AbsProbe2.U : Sort 1` with `mk : Sort 1 → U`. Does `add_inductive`
//!    accept an inductive that stores its own universe?
//! 2. If so, is LARGE ELIMINATION out of it available — `el : U → Sort 1` —
//!    and does `el (mk X)` reduce to `X`? Together with `mk`, that makes
//!    `Sort 1` a retract of a `Sort 1`-inhabitant, the standard
//!    `Type : Type` precondition for Girard's paradox.
//! 3. The same at one level up (`Sort 2` storing `Sort 2`), to show the
//!    behaviour is not specific to level 1.
//! 4. **Positive control**: a genuinely non-strictly-positive inductive
//!    (`Bad : Sort 1`, `mk : (Bad → Bad) → Bad`) must still be REFUSED. Without
//!    it, "accepted" above could mean the checker is not running at all rather
//!    than that this particular constraint is absent.
//!
//! This probe does NOT derive `False`; deriving Hurkens' paradox is a separate
//! and much larger undertaking. It reports the retraction and the missing
//! constraint, and says exactly that.

use axeyum_lean_kernel::{BinderInfo, Declaration, ExprId, Kernel, ReducibilityHint};

fn lam_over(k: &mut Kernel, fv: u64, ty: ExprId, body: ExprId) -> ExprId {
    let b = k.abstract_fvars(body, &[fv]);
    let anon = k.anon();
    k.lam(anon, ty, b, BinderInfo::Default)
}

fn main() {
    let mut k = Kernel::new();
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let l2 = k.level_succ(l1);
    let l3 = k.level_succ(l2);

    let root = k.anon();
    let ns = k.name_str(root, "AbsProbe2");

    let mut findings: Vec<String> = Vec::new();

    // --- Stage 4 first: positivity is alive (positive control) --------------
    {
        let bad = k.name_str(ns, "Bad");
        let bad_mk = k.name_str(bad, "mk");
        let sort1 = k.sort(l1);
        let bad_c = k.const_(bad, vec![]);
        let anon = k.anon();
        let neg = k.pi(anon, bad_c, bad_c, BinderInfo::Default);
        let ctor = k.pi(anon, neg, bad_c, BinderInfo::Default);
        match k.add_inductive(bad, &[], 0, sort1, &[(bad_mk, ctor)]) {
            Ok(()) => {
                println!("POSITIVITY CONTROL: FAILED -- non-positive inductive accepted");
                findings.push("positivity-control-failed".to_owned());
            }
            Err(e) => println!("positivity control: PASS -- refused: {e:?}"),
        }
    }

    // --- Stage 1/2: U : Sort 1 storing Sort 1 -------------------------------
    let u = k.name_str(ns, "U");
    let u_mk = k.name_str(u, "mk");
    let u_rec = k.name_str(u, "rec");
    let x_fv = 7_000_u64;
    let s_fv = 7_001_u64;

    let accepted_u = {
        let sort1 = k.sort(l1);
        let u_c = k.const_(u, vec![]);
        let anon = k.anon();
        let ctor = k.pi(anon, sort1, u_c, BinderInfo::Default);
        let sort1b = k.sort(l1);
        match k.add_inductive(u, &[], 0, sort1b, &[(u_mk, ctor)]) {
            Ok(()) => {
                println!("stage 1: AbsProbe2.U : Sort 1 with `mk : Sort 1 -> U` ACCEPTED");
                findings.push("U:Sort1 storing Sort 1 accepted".to_owned());
                true
            }
            Err(e) => {
                println!("stage 1: refused (Lean-consistent): {e:?}");
                false
            }
        }
    };

    if accepted_u {
        // el : U -> Sort 1, by large elimination (motive lands in Sort 2).
        let el = k.name_str(u, "el");
        let u_ty = k.const_(u, vec![]);
        let motive = {
            let s1 = k.sort(l1);
            lam_over(&mut k, s_fv, u_ty, s1)
        };
        let minor = {
            let x = k.fvar(x_fv);
            let s1 = k.sort(l1);
            lam_over(&mut k, x_fv, s1, x)
        };
        let value = {
            let rec = k.const_(u_rec, vec![l2]);
            let e = k.app(rec, motive);
            let e = k.app(e, minor);
            let s = k.fvar(s_fv);
            let e = k.app(e, s);
            lam_over(&mut k, s_fv, u_ty, e)
        };
        let ty = {
            let s1 = k.sort(l1);
            let anon = k.anon();
            k.pi(anon, u_ty, s1, BinderInfo::Default)
        };
        match k.add_declaration(Declaration::Definition {
            name: el,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        }) {
            Ok(()) => {
                println!("stage 2: `el : U -> Sort 1` by LARGE elimination ACCEPTED");
                findings.push("large elimination U -> Sort 1 accepted".to_owned());
                // el (mk X) =?= X  -- the retraction.
                let x = k.fvar(x_fv);
                let mk = k.const_(u_mk, vec![]);
                let boxed = k.app(mk, x);
                let el_c = k.const_(el, vec![]);
                let unboxed = k.app(el_c, boxed);
                if k.def_eq(unboxed, x) {
                    println!(
                        "stage 2: RETRACTION HOLDS -- el (mk X) def_eq X, so Sort 1 is a retract"
                    );
                    println!("         of an inhabitant of Sort 1 (Type : Type precondition)");
                    findings.push("retraction el(mk X) = X holds".to_owned());
                } else {
                    println!("stage 2: el (mk X) is NOT def_eq X -- no retraction");
                }
            }
            Err(e) => println!("stage 2: large elimination refused: {e:?}"),
        }
    }

    // --- Stage 3: one level up ---------------------------------------------
    {
        let v = k.name_str(ns, "V");
        let v_mk = k.name_str(v, "mk");
        let sort2 = k.sort(l2);
        let v_c = k.const_(v, vec![]);
        let anon = k.anon();
        let ctor = k.pi(anon, sort2, v_c, BinderInfo::Default);
        let sort2b = k.sort(l2);
        match k.add_inductive(v, &[], 0, sort2b, &[(v_mk, ctor)]) {
            Ok(()) => {
                println!("stage 3: AbsProbe2.V : Sort 2 with `mk : Sort 2 -> V` ACCEPTED too");
                findings.push("same at Sort 2".to_owned());
            }
            Err(e) => println!("stage 3: refused at Sort 2: {e:?}"),
        }
    }

    // --- Stage 5: what Lean would accept, for contrast ----------------------
    {
        let w = k.name_str(ns, "W");
        let w_mk = k.name_str(w, "mk");
        let sort2 = k.sort(l2);
        let w_c = k.const_(w, vec![]);
        let anon = k.anon();
        let sort1 = k.sort(l1);
        let ctor = k.pi(anon, sort1, w_c, BinderInfo::Default);
        match k.add_inductive(w, &[], 0, sort2, &[(w_mk, ctor)]) {
            Ok(()) => println!("stage 5: AbsProbe2.W : Sort 2 with `mk : Sort 1 -> W` ACCEPTED"),
            Err(e) => {
                println!("stage 5: FAIL -- the Lean-legal form was refused: {e:?}");
                findings.push("lean-legal-form-refused".to_owned());
            }
        }
    }
    let _ = l3;

    println!("FINDINGS: {findings:?}");
}
