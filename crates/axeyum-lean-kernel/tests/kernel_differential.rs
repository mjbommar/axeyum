//! ADR-0717 S5: kernel differential and mutation programme.
//!
//! Risk 1 of the trusted-library safety threat model
//! (`docs/research/09-decisions/adr-0717-library-construction-is-graph-directed-through-an-artifact-compatible-trust-anchor.md`,
//! `docs/plan/trusted-library-safety-roadmap-2026-08-30.md` S5) is that
//! Axeyum's kernel could have a semantic defect that no amount of
//! axiom-freedom detects, because every one of our proofs is checked by that
//! same kernel. This suite generates a deterministic corpus of well-typed and
//! nearly-well-typed core declarations across eight semantic subsystems
//! (conversion, universes, inductives, recursors, projections, literals,
//! quotient, proof irrelevance) and checks each one against BOTH kernels:
//! this crate's own [`Kernel`], and the pinned official Lean binary.
//!
//! Every case is hand-authored on BOTH sides independently (an Axeyum
//! construction via the kernel's term-builder API, and a plain `.lean`
//! source snippet expressing the same mathematical content in Lean's own
//! surface syntax), following the pattern already established by this
//! crate's `real_lean_*_crosscheck` suites. This is deliberately NOT a
//! render-then-replay pipeline: `Kernel::render_lean_module` only walks an
//! already-checked declaration closure, so it cannot express the
//! nearly-well-typed (Axeyum-rejects) half of the corpus, which never
//! reaches the environment. Two independent authorings is also the more
//! meaningful differential: each kernel decides accept/reject using its own
//! native surface, not a translation designed to please the other.
//!
//! # Classification
//!
//! * **Both accept** or **both reject**: agreement, the expected outcome for
//!   every case in this corpus except one documented exception (below).
//! * **Axeyum accepts, Lean rejects**: a potential Axeyum kernel
//!   unsoundness. This is P0 and the test hard-fails on it, unconditionally.
//! * **Axeyum rejects, Lean accepts**: incompleteness. Non-fatal by default,
//!   but any case in this corpus taking this branch must be pre-registered
//!   in [`EXPLAINED_INCOMPLETENESS`] with a citation, or the test fails —
//!   an "explained" bucket that accepts anything is not a bucket.
//!
//! The one pre-registered exception is `quotient::quot_sound_absent`:
//! this kernel implements exactly Lean's four-declaration quotient package
//! (`Quot`/`Quot.mk`/`Quot.lift`/`Quot.ind`) and deliberately has no
//! `Quot.sound` (ADR-0456; see `creal.rs`, `int_prelude.rs`, `rat_prelude.rs`
//! module docs). Lean's kernel treats `Quot.sound` as a fifth built-in
//! primitive, so a term citing it is trivially accepted there and rejected
//! here (the name does not exist). This is a known, deliberate design
//! decision, not a fresh finding, and the corpus exists partly to confirm
//! the differential correctly reports it as such rather than either hiding
//! it or crying wolf.
//!
//! # What this does NOT cover
//!
//! See the doc comment on `kernel_differential_corpus_matches_pinned_lean`
//! for the explicit, honest limitations statement required by the roadmap.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, Kernel, Lit, LogicPrelude, NameId, ReducibilityHint,
    build_logic_prelude,
};

#[path = "support/lean_probe.rs"]
mod lean_probe;

/// The eight semantic subsystems ADR-0717 S5 names, in the order it names
/// them. Every one of these must have a nonzero corpus count, or the test
/// fails naming the empty subsystem explicitly (never a silent zero).
const SUBSYSTEMS: &[&str] = &[
    "conversion",
    "universes",
    "inductives",
    "recursors",
    "projections",
    "literals",
    "quotient",
    "proof_irrelevance",
];

/// Pre-registered, cited exceptions to "every disagreement is either
/// agreement or P0". Each entry is `(case_name, citation)`. A disagreement
/// whose case name is NOT in this list is always treated as unexplained: for
/// an Axeyum-accepts/Lean-rejects disagreement that means P0 regardless of
/// this list (nothing may waive that); for an Axeyum-rejects/Lean-accepts
/// disagreement NOT listed here, the test fails just as loudly, because an
/// "explained incompleteness" bucket that accepts anything unregistered is
/// not doing any work.
const EXPLAINED_INCOMPLETENESS: &[(&str, &str)] = &[(
    "quotient::quot_sound_absent",
    "ADR-0456 / creal.rs, int_prelude.rs, rat_prelude.rs module docs: this \
     kernel implements exactly Lean's Quot/Quot.mk/Quot.lift/Quot.ind and \
     deliberately has no Quot.sound.",
)];

// ---------------------------------------------------------------------------
// Harness plumbing
// ---------------------------------------------------------------------------

struct CaseResult {
    subsystem: &'static str,
    name: &'static str,
    axeyum_accept: bool,
    lean_source: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Verdict {
    AgreeAccept,
    AgreeReject,
    /// Axeyum accepted something Lean rejects. P0.
    AxeyumAcceptsLeanRejects,
    /// Axeyum rejected something Lean accepts. Incompleteness.
    AxeyumRejectsLeanAccepts,
}

fn classify(axeyum_accept: bool, lean_accept: bool) -> Verdict {
    match (axeyum_accept, lean_accept) {
        (true, true) => Verdict::AgreeAccept,
        (false, false) => Verdict::AgreeReject,
        (true, false) => Verdict::AxeyumAcceptsLeanRejects,
        (false, true) => Verdict::AxeyumRejectsLeanAccepts,
    }
}

fn run_lean(lean: &Path, source: &str, tag: &str, dir: &Path) -> bool {
    let file = dir.join(format!("{tag}.lean"));
    std::fs::write(&file, source).unwrap_or_else(|e| panic!("write {tag}.lean: {e}"));
    let output = Command::new(lean)
        // Keep this viable under the repository's process memory bound; see
        // real_lean_structure_eta_crosscheck.rs for the same flags.
        .args(["-j", "1", "-s", "1024", "-M", "4096"])
        .arg(&file)
        .output()
        .unwrap_or_else(|e| panic!("run pinned lean on {tag}.lean: {e}"));
    output.status.success()
}

// ---------------------------------------------------------------------------
// Shared term-building helpers
// ---------------------------------------------------------------------------

/// Fold repeated application: `apps(k, f, [a, b])` builds `f a b`.
fn apps(kernel: &mut Kernel, head: ExprId, args: &[ExprId]) -> ExprId {
    let mut result = head;
    for &arg in args {
        result = kernel.app(result, arg);
    }
    result
}

/// A non-dependent Pi (`domain -> codomain`).
fn arrow(kernel: &mut Kernel, domain: ExprId, codomain: ExprId) -> ExprId {
    let anon = kernel.anon();
    kernel.pi(anon, domain, codomain, BinderInfo::Default)
}

/// `Eq.{level} a_ty x y`.
fn eq_ty(
    kernel: &mut Kernel,
    logic: &LogicPrelude,
    level: axeyum_lean_kernel::LevelId,
    a_ty: ExprId,
    x: ExprId,
    y: ExprId,
) -> ExprId {
    let eq_c = kernel.const_(logic.eq, vec![level]);
    apps(kernel, eq_c, &[a_ty, x, y])
}

/// `Eq.refl.{level} a_ty x : Eq a_ty x x`.
fn eq_refl(
    kernel: &mut Kernel,
    logic: &LogicPrelude,
    level: axeyum_lean_kernel::LevelId,
    a_ty: ExprId,
    x: ExprId,
) -> ExprId {
    let r = kernel.const_(logic.eq_refl, vec![level]);
    apps(kernel, r, &[a_ty, x])
}

/// Declares a fresh `axiom name : Sort level` and returns its `Const`.
fn declare_axiom_type(kernel: &mut Kernel, label: &str, level: axeyum_lean_kernel::LevelId) -> (NameId, ExprId) {
    let anon = kernel.anon();
    let name = kernel.name_str(anon, label);
    let ty = kernel.sort(level);
    kernel
        .add_declaration(Declaration::Axiom {
            name,
            uparams: Vec::new(),
            ty,
        })
        .unwrap_or_else(|e| panic!("declare axiom type {label}: {e:?}"));
    let c = kernel.const_(name, vec![]);
    (name, c)
}

/// Declares a fresh `axiom name : ty` and returns its `Const`.
fn declare_axiom(kernel: &mut Kernel, label: &str, ty: ExprId) -> (NameId, ExprId) {
    let anon = kernel.anon();
    let name = kernel.name_str(anon, label);
    kernel
        .add_declaration(Declaration::Axiom {
            name,
            uparams: Vec::new(),
            ty,
        })
        .unwrap_or_else(|e| panic!("declare axiom {label}: {e:?}"));
    let c = kernel.const_(name, vec![]);
    (name, c)
}

/// Declares a minimal `Nat`-shaped inductive (`zero`/`succ`, no params/
/// indices) matching exactly the reserved-declaration shape this kernel's
/// `Lit::Nat` bootstrap requires (`tc.rs::nat_literal_bootstrap`), without
/// pulling in the full `nat_prelude` (hundreds of unrelated theorems).
/// Returns `(nat_name, zero_name, succ_name, nat_const, zero_const, succ_const)`.
#[allow(clippy::type_complexity)]
fn declare_minimal_nat(
    kernel: &mut Kernel,
) -> (NameId, NameId, NameId, ExprId, ExprId, ExprId) {
    let anon = kernel.anon();
    let nat = kernel.name_str(anon, "Nat");
    let zero = kernel.name_str(nat, "zero");
    let succ = kernel.name_str(nat, "succ");
    let nat_const = kernel.const_(nat, vec![]);
    let zero_lvl = kernel.level_zero();
    let one_lvl = kernel.level_succ(zero_lvl);
    let nat_ty = kernel.sort(one_lvl);
    let succ_ty = arrow(kernel, nat_const, nat_const);
    kernel
        .add_inductive(nat, &[], 0, nat_ty, &[(zero, nat_const), (succ, succ_ty)])
        .expect("minimal Nat must admit");
    let zero_const = kernel.const_(zero, vec![]);
    let succ_const = kernel.const_(succ, vec![]);
    (nat, zero, succ, nat_const, zero_const, succ_const)
}

/// `close_pi`: given a body built against a set of free variables, abstract
/// each one out (innermost first) and wrap with a `Pi` of the given binder
/// name/type/info. Mirrors `quotient.rs`'s private `close_pi` exactly, using
/// only public API (`fvar`/`abstract_fvars`/`pi`), so an external test can
/// build the same canonical shapes without access to that private helper.
fn close_pi(
    kernel: &mut Kernel,
    binders: &[(NameId, u64, ExprId, BinderInfo)],
    mut body: ExprId,
) -> ExprId {
    for &(name, fv, ty, info) in binders.iter().rev() {
        body = kernel.abstract_fvars(body, &[fv]);
        body = kernel.pi(name, ty, body, info);
    }
    body
}

/// `alpha -> alpha -> Prop`.
fn relation_type(kernel: &mut Kernel, alpha: ExprId) -> ExprId {
    let prop = kernel.sort_zero();
    let inner = arrow(kernel, alpha, prop);
    arrow(kernel, alpha, inner)
}

// ---------------------------------------------------------------------------
// Subsystem: conversion (beta / delta chains)
// ---------------------------------------------------------------------------

fn conversion_cases() -> Vec<CaseResult> {
    let mut out = Vec::new();
    let one_lvl = |k: &mut Kernel| k.level_succ(k.level_zero());

    // P1: beta reduction (`idA a` reduces to `a`).
    {
        let mut kernel = Kernel::new();
        let logic = build_logic_prelude(&mut kernel).expect("logic prelude");
        let lvl = one_lvl(&mut kernel);
        let (_, a_ty) = declare_axiom_type(&mut kernel, "A", lvl);
        let (_, a_val) = declare_axiom(&mut kernel, "a", a_ty);
        let anon = kernel.anon();
        let ida_name = kernel.name_str(anon, "idA");
        let ida_ty = arrow(&mut kernel, a_ty, a_ty);
        let ida_val = kernel.lam(anon, a_ty, kernel.bvar(0), BinderInfo::Default);
        kernel
            .add_declaration(Declaration::Definition {
                name: ida_name,
                uparams: Vec::new(),
                ty: ida_ty,
                value: ida_val,
                hint: ReducibilityHint::Regular(0),
            })
            .expect("idA must admit");
        let ida_c = kernel.const_(ida_name, vec![]);
        let ida_a = kernel.app(ida_c, a_val);
        let goal = eq_ty(&mut kernel, &logic, lvl, a_ty, ida_a, a_val);
        let proof = eq_refl(&mut kernel, &logic, lvl, a_ty, a_val);
        let thm = kernel.name_str(anon, "case");
        let accept = kernel
            .add_declaration(Declaration::Theorem {
                name: thm,
                uparams: Vec::new(),
                ty: goal,
                value: proof,
            })
            .is_ok();
        out.push(CaseResult {
            subsystem: "conversion",
            name: "conversion::beta_positive",
            axeyum_accept: accept,
            lean_source: "set_option autoImplicit false\n\
                axiom A : Type\naxiom a : A\ndef idA (x : A) : A := x\n\
                theorem case1 : idA a = a := rfl\n"
                .to_string(),
        });
    }

    // P2: delta chain (`g` unfolds through `f` to `idA`).
    {
        let mut kernel = Kernel::new();
        let logic = build_logic_prelude(&mut kernel).expect("logic prelude");
        let lvl = one_lvl(&mut kernel);
        let (_, a_ty) = declare_axiom_type(&mut kernel, "A", lvl);
        let (_, a_val) = declare_axiom(&mut kernel, "a", a_ty);
        let anon = kernel.anon();
        let ida_name = kernel.name_str(anon, "idA");
        let ida_ty = arrow(&mut kernel, a_ty, a_ty);
        let ida_val = kernel.lam(anon, a_ty, kernel.bvar(0), BinderInfo::Default);
        kernel
            .add_declaration(Declaration::Definition {
                name: ida_name,
                uparams: Vec::new(),
                ty: ida_ty,
                value: ida_val,
                hint: ReducibilityHint::Regular(0),
            })
            .expect("idA must admit");
        let ida_c = kernel.const_(ida_name, vec![]);
        let f_name = kernel.name_str(anon, "f");
        kernel
            .add_declaration(Declaration::Definition {
                name: f_name,
                uparams: Vec::new(),
                ty: ida_ty,
                value: ida_c,
                hint: ReducibilityHint::Regular(1),
            })
            .expect("f must admit");
        let f_c = kernel.const_(f_name, vec![]);
        let g_name = kernel.name_str(anon, "g");
        kernel
            .add_declaration(Declaration::Definition {
                name: g_name,
                uparams: Vec::new(),
                ty: ida_ty,
                value: f_c,
                hint: ReducibilityHint::Regular(2),
            })
            .expect("g must admit");
        let g_c = kernel.const_(g_name, vec![]);
        let g_a = kernel.app(g_c, a_val);
        let goal = eq_ty(&mut kernel, &logic, lvl, a_ty, g_a, a_val);
        let proof = eq_refl(&mut kernel, &logic, lvl, a_ty, a_val);
        let thm = kernel.name_str(anon, "case");
        let accept = kernel
            .add_declaration(Declaration::Theorem {
                name: thm,
                uparams: Vec::new(),
                ty: goal,
                value: proof,
            })
            .is_ok();
        out.push(CaseResult {
            subsystem: "conversion",
            name: "conversion::delta_chain_positive",
            axeyum_accept: accept,
            lean_source: "set_option autoImplicit false\n\
                axiom A : Type\naxiom a : A\ndef idA (x : A) : A := x\n\
                def f := idA\ndef g := f\ntheorem case2 : g a = a := rfl\n"
                .to_string(),
        });
    }

    // N1: beta mismatch (`idA a` claimed equal to an unrelated axiom `b`).
    {
        let mut kernel = Kernel::new();
        let logic = build_logic_prelude(&mut kernel).expect("logic prelude");
        let lvl = one_lvl(&mut kernel);
        let (_, a_ty) = declare_axiom_type(&mut kernel, "A", lvl);
        let (_, a_val) = declare_axiom(&mut kernel, "a", a_ty);
        let (_, b_val) = declare_axiom(&mut kernel, "b", a_ty);
        let anon = kernel.anon();
        let ida_name = kernel.name_str(anon, "idA");
        let ida_ty = arrow(&mut kernel, a_ty, a_ty);
        let ida_val = kernel.lam(anon, a_ty, kernel.bvar(0), BinderInfo::Default);
        kernel
            .add_declaration(Declaration::Definition {
                name: ida_name,
                uparams: Vec::new(),
                ty: ida_ty,
                value: ida_val,
                hint: ReducibilityHint::Regular(0),
            })
            .expect("idA must admit");
        let ida_c = kernel.const_(ida_name, vec![]);
        let ida_a = kernel.app(ida_c, a_val);
        let goal = eq_ty(&mut kernel, &logic, lvl, a_ty, ida_a, b_val);
        let proof = eq_refl(&mut kernel, &logic, lvl, a_ty, a_val);
        let thm = kernel.name_str(anon, "case");
        let accept = kernel
            .add_declaration(Declaration::Theorem {
                name: thm,
                uparams: Vec::new(),
                ty: goal,
                value: proof,
            })
            .is_ok();
        out.push(CaseResult {
            subsystem: "conversion",
            name: "conversion::beta_mismatch_negative",
            axeyum_accept: accept,
            lean_source: "set_option autoImplicit false\n\
                axiom A : Type\naxiom a : A\naxiom b : A\ndef idA (x : A) : A := x\n\
                theorem case3 : idA a = b := rfl\n"
                .to_string(),
        });
    }

    // N2: delta-chain mismatch through the same `f`/`g` chain as P2.
    {
        let mut kernel = Kernel::new();
        let logic = build_logic_prelude(&mut kernel).expect("logic prelude");
        let lvl = one_lvl(&mut kernel);
        let (_, a_ty) = declare_axiom_type(&mut kernel, "A", lvl);
        let (_, a_val) = declare_axiom(&mut kernel, "a", a_ty);
        let (_, b_val) = declare_axiom(&mut kernel, "b", a_ty);
        let anon = kernel.anon();
        let ida_name = kernel.name_str(anon, "idA");
        let ida_ty = arrow(&mut kernel, a_ty, a_ty);
        let ida_val = kernel.lam(anon, a_ty, kernel.bvar(0), BinderInfo::Default);
        kernel
            .add_declaration(Declaration::Definition {
                name: ida_name,
                uparams: Vec::new(),
                ty: ida_ty,
                value: ida_val,
                hint: ReducibilityHint::Regular(0),
            })
            .expect("idA must admit");
        let ida_c = kernel.const_(ida_name, vec![]);
        let f_name = kernel.name_str(anon, "f");
        kernel
            .add_declaration(Declaration::Definition {
                name: f_name,
                uparams: Vec::new(),
                ty: ida_ty,
                value: ida_c,
                hint: ReducibilityHint::Regular(1),
            })
            .expect("f must admit");
        let f_c = kernel.const_(f_name, vec![]);
        let g_name = kernel.name_str(anon, "g");
        kernel
            .add_declaration(Declaration::Definition {
                name: g_name,
                uparams: Vec::new(),
                ty: ida_ty,
                value: f_c,
                hint: ReducibilityHint::Regular(2),
            })
            .expect("g must admit");
        let g_c = kernel.const_(g_name, vec![]);
        let g_a = kernel.app(g_c, a_val);
        let goal = eq_ty(&mut kernel, &logic, lvl, a_ty, g_a, b_val);
        let proof = eq_refl(&mut kernel, &logic, lvl, a_ty, a_val);
        let thm = kernel.name_str(anon, "case");
        let accept = kernel
            .add_declaration(Declaration::Theorem {
                name: thm,
                uparams: Vec::new(),
                ty: goal,
                value: proof,
            })
            .is_ok();
        out.push(CaseResult {
            subsystem: "conversion",
            name: "conversion::delta_chain_mismatch_negative",
            axeyum_accept: accept,
            lean_source: "set_option autoImplicit false\n\
                axiom A : Type\naxiom a : A\naxiom b : A\ndef idA (x : A) : A := x\n\
                def f := idA\ndef g := f\ntheorem case4 : g a = b := rfl\n"
                .to_string(),
        });
    }

    out
}

// ---------------------------------------------------------------------------
// Subsystem: universes
// ---------------------------------------------------------------------------

fn universes_cases() -> Vec<CaseResult> {
    let mut out = Vec::new();

    fn declare_idu(kernel: &mut Kernel) -> (NameId, NameId) {
        let anon = kernel.anon();
        let u_name = kernel.name_str(anon, "u");
        let u = kernel.level_param(u_name);
        let sort_u = kernel.sort(u);
        let a_name = kernel.name_str(anon, "A");
        let a_val_name = kernel.name_str(anon, "a");
        let idu_ty = kernel.pi(
            a_name,
            sort_u,
            {
                let inner_ty = kernel.bvar(0);
                let inner_body = kernel.bvar(1);
                kernel.pi(a_val_name, inner_ty, inner_body, BinderInfo::Default)
            },
            BinderInfo::Implicit,
        );
        let idu_val = kernel.lam(
            a_name,
            sort_u,
            {
                let inner_ty = kernel.bvar(0);
                let inner_body = kernel.bvar(0);
                kernel.lam(a_val_name, inner_ty, inner_body, BinderInfo::Default)
            },
            BinderInfo::Implicit,
        );
        let idu_name = kernel.name_str(anon, "idU");
        kernel
            .add_declaration(Declaration::Definition {
                name: idu_name,
                uparams: vec![u_name],
                ty: idu_ty,
                value: idu_val,
                hint: ReducibilityHint::Regular(0),
            })
            .expect("idU must admit");
        (idu_name, u_name)
    }

    // P1: instantiated at Prop.
    {
        let mut kernel = Kernel::new();
        let logic = build_logic_prelude(&mut kernel).expect("logic prelude");
        let (idu_name, _) = declare_idu(&mut kernel);
        let zero_lvl = kernel.level_zero();
        let true_c = kernel.const_(logic.true_, vec![]);
        let true_intro_c = kernel.const_(logic.true_intro, vec![]);
        let idu0 = kernel.const_(idu_name, vec![zero_lvl]);
        let applied = apps(&mut kernel, idu0, &[true_c, true_intro_c]);
        let goal = eq_ty(&mut kernel, &logic, zero_lvl, true_c, applied, true_intro_c);
        let proof = eq_refl(&mut kernel, &logic, zero_lvl, true_c, true_intro_c);
        let anon = kernel.anon();
        let thm = kernel.name_str(anon, "case");
        let accept = kernel
            .add_declaration(Declaration::Theorem {
                name: thm,
                uparams: Vec::new(),
                ty: goal,
                value: proof,
            })
            .is_ok();
        out.push(CaseResult {
            subsystem: "universes",
            name: "universes::poly_identity_at_prop",
            axeyum_accept: accept,
            lean_source: "set_option autoImplicit false\n\
                universe u\ndef idU {A : Sort u} (a : A) : A := a\n\
                example : @idU _ True.intro = True.intro := rfl\n"
                .to_string(),
        });
    }

    // P2: instantiated at Type.
    {
        let mut kernel = Kernel::new();
        let logic = build_logic_prelude(&mut kernel).expect("logic prelude");
        let (idu_name, _) = declare_idu(&mut kernel);
        let zero_lvl = kernel.level_zero();
        let one_lvl = kernel.level_succ(zero_lvl);
        let (_, a2_ty) = declare_axiom_type(&mut kernel, "A2", one_lvl);
        let (_, a2_val) = declare_axiom(&mut kernel, "a2", a2_ty);
        let idu1 = kernel.const_(idu_name, vec![one_lvl]);
        let applied = apps(&mut kernel, idu1, &[a2_ty, a2_val]);
        let goal = eq_ty(&mut kernel, &logic, one_lvl, a2_ty, applied, a2_val);
        let proof = eq_refl(&mut kernel, &logic, one_lvl, a2_ty, a2_val);
        let anon = kernel.anon();
        let thm = kernel.name_str(anon, "case");
        let accept = kernel
            .add_declaration(Declaration::Theorem {
                name: thm,
                uparams: Vec::new(),
                ty: goal,
                value: proof,
            })
            .is_ok();
        out.push(CaseResult {
            subsystem: "universes",
            name: "universes::poly_identity_at_type",
            axeyum_accept: accept,
            lean_source: "set_option autoImplicit false\n\
                universe u\ndef idU {A : Sort u} (a : A) : A := a\n\
                axiom A2 : Type\naxiom a2 : A2\nexample : idU a2 = a2 := rfl\n"
                .to_string(),
        });
    }

    // N1: undeclared universe param (`u` used but not in `uparams`).
    {
        let mut kernel = Kernel::new();
        let anon = kernel.anon();
        let u_name = kernel.name_str(anon, "u");
        let u = kernel.level_param(u_name);
        let sort_u = kernel.sort(u);
        let bad_name = kernel.name_str(anon, "Bad");
        let accept = kernel
            .add_declaration(Declaration::Axiom {
                name: bad_name,
                uparams: Vec::new(),
                ty: sort_u,
            })
            .is_ok();
        out.push(CaseResult {
            subsystem: "universes",
            name: "universes::undeclared_universe_param_negative",
            axeyum_accept: accept,
            lean_source: "set_option autoImplicit false\naxiom Bad : Sort u\n".to_string(),
        });
    }

    // N2: sort promotion (`A : Sort u` wrongly claimed to also be `Sort (u+1)`).
    {
        let mut kernel = Kernel::new();
        let anon = kernel.anon();
        let u_name = kernel.name_str(anon, "u");
        let u = kernel.level_param(u_name);
        let u_plus_1 = kernel.level_succ(u);
        let sort_u = kernel.sort(u);
        let sort_u_plus_1 = kernel.sort(u_plus_1);
        let a_name = kernel.name_str(anon, "A");
        let ty = kernel.pi(a_name, sort_u, sort_u_plus_1, BinderInfo::Default);
        let value = kernel.lam(a_name, sort_u, kernel.bvar(0), BinderInfo::Default);
        let name = kernel.name_str(anon, "bad_promote");
        let accept = kernel
            .add_declaration(Declaration::Definition {
                name,
                uparams: vec![u_name],
                ty,
                value,
                hint: ReducibilityHint::Regular(0),
            })
            .is_ok();
        out.push(CaseResult {
            subsystem: "universes",
            name: "universes::sort_promotion_negative",
            axeyum_accept: accept,
            lean_source: "set_option autoImplicit false\nuniverse u\n\
                def bad_promote (A : Sort u) : Sort (u+1) := A\n"
                .to_string(),
        });
    }

    out
}

// ---------------------------------------------------------------------------
// Subsystem: inductives (family formation, positivity)
// ---------------------------------------------------------------------------

fn inductives_cases() -> Vec<CaseResult> {
    let mut out = Vec::new();

    // P1: a plain two-constructor enum.
    {
        let mut kernel = Kernel::new();
        let anon = kernel.anon();
        let two = kernel.name_str(anon, "TwoVals");
        let two_c = kernel.const_(two, vec![]);
        let one_lvl = kernel.level_succ(kernel.level_zero());
        let ty = kernel.sort(one_lvl);
        let ff = kernel.name_str(two, "ff");
        let tt = kernel.name_str(two, "tt");
        let accept = kernel
            .add_inductive(two, &[], 0, ty, &[(ff, two_c), (tt, two_c)])
            .is_ok();
        out.push(CaseResult {
            subsystem: "inductives",
            name: "inductives::two_constructor_enum_positive",
            axeyum_accept: accept,
            lean_source: "set_option autoImplicit false\n\
                inductive TwoVals where\n  | ff\n  | tt\n"
                .to_string(),
        });
    }

    // P2: a parametric one-field container.
    {
        let mut kernel = Kernel::new();
        let anon = kernel.anon();
        let one_lvl = kernel.level_succ(kernel.level_zero());
        let box_name = kernel.name_str(anon, "Box");
        let a_name = kernel.name_str(anon, "A");
        let sort_1 = kernel.sort(one_lvl);
        // ty : (A : Type) -> Type
        let ty = kernel.pi(a_name, sort_1, sort_1, BinderInfo::Default);
        let box_a = {
            // Box A, where A is bvar(0) inside the ctor's own telescope.
            let box_c = kernel.const_(box_name, vec![]);
            let a_ref = kernel.bvar(0);
            kernel.app(box_c, a_ref)
        };
        // mk : (A : Type) -> A -> Box A
        let mk_ty = {
            let a_ref = kernel.bvar(0);
            let inner = kernel.pi(anon, a_ref, box_a, BinderInfo::Default);
            kernel.pi(a_name, sort_1, inner, BinderInfo::Default)
        };
        let mk = kernel.name_str(box_name, "mk");
        let accept = kernel
            .add_inductive(box_name, &[], 1, ty, &[(mk, mk_ty)])
            .is_ok();
        out.push(CaseResult {
            subsystem: "inductives",
            name: "inductives::parametric_container_positive",
            axeyum_accept: accept,
            lean_source: "set_option autoImplicit false\n\
                inductive Box (A : Type) where\n  | mk : A -> Box A\n"
                .to_string(),
        });
    }

    // N1: non-positive occurrence (`Bad` occurs in a function domain).
    {
        let mut kernel = Kernel::new();
        let anon = kernel.anon();
        let one_lvl = kernel.level_succ(kernel.level_zero());
        let bad = kernel.name_str(anon, "Bad");
        let bad_c = kernel.const_(bad, vec![]);
        let ty = kernel.sort(one_lvl);
        let (_, nat_c) = {
            // Reuse a minimal Nat purely as the codomain; positivity does not
            // care what it is, only that Bad occurs in a function argument.
            let (_, _, _, nat_const, _, _) = declare_minimal_nat(&mut kernel);
            ((), nat_const)
        };
        let field_ty = arrow(&mut kernel, bad_c, nat_c);
        let mk_ty = arrow(&mut kernel, field_ty, bad_c);
        let mk = kernel.name_str(bad, "mk");
        let accept = kernel.add_inductive(bad, &[], 0, ty, &[(mk, mk_ty)]).is_ok();
        out.push(CaseResult {
            subsystem: "inductives",
            name: "inductives::non_positive_occurrence_negative",
            axeyum_accept: accept,
            lean_source: "set_option autoImplicit false\n\
                inductive Bad where\n  | mk : (Bad -> Nat) -> Bad\n"
                .to_string(),
        });
    }

    // N2: constructor result mismatch (`mk` claims to build a different
    // family than the one being declared).
    {
        let mut kernel = Kernel::new();
        let anon = kernel.anon();
        let one_lvl = kernel.level_succ(kernel.level_zero());
        let two = kernel.name_str(anon, "TwoVals");
        let two_c = kernel.const_(two, vec![]);
        let sort_1 = kernel.sort(one_lvl);
        let ff = kernel.name_str(two, "ff");
        let tt = kernel.name_str(two, "tt");
        kernel
            .add_inductive(two, &[], 0, sort_1, &[(ff, two_c), (tt, two_c)])
            .expect("TwoVals must admit");
        let (_, _, _, nat_c, _, _) = declare_minimal_nat(&mut kernel);
        let bad2 = kernel.name_str(anon, "Bad2");
        let mk_ty = arrow(&mut kernel, nat_c, two_c);
        let mk = kernel.name_str(bad2, "mk");
        let accept = kernel
            .add_inductive(bad2, &[], 0, sort_1, &[(mk, mk_ty)])
            .is_ok();
        out.push(CaseResult {
            subsystem: "inductives",
            name: "inductives::constructor_result_mismatch_negative",
            axeyum_accept: accept,
            lean_source: "set_option autoImplicit false\n\
                inductive TwoVals where\n  | ff\n  | tt\n\
                inductive Bad2 where\n  | mk : Nat -> TwoVals\n"
                .to_string(),
        });
    }

    out
}

// ---------------------------------------------------------------------------
// Subsystem: recursors (iota reduction, motive/argument shape)
// ---------------------------------------------------------------------------

fn recursors_cases() -> Vec<CaseResult> {
    let mut out = Vec::new();

    /// Builds a fresh minimal Nat plus its generated recursor applied to a
    /// `pred`-shaped motive/zero-case/succ-case, missing only the final `n`
    /// argument. Returns `(kernel, nat_const, zero_const, succ_const,
    /// pred_partial)`.
    fn setup() -> (Kernel, ExprId, ExprId, ExprId, ExprId) {
        let mut kernel = Kernel::new();
        let (nat, zero, succ, nat_c, zero_c, succ_c) = declare_minimal_nat(&mut kernel);
        let one_lvl = kernel.level_succ(kernel.level_zero());
        let rec_name = kernel.name_str(nat, "rec");
        let anon = kernel.anon();
        let motive = kernel.lam(anon, nat_c, nat_c, BinderInfo::Default);
        let succ_case = {
            let inner = kernel.bvar(1); // k, from inside two extra binders
            let inner_lam = kernel.lam(anon, nat_c, inner, BinderInfo::Default);
            kernel.lam(anon, nat_c, inner_lam, BinderInfo::Default)
        };
        let rec_c = kernel.const_(rec_name, vec![one_lvl]);
        let pred_partial = apps(&mut kernel, rec_c, &[motive, zero_c, succ_case]);
        let _ = succ; // silence unused (used only through succ_c)
        (kernel, nat_c, zero_c, succ_c, pred_partial)
    }

    // P1: succ-case iota (`pred (succ (succ zero)) = succ zero`).
    {
        let (mut kernel, nat_c, zero_c, succ_c, pred_partial) = setup();
        let logic = build_logic_prelude(&mut kernel).expect("logic prelude");
        let one_lvl = kernel.level_succ(kernel.level_zero());
        let two_v = apps(&mut kernel, succ_c, &[apps(&mut kernel, succ_c, &[zero_c])]);
        let pred_two = kernel.app(pred_partial, two_v);
        let one_v = kernel.app(succ_c, zero_c);
        let goal = eq_ty(&mut kernel, &logic, one_lvl, nat_c, pred_two, one_v);
        let proof = eq_refl(&mut kernel, &logic, one_lvl, nat_c, one_v);
        let anon = kernel.anon();
        let thm = kernel.name_str(anon, "case");
        let accept = kernel
            .add_declaration(Declaration::Theorem {
                name: thm,
                uparams: Vec::new(),
                ty: goal,
                value: proof,
            })
            .is_ok();
        out.push(CaseResult {
            subsystem: "recursors",
            name: "recursors::succ_case_iota_positive",
            axeyum_accept: accept,
            lean_source: "set_option autoImplicit false\n\
                def pred (n : Nat) : Nat :=\n  \
                @Nat.rec (fun _ => Nat) Nat.zero (fun k _ => k) n\n\
                example : pred (Nat.succ (Nat.succ Nat.zero)) = Nat.succ Nat.zero := rfl\n"
                .to_string(),
        });
    }

    // P2: zero-case iota (`pred zero = zero`).
    {
        let (mut kernel, nat_c, zero_c, _succ_c, pred_partial) = setup();
        let logic = build_logic_prelude(&mut kernel).expect("logic prelude");
        let one_lvl = kernel.level_succ(kernel.level_zero());
        let pred_zero = kernel.app(pred_partial, zero_c);
        let goal = eq_ty(&mut kernel, &logic, one_lvl, nat_c, pred_zero, zero_c);
        let proof = eq_refl(&mut kernel, &logic, one_lvl, nat_c, zero_c);
        let anon = kernel.anon();
        let thm = kernel.name_str(anon, "case");
        let accept = kernel
            .add_declaration(Declaration::Theorem {
                name: thm,
                uparams: Vec::new(),
                ty: goal,
                value: proof,
            })
            .is_ok();
        out.push(CaseResult {
            subsystem: "recursors",
            name: "recursors::zero_case_iota_positive",
            axeyum_accept: accept,
            lean_source: "set_option autoImplicit false\n\
                def pred (n : Nat) : Nat :=\n  \
                @Nat.rec (fun _ => Nat) Nat.zero (fun k _ => k) n\n\
                example : pred Nat.zero = Nat.zero := rfl\n"
                .to_string(),
        });
    }

    // N1: swapped minor premises (zero-case slot given a function, succ-case
    // slot given a bare value) -- a structural shape error at the
    // application itself, checked via bare `infer`.
    {
        let mut kernel = Kernel::new();
        let (nat, _zero, _succ, nat_c, zero_c, succ_c) = declare_minimal_nat(&mut kernel);
        let one_lvl = kernel.level_succ(kernel.level_zero());
        let rec_name = kernel.name_str(nat, "rec");
        let anon = kernel.anon();
        let motive = kernel.lam(anon, nat_c, nat_c, BinderInfo::Default);
        let succ_case = {
            let inner = kernel.bvar(1);
            let inner_lam = kernel.lam(anon, nat_c, inner, BinderInfo::Default);
            kernel.lam(anon, nat_c, inner_lam, BinderInfo::Default)
        };
        let rec_c = kernel.const_(rec_name, vec![one_lvl]);
        // Zero-case slot given `succ_case` (a function), succ-case slot
        // given `zero_c` (a bare value): both wrong, deliberately swapped.
        let bad = apps(&mut kernel, rec_c, &[motive, succ_case, zero_c]);
        let applied = kernel.app(bad, succ_c);
        let accept = kernel.infer(applied).is_ok();
        out.push(CaseResult {
            subsystem: "recursors",
            name: "recursors::swapped_minors_negative",
            axeyum_accept: accept,
            lean_source: "set_option autoImplicit false\n\
                def pred (n : Nat) : Nat :=\n  \
                @Nat.rec (fun _ => Nat) (fun k _ => k) Nat.zero n\n"
                .to_string(),
        });
    }

    // N2: recursor computes correctly, but the claimed equality is wrong
    // (`pred (succ zero) = succ zero`, actually `zero`).
    {
        let (mut kernel, nat_c, zero_c, succ_c, pred_partial) = setup();
        let logic = build_logic_prelude(&mut kernel).expect("logic prelude");
        let one_lvl = kernel.level_succ(kernel.level_zero());
        let one_v = kernel.app(succ_c, zero_c);
        let pred_one = kernel.app(pred_partial, one_v);
        let goal = eq_ty(&mut kernel, &logic, one_lvl, nat_c, pred_one, one_v);
        let proof = eq_refl(&mut kernel, &logic, one_lvl, nat_c, zero_c);
        let anon = kernel.anon();
        let thm = kernel.name_str(anon, "case");
        let accept = kernel
            .add_declaration(Declaration::Theorem {
                name: thm,
                uparams: Vec::new(),
                ty: goal,
                value: proof,
            })
            .is_ok();
        out.push(CaseResult {
            subsystem: "recursors",
            name: "recursors::wrong_computed_value_negative",
            axeyum_accept: accept,
            lean_source: "set_option autoImplicit false\n\
                def pred (n : Nat) : Nat :=\n  \
                @Nat.rec (fun _ => Nat) Nat.zero (fun k _ => k) n\n\
                example : pred (Nat.succ Nat.zero) = Nat.succ Nat.zero := rfl\n"
                .to_string(),
        });
    }

    out
}

// ---------------------------------------------------------------------------
// Subsystem: projections (structure field access, index bounds)
// ---------------------------------------------------------------------------

fn projections_cases() -> Vec<CaseResult> {
    let mut out = Vec::new();

    fn setup() -> (Kernel, NameId, ExprId, ExprId, ExprId, ExprId) {
        let mut kernel = Kernel::new();
        let anon = kernel.anon();
        let one_lvl = kernel.level_succ(kernel.level_zero());
        let (_, a_ty) = declare_axiom_type(&mut kernel, "A", one_lvl);
        let (_, a_val) = declare_axiom(&mut kernel, "a", a_ty);
        let (_, b_val) = declare_axiom(&mut kernel, "b", a_ty);
        let pair = kernel.name_str(anon, "Pair");
        let pair_c = kernel.const_(pair, vec![]);
        let sort_1 = kernel.sort(one_lvl);
        let mk_ty = {
            let inner = arrow(&mut kernel, a_ty, pair_c);
            arrow(&mut kernel, a_ty, inner)
        };
        let mk = kernel.name_str(pair, "mk");
        kernel
            .add_inductive(pair, &[], 0, sort_1, &[(mk, mk_ty)])
            .expect("Pair must admit");
        let mk_c = kernel.const_(mk, vec![]);
        let mk_val = apps(&mut kernel, mk_c, &[a_val, b_val]);
        (kernel, pair, a_ty, a_val, b_val, mk_val)
    }

    // P1: field 0 (`.fst`) reduces to `a`.
    {
        let (mut kernel, pair, a_ty, a_val, _b_val, mk_val) = setup();
        let logic = build_logic_prelude(&mut kernel).expect("logic prelude");
        let one_lvl = kernel.level_succ(kernel.level_zero());
        let proj0 = kernel.proj(pair, 0, mk_val);
        let goal = eq_ty(&mut kernel, &logic, one_lvl, a_ty, proj0, a_val);
        let proof = eq_refl(&mut kernel, &logic, one_lvl, a_ty, a_val);
        let anon = kernel.anon();
        let thm = kernel.name_str(anon, "case");
        let accept = kernel
            .add_declaration(Declaration::Theorem {
                name: thm,
                uparams: Vec::new(),
                ty: goal,
                value: proof,
            })
            .is_ok();
        out.push(CaseResult {
            subsystem: "projections",
            name: "projections::field_zero_positive",
            axeyum_accept: accept,
            lean_source: "set_option autoImplicit false\n\
                structure Pair where\n  fst : Nat\n  snd : Nat\n\
                axiom a : Nat\naxiom b : Nat\n\
                example : (Pair.mk a b).fst = a := rfl\n"
                .to_string(),
        });
    }

    // P2: field 1 (`.snd`) reduces to `b`.
    {
        let (mut kernel, pair, a_ty, _a_val, b_val, mk_val) = setup();
        let logic = build_logic_prelude(&mut kernel).expect("logic prelude");
        let one_lvl = kernel.level_succ(kernel.level_zero());
        let proj1 = kernel.proj(pair, 1, mk_val);
        let goal = eq_ty(&mut kernel, &logic, one_lvl, a_ty, proj1, b_val);
        let proof = eq_refl(&mut kernel, &logic, one_lvl, a_ty, b_val);
        let anon = kernel.anon();
        let thm = kernel.name_str(anon, "case");
        let accept = kernel
            .add_declaration(Declaration::Theorem {
                name: thm,
                uparams: Vec::new(),
                ty: goal,
                value: proof,
            })
            .is_ok();
        out.push(CaseResult {
            subsystem: "projections",
            name: "projections::field_one_positive",
            axeyum_accept: accept,
            lean_source: "set_option autoImplicit false\n\
                structure Pair where\n  fst : Nat\n  snd : Nat\n\
                axiom a : Nat\naxiom b : Nat\n\
                example : (Pair.mk a b).snd = b := rfl\n"
                .to_string(),
        });
    }

    // N1: wrong field claimed (`.fst` claimed equal to `b`, actually `a`).
    {
        let (mut kernel, pair, a_ty, _a_val, b_val, mk_val) = setup();
        let logic = build_logic_prelude(&mut kernel).expect("logic prelude");
        let one_lvl = kernel.level_succ(kernel.level_zero());
        let proj0 = kernel.proj(pair, 0, mk_val);
        let goal = eq_ty(&mut kernel, &logic, one_lvl, a_ty, proj0, b_val);
        let proof = eq_refl(&mut kernel, &logic, one_lvl, a_ty, b_val);
        let anon = kernel.anon();
        let thm = kernel.name_str(anon, "case");
        let accept = kernel
            .add_declaration(Declaration::Theorem {
                name: thm,
                uparams: Vec::new(),
                ty: goal,
                value: proof,
            })
            .is_ok();
        out.push(CaseResult {
            subsystem: "projections",
            name: "projections::wrong_field_negative",
            axeyum_accept: accept,
            lean_source: "set_option autoImplicit false\n\
                structure Pair where\n  fst : Nat\n  snd : Nat\n\
                axiom a : Nat\naxiom b : Nat\n\
                example : (Pair.mk a b).fst = b := rfl\n"
                .to_string(),
        });
    }

    // N2: out-of-range field index (only 2 fields, index 2 requested).
    {
        let (mut kernel, pair, _a_ty, _a_val, _b_val, mk_val) = setup();
        let proj2 = kernel.proj(pair, 2, mk_val);
        let accept = kernel.infer(proj2).is_ok();
        out.push(CaseResult {
            subsystem: "projections",
            name: "projections::out_of_range_index_negative",
            axeyum_accept: accept,
            lean_source: "set_option autoImplicit false\n\
                structure Pair where\n  fst : Nat\n  snd : Nat\n\
                axiom a : Nat\naxiom b : Nat\n\
                example : (Pair.mk a b).3 = a := rfl\n"
                .to_string(),
        });
    }

    out
}

// ---------------------------------------------------------------------------
// Subsystem: literals (Nat literal <-> constructor semantics)
// ---------------------------------------------------------------------------

fn literals_cases() -> Vec<CaseResult> {
    let mut out = Vec::new();

    // P1: `3 = succ (succ (succ zero))`.
    {
        let mut kernel = Kernel::new();
        let (_, _, _, nat_c, zero_c, succ_c) = declare_minimal_nat(&mut kernel);
        let logic = build_logic_prelude(&mut kernel).expect("logic prelude");
        let one_lvl = kernel.level_succ(kernel.level_zero());
        let three_lit = kernel.lit(Lit::nat(3u64));
        let unary_three = {
            let s1 = kernel.app(succ_c, zero_c);
            let s2 = kernel.app(succ_c, s1);
            kernel.app(succ_c, s2)
        };
        let goal = eq_ty(&mut kernel, &logic, one_lvl, nat_c, three_lit, unary_three);
        let proof = eq_refl(&mut kernel, &logic, one_lvl, nat_c, unary_three);
        let anon = kernel.anon();
        let thm = kernel.name_str(anon, "case");
        let accept = kernel
            .add_declaration(Declaration::Theorem {
                name: thm,
                uparams: Vec::new(),
                ty: goal,
                value: proof,
            })
            .is_ok();
        out.push(CaseResult {
            subsystem: "literals",
            name: "literals::three_equals_unary_positive",
            axeyum_accept: accept,
            lean_source: "set_option autoImplicit false\n\
                example : (3 : Nat) = Nat.succ (Nat.succ (Nat.succ Nat.zero)) := rfl\n"
                .to_string(),
        });
    }

    // P2: `0 = zero`.
    {
        let mut kernel = Kernel::new();
        let (_, _, _, nat_c, zero_c, _succ_c) = declare_minimal_nat(&mut kernel);
        let logic = build_logic_prelude(&mut kernel).expect("logic prelude");
        let one_lvl = kernel.level_succ(kernel.level_zero());
        let zero_lit = kernel.lit(Lit::nat(0u64));
        let goal = eq_ty(&mut kernel, &logic, one_lvl, nat_c, zero_lit, zero_c);
        let proof = eq_refl(&mut kernel, &logic, one_lvl, nat_c, zero_c);
        let anon = kernel.anon();
        let thm = kernel.name_str(anon, "case");
        let accept = kernel
            .add_declaration(Declaration::Theorem {
                name: thm,
                uparams: Vec::new(),
                ty: goal,
                value: proof,
            })
            .is_ok();
        out.push(CaseResult {
            subsystem: "literals",
            name: "literals::zero_equals_ctor_positive",
            axeyum_accept: accept,
            lean_source: "set_option autoImplicit false\n\
                example : (0 : Nat) = Nat.zero := rfl\n"
                .to_string(),
        });
    }

    // N1: `3 = succ (succ zero)` -- literal claimed equal to unary 2.
    {
        let mut kernel = Kernel::new();
        let (_, _, _, nat_c, zero_c, succ_c) = declare_minimal_nat(&mut kernel);
        let logic = build_logic_prelude(&mut kernel).expect("logic prelude");
        let one_lvl = kernel.level_succ(kernel.level_zero());
        let three_lit = kernel.lit(Lit::nat(3u64));
        let unary_two = {
            let s1 = kernel.app(succ_c, zero_c);
            kernel.app(succ_c, s1)
        };
        let goal = eq_ty(&mut kernel, &logic, one_lvl, nat_c, three_lit, unary_two);
        let proof = eq_refl(&mut kernel, &logic, one_lvl, nat_c, unary_two);
        let anon = kernel.anon();
        let thm = kernel.name_str(anon, "case");
        let accept = kernel
            .add_declaration(Declaration::Theorem {
                name: thm,
                uparams: Vec::new(),
                ty: goal,
                value: proof,
            })
            .is_ok();
        out.push(CaseResult {
            subsystem: "literals",
            name: "literals::three_equals_two_negative",
            axeyum_accept: accept,
            lean_source: "set_option autoImplicit false\n\
                example : (3 : Nat) = Nat.succ (Nat.succ Nat.zero) := rfl\n"
                .to_string(),
        });
    }

    // N2: literal placed at an unrelated declared type.
    {
        let mut kernel = Kernel::new();
        let (_, _, _, _nat_c, _zero_c, _succ_c) = declare_minimal_nat(&mut kernel);
        let one_lvl = kernel.level_succ(kernel.level_zero());
        let (_, not_nat) = declare_axiom_type(&mut kernel, "NotNat", one_lvl);
        let three_lit = kernel.lit(Lit::nat(3u64));
        let anon = kernel.anon();
        let bad = kernel.name_str(anon, "bad");
        let accept = kernel
            .add_declaration(Declaration::Definition {
                name: bad,
                uparams: Vec::new(),
                ty: not_nat,
                value: three_lit,
                hint: ReducibilityHint::Regular(0),
            })
            .is_ok();
        out.push(CaseResult {
            subsystem: "literals",
            name: "literals::wrong_carrier_negative",
            axeyum_accept: accept,
            lean_source: "set_option autoImplicit false\n\
                axiom NotNat : Type\ndef bad : NotNat := 3\n"
                .to_string(),
        });
    }

    out
}

// ---------------------------------------------------------------------------
// Subsystem: quotient (Quot/Quot.mk/Quot.lift/Quot.ind rules)
// ---------------------------------------------------------------------------

struct QuotPkg {
    quot: NameId,
    quot_mk: NameId,
    quot_lift: NameId,
    _quot_ind: NameId,
    u: NameId,
    v: NameId,
}

/// Builds and admits Lean's exact four-declaration quotient package
/// (`Quot`/`Quot.mk`/`Quot.lift`/`Quot.ind`), replicating
/// `quotient.rs`'s private `expected_quot_*_type`/`canonical_quotient_package`
/// recipe using only this crate's PUBLIC term-builder API (that recipe is
/// read from source, not called: those helpers are private to the crate and
/// unreachable from an external integration test).
fn build_quotient_package(kernel: &mut Kernel, logic: &LogicPrelude) -> QuotPkg {
    let anon = kernel.anon();
    let quot = kernel.name_str(anon, "Quot");
    let quot_mk = kernel.name_str(quot, "mk");
    let quot_lift = kernel.name_str(quot, "lift");
    let quot_ind = kernel.name_str(quot, "ind");
    let u_name = kernel.name_str(anon, "quot_u");
    let v_name = kernel.name_str(anon, "quot_v");
    let lu = kernel.level_param(u_name);
    let lv = kernel.level_param(v_name);
    let sort_u = kernel.sort(lu);
    let sort_v = kernel.sort(lv);
    let prop = kernel.sort_zero();

    let alpha_name = kernel.name_str(anon, "alpha");
    let r_name = kernel.name_str(anon, "r");
    let beta_name = kernel.name_str(anon, "beta");
    let f_name = kernel.name_str(anon, "f");
    let sanity_name = kernel.name_str(anon, "h");
    let q_name = kernel.name_str(anon, "q");
    let a_name = kernel.name_str(anon, "a");
    let b_name = kernel.name_str(anon, "b");

    // `Quot.{u} : {alpha : Sort u} -> (alpha -> alpha -> Prop) -> Sort u`.
    let quot_ty = {
        let alpha_fv = kernel.fresh_fvar();
        let r_fv = kernel.fresh_fvar();
        let alpha = kernel.fvar(alpha_fv);
        let relation = relation_type(kernel, alpha);
        close_pi(
            kernel,
            &[
                (alpha_name, alpha_fv, sort_u, BinderInfo::Implicit),
                (r_name, r_fv, relation, BinderInfo::Default),
            ],
            sort_u,
        )
    };
    kernel
        .add_declaration(Declaration::Quotient {
            name: quot,
            uparams: vec![u_name],
            ty: quot_ty,
            kind: axeyum_lean_kernel::QuotKind::Type,
        })
        .unwrap_or_else(|e| panic!("Quot must admit: {e:?}"));

    // `Quot.mk.{u} : {alpha} -> (r : alpha -> alpha -> Prop) -> (a : alpha) -> Quot.{u} alpha r`.
    let quot_mk_ty = {
        let alpha_fv = kernel.fresh_fvar();
        let r_fv = kernel.fresh_fvar();
        let a_fv = kernel.fresh_fvar();
        let alpha = kernel.fvar(alpha_fv);
        let r = kernel.fvar(r_fv);
        let relation = relation_type(kernel, alpha);
        let quot_c = kernel.const_(quot, vec![lu]);
        let result = apps(kernel, quot_c, &[alpha, r]);
        close_pi(
            kernel,
            &[
                (alpha_name, alpha_fv, sort_u, BinderInfo::Implicit),
                (r_name, r_fv, relation, BinderInfo::Default),
                (a_name, a_fv, alpha, BinderInfo::Default),
            ],
            result,
        )
    };
    kernel
        .add_declaration(Declaration::Quotient {
            name: quot_mk,
            uparams: vec![u_name],
            ty: quot_mk_ty,
            kind: axeyum_lean_kernel::QuotKind::Ctor,
        })
        .unwrap_or_else(|e| panic!("Quot.mk must admit: {e:?}"));

    // `Quot.lift.{u,v} : {alpha} -> {r} -> {beta : Sort v} -> (f : alpha -> beta)
    //   -> (h : forall a b, r a b -> Eq beta (f a) (f b)) -> Quot.{u} alpha r -> beta`.
    let quot_lift_ty = {
        let alpha_fv = kernel.fresh_fvar();
        let r_fv = kernel.fresh_fvar();
        let beta_fv = kernel.fresh_fvar();
        let f_fv = kernel.fresh_fvar();
        let sanity_fv = kernel.fresh_fvar();
        let q_fv = kernel.fresh_fvar();
        let a_fv = kernel.fresh_fvar();
        let b_fv = kernel.fresh_fvar();
        let alpha = kernel.fvar(alpha_fv);
        let r = kernel.fvar(r_fv);
        let beta = kernel.fvar(beta_fv);
        let f = kernel.fvar(f_fv);
        let a = kernel.fvar(a_fv);
        let b = kernel.fvar(b_fv);
        let r_ab = apps(kernel, r, &[a, b]);
        let f_a = kernel.app(f, a);
        let f_b = kernel.app(f, b);
        let equality = eq_ty(kernel, logic, lv, beta, f_a, f_b);
        let proof_ty = arrow(kernel, r_ab, equality);
        let sanity_ty = close_pi(
            kernel,
            &[
                (a_name, a_fv, alpha, BinderInfo::Default),
                (b_name, b_fv, alpha, BinderInfo::Default),
            ],
            proof_ty,
        );
        let function_ty = arrow(kernel, alpha, beta);
        let relation = relation_type(kernel, alpha);
        let quot_c = kernel.const_(quot, vec![lu]);
        let quot_alpha_r = apps(kernel, quot_c, &[alpha, r]);
        close_pi(
            kernel,
            &[
                (alpha_name, alpha_fv, sort_u, BinderInfo::Implicit),
                (r_name, r_fv, relation, BinderInfo::Implicit),
                (beta_name, beta_fv, sort_v, BinderInfo::Implicit),
                (f_name, f_fv, function_ty, BinderInfo::Default),
                (sanity_name, sanity_fv, sanity_ty, BinderInfo::Default),
                (q_name, q_fv, quot_alpha_r, BinderInfo::Default),
            ],
            beta,
        )
    };
    kernel
        .add_declaration(Declaration::Quotient {
            name: quot_lift,
            uparams: vec![u_name, v_name],
            ty: quot_lift_ty,
            kind: axeyum_lean_kernel::QuotKind::Lift,
        })
        .unwrap_or_else(|e| panic!("Quot.lift must admit: {e:?}"));

    // `Quot.ind.{u} : {alpha} -> {r} -> {beta : Quot alpha r -> Prop}
    //   -> (forall a, beta (Quot.mk r a)) -> forall q, beta q`.
    let quot_ind_ty = {
        let alpha_fv = kernel.fresh_fvar();
        let r_fv = kernel.fresh_fvar();
        let beta_fv = kernel.fresh_fvar();
        let minor_fv = kernel.fresh_fvar();
        let q_fv = kernel.fresh_fvar();
        let a_fv = kernel.fresh_fvar();
        let alpha = kernel.fvar(alpha_fv);
        let r = kernel.fvar(r_fv);
        let beta = kernel.fvar(beta_fv);
        let q = kernel.fvar(q_fv);
        let a = kernel.fvar(a_fv);
        let quot_c = kernel.const_(quot, vec![lu]);
        let quot_alpha_r = apps(kernel, quot_c, &[alpha, r]);
        let mk_c = kernel.const_(quot_mk, vec![lu]);
        let mk_a = apps(kernel, mk_c, &[alpha, r, a]);
        let beta_mk_a = kernel.app(beta, mk_a);
        let minor_ty = close_pi(
            kernel,
            &[(a_name, a_fv, alpha, BinderInfo::Default)],
            beta_mk_a,
        );
        let predicate = arrow(kernel, quot_alpha_r, prop);
        let result = kernel.app(beta, q);
        let relation = relation_type(kernel, alpha);
        close_pi(
            kernel,
            &[
                (alpha_name, alpha_fv, sort_u, BinderInfo::Implicit),
                (r_name, r_fv, relation, BinderInfo::Implicit),
                (beta_name, beta_fv, predicate, BinderInfo::Implicit),
                (sanity_name, minor_fv, minor_ty, BinderInfo::Default),
                (q_name, q_fv, quot_alpha_r, BinderInfo::Default),
            ],
            result,
        )
    };
    kernel
        .add_declaration(Declaration::Quotient {
            name: quot_ind,
            uparams: vec![u_name],
            ty: quot_ind_ty,
            kind: axeyum_lean_kernel::QuotKind::Ind,
        })
        .unwrap_or_else(|e| panic!("Quot.ind must admit: {e:?}"));

    QuotPkg {
        quot,
        quot_mk,
        quot_lift,
        _quot_ind: quot_ind,
        u: u_name,
        v: v_name,
    }
}

fn quotient_cases() -> Vec<CaseResult> {
    let mut out = Vec::new();

    // P1: Quot.lift computation rule, constant function.
    {
        let mut kernel = Kernel::new();
        let logic = build_logic_prelude(&mut kernel).expect("logic prelude");
        let one_lvl = kernel.level_succ(kernel.level_zero());
        let pkg = build_quotient_package(&mut kernel, &logic);
        let lu = kernel.level_param(pkg.u);
        let lv = kernel.level_param(pkg.v);
        let (_, carrier) = declare_axiom_type(&mut kernel, "Carrier", one_lvl);
        let (_, a0) = declare_axiom(&mut kernel, "a0", carrier);
        let anon = kernel.anon();
        let r_name = kernel.name_str(anon, "r");
        let r_ty = relation_type(&mut kernel, carrier);
        let (_, r) = declare_axiom(&mut kernel, "r", r_ty);
        let _ = r_name;
        // beta := Bool (a tiny concrete inductive), f := constant `true`.
        let bool_name = kernel.name_str(anon, "Bool");
        let bool_c = kernel.const_(bool_name, vec![]);
        let btrue = kernel.name_str(bool_name, "true");
        let bfalse = kernel.name_str(bool_name, "false");
        let bool_sort = kernel.sort_zero();
        kernel
            .add_inductive(
                bool_name,
                &[],
                0,
                bool_sort,
                &[(bfalse, bool_c), (btrue, bool_c)],
            )
            .expect("Bool must admit");
        let btrue_c = kernel.const_(btrue, vec![]);
        let f_name = kernel.name_str(anon, "fconst");
        let f_ty = arrow(&mut kernel, carrier, bool_c);
        let f_val = kernel.lam(anon, carrier, btrue_c, BinderInfo::Default);
        kernel
            .add_declaration(Declaration::Definition {
                name: f_name,
                uparams: Vec::new(),
                ty: f_ty,
                value: f_val,
                hint: ReducibilityHint::Regular(0),
            })
            .expect("fconst must admit");
        let f_c = kernel.const_(f_name, vec![]);
        // h : forall a b, r a b -> Eq Bool (f a) (f b), proved by refl since f is constant.
        let h_ty = {
            let a_fv = kernel.fresh_fvar();
            let b_fv = kernel.fresh_fvar();
            let a_name = kernel.name_str(anon, "a");
            let b_name = kernel.name_str(anon, "b");
            let a = kernel.fvar(a_fv);
            let b = kernel.fvar(b_fv);
            let r_ab = apps(&mut kernel, r, &[a, b]);
            let f_a = kernel.app(f_c, a);
            let f_b = kernel.app(f_c, b);
            let eq_ab = eq_ty(&mut kernel, &logic, kernel.level_zero(), bool_c, f_a, f_b);
            let arrow_ty = arrow(&mut kernel, r_ab, eq_ab);
            close_pi(
                &mut kernel,
                &[
                    (a_name, a_fv, carrier, BinderInfo::Default),
                    (b_name, b_fv, carrier, BinderInfo::Default),
                ],
                arrow_ty,
            )
        };
        let h_val = {
            let a_fv = kernel.fresh_fvar();
            let b_fv = kernel.fresh_fvar();
            let hyp_fv = kernel.fresh_fvar();
            let a_name = kernel.name_str(anon, "a");
            let b_name = kernel.name_str(anon, "b");
            let hyp_name = kernel.name_str(anon, "hyp");
            let f_c2 = kernel.const_(f_name, vec![]);
            let f_a = kernel.app(f_c2, kernel.fvar(a_fv));
            let refl_body = eq_refl(&mut kernel, &logic, kernel.level_zero(), bool_c, f_a);
            let r_ab_ty = {
                let a = kernel.fvar(a_fv);
                let b = kernel.fvar(b_fv);
                apps(&mut kernel, r, &[a, b])
            };
            close_pi(
                &mut kernel,
                &[
                    (a_name, a_fv, carrier, BinderInfo::Default),
                    (b_name, b_fv, carrier, BinderInfo::Default),
                    (hyp_name, hyp_fv, r_ab_ty, BinderInfo::Default),
                ],
                refl_body,
            )
        };
        let h_name = kernel.name_str(anon, "hresp");
        kernel
            .add_declaration(Declaration::Theorem {
                name: h_name,
                uparams: Vec::new(),
                ty: h_ty,
                value: h_val,
            })
            .expect("hresp must admit");
        let h_c = kernel.const_(h_name, vec![]);
        let lift_c = kernel.const_(pkg.quot_lift, vec![lu, lv]);
        let mk_c = kernel.const_(pkg.quot_mk, vec![lu]);
        let mk_a0 = apps(&mut kernel, mk_c, &[carrier, r, a0]);
        let lifted = apps(&mut kernel, lift_c, &[carrier, r, bool_c, f_c, h_c, mk_a0]);
        let f_a0 = kernel.app(f_c, a0);
        let goal = eq_ty(&mut kernel, &logic, kernel.level_zero(), bool_c, lifted, f_a0);
        let proof = eq_refl(&mut kernel, &logic, kernel.level_zero(), bool_c, f_a0);
        let thm = kernel.name_str(anon, "case");
        let accept = kernel
            .add_declaration(Declaration::Theorem {
                name: thm,
                uparams: Vec::new(),
                ty: goal,
                value: proof,
            })
            .is_ok();
        out.push(CaseResult {
            subsystem: "quotient",
            name: "quotient::lift_computation_positive",
            axeyum_accept: accept,
            lean_source: "set_option autoImplicit false\n\
                axiom Carrier : Type\naxiom r : Carrier -> Carrier -> Prop\naxiom a0 : Carrier\n\
                def fconst (_ : Carrier) : Bool := true\n\
                theorem hresp : forall (x y : Carrier), r x y -> fconst x = fconst y :=\n  \
                fun _ _ _ => rfl\n\
                example : Quot.lift fconst hresp (Quot.mk r a0) = fconst a0 := rfl\n"
                .to_string(),
        });
    }

    // P2: Quot.ind.
    {
        let mut kernel = Kernel::new();
        let logic = build_logic_prelude(&mut kernel).expect("logic prelude");
        let one_lvl = kernel.level_succ(kernel.level_zero());
        let pkg = build_quotient_package(&mut kernel, &logic);
        let lu = kernel.level_param(pkg.u);
        let (_, carrier) = declare_axiom_type(&mut kernel, "Carrier", one_lvl);
        let (_, a0) = declare_axiom(&mut kernel, "a0", carrier);
        let anon = kernel.anon();
        let r_ty = relation_type(&mut kernel, carrier);
        let (_, r) = declare_axiom(&mut kernel, "r", r_ty);
        let true_c = kernel.const_(logic.true_, vec![]);
        let true_intro_c = kernel.const_(logic.true_intro, vec![]);
        // beta := fun _ => True; minor := fun _ => True.intro.
        let beta_val = kernel.lam(anon, {
            let quot_c = kernel.const_(pkg.quot, vec![lu]);
            apps(&mut kernel, quot_c, &[carrier, r])
        }, true_c, BinderInfo::Default);
        let minor_val = kernel.lam(anon, carrier, true_intro_c, BinderInfo::Default);
        let ind_c = kernel.const_(pkg._quot_ind, vec![lu]);
        let all_trivial = apps(&mut kernel, ind_c, &[carrier, r, beta_val, minor_val]);
        let mk_c = kernel.const_(pkg.quot_mk, vec![lu]);
        let mk_a0 = apps(&mut kernel, mk_c, &[carrier, r, a0]);
        let applied = kernel.app(all_trivial, mk_a0);
        let thm = kernel.name_str(anon, "case");
        let accept = kernel
            .add_declaration(Declaration::Theorem {
                name: thm,
                uparams: Vec::new(),
                ty: true_c,
                value: applied,
            })
            .is_ok();
        out.push(CaseResult {
            subsystem: "quotient",
            name: "quotient::ind_positive",
            axeyum_accept: accept,
            lean_source: "set_option autoImplicit false\n\
                axiom Carrier : Type\naxiom r : Carrier -> Carrier -> Prop\naxiom a0 : Carrier\n\
                theorem allTrivial : forall q : Quot r, True :=\n  \
                Quot.ind (fun _ => True.intro)\n\
                example : True := allTrivial (Quot.mk r a0)\n"
                .to_string(),
        });
    }

    // N1: `Quot.sound` is absent by design (ADR-0456). EXPLAINED incompleteness.
    {
        let mut kernel = Kernel::new();
        let logic = build_logic_prelude(&mut kernel).expect("logic prelude");
        let one_lvl = kernel.level_succ(kernel.level_zero());
        let pkg = build_quotient_package(&mut kernel, &logic);
        let lu = kernel.level_param(pkg.u);
        let _ = lu;
        let (_, carrier) = declare_axiom_type(&mut kernel, "Carrier", one_lvl);
        let anon = kernel.anon();
        let quot_sound = kernel.name_str(pkg.quot, "sound");
        let _ = carrier;
        // Never declared: referencing it must fail to infer.
        let level_zero = kernel.level_zero();
        let sound_c = kernel.const_(quot_sound, vec![level_zero]);
        let accept = kernel.infer(sound_c).is_ok();
        let _ = anon;
        out.push(CaseResult {
            subsystem: "quotient",
            name: "quotient::quot_sound_absent",
            axeyum_accept: accept,
            lean_source: "set_option autoImplicit false\n\
                axiom Carrier : Type\naxiom r : Carrier -> Carrier -> Prop\n\
                axiom a1 : Carrier\naxiom a2 : Carrier\naxiom hr : r a1 a2\n\
                example : Quot.mk r a1 = Quot.mk r a2 := Quot.sound hr\n"
                .to_string(),
        });
    }

    // N2: Quot.lift misapplied with a wrong-typed sanity hypothesis.
    {
        let mut kernel = Kernel::new();
        let logic = build_logic_prelude(&mut kernel).expect("logic prelude");
        let one_lvl = kernel.level_succ(kernel.level_zero());
        let pkg = build_quotient_package(&mut kernel, &logic);
        let lu = kernel.level_param(pkg.u);
        let lv = kernel.level_param(pkg.v);
        let (_, carrier) = declare_axiom_type(&mut kernel, "Carrier", one_lvl);
        let (_, a0) = declare_axiom(&mut kernel, "a0", carrier);
        let anon = kernel.anon();
        let r_ty = relation_type(&mut kernel, carrier);
        let (_, r) = declare_axiom(&mut kernel, "r", r_ty);
        let bool_name = kernel.name_str(anon, "Bool");
        let bool_c = kernel.const_(bool_name, vec![]);
        let btrue = kernel.name_str(bool_name, "true");
        let bfalse = kernel.name_str(bool_name, "false");
        let bool_sort = kernel.sort_zero();
        kernel
            .add_inductive(
                bool_name,
                &[],
                0,
                bool_sort,
                &[(bfalse, bool_c), (btrue, bool_c)],
            )
            .expect("Bool must admit");
        let btrue_c = kernel.const_(btrue, vec![]);
        let f_name = kernel.name_str(anon, "fconst");
        let f_ty = arrow(&mut kernel, carrier, bool_c);
        let f_val = kernel.lam(anon, carrier, btrue_c, BinderInfo::Default);
        kernel
            .add_declaration(Declaration::Definition {
                name: f_name,
                uparams: Vec::new(),
                ty: f_ty,
                value: f_val,
                hint: ReducibilityHint::Regular(0),
            })
            .expect("fconst must admit");
        let f_c = kernel.const_(f_name, vec![]);
        // wrong_proof : True, used where `forall a b, r a b -> ...` is needed.
        let (_, wrong_proof) = declare_axiom(&mut kernel, "wrongProof", {
            kernel.const_(logic.true_, vec![])
        });
        let lift_c = kernel.const_(pkg.quot_lift, vec![lu, lv]);
        let mk_c = kernel.const_(pkg.quot_mk, vec![lu]);
        let mk_a0 = apps(&mut kernel, mk_c, &[carrier, r, a0]);
        let bad = apps(
            &mut kernel,
            lift_c,
            &[carrier, r, bool_c, f_c, wrong_proof, mk_a0],
        );
        let accept = kernel.infer(bad).is_ok();
        out.push(CaseResult {
            subsystem: "quotient",
            name: "quotient::lift_wrong_hypothesis_negative",
            axeyum_accept: accept,
            lean_source: "set_option autoImplicit false\n\
                axiom Carrier : Type\naxiom r : Carrier -> Carrier -> Prop\naxiom a0 : Carrier\n\
                def fconst (_ : Carrier) : Bool := true\n\
                axiom wrongProof : True\n\
                example : Bool := Quot.lift fconst wrongProof (Quot.mk r a0)\n"
                .to_string(),
        });
    }

    out
}

// ---------------------------------------------------------------------------
// Subsystem: proof irrelevance
// ---------------------------------------------------------------------------

fn proof_irrelevance_cases() -> Vec<CaseResult> {
    let mut out = Vec::new();

    // P1: two distinct axiom proofs of the same Prop are defeq.
    {
        let mut kernel = Kernel::new();
        let logic = build_logic_prelude(&mut kernel).expect("logic prelude");
        let zero_lvl = kernel.level_zero();
        let (_, p_ty) = declare_axiom_type(&mut kernel, "P", zero_lvl);
        let (_, p1) = declare_axiom(&mut kernel, "p1", p_ty);
        let (_, p2) = declare_axiom(&mut kernel, "p2", p_ty);
        let goal = eq_ty(&mut kernel, &logic, zero_lvl, p_ty, p1, p2);
        let proof = eq_refl(&mut kernel, &logic, zero_lvl, p_ty, p1);
        let anon = kernel.anon();
        let thm = kernel.name_str(anon, "case");
        let accept = kernel
            .add_declaration(Declaration::Theorem {
                name: thm,
                uparams: Vec::new(),
                ty: goal,
                value: proof,
            })
            .is_ok();
        out.push(CaseResult {
            subsystem: "proof_irrelevance",
            name: "proof_irrelevance::two_proofs_defeq_positive",
            axeyum_accept: accept,
            lean_source: "set_option autoImplicit false\n\
                axiom P : Prop\naxiom p1 : P\naxiom p2 : P\nexample : p1 = p2 := rfl\n"
                .to_string(),
        });
    }

    // P2: proof irrelevance propagates through a dependent (Type-valued)
    // family: `C p1` and `C p2` are defeq because `p1`/`p2` are.
    {
        let mut kernel = Kernel::new();
        let zero_lvl = kernel.level_zero();
        let one_lvl = kernel.level_succ(zero_lvl);
        let (_, p_ty) = declare_axiom_type(&mut kernel, "P", zero_lvl);
        let (_, p1) = declare_axiom(&mut kernel, "p1", p_ty);
        let (_, p2) = declare_axiom(&mut kernel, "p2", p_ty);
        let c_ty = arrow(&mut kernel, p_ty, kernel.sort(one_lvl));
        let (c_name, c_c) = declare_axiom(&mut kernel, "C", c_ty);
        let _ = c_name;
        let c_p1 = kernel.app(c_c, p1);
        let (_, c1) = declare_axiom(&mut kernel, "c1", c_p1);
        let c_p2 = kernel.app(c_c, p2);
        let anon = kernel.anon();
        let dummy = kernel.name_str(anon, "dummy");
        let accept = kernel
            .add_declaration(Declaration::Definition {
                name: dummy,
                uparams: Vec::new(),
                ty: c_p2,
                value: c1,
                hint: ReducibilityHint::Regular(0),
            })
            .is_ok();
        out.push(CaseResult {
            subsystem: "proof_irrelevance",
            name: "proof_irrelevance::congruence_through_dependent_family_positive",
            axeyum_accept: accept,
            lean_source: "set_option autoImplicit false\n\
                axiom P : Prop\naxiom p1 : P\naxiom p2 : P\naxiom C : P -> Type\n\
                axiom c1 : C p1\nnoncomputable def dummy : C p2 := c1\n"
                .to_string(),
        });
    }

    // N1 (critical): `Type` is NOT proof-irrelevant. Two distinct axioms of
    // a `Type`-sorted carrier must NOT be defeq.
    {
        let mut kernel = Kernel::new();
        let logic = build_logic_prelude(&mut kernel).expect("logic prelude");
        let one_lvl = kernel.level_succ(kernel.level_zero());
        let (_, a_ty) = declare_axiom_type(&mut kernel, "A", one_lvl);
        let (_, a1) = declare_axiom(&mut kernel, "a1", a_ty);
        let (_, a2) = declare_axiom(&mut kernel, "a2", a_ty);
        let goal = eq_ty(&mut kernel, &logic, one_lvl, a_ty, a1, a2);
        let proof = eq_refl(&mut kernel, &logic, one_lvl, a_ty, a1);
        let anon = kernel.anon();
        let thm = kernel.name_str(anon, "case");
        let accept = kernel
            .add_declaration(Declaration::Theorem {
                name: thm,
                uparams: Vec::new(),
                ty: goal,
                value: proof,
            })
            .is_ok();
        out.push(CaseResult {
            subsystem: "proof_irrelevance",
            name: "proof_irrelevance::type_is_not_irrelevant_negative",
            axeyum_accept: accept,
            lean_source: "set_option autoImplicit false\n\
                axiom A : Type\naxiom a1 : A\naxiom a2 : A\nexample : a1 = a2 := rfl\n"
                .to_string(),
        });
    }

    // N2: two unrelated, non-defeq Props are not interchangeable.
    {
        let mut kernel = Kernel::new();
        let zero_lvl = kernel.level_zero();
        let (_, p_ty) = declare_axiom_type(&mut kernel, "P", zero_lvl);
        let (_, q_ty) = declare_axiom_type(&mut kernel, "Q", zero_lvl);
        let (_, p) = declare_axiom(&mut kernel, "p", p_ty);
        let anon = kernel.anon();
        let thm = kernel.name_str(anon, "case");
        let accept = kernel
            .add_declaration(Declaration::Theorem {
                name: thm,
                uparams: Vec::new(),
                ty: q_ty,
                value: p,
            })
            .is_ok();
        out.push(CaseResult {
            subsystem: "proof_irrelevance",
            name: "proof_irrelevance::unrelated_props_negative",
            axeyum_accept: accept,
            lean_source: "set_option autoImplicit false\n\
                axiom P : Prop\naxiom Q : Prop\naxiom p : P\nexample : Q := p\n"
                .to_string(),
        });
    }

    out
}

// ---------------------------------------------------------------------------
// The corpus and the test
// ---------------------------------------------------------------------------

fn full_corpus() -> Vec<CaseResult> {
    let mut cases = Vec::new();
    cases.extend(conversion_cases());
    cases.extend(universes_cases());
    cases.extend(inductives_cases());
    cases.extend(recursors_cases());
    cases.extend(projections_cases());
    cases.extend(literals_cases());
    cases.extend(quotient_cases());
    cases.extend(proof_irrelevance_cases());
    cases
}

/// ADR-0717 S5: the kernel differential corpus.
///
/// # What this does NOT cover (required honesty statement)
///
/// This corpus is deliberately small (four cases per subsystem, thirty-two
/// total) and hand-authored rather than randomly fuzzed: it demonstrates the
/// differential harness end to end and exercises one concrete "one step from
/// valid" mutation per subsystem, not an exhaustive enumeration of that
/// subsystem's defect space. It does NOT cover: mutual/nested inductive
/// families, indexed families beyond the trivial 0-index case, large
/// (Prop-restricted) elimination, structure eta beyond plain projection,
/// string literals, `let`/zeta reduction, well-founded recursion, or
/// multi-step reduction chains longer than the two-hop delta chain in
/// `conversion`. Widening this corpus (more cases per subsystem, randomized
/// generation with a fixed seed, coverage of the subsystems just named) is
/// the natural next slice of this lane's work, not a claim this file already
/// makes.
#[test]
fn kernel_differential_corpus_matches_pinned_lean() {
    let corpus = full_corpus();
    assert!(!corpus.is_empty(), "KERNEL-DIFFERENTIAL: corpus is EMPTY");

    let mut counts: BTreeMap<&str, usize> = BTreeMap::new();
    for case in &corpus {
        *counts.entry(case.subsystem).or_default() += 1;
    }
    for subsystem in SUBSYSTEMS {
        let n = counts.get(subsystem).copied().unwrap_or(0);
        assert!(
            n > 0,
            "KERNEL-DIFFERENTIAL: subsystem `{subsystem}` has ZERO cases -- \
             every subsystem in SUBSYSTEMS must be nonempty"
        );
    }

    let Some(lean) = lean_probe::lean_bin_or_skip("kernel-differential", corpus.len()) else {
        return;
    };

    let directory =
        std::env::temp_dir().join(format!("axeyum_kernel_differential_{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("create kernel-differential scratch directory");

    let mut lean_checked = 0usize;
    let mut p0: Vec<String> = Vec::new();
    let mut unexplained_incompleteness: Vec<String> = Vec::new();
    let mut explained_seen: BTreeMap<&str, bool> = BTreeMap::new();
    for &(name, _) in EXPLAINED_INCOMPLETENESS {
        explained_seen.insert(name, false);
    }

    for case in &corpus {
        let tag = case.name.replace("::", "_");
        let lean_accept = run_lean(&lean, &case.lean_source, &tag, &directory);
        lean_checked += 1;
        let verdict = classify(case.axeyum_accept, lean_accept);
        println!(
            "KERNEL-DIFFERENTIAL subsystem={} name={} axeyum={} lean={} verdict={:?}",
            case.subsystem, case.name, case.axeyum_accept, lean_accept, verdict
        );
        match verdict {
            Verdict::AgreeAccept | Verdict::AgreeReject => {}
            Verdict::AxeyumAcceptsLeanRejects => {
                p0.push(format!(
                    "{} (Axeyum ACCEPTED, real Lean REJECTED -- possible kernel unsoundness)",
                    case.name
                ));
            }
            Verdict::AxeyumRejectsLeanAccepts => {
                if let Some(seen) = explained_seen.get_mut(case.name) {
                    *seen = true;
                } else {
                    unexplained_incompleteness.push(format!(
                        "{} (Axeyum REJECTED, real Lean ACCEPTED, not registered in \
                         EXPLAINED_INCOMPLETENESS)",
                        case.name
                    ));
                }
            }
        }
    }

    let _ = std::fs::remove_dir_all(&directory);

    assert!(
        p0.is_empty(),
        "KERNEL-DIFFERENTIAL P0: Axeyum accepted something the real Lean kernel \
         rejects. This is a potential kernel unsoundness and preempts all other \
         work per ADR-0717 S5:\n{}",
        p0.join("\n")
    );
    assert!(
        unexplained_incompleteness.is_empty(),
        "KERNEL-DIFFERENTIAL: unexplained incompleteness -- Axeyum rejected \
         something Lean accepts, and the case is not registered in \
         EXPLAINED_INCOMPLETENESS with a citation:\n{}",
        unexplained_incompleteness.join("\n")
    );
    for (name, seen) in &explained_seen {
        assert!(
            *seen,
            "KERNEL-DIFFERENTIAL: EXPLAINED_INCOMPLETENESS registers `{name}` but the \
             corpus run did not observe that disagreement -- either the entry is stale \
             (the gap was closed) or the case regressed to agreement; remove or update it"
        );
    }

    lean_probe::report_checked("kernel-differential", lean_checked);
}

/// Standalone re-check of just the Axeyum side, so the corpus's own internal
/// self-consistency (every case function returns at least one result, and
/// running it twice is deterministic) is verified even on a host with no
/// Lean toolchain at all.
#[test]
fn kernel_differential_corpus_is_deterministic_without_lean() {
    let first: Vec<(&str, &str, bool)> = full_corpus()
        .iter()
        .map(|c| (c.subsystem, c.name, c.axeyum_accept))
        .collect();
    let second: Vec<(&str, &str, bool)> = full_corpus()
        .iter()
        .map(|c| (c.subsystem, c.name, c.axeyum_accept))
        .collect();
    assert_eq!(
        first, second,
        "KERNEL-DIFFERENTIAL: corpus is not deterministic across two runs"
    );
    assert!(first.len() >= SUBSYSTEMS.len() * 4);
}
