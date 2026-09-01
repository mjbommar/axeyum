// Single-character bindings mirror the kernel's own de Bruijn-ish naming.
#![allow(
    clippy::many_single_char_names,
    clippy::too_many_lines,
    clippy::similar_names
)]

//! **Probe for ADR-1495 — can a statement quantify over a *structure*?**
//!
//! `docs/research/11-design-review/2026-09-01-the-abstraction-question-has-never-been-asked.md`
//! asks whether this kernel has any mechanism by which a proposition quantifies
//! over an algebraic structure — a field, a vector space, a group — rather than
//! over a fixed carrier. `docs/curriculum/foundational-books/axler.md` tags
//! roughly half of Axler's chapters `X-TA` on the premise that it does not.
//!
//! `g4_pilot_generic_assoc_probe.rs` (2026-08-30, ADR-0865) already settled the
//! **unbundled** half: a raw `∀ (α : Sort 1) (op : α→α→α), …` statement is
//! admitted. This probe settles the **bundled** half, which is the one the
//! curriculum's `X-TA` verdict actually rests on:
//!
//! 1. Declare `AbsProbe.Field` — a ONE-CONSTRUCTOR inductive in `Sort 2` whose
//!    constructor carries a **carrier `Sort 1` as a field** (not a parameter),
//!    seven operations, and **ten laws**, including one with a hypothesis
//!    (`a ≠ 0 → a * a⁻¹ = 1`). This is a full field, not a toy.
//! 2. Build seven field selectors out of the auto-generated recursor by large
//!    elimination (`carrier` eliminates into `Sort 1`, i.e. motive level 2).
//! 3. Admit `AbsProbe.Field.addLeftCancel`, a theorem QUANTIFIED OVER THE
//!    STRUCTURE: `∀ (F : Field) (a b c : F.carrier), a + b = a + c → b = c`,
//!    proved by recursion on `F` from `addAssoc`, `zeroAdd` and `negAdd`. This
//!    is a DERIVED theorem, not a projection — every step is a transport.
//!
//! Three controls, so that a PASS is not vacuous:
//!
//! - **Universe control.** The same inductive declared at `Sort 1` must be
//!   REFUSED; a bundle carrying `Sort 1` genuinely lives one universe up.
//! - **Content control.** The cancellation proof term against the wrong
//!   conclusion (`a = c`, not derivable from `a + b = a + c`) must be REFUSED.
//! - **Iota control.** `carrier` applied to an explicit `Field.mk …` must
//!   reduce, checked by `def_eq`.
//!
//! Exit 0 = every stage as expected; nonzero = a stage disagreed, and the
//! stage is named. TEMPORARY probe evidence in the style of
//! `g4_pilot_generic_assoc_probe.rs`, not a library contribution.

use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, Kernel, LevelId, LogicPrelude, NameId, ReducibilityHint,
    build_logic_prelude,
};

// --- small term helpers (same shape as the G4 pilot probes) ------------------

fn pi_over(k: &mut Kernel, fv: u64, ty: ExprId, body: ExprId) -> ExprId {
    let b = k.abstract_fvars(body, &[fv]);
    let anon = k.anon();
    k.pi(anon, ty, b, BinderInfo::Default)
}

fn lam_over(k: &mut Kernel, fv: u64, ty: ExprId, body: ExprId) -> ExprId {
    let b = k.abstract_fvars(body, &[fv]);
    let anon = k.anon();
    k.lam(anon, ty, b, BinderInfo::Default)
}

fn arrow(k: &mut Kernel, dom: ExprId, cod: ExprId) -> ExprId {
    let anon = k.anon();
    k.pi(anon, dom, cod, BinderInfo::Default)
}

fn app2(k: &mut Kernel, f: ExprId, x: ExprId, y: ExprId) -> ExprId {
    let fx = k.app(f, x);
    k.app(fx, y)
}

fn eq_of(
    k: &mut Kernel,
    lg: &LogicPrelude,
    lvl: LevelId,
    ty: ExprId,
    a: ExprId,
    b: ExprId,
) -> ExprId {
    let c = k.const_(lg.eq, vec![lvl]);
    let e = k.app(c, ty);
    let e = k.app(e, a);
    k.app(e, b)
}

fn refl_of(k: &mut Kernel, lg: &LogicPrelude, lvl: LevelId, ty: ExprId, a: ExprId) -> ExprId {
    let c = k.const_(lg.eq_refl, vec![lvl]);
    let e = k.app(c, ty);
    k.app(e, a)
}

fn symm_of(
    k: &mut Kernel,
    lg: &LogicPrelude,
    lvl: LevelId,
    ty: ExprId,
    a: ExprId,
    b: ExprId,
    h: ExprId,
) -> ExprId {
    let c = k.const_(lg.eq_symm, vec![lvl]);
    let e = k.app(c, ty);
    let e = k.app(e, a);
    let e = k.app(e, b);
    k.app(e, h)
}

/// `Eq.rec` transport with the carrier's universe `lvl` and a `Prop` motive.
#[allow(clippy::too_many_arguments)]
fn transport(
    k: &mut Kernel,
    lg: &LogicPrelude,
    lvl: LevelId,
    ty: ExprId,
    p: ExprId,
    motive: ExprId,
    refl_case: ExprId,
    q: ExprId,
    h: ExprId,
) -> ExprId {
    let zero = k.level_zero();
    let rec = k.const_(lg.eq_rec, vec![zero, lvl]);
    let e = k.app(rec, ty);
    let e = k.app(e, p);
    let e = k.app(e, motive);
    let e = k.app(e, refl_case);
    let e = k.app(e, q);
    k.app(e, h)
}

/// `fun (x : ty) (_ : Eq ty a x) => body x`.
fn eq_motive(
    k: &mut Kernel,
    lg: &LogicPrelude,
    lvl: LevelId,
    ty: ExprId,
    a: ExprId,
    x_fv: u64,
    body: &dyn Fn(&mut Kernel, ExprId) -> ExprId,
) -> ExprId {
    let x = k.fvar(x_fv);
    let concl = body(k, x);
    let hyp = eq_of(k, lg, lvl, ty, a, x);
    let anon = k.anon();
    let inner = k.lam(anon, hyp, concl, BinderInfo::Default);
    lam_over(k, x_fv, ty, inner)
}

/// `h1 : Eq a b`, `h2 : Eq b c`  ⊢  `Eq a c`.
#[allow(clippy::too_many_arguments)]
fn trans_of(
    k: &mut Kernel,
    lg: &LogicPrelude,
    lvl: LevelId,
    ty: ExprId,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    h1: ExprId,
    h2: ExprId,
    scratch_fv: u64,
) -> ExprId {
    let motive = eq_motive(k, lg, lvl, ty, b, scratch_fv, &|k2, x| {
        eq_of(k2, lg, lvl, ty, a, x)
    });
    transport(k, lg, lvl, ty, b, motive, h1, c, h2)
}

/// `h : Eq a b` ⊢ `Eq (f a) (f b)`, for a carrier-generic `f`.
#[allow(clippy::too_many_arguments)]
fn congr_arg(
    k: &mut Kernel,
    lg: &LogicPrelude,
    lvl: LevelId,
    ty: ExprId,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    scratch_fv: u64,
    f: &dyn Fn(&mut Kernel, ExprId) -> ExprId,
) -> ExprId {
    let fa = f(k, a);
    let motive = eq_motive(k, lg, lvl, ty, a, scratch_fv, &|k2, x| {
        let fx = f(k2, x);
        eq_of(k2, lg, lvl, ty, fa, fx)
    });
    let refl_case = refl_of(k, lg, lvl, ty, fa);
    transport(k, lg, lvl, ty, a, motive, refl_case, b, h)
}

// --- the seventeen fields of `AbsProbe.Field` --------------------------------

/// Stable fvar ids, one per constructor field, in declaration order.
const F_A: u64 = 8_000;
const F_ZERO: u64 = 8_001;
const F_ONE: u64 = 8_002;
const F_ADD: u64 = 8_003;
const F_MUL: u64 = 8_004;
const F_NEG: u64 = 8_005;
const F_INV: u64 = 8_006;
const F_ADD_ASSOC: u64 = 8_007;
const F_ADD_COMM: u64 = 8_008;
const F_ZERO_ADD: u64 = 8_009;
const F_NEG_ADD: u64 = 8_010;
const F_MUL_ASSOC: u64 = 8_011;
const F_MUL_COMM: u64 = 8_012;
const F_ONE_MUL: u64 = 8_013;
const F_MUL_INV: u64 = 8_014;
const F_DISTRIB: u64 = 8_015;
const F_ONE_NE_ZERO: u64 = 8_016;

const FIELD_FVARS: [u64; 17] = [
    F_A,
    F_ZERO,
    F_ONE,
    F_ADD,
    F_MUL,
    F_NEG,
    F_INV,
    F_ADD_ASSOC,
    F_ADD_COMM,
    F_ZERO_ADD,
    F_NEG_ADD,
    F_MUL_ASSOC,
    F_MUL_COMM,
    F_ONE_MUL,
    F_MUL_INV,
    F_DISTRIB,
    F_ONE_NE_ZERO,
];

// Scratch fvars for bound variables inside law statements.
const V_A: u64 = 8_100;
const V_B: u64 = 8_101;
const V_C: u64 = 8_102;
const V_X: u64 = 8_103;

/// Build the seventeen field types, in order, each in terms of the earlier
/// fields' fvars. Returns `(fvar, type)` pairs.
fn field_types(k: &mut Kernel, lg: &LogicPrelude, one_lvl: LevelId) -> Vec<(u64, ExprId)> {
    let sort1 = k.sort(one_lvl);
    let a_ty = k.fvar(F_A);
    let zero = k.fvar(F_ZERO);
    let one = k.fvar(F_ONE);
    let add = k.fvar(F_ADD);
    let mul = k.fvar(F_MUL);
    let neg = k.fvar(F_NEG);
    let inv = k.fvar(F_INV);
    let false_ = k.const_(lg.false_, vec![]);

    let binop = {
        let inner = arrow(k, a_ty, a_ty);
        arrow(k, a_ty, inner)
    };
    let unop = arrow(k, a_ty, a_ty);

    // ∀ a b c, Eq A (op (op a b) c) (op a (op b c))
    let assoc = |k: &mut Kernel, op: ExprId| {
        let va = k.fvar(V_A);
        let vb = k.fvar(V_B);
        let vc = k.fvar(V_C);
        let ab = app2(k, op, va, vb);
        let lhs = app2(k, op, ab, vc);
        let bc = app2(k, op, vb, vc);
        let rhs = app2(k, op, va, bc);
        let body = eq_of(k, lg, one_lvl, a_ty, lhs, rhs);
        let t = pi_over(k, V_C, a_ty, body);
        let t = pi_over(k, V_B, a_ty, t);
        pi_over(k, V_A, a_ty, t)
    };
    // ∀ a b, Eq A (op a b) (op b a)
    let comm = |k: &mut Kernel, op: ExprId| {
        let va = k.fvar(V_A);
        let vb = k.fvar(V_B);
        let lhs = app2(k, op, va, vb);
        let rhs = app2(k, op, vb, va);
        let body = eq_of(k, lg, one_lvl, a_ty, lhs, rhs);
        let t = pi_over(k, V_B, a_ty, body);
        pi_over(k, V_A, a_ty, t)
    };
    // ∀ a, Eq A (op unit a) a
    let unit_left = |k: &mut Kernel, op: ExprId, unit: ExprId| {
        let va = k.fvar(V_A);
        let lhs = app2(k, op, unit, va);
        let body = eq_of(k, lg, one_lvl, a_ty, lhs, va);
        pi_over(k, V_A, a_ty, body)
    };

    let add_assoc = assoc(k, add);
    let add_comm = comm(k, add);
    let zero_add = unit_left(k, add, zero);
    // ∀ a, Eq A (add (neg a) a) zero
    let neg_add = {
        let va = k.fvar(V_A);
        let na = k.app(neg, va);
        let lhs = app2(k, add, na, va);
        let body = eq_of(k, lg, one_lvl, a_ty, lhs, zero);
        pi_over(k, V_A, a_ty, body)
    };
    let mul_assoc = assoc(k, mul);
    let mul_comm = comm(k, mul);
    let one_mul = unit_left(k, mul, one);
    // ∀ a, (Eq A a zero → False) → Eq A (mul a (inv a)) one
    let mul_inv = {
        let va = k.fvar(V_A);
        let is_zero = eq_of(k, lg, one_lvl, a_ty, va, zero);
        let hyp = arrow(k, is_zero, false_);
        let ia = k.app(inv, va);
        let lhs = app2(k, mul, va, ia);
        let concl = eq_of(k, lg, one_lvl, a_ty, lhs, one);
        let body = arrow(k, hyp, concl);
        pi_over(k, V_A, a_ty, body)
    };
    // ∀ a b c, Eq A (mul a (add b c)) (add (mul a b) (mul a c))
    let distrib = {
        let va = k.fvar(V_A);
        let vb = k.fvar(V_B);
        let vc = k.fvar(V_C);
        let bc = app2(k, add, vb, vc);
        let lhs = app2(k, mul, va, bc);
        let ab = app2(k, mul, va, vb);
        let ac = app2(k, mul, va, vc);
        let rhs = app2(k, add, ab, ac);
        let body = eq_of(k, lg, one_lvl, a_ty, lhs, rhs);
        let t = pi_over(k, V_C, a_ty, body);
        let t = pi_over(k, V_B, a_ty, t);
        pi_over(k, V_A, a_ty, t)
    };
    // Eq A one zero → False
    let one_ne_zero = {
        let e = eq_of(k, lg, one_lvl, a_ty, one, zero);
        arrow(k, e, false_)
    };

    vec![
        (F_A, sort1),
        (F_ZERO, a_ty),
        (F_ONE, a_ty),
        (F_ADD, binop),
        (F_MUL, binop),
        (F_NEG, unop),
        (F_INV, unop),
        (F_ADD_ASSOC, add_assoc),
        (F_ADD_COMM, add_comm),
        (F_ZERO_ADD, zero_add),
        (F_NEG_ADD, neg_add),
        (F_MUL_ASSOC, mul_assoc),
        (F_MUL_COMM, mul_comm),
        (F_ONE_MUL, one_mul),
        (F_MUL_INV, mul_inv),
        (F_DISTRIB, distrib),
        (F_ONE_NE_ZERO, one_ne_zero),
    ]
}

/// `Π (fields…), result` over the seventeen field types.
fn close_pi(k: &mut Kernel, fields: &[(u64, ExprId)], result: ExprId) -> ExprId {
    let mut t = result;
    for &(fv, ty) in fields.iter().rev() {
        t = pi_over(k, fv, ty, t);
    }
    t
}

/// `fun (fields…) => body` over the seventeen field types.
fn close_lam(k: &mut Kernel, fields: &[(u64, ExprId)], body: ExprId) -> ExprId {
    let mut t = body;
    for &(fv, ty) in fields.iter().rev() {
        t = lam_over(k, fv, ty, t);
    }
    t
}

/// One field selector, built out of the auto-generated recursor.
///
/// `name : Π (s : Field), motive s := fun s => Field.rec.{w} motive
/// (fun fields… => field_i) s`.
#[allow(clippy::too_many_arguments)]
fn declare_selector(
    k: &mut Kernel,
    field_ind: NameId,
    field_rec: NameId,
    name: NameId,
    motive_lvl: LevelId,
    s_fv: u64,
    motive_body: &dyn Fn(&mut Kernel, ExprId) -> ExprId,
    index: usize,
    lg: &LogicPrelude,
    one_lvl: LevelId,
) -> Result<(), String> {
    let field_ty = k.const_(field_ind, vec![]);
    let s = k.fvar(s_fv);
    let mb = motive_body(k, s);
    let motive = lam_over(k, s_fv, field_ty, mb);

    let fields = field_types(k, lg, one_lvl);
    let picked = k.fvar(FIELD_FVARS[index]);
    let minor = close_lam(k, &fields, picked);

    let rec = k.const_(field_rec, vec![motive_lvl]);
    let applied = {
        let e = k.app(rec, motive);
        let e = k.app(e, minor);
        let s2 = k.fvar(s_fv);
        k.app(e, s2)
    };
    let value = lam_over(k, s_fv, field_ty, applied);

    let s3 = k.fvar(s_fv);
    let result = motive_body(k, s3);
    let ty = pi_over(k, s_fv, field_ty, result);

    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
    .map_err(|e| format!("{e:?}"))
}

const S_FV: u64 = 8_200;

fn main() {
    let mut k = Kernel::new();
    let lg = build_logic_prelude(&mut k).expect("logic prelude must build");

    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let l2 = k.level_succ(l1);

    let root = k.anon();
    let ns = k.name_str(root, "AbsProbe");
    let field_ind = k.name_str(ns, "Field");
    let field_mk = k.name_str(field_ind, "mk");
    let field_rec = k.name_str(field_ind, "rec");

    let mut failures: Vec<&'static str> = Vec::new();

    // === Stage 1: does the bundle admit? ====================================
    let fields = field_types(&mut k, &lg, l1);
    println!("-- ADR-1495 bundled-structure probe --");
    println!(
        "stage 1: AbsProbe.Field, one constructor, {} fields",
        fields.len()
    );

    // Universe CONTROL first: the same inductive at Sort 1 must be REFUSED.
    {
        let ctrl_ns = k.name_str(root, "AbsProbeCtl");
        let ctrl_ind = k.name_str(ctrl_ns, "FieldTooLow");
        let ctrl_mk = k.name_str(ctrl_ind, "mk");
        let sort1 = k.sort(l1);
        let ctrl_const = k.const_(ctrl_ind, vec![]);
        let ctrl_ctor = close_pi(&mut k, &fields, ctrl_const);
        match k.add_inductive(ctrl_ind, &[], 0, sort1, &[(ctrl_mk, ctrl_ctor)]) {
            Ok(()) => {
                println!(
                    "  UNIVERSE CONTROL: FAILED -- Sort 1 accepted for a Sort-1-carrying bundle"
                );
                failures.push("universe-control");
            }
            Err(e) => println!("  universe control: PASS -- Sort 1 refused: {e:?}"),
        }
    }

    let sort2 = k.sort(l2);
    let field_const = k.const_(field_ind, vec![]);
    let ctor_ty = close_pi(&mut k, &fields, field_const);
    match k.add_inductive(field_ind, &[], 0, sort2, &[(field_mk, ctor_ty)]) {
        Ok(()) => println!("  add_inductive(AbsProbe.Field : Sort 2): PASS"),
        Err(e) => {
            println!("  add_inductive(AbsProbe.Field : Sort 2): FAIL -- {e:?}");
            std::process::exit(1);
        }
    }
    if let Some(d) = k.environment().get(field_rec) {
        let rendered = k.render_lean_decl(d);
        println!("  recursor generated ({} chars)", rendered.len());
    } else {
        println!("  recursor generated: FAIL -- AbsProbe.Field.rec absent");
        std::process::exit(1);
    }

    // === Stage 2: selectors by large elimination ============================
    println!("stage 2: selectors");
    let sel_carrier = k.name_str(field_ind, "carrier");
    let sel_zero = k.name_str(field_ind, "zero");
    let sel_add = k.name_str(field_ind, "add");
    let sel_neg = k.name_str(field_ind, "neg");
    let sel_add_assoc = k.name_str(field_ind, "addAssoc");
    let sel_zero_add = k.name_str(field_ind, "zeroAdd");
    let sel_neg_add = k.name_str(field_ind, "negAdd");

    // carrier : Field → Sort 1   (LARGE elimination: motive lands in Sort 2)
    if let Err(e) = declare_selector(
        &mut k,
        field_ind,
        field_rec,
        sel_carrier,
        l2,
        S_FV,
        &|k2, _s| k2.sort(l1),
        0,
        &lg,
        l1,
    ) {
        println!("  carrier (large elimination): FAIL -- {e}");
        std::process::exit(1);
    }
    println!("  carrier : Field -> Sort 1 (large elimination): PASS");

    let carrier_of = |k: &mut Kernel, s: ExprId| {
        let c = k.const_(sel_carrier, vec![]);
        k.app(c, s)
    };

    // zero : Π (s : Field), s.carrier
    if let Err(e) = declare_selector(
        &mut k,
        field_ind,
        field_rec,
        sel_zero,
        l1,
        S_FV,
        &|k2, s| carrier_of(k2, s),
        1,
        &lg,
        l1,
    ) {
        println!("  zero: FAIL -- {e}");
        std::process::exit(1);
    }

    // add : Π (s : Field), s.carrier → s.carrier → s.carrier
    if let Err(e) = declare_selector(
        &mut k,
        field_ind,
        field_rec,
        sel_add,
        l1,
        S_FV,
        &|k2, s| {
            let a = carrier_of(k2, s);
            let inner = arrow(k2, a, a);
            arrow(k2, a, inner)
        },
        3,
        &lg,
        l1,
    ) {
        println!("  add: FAIL -- {e}");
        std::process::exit(1);
    }

    // neg : Π (s : Field), s.carrier → s.carrier
    if let Err(e) = declare_selector(
        &mut k,
        field_ind,
        field_rec,
        sel_neg,
        l1,
        S_FV,
        &|k2, s| {
            let a = carrier_of(k2, s);
            arrow(k2, a, a)
        },
        5,
        &lg,
        l1,
    ) {
        println!("  neg: FAIL -- {e}");
        std::process::exit(1);
    }
    println!("  zero / add / neg: PASS");

    // The three law selectors. Their motives are Props stated THROUGH the
    // earlier selectors, so admitting them is itself evidence that a law can
    // be read off an abstract structure.
    let add_of = |k: &mut Kernel, s: ExprId| {
        let c = k.const_(sel_add, vec![]);
        k.app(c, s)
    };
    let zero_of = |k: &mut Kernel, s: ExprId| {
        let c = k.const_(sel_zero, vec![]);
        k.app(c, s)
    };
    let neg_of = |k: &mut Kernel, s: ExprId| {
        let c = k.const_(sel_neg, vec![]);
        k.app(c, s)
    };

    if let Err(e) = declare_selector(
        &mut k,
        field_ind,
        field_rec,
        sel_add_assoc,
        l0,
        S_FV,
        &|k2, s| {
            let a_ty = carrier_of(k2, s);
            let add = add_of(k2, s);
            let va = k2.fvar(V_A);
            let vb = k2.fvar(V_B);
            let vc = k2.fvar(V_C);
            let ab = app2(k2, add, va, vb);
            let lhs = app2(k2, add, ab, vc);
            let bc = app2(k2, add, vb, vc);
            let rhs = app2(k2, add, va, bc);
            let body = eq_of(k2, &lg, l1, a_ty, lhs, rhs);
            let t = pi_over(k2, V_C, a_ty, body);
            let t = pi_over(k2, V_B, a_ty, t);
            pi_over(k2, V_A, a_ty, t)
        },
        7,
        &lg,
        l1,
    ) {
        println!("  addAssoc: FAIL -- {e}");
        std::process::exit(1);
    }

    if let Err(e) = declare_selector(
        &mut k,
        field_ind,
        field_rec,
        sel_zero_add,
        l0,
        S_FV,
        &|k2, s| {
            let a_ty = carrier_of(k2, s);
            let add = add_of(k2, s);
            let z = zero_of(k2, s);
            let va = k2.fvar(V_A);
            let lhs = app2(k2, add, z, va);
            let body = eq_of(k2, &lg, l1, a_ty, lhs, va);
            pi_over(k2, V_A, a_ty, body)
        },
        9,
        &lg,
        l1,
    ) {
        println!("  zeroAdd: FAIL -- {e}");
        std::process::exit(1);
    }

    if let Err(e) = declare_selector(
        &mut k,
        field_ind,
        field_rec,
        sel_neg_add,
        l0,
        S_FV,
        &|k2, s| {
            let a_ty = carrier_of(k2, s);
            let add = add_of(k2, s);
            let ng = neg_of(k2, s);
            let z = zero_of(k2, s);
            let va = k2.fvar(V_A);
            let na = k2.app(ng, va);
            let lhs = app2(k2, add, na, va);
            let body = eq_of(k2, &lg, l1, a_ty, lhs, z);
            pi_over(k2, V_A, a_ty, body)
        },
        10,
        &lg,
        l1,
    ) {
        println!("  negAdd: FAIL -- {e}");
        std::process::exit(1);
    }
    println!("  addAssoc / zeroAdd / negAdd (laws through selectors): PASS");

    // Iota control: `carrier (mk A …)` must reduce to `A`. Without this a
    // selector could be admitted and mean nothing.
    {
        let fields2 = field_types(&mut k, &lg, l1);
        let mk = k.const_(field_mk, vec![]);
        let mut applied = mk;
        for &(fv, _) in &fields2 {
            let x = k.fvar(fv);
            applied = k.app(applied, x);
        }
        let projected = carrier_of(&mut k, applied);
        let a_ty = k.fvar(F_A);
        if k.def_eq(projected, a_ty) {
            println!("  iota control: PASS -- carrier (mk A ...) def_eq A");
        } else {
            println!("  iota control: FAILED -- carrier (mk A ...) is NOT def_eq A");
            failures.push("iota-control");
        }
    }

    // === Stage 3: a DERIVED theorem quantified over the structure ===========
    println!("stage 3: theorem quantified over the structure");

    let a_fv = 8_300_u64;
    let b_fv = 8_301_u64;
    let c_fv = 8_302_u64;
    let h_fv = 8_303_u64;
    let sc1 = 8_400_u64;
    let sc2 = 8_401_u64;

    // ∀ (a b c : A), add a b = add a c → (b = c | a = c for the control)
    let stmt_over = |k2: &mut Kernel, a_ty: ExprId, add: ExprId, swap_conclusion: bool| -> ExprId {
        let va = k2.fvar(a_fv);
        let vb = k2.fvar(b_fv);
        let vc = k2.fvar(c_fv);
        let lhs = app2(k2, add, va, vb);
        let rhs = app2(k2, add, va, vc);
        let hyp = eq_of(k2, &lg, l1, a_ty, lhs, rhs);
        let concl = if swap_conclusion {
            eq_of(k2, &lg, l1, a_ty, va, vc)
        } else {
            eq_of(k2, &lg, l1, a_ty, vb, vc)
        };
        let body = arrow(k2, hyp, concl);
        let t = pi_over(k2, c_fv, a_ty, body);
        let t = pi_over(k2, b_fv, a_ty, t);
        pi_over(k2, a_fv, a_ty, t)
    };

    let field_ty = k.const_(field_ind, vec![]);
    let goal_ty = {
        let s = k.fvar(S_FV);
        let a_ty = carrier_of(&mut k, s);
        let add = add_of(&mut k, s);
        let inner = stmt_over(&mut k, a_ty, add, false);
        pi_over(&mut k, S_FV, field_ty, inner)
    };
    let bad_goal_ty = {
        let s = k.fvar(S_FV);
        let a_ty = carrier_of(&mut k, s);
        let add = add_of(&mut k, s);
        let inner = stmt_over(&mut k, a_ty, add, true);
        pi_over(&mut k, S_FV, field_ty, inner)
    };

    // The proof, built over the RAW unbundled components (which is what the
    // minor premise sees after iota), then wrapped by the recursor.
    let raw_proof = {
        let a_ty = k.fvar(F_A);
        let add = k.fvar(F_ADD);
        let ng = k.fvar(F_NEG);
        let z = k.fvar(F_ZERO);
        let aa = k.fvar(F_ADD_ASSOC);
        let za = k.fvar(F_ZERO_ADD);
        let na_law = k.fvar(F_NEG_ADD);

        let va = k.fvar(a_fv);
        let vb = k.fvar(b_fv);
        let vc = k.fvar(c_fv);
        let h = k.fvar(h_fv);

        let nega = k.app(ng, va);
        let ab = app2(&mut k, add, va, vb);
        let ac = app2(&mut k, add, va, vc);

        // e1 : Eq (nega + (a+b)) (nega + (a+c))
        let e1 = congr_arg(&mut k, &lg, l1, a_ty, ab, ac, h, V_X, &|k2, x| {
            let n = k2.fvar(a_fv);
            let ngf = k2.fvar(F_NEG);
            let nn = k2.app(ngf, n);
            let addf = k2.fvar(F_ADD);
            app2(k2, addf, nn, x)
        });

        // e2 : Eq ((nega + a) + b) (nega + (a + b))
        let e2 = {
            let e = k.app(aa, nega);
            let e = k.app(e, va);
            k.app(e, vb)
        };
        // e3 : Eq ((nega + a) + c) (nega + (a + c))
        let e3 = {
            let e = k.app(aa, nega);
            let e = k.app(e, va);
            k.app(e, vc)
        };

        // e4 : Eq (nega + a) zero
        let e4 = k.app(na_law, va);

        let nega_a = app2(&mut k, add, nega, va);
        // e5 : Eq ((nega+a)+b) (zero+b)
        let e5 = congr_arg(&mut k, &lg, l1, a_ty, nega_a, z, e4, V_X, &|k2, x| {
            let addf = k2.fvar(F_ADD);
            let vbb = k2.fvar(b_fv);
            app2(k2, addf, x, vbb)
        });
        // e6 : Eq ((nega+a)+c) (zero+c)
        let e6 = congr_arg(&mut k, &lg, l1, a_ty, nega_a, z, e4, V_X, &|k2, x| {
            let addf = k2.fvar(F_ADD);
            let vcc = k2.fvar(c_fv);
            app2(k2, addf, x, vcc)
        });

        // e7 : Eq (zero+b) b ; e8 : Eq (zero+c) c
        let e7 = k.app(za, vb);
        let e8 = k.app(za, vc);

        let zb = app2(&mut k, add, z, vb);
        let zc = app2(&mut k, add, z, vc);
        let naab = app2(&mut k, add, nega_a, vb);
        let naac = app2(&mut k, add, nega_a, vc);
        let nab = app2(&mut k, add, nega, ab);
        let nac = app2(&mut k, add, nega, ac);

        let s7 = symm_of(&mut k, &lg, l1, a_ty, zb, vb, e7);
        let s5 = symm_of(&mut k, &lg, l1, a_ty, naab, zb, e5);
        let s3 = symm_of(&mut k, &lg, l1, a_ty, naac, nac, e3);

        let t1 = trans_of(&mut k, &lg, l1, a_ty, vb, zb, naab, s7, s5, sc1);
        let t2 = trans_of(&mut k, &lg, l1, a_ty, vb, naab, nab, t1, e2, sc1);
        let t3 = trans_of(&mut k, &lg, l1, a_ty, vb, nab, nac, t2, e1, sc1);
        let t4 = trans_of(&mut k, &lg, l1, a_ty, vb, nac, naac, t3, s3, sc2);
        let t5 = trans_of(&mut k, &lg, l1, a_ty, vb, naac, zc, t4, e6, sc1);
        let t6 = trans_of(&mut k, &lg, l1, a_ty, vb, zc, vc, t5, e8, sc2);

        let hyp_ty = eq_of(&mut k, &lg, l1, a_ty, ab, ac);
        let p = lam_over(&mut k, h_fv, hyp_ty, t6);
        let p = lam_over(&mut k, c_fv, a_ty, p);
        let p = lam_over(&mut k, b_fv, a_ty, p);
        lam_over(&mut k, a_fv, a_ty, p)
    };

    // Wrap by the recursor.
    let build_wrapped = |k2: &mut Kernel, swap: bool| -> ExprId {
        let s = k2.fvar(S_FV);
        let a_ty = carrier_of(k2, s);
        let add = add_of(k2, s);
        let mb = stmt_over(k2, a_ty, add, swap);
        let fty = k2.const_(field_ind, vec![]);
        let motive = lam_over(k2, S_FV, fty, mb);
        let flds = field_types(k2, &lg, l1);
        let minor = close_lam(k2, &flds, raw_proof);
        let rec = k2.const_(field_rec, vec![l0]);
        let e = k2.app(rec, motive);
        let e = k2.app(e, minor);
        let s2 = k2.fvar(S_FV);
        let e = k2.app(e, s2);
        let fty2 = k2.const_(field_ind, vec![]);
        lam_over(k2, S_FV, fty2, e)
    };

    let value = build_wrapped(&mut k, false);
    let bad_value = build_wrapped(&mut k, true);

    let thm = k.name_str(field_ind, "addLeftCancel");
    println!("goal: {}", k.render_lean(goal_ty));
    match k.add_declaration(Declaration::Theorem {
        name: thm,
        uparams: vec![],
        ty: goal_ty,
        value,
    }) {
        Ok(()) => println!("  RESULT: PASS -- AbsProbe.Field.addLeftCancel admitted"),
        Err(e) => {
            println!("  RESULT: FAIL -- {e:?}");
            std::process::exit(1);
        }
    }

    // Content control: same proof shape, wrong conclusion, must be REFUSED.
    let bad_thm = k.name_str(field_ind, "addLeftCancelWrongConclusion");
    match k.add_declaration(Declaration::Theorem {
        name: bad_thm,
        uparams: vec![],
        ty: bad_goal_ty,
        value: bad_value,
    }) {
        Ok(()) => {
            println!("  CONTENT CONTROL: FAILED -- kernel accepted `a = c` from `a + b = a + c`");
            failures.push("content-control");
        }
        Err(_) => println!("  content control: PASS -- wrong conclusion refused"),
    }

    // === Axiom footprint ====================================================
    let fp = k.axiom_footprint(thm);
    let names: Vec<String> = fp.iter().map(|&n| k.display_name(n).to_string()).collect();
    println!("axiom_footprint(AbsProbe.Field.addLeftCancel) = {names:?}");
    if !fp.is_empty() {
        failures.push("axiom-footprint-nonempty");
    }

    if failures.is_empty() {
        println!("ALL STAGES AND CONTROLS AS EXPECTED");
    } else {
        println!("UNEXPECTED: {failures:?}");
        std::process::exit(3);
    }
}
