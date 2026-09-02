#![allow(clippy::many_single_char_names, clippy::too_many_lines)]

//! **Third probe for ADR-1495: a bundle whose field is ANOTHER bundle.**
//!
//! `bundled_structure_probe.rs` settled the single-carrier case (a `Field`).
//! Axler Chapters 1–2 — the chapters `docs/curriculum/foundational-books/axler.md`
//! tags `X-TA` and calls permanently unstateable — need something strictly
//! more: **"a vector space `V` over a field `F`"** is a bundle carrying a
//! *previous bundle* as a field, with later fields whose types are stated
//! through a projection OF that field (`smul : F.carrier → V → V`).
//!
//! That is the shape this probe tests, and nothing else in the tree does:
//!
//! ```text
//! AbsMod.Field  : Sort 2   -- carrier + zero + one + add + mul  (5 fields)
//! AbsMod.VecSp  : Sort 2
//!   mk : (F : AbsMod.Field)            -- a BUNDLE as a field
//!        (V : Sort 1)
//!        (addV  : V → V → V)
//!        (smul  : AbsMod.Field.carrier F → V → V)   -- through a PROJECTION
//!        (oneSmul : ∀ v, smul (AbsMod.Field.one F) v = v)
//!        (smulAdd : ∀ a v w, smul a (addV v w) = addV (smul a v) (smul a w))
//!     → AbsMod.VecSp
//! ```
//!
//! Then it admits a theorem quantified over the vector space, derived from two
//! of its laws rather than read off one:
//!
//! ```text
//! AbsMod.VecSp.oneSmulAdd :
//!   ∀ (M : VecSp) (v w : M.carrier),
//!     M.addV (M.smul M.scalarOne v) (M.smul M.scalarOne w) = M.addV v w
//! ```
//!
//! Controls: the same proof term against a swapped conclusion must be REFUSED,
//! and the axiom footprint must be empty.
//!
//! TEMPORARY probe evidence, not a library contribution.

use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, Kernel, LevelId, LogicPrelude, NameId, ReducibilityHint,
    build_logic_prelude,
};

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

/// `h : Eq a b` ⊢ `Eq (f a) (f b)`.
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

// --- Field fvars (5 fields) --------------------------------------------------
const G_A: u64 = 6_000;
const G_ZERO: u64 = 6_001;
const G_ONE: u64 = 6_002;
const G_ADD: u64 = 6_003;
const G_MUL: u64 = 6_004;

// --- VecSp fvars (6 fields) --------------------------------------------------
const M_F: u64 = 6_100;
const M_V: u64 = 6_101;
const M_ADDV: u64 = 6_102;
const M_SMUL: u64 = 6_103;
const M_ONE_SMUL: u64 = 6_104;
const M_SMUL_ADD: u64 = 6_105;

const V_A: u64 = 6_200;
const V_V: u64 = 6_201;
const V_W: u64 = 6_202;
const S_FV: u64 = 6_300;
const SC1: u64 = 6_400;
const SC2: u64 = 6_401;

fn field_field_types(k: &mut Kernel, one_lvl: LevelId) -> Vec<(u64, ExprId)> {
    let sort1 = k.sort(one_lvl);
    let a = k.fvar(G_A);
    let binop = {
        let inner = arrow(k, a, a);
        arrow(k, a, inner)
    };
    vec![
        (G_A, sort1),
        (G_ZERO, a),
        (G_ONE, a),
        (G_ADD, binop),
        (G_MUL, binop),
    ]
}

fn close_pi(k: &mut Kernel, fields: &[(u64, ExprId)], result: ExprId) -> ExprId {
    let mut t = result;
    for &(fv, ty) in fields.iter().rev() {
        t = pi_over(k, fv, ty, t);
    }
    t
}

fn close_lam(k: &mut Kernel, fields: &[(u64, ExprId)], body: ExprId) -> ExprId {
    let mut t = body;
    for &(fv, ty) in fields.iter().rev() {
        t = lam_over(k, fv, ty, t);
    }
    t
}

/// Selector `name : Π (s : ind), motive s`, built out of `ind.rec`.
#[allow(clippy::too_many_arguments)]
fn declare_selector(
    k: &mut Kernel,
    ind: NameId,
    rec: NameId,
    name: NameId,
    motive_lvl: LevelId,
    fields: &[(u64, ExprId)],
    picked_fv: u64,
    motive_body: &dyn Fn(&mut Kernel, ExprId) -> ExprId,
) -> Result<(), String> {
    let ind_ty = k.const_(ind, vec![]);
    let s = k.fvar(S_FV);
    let mb = motive_body(k, s);
    let motive = lam_over(k, S_FV, ind_ty, mb);

    let picked = k.fvar(picked_fv);
    let minor = close_lam(k, fields, picked);

    let rec_c = k.const_(rec, vec![motive_lvl]);
    let applied = {
        let e = k.app(rec_c, motive);
        let e = k.app(e, minor);
        let s2 = k.fvar(S_FV);
        k.app(e, s2)
    };
    let value = lam_over(k, S_FV, ind_ty, applied);

    let s3 = k.fvar(S_FV);
    let result = motive_body(k, s3);
    let ty = pi_over(k, S_FV, ind_ty, result);

    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
    .map_err(|e| format!("{e:?}"))
}

fn main() {
    let mut k = Kernel::new();
    let lg = build_logic_prelude(&mut k).expect("logic prelude must build");

    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let l2 = k.level_succ(l1);

    let root = k.anon();
    let ns = k.name_str(root, "AbsMod");

    println!("-- ADR-1495 probe 3: a bundle carrying another bundle --");

    // === The scalar Field =====================================================
    let fld = k.name_str(ns, "Field");
    let fld_mk = k.name_str(fld, "mk");
    let fld_rec = k.name_str(fld, "rec");
    {
        let ffs = field_field_types(&mut k, l1);
        let fld_c = k.const_(fld, vec![]);
        let ctor = close_pi(&mut k, &ffs, fld_c);
        let sort2 = k.sort(l2);
        match k.add_inductive(fld, &[], 0, sort2, &[(fld_mk, ctor)]) {
            Ok(()) => println!("  AbsMod.Field : Sort 2 (5 fields): PASS"),
            Err(e) => {
                println!("  AbsMod.Field: FAIL -- {e:?}");
                std::process::exit(1);
            }
        }
    }

    let f_carrier = k.name_str(fld, "carrier");
    let f_one = k.name_str(fld, "one");
    {
        let ffs = field_field_types(&mut k, l1);
        if let Err(e) =
            declare_selector(&mut k, fld, fld_rec, f_carrier, l2, &ffs, G_A, &|k2, _s| {
                k2.sort(l1)
            })
        {
            println!("  Field.carrier: FAIL -- {e}");
            std::process::exit(1);
        }
    }
    let carrier_of = |k: &mut Kernel, s: ExprId| {
        let c = k.const_(f_carrier, vec![]);
        k.app(c, s)
    };
    {
        let ffs = field_field_types(&mut k, l1);
        if let Err(e) = declare_selector(&mut k, fld, fld_rec, f_one, l1, &ffs, G_ONE, &|k2, s| {
            carrier_of(k2, s)
        }) {
            println!("  Field.one: FAIL -- {e}");
            std::process::exit(1);
        }
    }
    let one_of = |k: &mut Kernel, s: ExprId| {
        let c = k.const_(f_one, vec![]);
        k.app(c, s)
    };
    println!("  Field.carrier / Field.one: PASS");

    // === The vector space: a bundle carrying the Field bundle ================
    let vec = k.name_str(ns, "VecSp");
    let vec_mk = k.name_str(vec, "mk");
    let vec_rec = k.name_str(vec, "rec");

    // Build the six VecSp field types. `smul`'s type and both laws are stated
    // THROUGH `AbsMod.Field.carrier`/`AbsMod.Field.one` applied to the earlier
    // bundle-valued field `F` -- the shape that decides Axler Ch.1-2.
    let vec_field_types = |k: &mut Kernel| -> Vec<(u64, ExprId)> {
        let fld_ty = k.const_(fld, vec![]);
        let sort1 = k.sort(l1);
        let f = k.fvar(M_F);
        let scal = carrier_of(k, f);
        let v = k.fvar(M_V);
        let addv_ty = {
            let inner = arrow(k, v, v);
            arrow(k, v, inner)
        };
        let smul_ty = {
            let inner = arrow(k, v, v);
            arrow(k, scal, inner)
        };
        let addv = k.fvar(M_ADDV);
        let smul = k.fvar(M_SMUL);
        // ∀ v, smul (Field.one F) v = v
        let one_smul = {
            let o = one_of(k, f);
            let vv = k.fvar(V_V);
            let lhs = app2(k, smul, o, vv);
            let body = eq_of(k, &lg, l1, v, lhs, vv);
            pi_over(k, V_V, v, body)
        };
        // ∀ a v w, smul a (addV v w) = addV (smul a v) (smul a w)
        let smul_add = {
            let va = k.fvar(V_A);
            let vv = k.fvar(V_V);
            let vw = k.fvar(V_W);
            let sum = app2(k, addv, vv, vw);
            let lhs = app2(k, smul, va, sum);
            let sv = app2(k, smul, va, vv);
            let sw = app2(k, smul, va, vw);
            let rhs = app2(k, addv, sv, sw);
            let body = eq_of(k, &lg, l1, v, lhs, rhs);
            let t = pi_over(k, V_W, v, body);
            let t = pi_over(k, V_V, v, t);
            pi_over(k, V_A, scal, t)
        };
        vec![
            (M_F, fld_ty),
            (M_V, sort1),
            (M_ADDV, addv_ty),
            (M_SMUL, smul_ty),
            (M_ONE_SMUL, one_smul),
            (M_SMUL_ADD, smul_add),
        ]
    };

    {
        let vfs = vec_field_types(&mut k);
        let vec_c = k.const_(vec, vec![]);
        let ctor = close_pi(&mut k, &vfs, vec_c);
        let sort2 = k.sort(l2);
        match k.add_inductive(vec, &[], 0, sort2, &[(vec_mk, ctor)]) {
            Ok(()) => println!("  AbsMod.VecSp : Sort 2, carrying AbsMod.Field as a FIELD: PASS"),
            Err(e) => {
                println!("  AbsMod.VecSp: FAIL -- {e:?}");
                std::process::exit(1);
            }
        }
    }

    // Selectors. `vecs` is the scalar field; the rest are stated through it.
    let m_scalars = k.name_str(vec, "scalars");
    let m_carrier = k.name_str(vec, "carrier");
    let m_addv = k.name_str(vec, "addV");
    let m_smul = k.name_str(vec, "smul");
    let m_one_smul = k.name_str(vec, "oneSmul");
    let m_smul_add = k.name_str(vec, "smulAdd");

    {
        let vfs = vec_field_types(&mut k);
        if let Err(e) =
            declare_selector(&mut k, vec, vec_rec, m_scalars, l2, &vfs, M_F, &|k2, _s| {
                k2.const_(fld, vec![])
            })
        {
            println!("  VecSp.scalars: FAIL -- {e}");
            std::process::exit(1);
        }
    }
    let scalars_of = |k: &mut Kernel, s: ExprId| {
        let c = k.const_(m_scalars, vec![]);
        k.app(c, s)
    };
    {
        let vfs = vec_field_types(&mut k);
        if let Err(e) =
            declare_selector(&mut k, vec, vec_rec, m_carrier, l2, &vfs, M_V, &|k2, _s| {
                k2.sort(l1)
            })
        {
            println!("  VecSp.carrier: FAIL -- {e}");
            std::process::exit(1);
        }
    }
    let vcarrier_of = |k: &mut Kernel, s: ExprId| {
        let c = k.const_(m_carrier, vec![]);
        k.app(c, s)
    };
    {
        let vfs = vec_field_types(&mut k);
        if let Err(e) =
            declare_selector(&mut k, vec, vec_rec, m_addv, l1, &vfs, M_ADDV, &|k2, s| {
                let v = vcarrier_of(k2, s);
                let inner = arrow(k2, v, v);
                arrow(k2, v, inner)
            })
        {
            println!("  VecSp.addV: FAIL -- {e}");
            std::process::exit(1);
        }
    }
    let addv_of = |k: &mut Kernel, s: ExprId| {
        let c = k.const_(m_addv, vec![]);
        k.app(c, s)
    };
    {
        let vfs = vec_field_types(&mut k);
        if let Err(e) =
            declare_selector(&mut k, vec, vec_rec, m_smul, l1, &vfs, M_SMUL, &|k2, s| {
                // scalars s |> carrier   ->   VecSp.carrier s   ->   VecSp.carrier s
                let sc = scalars_of(k2, s);
                let scal = carrier_of(k2, sc);
                let v = vcarrier_of(k2, s);
                let inner = arrow(k2, v, v);
                arrow(k2, scal, inner)
            })
        {
            println!("  VecSp.smul (type through TWO nested projections): FAIL -- {e}");
            std::process::exit(1);
        }
    }
    let smul_of = |k: &mut Kernel, s: ExprId| {
        let c = k.const_(m_smul, vec![]);
        k.app(c, s)
    };
    println!("  VecSp.scalars / carrier / addV / smul: PASS");

    {
        let vfs = vec_field_types(&mut k);
        if let Err(e) = declare_selector(
            &mut k,
            vec,
            vec_rec,
            m_one_smul,
            l0,
            &vfs,
            M_ONE_SMUL,
            &|k2, s| {
                let sc = scalars_of(k2, s);
                let o = one_of(k2, sc);
                let v = vcarrier_of(k2, s);
                let sm = smul_of(k2, s);
                let vv = k2.fvar(V_V);
                let lhs = app2(k2, sm, o, vv);
                let body = eq_of(k2, &lg, l1, v, lhs, vv);
                pi_over(k2, V_V, v, body)
            },
        ) {
            println!("  VecSp.oneSmul: FAIL -- {e}");
            std::process::exit(1);
        }
    }
    {
        let vfs = vec_field_types(&mut k);
        if let Err(e) = declare_selector(
            &mut k,
            vec,
            vec_rec,
            m_smul_add,
            l0,
            &vfs,
            M_SMUL_ADD,
            &|k2, s| {
                let sc = scalars_of(k2, s);
                let scal = carrier_of(k2, sc);
                let v = vcarrier_of(k2, s);
                let sm = smul_of(k2, s);
                let ad = addv_of(k2, s);
                let va = k2.fvar(V_A);
                let vv = k2.fvar(V_V);
                let vw = k2.fvar(V_W);
                let sum = app2(k2, ad, vv, vw);
                let lhs = app2(k2, sm, va, sum);
                let sv = app2(k2, sm, va, vv);
                let sw = app2(k2, sm, va, vw);
                let rhs = app2(k2, ad, sv, sw);
                let body = eq_of(k2, &lg, l1, v, lhs, rhs);
                let t = pi_over(k2, V_W, v, body);
                let t = pi_over(k2, V_V, v, t);
                pi_over(k2, V_A, scal, t)
            },
        ) {
            println!("  VecSp.smulAdd: FAIL -- {e}");
            std::process::exit(1);
        }
    }
    println!("  VecSp.oneSmul / smulAdd (laws through nested projections): PASS");

    // === A DERIVED theorem quantified over the vector space ==================
    // ∀ (M : VecSp) (v w : M.carrier),
    //   M.addV (M.smul M.scalars.one v) (M.smul M.scalars.one w) = M.addV v w
    //
    // Derived by chaining smulAdd (backwards) with oneSmul, not read off one
    // law: smul 1 (v+w) = (smul 1 v) + (smul 1 w)  and  smul 1 (v+w) = v+w.
    let goal_over = |k2: &mut Kernel, s: ExprId, swap: bool| -> ExprId {
        let v = vcarrier_of(k2, s);
        let sc = scalars_of(k2, s);
        let o = one_of(k2, sc);
        let sm = smul_of(k2, s);
        let ad = addv_of(k2, s);
        let vv = k2.fvar(V_V);
        let vw = k2.fvar(V_W);
        let sv = app2(k2, sm, o, vv);
        let sw = app2(k2, sm, o, vw);
        let lhs = app2(k2, ad, sv, sw);
        // The CONTROL claims `= addV w v`, which needs commutativity this
        // structure never assumes.
        let rhs = if swap {
            app2(k2, ad, vw, vv)
        } else {
            app2(k2, ad, vv, vw)
        };
        let body = eq_of(k2, &lg, l1, v, lhs, rhs);
        let t = pi_over(k2, V_W, v, body);
        pi_over(k2, V_V, v, t)
    };

    let vec_ty = k.const_(vec, vec![]);
    let goal_ty = {
        let s = k.fvar(S_FV);
        let inner = goal_over(&mut k, s, false);
        pi_over(&mut k, S_FV, vec_ty, inner)
    };
    let bad_ty = {
        let s = k.fvar(S_FV);
        let inner = goal_over(&mut k, s, true);
        pi_over(&mut k, S_FV, vec_ty, inner)
    };

    // Raw proof over the unbundled components (what the minor premise sees).
    let raw = {
        let v = k.fvar(M_V);
        let addv = k.fvar(M_ADDV);
        let smul = k.fvar(M_SMUL);
        let one_smul = k.fvar(M_ONE_SMUL);
        let smul_add = k.fvar(M_SMUL_ADD);
        let f = k.fvar(M_F);
        let o = one_of(&mut k, f);

        let vv = k.fvar(V_V);
        let vw = k.fvar(V_W);
        let sum = app2(&mut k, addv, vv, vw);
        let sv = app2(&mut k, smul, o, vv);
        let sw = app2(&mut k, smul, o, vw);
        let lhs = app2(&mut k, addv, sv, sw);
        let smul_sum = app2(&mut k, smul, o, sum);

        // h1 : smul 1 (v+w) = (smul 1 v) + (smul 1 w)
        let h1 = {
            let e = k.app(smul_add, o);
            let e = k.app(e, vv);
            k.app(e, vw)
        };
        // h2 : smul 1 (v+w) = v+w
        let h2 = k.app(one_smul, sum);
        // (smul 1 v)+(smul 1 w) = smul 1 (v+w)      [symm h1]
        let s1 = {
            let c = k.const_(lg.eq_symm, vec![l1]);
            let e = k.app(c, v);
            let e = k.app(e, smul_sum);
            let e = k.app(e, lhs);
            k.app(e, h1)
        };
        // chain to v+w
        let proof = trans_of(&mut k, &lg, l1, v, lhs, smul_sum, sum, s1, h2, SC1);
        let p = lam_over(&mut k, V_W, v, proof);
        lam_over(&mut k, V_V, v, p)
    };
    let _ = SC2;

    let build = |k2: &mut Kernel, swap: bool| -> ExprId {
        let s = k2.fvar(S_FV);
        let mb = goal_over(k2, s, swap);
        let vt = k2.const_(vec, vec![]);
        let motive = lam_over(k2, S_FV, vt, mb);
        let vfs = vec_field_types(k2);
        let minor = close_lam(k2, &vfs, raw);
        let rec_c = k2.const_(vec_rec, vec![l0]);
        let e = k2.app(rec_c, motive);
        let e = k2.app(e, minor);
        let s2 = k2.fvar(S_FV);
        let e = k2.app(e, s2);
        let vt2 = k2.const_(vec, vec![]);
        lam_over(k2, S_FV, vt2, e)
    };

    let value = build(&mut k, false);
    let bad_value = build(&mut k, true);
    let thm = k.name_str(vec, "oneSmulAdd");
    println!("goal: {}", k.render_lean(goal_ty));

    let mut failures: Vec<&'static str> = Vec::new();
    match k.add_declaration(Declaration::Theorem {
        name: thm,
        uparams: vec![],
        ty: goal_ty,
        value,
    }) {
        Ok(()) => println!("  RESULT: PASS -- AbsMod.VecSp.oneSmulAdd admitted"),
        Err(e) => {
            println!("  RESULT: FAIL -- {e:?}");
            std::process::exit(1);
        }
    }
    let bad_name = k.name_str(vec, "oneSmulAddSwapped");
    match k.add_declaration(Declaration::Theorem {
        name: bad_name,
        uparams: vec![],
        ty: bad_ty,
        value: bad_value,
    }) {
        Ok(()) => {
            println!("  CONTENT CONTROL: FAILED -- commutativity accepted without assuming it");
            failures.push("content-control");
        }
        Err(_) => println!("  content control: PASS -- swapped conclusion refused"),
    }

    let fp = k.axiom_footprint(thm);
    let names: Vec<String> = fp.iter().map(|&n| k.display_name(n).to_string()).collect();
    println!("axiom_footprint(AbsMod.VecSp.oneSmulAdd) = {names:?}");
    if !fp.is_empty() {
        failures.push("axiom-footprint-nonempty");
    }

    // A three-argument congr_arg is unused here but keeps the helper honest:
    // exercise it once so a dead-code refactor cannot silently drop it.
    {
        let v = k.fvar(M_V);
        let a = k.fvar(V_V);
        let h = refl_of(&mut k, &lg, l1, v, a);
        let _ = congr_arg(&mut k, &lg, l1, v, a, a, h, SC2, &|_k, x| x);
    }

    if failures.is_empty() {
        println!("ALL STAGES AND CONTROLS AS EXPECTED");
    } else {
        println!("UNEXPECTED: {failures:?}");
        std::process::exit(3);
    }
}
