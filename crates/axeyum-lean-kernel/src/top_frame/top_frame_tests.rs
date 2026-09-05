//! Does the kernel accept [`build_top_frame_prelude`], is every declaration it
//! produces axiom-free, and — the part that matters — is each law of the
//! `Top.Frame` record and each constant of the ℝ instance load-bearing?
//!
//! The negative controls are the point of the file. Each one changes **one**
//! slot and requires `Kernel::add_declaration` to refuse, and each is paired
//! with a positive control at the same slot so that "it was refused" cannot be
//! satisfied by refusing everything. ADR-1602 §6 measured that mutating a
//! record's *field shapes* poisons the shared build and kills all N tests
//! without attributing anything; every control here therefore mutates an
//! INSTANCE ARGUMENT or a STATEMENT, never a field shape.

use super::{
    BOT, BOT_LE, CARRIER, FIELD_COUNT, FRAME_LE, INF, INF_LE_LEFT, INF_LE_RIGHT, LE, LE_INF,
    LE_REFL, LE_SUP, LE_TOP, LE_TRANS, SUP, SUP_LE, TOP, TopFramePrelude, build_top_frame_prelude,
    cle, embed, exists_at, mem_ball_body, opens_ty, radius, rat_ty,
};
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::nat_prelude::structures::mk_instance;
use crate::{Kernel, on_a_deep_stack};

fn built() -> (Kernel, TopFramePrelude) {
    use std::sync::OnceLock;
    static TEMPLATE: OnceLock<(Kernel, TopFramePrelude)> = OnceLock::new();
    let (kernel, prelude) = TEMPLATE.get_or_init(|| {
        on_a_deep_stack(|| {
            let mut kernel = Kernel::new();
            let prelude =
                build_top_frame_prelude(&mut kernel).expect("Top.Frame prelude must build");
            (kernel, prelude)
        })
    });
    (kernel.clone(), *prelude)
}

/// The build itself, with the kernel's rejection rendered rather than
/// `Debug`-formatted.
#[test]
fn top_frame_prelude_builds() {
    on_a_deep_stack(|| {
        let mut kernel = Kernel::new();
        match build_top_frame_prelude(&mut kernel) {
            Ok(_) => {}
            Err(error) => {
                let nat = crate::build_nat_prelude(&mut kernel).expect("Nat prelude must build");
                let mut dev = crate::NatDev::new(&mut kernel, nat);
                let explained = crate::NatOps::explain(&mut dev, &error);
                panic!("the kernel refused a real proof: {explained}");
            }
        }
    });
}

/// Every name this module declares, paired with its label. **Derived from the
/// prelude handle, not from a literal list** — the record's sixteen selectors
/// come from `RecordNames` itself, so a seventeenth field cannot be added
/// without appearing here.
fn all_declarations(p: TopFramePrelude) -> Vec<(String, crate::name::NameId)> {
    let mut out: Vec<(String, crate::name::NameId)> = vec![
        ("Top.Frame".into(), p.record.ind),
        ("Top.Frame.mk".into(), p.record.mk),
        ("Top.Frame.rec".into(), p.record.rec),
        ("Top.Frame.Equiv".into(), p.equiv),
        ("Top.Frame.equiv_refl".into(), p.equiv_refl),
        ("Top.Frame.equiv_symm".into(), p.equiv_symm),
        ("Top.Frame.equiv_trans".into(), p.equiv_trans),
        ("Top.Frame.sup_mono".into(), p.sup_mono),
        ("Top.Frame.sup_const".into(), p.sup_const),
        ("Top.Frame.le_inf_sup".into(), p.le_inf_sup),
        ("Top.Frame.frame_law".into(), p.frame_law),
        ("Top.Frame.inf_comm".into(), p.inf_comm),
        ("Top.Opens".into(), p.opens),
        ("Top.Opens.le".into(), p.opens_le),
        ("Top.Opens.inf".into(), p.opens_inf),
        ("Top.Opens.top".into(), p.opens_top),
        ("Top.Opens.bot".into(), p.opens_bot),
        ("Top.Opens.sup".into(), p.opens_sup),
        ("Top.Opens.le_refl".into(), p.opens_le_refl),
        ("Top.Opens.le_trans".into(), p.opens_le_trans),
        ("Top.Opens.inf_le_left".into(), p.opens_inf_le_left),
        ("Top.Opens.inf_le_right".into(), p.opens_inf_le_right),
        ("Top.Opens.le_inf".into(), p.opens_le_inf),
        ("Top.Opens.le_top".into(), p.opens_le_top),
        ("Top.Opens.bot_le".into(), p.opens_bot_le),
        ("Top.Opens.le_sup".into(), p.opens_le_sup),
        ("Top.Opens.sup_le".into(), p.opens_sup_le),
        ("Top.Opens.frame_le".into(), p.opens_frame_le),
        ("Top.ballFrame".into(), p.ball_frame),
        ("Top.ballFrame_inf".into(), p.ball_frame_inf),
        ("Top.MemBall".into(), p.mem_ball),
        ("Top.MemOpen".into(), p.mem_open),
        ("Top.ball_mem_self".into(), p.ball_mem_self),
        ("Top.ball_density".into(), p.ball_density),
        ("Top.mem_top".into(), p.mem_top),
        ("Top.mem_open_mono".into(), p.mem_open_mono),
        ("Top.ball_separated".into(), p.ball_separated),
    ];
    for i in 0..p.record.field_count() {
        out.push((format!("Top.Frame.<field {i}>"), p.record.sel(i)));
    }
    out
}

/// Every `Top.*` declaration in the kernel is on `all_declarations`. Derives
/// its population from the ENVIRONMENT, not from the list under test, so a
/// declaration added to `build_top_frame_prelude` and forgotten here fails.
#[test]
fn every_top_namespace_declaration_is_accounted_for() {
    let (kernel, p) = built();
    let listed: std::collections::BTreeSet<crate::name::NameId> =
        all_declarations(p).into_iter().map(|(_, n)| n).collect();

    let mut missing: Vec<String> = Vec::new();
    let mut seen = 0usize;
    for (name, _decl) in kernel.environment().iter() {
        let rendered = format!("{}", kernel.display_name(*name));
        if rendered == "Top" || rendered.starts_with("Top.") {
            // `declare_record`'s ADR-1578 universe control interns (but never
            // admits) `Top.Frame.sort1Control`; anything that IS in the
            // environment must be on the list.
            seen += 1;
            if !listed.contains(name) {
                missing.push(rendered);
            }
        }
    }
    assert!(
        seen > 0,
        "coverage control: the environment reported no Top.* declarations at all"
    );
    missing.sort();
    assert!(
        missing.is_empty(),
        "{} Top.* declaration(s) exist in the kernel but are not on all_declarations: {missing:?}",
        missing.len()
    );
}

/// Every listed name is actually in the environment. Run FIRST, because an
/// empty axiom footprint is also what a missing name returns.
#[test]
fn every_top_declaration_is_present_and_derived() {
    let (kernel, p) = built();
    let named = all_declarations(p);
    assert!(
        named.len() >= 37,
        "the declaration list shrank unexpectedly"
    );
    for (label, name) in named {
        assert!(
            kernel.environment().get(name).is_some(),
            "{label} is not in the environment"
        );
    }
}

/// Read from `Kernel::axiom_footprint`, never from a rendered name.
#[test]
fn every_top_declaration_is_axiom_free() {
    let (kernel, p) = built();
    for (label, name) in all_declarations(p) {
        assert!(
            kernel.environment().get(name).is_some(),
            "presence precondition failed for {label}"
        );
        let footprint = kernel.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "{label} has a nonempty axiom footprint: {footprint:?}"
        );
    }
}

/// The record has exactly sixteen fields, in the documented order.
#[test]
fn top_frame_record_field_layout_is_pinned() {
    let (kernel, p) = built();
    assert_eq!(p.record.field_count(), FIELD_COUNT);
    let expected = [
        (CARRIER, "carrier"),
        (LE, "le"),
        (LE_REFL, "leRefl"),
        (LE_TRANS, "leTrans"),
        (INF, "inf"),
        (TOP, "top"),
        (BOT, "bot"),
        (SUP, "sup"),
        (INF_LE_LEFT, "infLeLeft"),
        (INF_LE_RIGHT, "infLeRight"),
        (LE_INF, "leInf"),
        (LE_TOP, "leTop"),
        (BOT_LE, "botLe"),
        (LE_SUP, "leSup"),
        (SUP_LE, "supLe"),
        (FRAME_LE, "frameLe"),
    ];
    assert_eq!(expected.len(), FIELD_COUNT);
    for (index, suffix) in expected {
        let rendered = format!("{}", kernel.display_name(p.record.sel(index)));
        assert_eq!(
            rendered,
            format!("Top.Frame.{suffix}"),
            "field {index} is not {suffix}"
        );
    }
}

/// The instance arguments, in field order, with `slot` replaced by
/// `replacement`. `None` rebuilds the real instance (the positive control).
fn instance_with(
    kernel: &mut Kernel,
    p: TopFramePrelude,
    swap: Option<(usize, crate::name::NameId)>,
) -> ExprId {
    let names = [
        p.opens_le,
        p.opens_le_refl,
        p.opens_le_trans,
        p.opens_inf,
        p.opens_top,
        p.opens_bot,
        p.opens_sup,
        p.opens_inf_le_left,
        p.opens_inf_le_right,
        p.opens_le_inf,
        p.opens_le_top,
        p.opens_bot_le,
        p.opens_le_sup,
        p.opens_sup_le,
        p.opens_frame_le,
    ];
    let opens = kernel.const_(p.opens, vec![]);
    let mut args: Vec<ExprId> = Vec::with_capacity(FIELD_COUNT);
    args.push(opens);
    for (i, n) in names.into_iter().enumerate() {
        let chosen = match swap {
            Some((slot, replacement)) if slot == i + 1 => replacement,
            _ => n,
        };
        let c = kernel.const_(chosen, vec![]);
        args.push(c);
    }
    assert_eq!(args.len(), FIELD_COUNT);
    mk_instance(kernel, &p.record, &args)
}

fn try_instance(
    kernel: &mut Kernel,
    p: TopFramePrelude,
    label: &str,
    swap: Option<(usize, crate::name::NameId)>,
) -> Result<(), crate::KernelError> {
    let value = instance_with(kernel, p, swap);
    let ty = kernel.const_(p.record.ind, vec![]);
    let anon = kernel.anon();
    let name = kernel.name_str(anon, label);
    kernel.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: crate::env::ReducibilityHint::Regular(1),
    })
}

/// **The frame law is load-bearing.** Putting `Top.Opens.le_refl` — a true
/// theorem of the same carrier, with a different type — into the `frameLe`
/// slot must be refused, and the untouched instance must be accepted at the
/// same call site. Without the positive half this control could pass because
/// `mk_instance` is broken.
#[test]
fn the_frame_law_slot_is_load_bearing() {
    on_a_deep_stack(|| {
        let (mut kernel, p) = built();
        let good = try_instance(&mut kernel, p, "Control.frameOk", None);
        assert!(
            good.is_ok(),
            "positive control failed: the untouched instance was refused: {good:?}"
        );
        let bad = try_instance(
            &mut kernel,
            p,
            "Control.frameSwapped",
            Some((FRAME_LE, p.opens_le_refl)),
        );
        assert!(
            bad.is_err(),
            "the frameLe slot accepted Top.Opens.le_refl -- the frame law is not load-bearing"
        );
    });
}

/// **The countable join's universal property is load-bearing.** Same shape as
/// [`the_frame_law_slot_is_load_bearing`], at the `supLe` slot.
#[test]
fn the_sup_le_slot_is_load_bearing() {
    on_a_deep_stack(|| {
        let (mut kernel, p) = built();
        let bad = try_instance(
            &mut kernel,
            p,
            "Control.supLeWrong",
            Some((SUP_LE, p.opens_le_refl)),
        );
        assert!(
            bad.is_err(),
            "the supLe slot accepted Top.Opens.le_refl -- the join law is not load-bearing"
        );
    });
}

/// The ball radius, as a rational: `natDivSucc 1 k` is `1/(k+1)`;
/// `Rat.div Rat.one (natDivSucc k 0)` is the DEGENERATE `1/k`, which divides
/// by zero at `k = 0`.
fn radius_variant(d: &mut IntDev<'_>, p: TopFramePrelude, k: ExprId, degenerate: bool) -> ExprId {
    if degenerate {
        let zero = d.zero();
        let cast = d.const_app(p.creal.rat.nat_div_succ, &[k, zero]);
        let one = d.kernel().const_(p.creal.rat.one, vec![]);
        d.const_app(p.creal.rat.div, &[one, cast])
    } else {
        radius(d, p, k)
    }
}

/// `∃ q, x ∈ ball(q, <radius>)`, spelled out so the radius can be varied.
fn density_statement(
    d: &mut IntDev<'_>,
    p: TopFramePrelude,
    x: ExprId,
    k: ExprId,
    degenerate: bool,
) -> ExprId {
    let rat = rat_ty(d, p);
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let eps = radius_variant(d, p, k, degenerate);
    let upper = {
        let add = p.creal.rat.int.rat_add;
        let hi = d.const_app(add, &[q, eps]);
        let e = embed(d, p, hi);
        cle(d, p, x, e)
    };
    let lower = {
        let sub = p.creal.rat.sub;
        let lo = d.const_app(sub, &[q, eps]);
        let e = embed(d, p, lo);
        cle(d, p, e, x)
    };
    let body = d.and(upper, lower);
    let pred = d.lam_fv(q_fv, rat, body);
    exists_at(d, p, rat, pred)
}

/// **The `+1` in the radius is load-bearing.** `CReal.density` proves the
/// covering property at radius `1/(k+1)` and NOTHING proves it at `1/k`: the
/// degenerate form divides by zero at `k = 0`, which is exactly the index the
/// frame's `sup_const` witness uses. Positive control first, at the same call
/// site with the same proof term.
#[test]
fn the_ball_radius_must_carry_the_plus_one() {
    on_a_deep_stack(|| {
        let (mut kernel, p) = built();
        let int = p.creal.rat.int;
        let mut d = IntDev::new(&mut kernel, int);
        let creal = d.kernel().const_(p.creal.creal, vec![]);
        let nat = d.nat_ty();

        let attempt = |d: &mut IntDev<'_>, label: &str, degenerate: bool| {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let stmt = density_statement(d, p, x, k, degenerate);
            let proof = d.lemma(p.creal.density, &[x, k]);
            let ty = {
                let t = d.pi_fv(k_fv, nat, stmt);
                d.pi_fv(x_fv, creal, t)
            };
            let value = {
                let t = d.lam_fv(k_fv, nat, proof);
                d.lam_fv(x_fv, creal, t)
            };
            let anon = d.kernel().anon();
            let name = d.kernel().name_str(anon, label);
            d.kernel().add_declaration(Declaration::Theorem {
                name,
                uparams: vec![],
                ty,
                value,
            })
        };

        let good = attempt(&mut d, "Control.radiusPlusOne", false);
        assert!(
            good.is_ok(),
            "positive control failed: CReal.density did not prove the 1/(k+1) form: {good:?}"
        );
        let bad = attempt(&mut d, "Control.radiusOverK", true);
        assert!(
            bad.is_err(),
            "the kernel accepted CReal.density as a proof of the 1/k (divide-by-zero at k=0) form"
        );
    });
}

/// **The separation hypothesis is load-bearing.** `Top.ball_separated`'s proof
/// needs `upper(ball 1) < lower(ball 2)`; handed the reversed inequality — true
/// whenever the balls DO overlap — the same term must be refused.
#[test]
fn ball_separation_needs_the_hypothesis_in_the_right_direction() {
    on_a_deep_stack(|| {
        let (mut kernel, p) = built();
        let int = p.creal.rat.int;
        let mut d = IntDev::new(&mut kernel, int);
        let creal = d.kernel().const_(p.creal.creal, vec![]);
        let rat = rat_ty(&mut d, p);
        let nat = d.nat_ty();

        let attempt = |d: &mut IntDev<'_>, label: &str, reversed: bool| {
            let q_fv = d.fresh_fvar();
            let q = d.kernel().fvar(q_fv);
            let r_fv = d.fresh_fvar();
            let r = d.kernel().fvar(r_fv);
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let m_fv = d.fresh_fvar();
            let m = d.kernel().fvar(m_fv);
            let hsep_fv = d.fresh_fvar();
            let hsep = d.kernel().fvar(hsep_fv);
            let z_fv = d.fresh_fvar();
            let z = d.kernel().fvar(z_fv);
            let h1_fv = d.fresh_fvar();
            let h1 = d.kernel().fvar(h1_fv);
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);

            let eps = radius(d, p, k);
            let delta = radius(d, p, m);
            let add = p.creal.rat.int.rat_add;
            let sub = p.creal.rat.sub;
            let hi = d.const_app(add, &[q, eps]);
            let lo = d.const_app(sub, &[r, delta]);
            let hi_e = embed(d, p, hi);
            let lo_e = embed(d, p, lo);
            let sep = {
                let n = p.creal.lt;
                if reversed {
                    d.const_app(n, &[lo_e, hi_e])
                } else {
                    d.const_app(n, &[hi_e, lo_e])
                }
            };
            let mem1 = mem_ball_body(d, p, z, q, k);
            let mem2 = mem_ball_body(d, p, z, r, m);
            let up1 = {
                let l = cle(d, p, z, hi_e);
                let lo_q = d.const_app(sub, &[q, eps]);
                let lo_qe = embed(d, p, lo_q);
                let rr = cle(d, p, lo_qe, z);
                d.and_left(l, rr, h1)
            };
            let low2 = {
                let hi_r = d.const_app(add, &[r, delta]);
                let hi_re = embed(d, p, hi_r);
                let l = cle(d, p, z, hi_re);
                let rr = cle(d, p, lo_e, z);
                d.and_right(l, rr, h2)
            };
            let chained = d.lemma(p.creal.le_trans, &[lo_e, z, hi_e, low2, up1]);
            let bad = d.lemma(p.creal.lt_of_le_of_lt, &[lo_e, hi_e, lo_e, chained, hsep]);
            let irrefl = d.lemma(p.creal.lt_irrefl, &[lo_e]);
            let body = d.apply(irrefl, &[bad]);
            let false_ty = d.false_ty();

            let value = {
                let i = d.lam_fv(h2_fv, mem2, body);
                let i = d.lam_fv(h1_fv, mem1, i);
                let i = d.lam_fv(z_fv, creal, i);
                let i = d.lam_fv(hsep_fv, sep, i);
                let i = d.lam_fv(m_fv, nat, i);
                let i = d.lam_fv(k_fv, nat, i);
                let i = d.lam_fv(r_fv, rat, i);
                d.lam_fv(q_fv, rat, i)
            };
            let ty = {
                let i = d.arrow(mem2, false_ty);
                let i = d.arrow(mem1, i);
                let i = d.pi_fv(z_fv, creal, i);
                let i = d.arrow(sep, i);
                let i = d.pi_fv(m_fv, nat, i);
                let i = d.pi_fv(k_fv, nat, i);
                let i = d.pi_fv(r_fv, rat, i);
                d.pi_fv(q_fv, rat, i)
            };
            let anon = d.kernel().anon();
            let name = d.kernel().name_str(anon, label);
            d.kernel().add_declaration(Declaration::Theorem {
                name,
                uparams: vec![],
                ty,
                value,
            })
        };

        let good = attempt(&mut d, "Control.sepForward", false);
        assert!(
            good.is_ok(),
            "positive control failed: the real separation proof was refused: {good:?}"
        );
        let bad = attempt(&mut d, "Control.sepReversed", true);
        assert!(
            bad.is_err(),
            "the kernel accepted the separation proof with the hypothesis reversed"
        );
    });
}

/// The reduction probe is not vacuous: `Top.ballFrame_inf` is `Eq.refl`, so it
/// only means something if the SAME `Eq.refl` fails to prove the equation
/// against a different constant. `Top.Opens.sup`'s type is different, so the
/// discriminating comparison is `Top.Opens.top` — the same `Top.Opens` value
/// slot, a different value.
#[test]
fn the_ball_frame_reduction_probe_is_not_vacuous() {
    on_a_deep_stack(|| {
        let (mut kernel, p) = built();
        let int = p.creal.rat.int;
        let mut d = IntDev::new(&mut kernel, int);
        let opens = opens_ty(&mut d, p);
        let one = d.level_one();

        let attempt = |d: &mut IntDev<'_>, label: &str, honest: bool| {
            let s_fv = d.fresh_fvar();
            let s = d.kernel().fvar(s_fv);
            let t_fv = d.fresh_fvar();
            let t = d.kernel().fvar(t_fv);
            let frame = d.kernel().const_(p.ball_frame, vec![]);
            let lhs = {
                let sel = d.kernel().const_(p.record.sel(INF), vec![]);
                let applied = d.apply(sel, &[frame]);
                d.apply(applied, &[s, t])
            };
            let rhs = if honest {
                d.const_app(p.opens_inf, &[s, t])
            } else {
                d.kernel().const_(p.opens_top, vec![])
            };
            let eq_c = {
                let n = p.creal.rat.int.logic.eq;
                d.kernel().const_(n, vec![one])
            };
            let stmt = d.apply(eq_c, &[opens, lhs, rhs]);
            let refl_c = {
                let n = p.creal.rat.int.logic.eq_refl;
                d.kernel().const_(n, vec![one])
            };
            let proof = d.apply(refl_c, &[opens, lhs]);
            let value = {
                let i = d.lam_fv(t_fv, opens, proof);
                d.lam_fv(s_fv, opens, i)
            };
            let ty = {
                let i = d.pi_fv(t_fv, opens, stmt);
                d.pi_fv(s_fv, opens, i)
            };
            let anon = d.kernel().anon();
            let name = d.kernel().name_str(anon, label);
            d.kernel().add_declaration(Declaration::Theorem {
                name,
                uparams: vec![],
                ty,
                value,
            })
        };

        let good = attempt(&mut d, "Control.probeHonest", true);
        assert!(
            good.is_ok(),
            "positive control failed: the selector did not reduce: {good:?}"
        );
        let bad = attempt(&mut d, "Control.probeVacuous", false);
        assert!(
            bad.is_err(),
            "Eq.refl proved the selector equal to Top.Opens.top -- the probe is vacuous"
        );
    });
}

/// Rebuilding the prelude in a kernel that already has it must be a no-op that
/// returns the same handle, not a second set of declarations.
#[test]
fn building_twice_is_idempotent() {
    on_a_deep_stack(|| {
        let mut kernel = Kernel::new();
        let first = build_top_frame_prelude(&mut kernel).expect("first build");
        let before = kernel.environment().iter().count();
        let second = build_top_frame_prelude(&mut kernel).expect("second build");
        let after = kernel.environment().iter().count();
        assert_eq!(first, second, "the handle changed on the second build");
        assert_eq!(before, after, "the second build added declarations");
    });
}
