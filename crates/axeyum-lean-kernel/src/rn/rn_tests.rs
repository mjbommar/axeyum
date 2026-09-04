//! Does the kernel accept [`build_rn_prelude`], is every declaration it
//! produces axiom-free, does each `Definition` compute what its name says, and
//! — the part that matters — would a WRONG ℝⁿ be refused?
//!
//! The negative controls are the point of the file, and they come in two
//! shapes:
//!
//! - **Evaluation controls.** Every `Definition` is probed by an ad-hoc
//!   `Equiv.refl` theorem at SYMBOLIC arguments, paired with a sibling that
//!   differs in one small subterm and must be refused. Symbolic arguments are
//!   mandatory: `CReal` numerals compute, so a probe at concrete literals can
//!   pass by arithmetic coincidence rather than by the definition unfolding
//!   the way the doc comment claims.
//! - **Instance controls.** The `Metric` record is rebuilt with one slot
//!   replaced by a plausible wrong choice — the SQUARED distance, a norm that
//!   drops the square root, the wrong dimension in the equivalence — and
//!   `Kernel::add_declaration` must refuse each. Without these, "ℝⁿ is a
//!   metric space" is a claim about a comment.

use super::{RNPrelude, build_rn_prelude};
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::nat_prelude::structures::mk_instance;
use crate::{Kernel, on_a_deep_stack};

fn built() -> (Kernel, RNPrelude) {
    use std::sync::OnceLock;
    static TEMPLATE: OnceLock<(Kernel, RNPrelude)> = OnceLock::new();
    let (kernel, prelude) = TEMPLATE.get_or_init(|| {
        on_a_deep_stack(|| {
            let mut kernel = Kernel::new();
            let prelude = build_rn_prelude(&mut kernel).expect("RN prelude must build");
            (kernel, prelude)
        })
    });
    (kernel.clone(), *prelude)
}

/// The build itself, with the kernel's rejection rendered rather than
/// `Debug`-formatted.
#[test]
fn rn_prelude_builds() {
    on_a_deep_stack(|| {
        let mut kernel = Kernel::new();
        match build_rn_prelude(&mut kernel) {
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

/// Every name this module declares, paired with its label.
///
/// **Derived from the prelude handle, not from a source scan** — a field added
/// to [`RNPrelude`] and left out of this list makes
/// [`the_declaration_list_covers_every_handle_field`] fail, so the two cannot
/// drift silently.
fn all_declarations(p: RNPrelude) -> Vec<(String, crate::name::NameId)> {
    vec![
        ("RN.CReal.negUnique".into(), p.creal_neg_unique),
        ("RN.CReal.eqOfSubZero".into(), p.creal_eq_of_sub_zero),
        ("RN.CReal.zeroAdd".into(), p.creal_zero_add),
        ("RN.CReal.rightDistrib".into(), p.creal_right_distrib),
        ("RN.CReal.addNonneg".into(), p.creal_add_nonneg),
        ("RN.CReal.negSub".into(), p.creal_neg_sub),
        (
            "RN.CReal.sumRangeCongrLt".into(),
            p.creal_sum_range_congr_lt,
        ),
        (
            "RN.CReal.sumRangeZeroConst".into(),
            p.creal_sum_range_zero_const,
        ),
        ("RN.CReal.sumRangeNonneg".into(), p.creal_sum_range_nonneg),
        (
            "RN.CReal.sumRangeTermZero".into(),
            p.creal_sum_range_term_zero,
        ),
        ("RN.Vec".into(), p.vec),
        ("RN.EqOn".into(), p.eq_on),
        ("RN.eqOn_refl".into(), p.eq_on_refl),
        ("RN.eqOn_symm".into(), p.eq_on_symm),
        ("RN.eqOn_trans".into(), p.eq_on_trans),
        ("RN.zero".into(), p.zero),
        ("RN.add".into(), p.add),
        ("RN.neg".into(), p.neg),
        ("RN.sub".into(), p.sub),
        ("RN.smul".into(), p.smul),
        ("RN.add_congr".into(), p.add_congr),
        ("RN.sub_congr".into(), p.sub_congr),
        ("RN.smul_congr".into(), p.smul_congr),
        ("RN.add_comm".into(), p.add_comm),
        ("RN.add_assoc".into(), p.add_assoc),
        ("RN.add_zero".into(), p.add_zero),
        ("RN.add_neg".into(), p.add_neg),
        ("RN.dot".into(), p.dot),
        ("RN.dot_zero".into(), p.dot_zero),
        ("RN.dot_succ".into(), p.dot_succ),
        ("RN.dot_comm".into(), p.dot_comm),
        ("RN.dot_congr".into(), p.dot_congr),
        ("RN.dot_add_left".into(), p.dot_add_left),
        ("RN.dot_add_right".into(), p.dot_add_right),
        ("RN.dot_smul_left".into(), p.dot_smul_left),
        ("RN.dot_self_nonneg".into(), p.dot_self_nonneg),
        ("RN.dot_two".into(), p.dot_two),
        ("RN.norm".into(), p.norm),
        ("RN.norm_nonneg".into(), p.norm_nonneg),
        ("RN.norm_sq".into(), p.norm_sq),
        ("RN.norm_congr".into(), p.norm_congr),
        ("RN.cauchy_schwarz".into(), p.cauchy_schwarz),
        ("RN.norm_add_le".into(), p.norm_add_le),
        ("RN.dist".into(), p.dist),
        ("RN.dist_congr".into(), p.dist_congr),
        ("RN.dist_nonneg".into(), p.dist_nonneg),
        ("RN.dist_self".into(), p.dist_self),
        ("RN.dist_eqOn".into(), p.dist_eq_on),
        ("RN.dist_comm".into(), p.dist_comm),
        ("RN.dist_triangle".into(), p.dist_triangle),
        ("RN.metric".into(), p.metric_inst),
        ("RN.metric_dist".into(), p.metric_dist),
        ("RN.ofCPoint".into(), p.of_cpoint),
        ("RN.ofCPoint_dot".into(), p.of_cpoint_dot),
        ("RN.ofCPoint_distSq".into(), p.of_cpoint_dist_sq),
        ("RN.ofCPoint_dist".into(), p.of_cpoint_dist),
        ("RN.ofCPoint_congr".into(), p.of_cpoint_congr),
        ("RN.cpointEquiv_of_eqOn".into(), p.cpoint_equiv_of_eq_on),
    ]
}

/// **The list above is answerable to the KERNEL, not to memory.**
///
/// The authority is `Environment::iter()` filtered to the `RN.` namespace: a
/// declaration this module makes and forgets to list fails here, and so does a
/// listed name that was never declared. The count is pinned separately so a
/// row silently dropped from both sides is still caught.
#[test]
fn the_declaration_list_covers_every_rn_name() {
    on_a_deep_stack(|| {
        let (kernel, p) = built();
        let listed: std::collections::BTreeSet<_> =
            all_declarations(p).into_iter().map(|(_, n)| n).collect();
        assert_eq!(
            listed.len(),
            58,
            "the RN declaration list changed; update this count deliberately"
        );
        for name in &listed {
            assert!(
                kernel.environment().get(*name).is_some(),
                "{} is listed but not declared",
                kernel.display_name(*name)
            );
        }
        let mut missed: Vec<String> = Vec::new();
        for (name, _) in kernel.environment().iter() {
            let rendered = kernel.display_name(*name).to_string();
            if (rendered == "RN" || rendered.starts_with("RN.")) && !listed.contains(name) {
                missed.push(rendered);
            }
        }
        missed.sort();
        assert!(
            missed.is_empty(),
            "declarations in the `RN` namespace that the list does not name: {missed:?}"
        );
    });
}

/// Everything declared here is present, and nothing is an `Axiom` or an
/// `Opaque`.
#[test]
fn every_rn_declaration_is_present_and_derived() {
    on_a_deep_stack(|| {
        let (kernel, p) = built();
        for (label, name) in all_declarations(p) {
            let decl = kernel
                .environment()
                .get(name)
                .unwrap_or_else(|| panic!("{label} must be declared"));
            assert!(
                !matches!(decl, Declaration::Axiom { .. } | Declaration::Opaque { .. }),
                "{label} is asserted, not derived"
            );
        }
    });
}

/// **The headline metric.** Read from `Kernel::axiom_footprint`, never from a
/// rendered name.
#[test]
fn every_rn_declaration_is_axiom_free() {
    on_a_deep_stack(|| {
        let (kernel, p) = built();
        for (label, name) in all_declarations(p) {
            let footprint = kernel.axiom_footprint(name);
            assert!(
                footprint.is_empty(),
                "{label} has a nonempty axiom footprint: {footprint:?}"
            );
        }
    });
}

fn ty_of(kernel: &Kernel, name: crate::name::NameId) -> ExprId {
    match kernel
        .environment()
        .get(name)
        .expect("declaration must exist")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    }
}

/// **The carrier is what the module doc says it is.** `RN.Vec` unfolds to
/// `Nat -> CReal` and to nothing else.
#[test]
fn vec_is_the_function_carrier() {
    on_a_deep_stack(|| {
        let (kernel, p) = built();
        assert_eq!(kernel.render_lean(ty_of(&kernel, p.vec)), "Sort (1)");
        let value = match kernel.environment().get(p.vec).expect("RN.Vec") {
            Declaration::Definition { value, .. } => *value,
            other => panic!("{other:?} is not a definition"),
        };
        assert_eq!(kernel.render_lean(value), "((x0 : AxNat) -> CReal)");
    });
}

/// **Cauchy-Schwarz, unsquared, verbatim.** The statement is checked as text
/// because the whole point of the theorem is which form it takes: a squared
/// statement, or one at a fixed dimension, would still typecheck and would not
/// be this.
#[test]
fn cauchy_schwarz_statement_is_exact() {
    on_a_deep_stack(|| {
        let (kernel, p) = built();
        assert_eq!(
            kernel.render_lean(ty_of(&kernel, p.cauchy_schwarz)),
            "((x0 : RN.Vec) -> ((x1 : RN.Vec) -> ((x2 : AxNat) -> CReal.le (RN.dot x0 x1 x2) \
             (CReal.mul (RN.norm x0 x2) (RN.norm x1 x2)))))"
        );
    });
}

/// **The dimension is a parameter of the RELATION, not of the type.** If this
/// ever renders with a `Fin`, a `Subtype` or a length index, the design
/// recorded in ADR-1606 has changed and the ADR is stale.
#[test]
fn eq_on_statement_is_exact() {
    on_a_deep_stack(|| {
        let (kernel, p) = built();
        assert_eq!(
            kernel.render_lean(ty_of(&kernel, p.eq_on)),
            "((x0 : AxNat) -> ((x1 : RN.Vec) -> ((x2 : RN.Vec) -> Prop)))"
        );
        let value = match kernel.environment().get(p.eq_on).expect("RN.EqOn") {
            Declaration::Definition { value, .. } => *value,
            other => panic!("{other:?} is not a definition"),
        };
        assert_eq!(
            kernel.render_lean(value),
            "fun (x0 : AxNat) => fun (x1 : RN.Vec) => fun (x2 : RN.Vec) => ((x3 : AxNat) -> \
             ((x4 : AxNat.lt x3 x0) -> CReal.Equiv (x1 x3) (x2 x3)))"
        );
    });
}

/// The metric instance really is a `Metric`, parameterised by the dimension.
#[test]
fn metric_instance_statement_is_exact() {
    on_a_deep_stack(|| {
        let (kernel, p) = built();
        assert_eq!(
            kernel.render_lean(ty_of(&kernel, p.metric_inst)),
            "((x0 : AxNat) -> Metric)"
        );
        assert_eq!(
            kernel.render_lean(ty_of(&kernel, p.dist_triangle)),
            "((x0 : AxNat) -> ((x1 : RN.Vec) -> ((x2 : RN.Vec) -> ((x3 : RN.Vec) -> CReal.le \
             (RN.dist x0 x1 x3) (CReal.add (RN.dist x0 x1 x2) (RN.dist x0 x2 x3))))))"
        );
    });
}

/// The n = 2 bridge: the two developments agree on the inner product, on the
/// squared distance, and on the metric distance itself.
#[test]
fn cpoint_bridge_statements_are_exact() {
    on_a_deep_stack(|| {
        let (kernel, p) = built();
        assert_eq!(
            kernel.render_lean(ty_of(&kernel, p.of_cpoint_dot)),
            "((x0 : CPoint) -> ((x1 : CPoint) -> CReal.Equiv (RN.dot (RN.ofCPoint x0) \
             (RN.ofCPoint x1) (AxNat.succ (AxNat.succ AxNat.zero))) (CPoint.dot x0 x1)))"
        );
        assert_eq!(
            kernel.render_lean(ty_of(&kernel, p.of_cpoint_dist)),
            "((x0 : CPoint) -> ((x1 : CPoint) -> CReal.Equiv (RN.dist (AxNat.succ (AxNat.succ \
             AxNat.zero)) (RN.ofCPoint x0) (RN.ofCPoint x1)) (Metric.CPoint.dist x0 x1)))"
        );
    });
}

// ---------------------------------------------------------------------------
// Evaluation probes. Each `Definition` is unfolded at SYMBOLIC arguments and
// compared against an explicitly written term; the sibling control differs in
// one small subterm and must be refused.
// ---------------------------------------------------------------------------

/// The symbols an evaluation probe reasons about: two vectors, a dimension and
/// a plane point. [`refl_probe`] mints them, binds them, and quantifies the
/// statement over all four — a declaration with a loose free variable is
/// rejected by the gate for that reason alone, which would make every probe
/// below "fail" without saying anything about the definition.
struct ProbeSyms {
    u: ExprId,
    v: ExprId,
    n: ExprId,
    point: ExprId,
}

/// Admit `theorem <fresh> : forall u v n P, CReal.Equiv lhs rhs :=
/// fun u v n P => CReal.Equiv.refl rhs` in a scratch copy of the kernel, and
/// report whether the trusted gate took it.
///
/// This is a **defeq probe**: it succeeds exactly when `lhs` and `rhs` are
/// definitionally equal under those universally quantified symbols, which for
/// a `Definition` is the question "does it compute what the doc says". The
/// symbols are BOUND VARIABLES, not literals, deliberately: `CReal` numerals
/// compute, so a probe at concrete values can pass by arithmetic coincidence
/// rather than by the definition unfolding.
fn refl_probe(
    build: &dyn Fn(&mut IntDev<'_>, RNPrelude, &ProbeSyms) -> (ExprId, ExprId),
) -> Result<(), crate::KernelError> {
    let (mut kernel, p) = built();
    let c = p.metric.cpoint.creal;
    let int = c.rat.int;
    let probe = {
        let root = kernel.anon();
        kernel.name_str(root, "RNProbe")
    };
    let mut d = IntDev::new(&mut kernel, int);
    let vec = d.kernel().const_(p.vec, vec![]);
    let nat = d.nat_ty();
    let point = d.kernel().const_(p.metric.cpoint.point, vec![]);

    let u_fv = d.fresh_fvar();
    let v_fv = d.fresh_fvar();
    let n_fv = d.fresh_fvar();
    let pt_fv = d.fresh_fvar();
    let syms = ProbeSyms {
        u: d.kernel().fvar(u_fv),
        v: d.kernel().fvar(v_fv),
        n: d.kernel().fvar(n_fv),
        point: d.kernel().fvar(pt_fv),
    };

    let (lhs, rhs) = build(&mut d, p, &syms);
    let ty = {
        let concl = d.const_app(c.equiv, &[lhs, rhs]);
        let t = d.pi_fv(pt_fv, point, concl);
        let t = d.pi_fv(n_fv, nat, t);
        let t = d.pi_fv(v_fv, vec, t);
        d.pi_fv(u_fv, vec, t)
    };
    let value = {
        let body = d.lemma(c.equiv_refl, &[rhs]);
        let t = d.lam_fv(pt_fv, point, body);
        let t = d.lam_fv(n_fv, nat, t);
        let t = d.lam_fv(v_fv, vec, t);
        d.lam_fv(u_fv, vec, t)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: probe,
        uparams: vec![],
        ty,
        value,
    })
}

/// `RN.add u v i` computes to `CReal.add (u i) (v i)`, and NOT to
/// `CReal.mul (u i) (v i)` — the smallest wrong choice that still typechecks.
#[test]
fn add_computes_pointwise() {
    on_a_deep_stack(|| {
        assert!(
            refl_probe(&|d, p, sym| {
                let c = p.metric.cpoint.creal;
                let (u, v, i) = (sym.u, sym.v, sym.n);
                let lhs = {
                    let f = d.const_app(p.add, &[u, v]);
                    d.apply(f, &[i])
                };
                let ui = d.apply(u, &[i]);
                let vi = d.apply(v, &[i]);
                let rhs = d.const_app(c.add, &[ui, vi]);
                (lhs, rhs)
            })
            .is_ok(),
            "RN.add must unfold to the pointwise CReal sum"
        );
        assert!(
            refl_probe(&|d, p, sym| {
                let c = p.metric.cpoint.creal;
                let (u, v, i) = (sym.u, sym.v, sym.n);
                let lhs = {
                    let f = d.const_app(p.add, &[u, v]);
                    d.apply(f, &[i])
                };
                let ui = d.apply(u, &[i]);
                let vi = d.apply(v, &[i]);
                let rhs = d.const_app(c.mul, &[ui, vi]);
                (lhs, rhs)
            })
            .is_err(),
            "NEGATIVE CONTROL: RN.add must not unfold to the pointwise product"
        );
    });
}

/// `RN.sub u v i` computes to `u i + -(v i)`, and NOT to `-(u i) + v i`.
#[test]
fn sub_computes_pointwise() {
    on_a_deep_stack(|| {
        assert!(
            refl_probe(&|d, p, sym| {
                let c = p.metric.cpoint.creal;
                let (u, v, i) = (sym.u, sym.v, sym.n);
                let lhs = {
                    let f = d.const_app(p.sub, &[u, v]);
                    d.apply(f, &[i])
                };
                let ui = d.apply(u, &[i]);
                let vi = d.apply(v, &[i]);
                let nvi = d.const_app(c.neg, &[vi]);
                let rhs = d.const_app(c.add, &[ui, nvi]);
                (lhs, rhs)
            })
            .is_ok(),
            "RN.sub must unfold to `u i + -(v i)`"
        );
        assert!(
            refl_probe(&|d, p, sym| {
                let c = p.metric.cpoint.creal;
                let (u, v, i) = (sym.u, sym.v, sym.n);
                let lhs = {
                    let f = d.const_app(p.sub, &[u, v]);
                    d.apply(f, &[i])
                };
                let ui = d.apply(u, &[i]);
                let vi = d.apply(v, &[i]);
                let nui = d.const_app(c.neg, &[ui]);
                let rhs = d.const_app(c.add, &[nui, vi]);
                (lhs, rhs)
            })
            .is_err(),
            "NEGATIVE CONTROL: RN.sub must not negate the FIRST argument"
        );
    });
}

/// `RN.dot u v (succ n)` computes to `dot u v n + u n * v n`, and NOT to
/// `dot u v n + u n * v (succ n)` — an off-by-one in the summand's index,
/// which is exactly the mistake `CReal.sumRange`'s bound convention invites.
#[test]
fn dot_computes_by_recursion_on_the_bound() {
    on_a_deep_stack(|| {
        assert!(
            refl_probe(&|d, p, sym| {
                let c = p.metric.cpoint.creal;
                let (u, v, n) = (sym.u, sym.v, sym.n);
                let sn = d.succ(n);
                let lhs = d.const_app(p.dot, &[u, v, sn]);
                let prior = d.const_app(p.dot, &[u, v, n]);
                let un = d.apply(u, &[n]);
                let vn = d.apply(v, &[n]);
                let last = d.const_app(c.mul, &[un, vn]);
                let rhs = d.const_app(c.add, &[prior, last]);
                (lhs, rhs)
            })
            .is_ok(),
            "RN.dot must unfold one step of the sum at `succ n`"
        );
        assert!(
            refl_probe(&|d, p, sym| {
                let c = p.metric.cpoint.creal;
                let (u, v, n) = (sym.u, sym.v, sym.n);
                let sn = d.succ(n);
                let lhs = d.const_app(p.dot, &[u, v, sn]);
                let prior = d.const_app(p.dot, &[u, v, n]);
                let un = d.apply(u, &[n]);
                let vsn = d.apply(v, &[sn]);
                let last = d.const_app(c.mul, &[un, vsn]);
                let rhs = d.const_app(c.add, &[prior, last]);
                (lhs, rhs)
            })
            .is_err(),
            "NEGATIVE CONTROL: the new summand is at index `n`, not `succ n`"
        );
    });
}

/// `RN.norm u n` computes to `sqrt (dot u u n)`, and NOT to `dot u u n`
/// (the squared norm, the wrong choice that makes the triangle inequality
/// false — see [`a_squared_distance_is_refused_as_a_metric`]).
#[test]
fn norm_takes_the_square_root() {
    on_a_deep_stack(|| {
        assert!(
            refl_probe(&|d, p, sym| {
                let c = p.metric.cpoint.creal;
                let (u, n) = (sym.u, sym.n);
                let lhs = d.const_app(p.norm, &[u, n]);
                let inner = d.const_app(p.dot, &[u, u, n]);
                let rhs = d.const_app(c.sqrt, &[inner]);
                (lhs, rhs)
            })
            .is_ok(),
            "RN.norm must unfold to the square root of the self inner product"
        );
        assert!(
            refl_probe(&|d, p, sym| {
                let (u, n) = (sym.u, sym.n);
                let lhs = d.const_app(p.norm, &[u, n]);
                let rhs = d.const_app(p.dot, &[u, u, n]);
                (lhs, rhs)
            })
            .is_err(),
            "NEGATIVE CONTROL: RN.norm must not be the SQUARED norm"
        );
    });
}

/// `RN.dist n u v` computes to `norm (sub u v) n`, and NOT to
/// `norm (sub v u) n` — the two are equal only up to `dist_comm`, which is a
/// theorem here and not a definitional fact.
#[test]
fn dist_is_the_norm_of_the_difference() {
    on_a_deep_stack(|| {
        assert!(
            refl_probe(&|d, p, sym| {
                let (u, v, n) = (sym.u, sym.v, sym.n);
                let lhs = d.const_app(p.dist, &[n, u, v]);
                let w = d.const_app(p.sub, &[u, v]);
                let rhs = d.const_app(p.norm, &[w, n]);
                (lhs, rhs)
            })
            .is_ok(),
            "RN.dist must unfold to the norm of `u - v`"
        );
        assert!(
            refl_probe(&|d, p, sym| {
                let (u, v, n) = (sym.u, sym.v, sym.n);
                let lhs = d.const_app(p.dist, &[n, u, v]);
                let w = d.const_app(p.sub, &[v, u]);
                let rhs = d.const_app(p.norm, &[w, n]);
                (lhs, rhs)
            })
            .is_err(),
            "NEGATIVE CONTROL: `dist n u v` is the norm of `u - v`, not of `v - u`"
        );
    });
}

/// `RN.ofCPoint P` puts the `x` coordinate at index 0 and the `y` coordinate at
/// every successor. The control swaps them.
#[test]
fn of_cpoint_places_the_coordinates() {
    on_a_deep_stack(|| {
        for (index, use_x) in [(0u32, true), (1u32, false), (2u32, false)] {
            assert!(
                refl_probe(&|d, p, sym| {
                    let cp = p.metric.cpoint;
                    let vecp = d.const_app(p.of_cpoint, &[sym.point]);
                    let idx = d.num(index);
                    let lhs = d.apply(vecp, &[idx]);
                    let sel = if use_x { cp.x } else { cp.y };
                    let rhs = d.const_app(sel, &[sym.point]);
                    (lhs, rhs)
                })
                .is_ok(),
                "RN.ofCPoint must place the right coordinate at index {index}"
            );
            assert!(
                refl_probe(&|d, p, sym| {
                    let cp = p.metric.cpoint;
                    let vecp = d.const_app(p.of_cpoint, &[sym.point]);
                    let idx = d.num(index);
                    let lhs = d.apply(vecp, &[idx]);
                    let sel = if use_x { cp.y } else { cp.x };
                    let rhs = d.const_app(sel, &[sym.point]);
                    (lhs, rhs)
                })
                .is_err(),
                "NEGATIVE CONTROL: RN.ofCPoint must not swap the coordinates at index {index}"
            );
        }
    });
}

// ---------------------------------------------------------------------------
// Instance controls: a WRONG ℝⁿ must be refused.
// ---------------------------------------------------------------------------

/// The edit an [`instance_probe`] makes: given the dimension binder and the
/// twelve field values, replace one of them.
type FieldEdit<'a> = &'a dyn Fn(&mut IntDev<'_>, RNPrelude, ExprId, &mut [ExprId]);

/// Rebuild `RN.metric` with one field replaced and report the gate's verdict.
fn instance_probe(replace: FieldEdit<'_>) -> Result<(), crate::KernelError> {
    let (mut kernel, p) = built();
    let int = p.metric.cpoint.creal.rat.int;
    let probe = {
        let root = kernel.anon();
        kernel.name_str(root, "RNInstanceProbe")
    };
    let mut d = IntDev::new(&mut kernel, int);
    let nat = d.nat_ty();
    let vec = d.kernel().const_(p.vec, vec![]);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let mut args = [
        vec,
        d.const_app(p.eq_on, &[n]),
        d.const_app(p.eq_on_refl, &[n]),
        d.const_app(p.eq_on_symm, &[n]),
        d.const_app(p.eq_on_trans, &[n]),
        d.const_app(p.dist, &[n]),
        d.const_app(p.dist_congr, &[n]),
        d.const_app(p.dist_nonneg, &[n]),
        d.const_app(p.dist_self, &[n]),
        d.const_app(p.dist_eq_on, &[n]),
        d.const_app(p.dist_comm, &[n]),
        d.const_app(p.dist_triangle, &[n]),
    ];
    replace(&mut d, p, n, &mut args);
    let body = mk_instance(d.kernel(), &p.metric.record, &args);
    let value = d.lam_fv(n_fv, nat, body);
    let metric_ty = d.kernel().const_(p.metric.record.ind, vec![]);
    let ty = d.arrow(nat, metric_ty);
    d.kernel().add_declaration(Declaration::Definition {
        name: probe,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

/// The unmodified rebuild is accepted — otherwise every control below would
/// "pass" vacuously.
#[test]
fn the_instance_probe_accepts_the_real_instance() {
    on_a_deep_stack(|| {
        assert!(
            instance_probe(&|_d, _p, _n, _args| {}).is_ok(),
            "the instance probe must accept the instance RN.metric actually uses"
        );
    });
}

/// **A squared distance is not a metric, and this record refuses it.**
///
/// `RN.dot (sub u v) (sub u v) n` is the squared Euclidean distance; it
/// satisfies every field of the record except the triangle inequality
/// (`d(0,2)² = 4 > 1 + 1`). Swapping it in must be refused — and the refusal
/// must be the `distTriangle` slot, not an incidental type error, which is why
/// the `distNonneg`/`distComm`/`distSelf` proofs are supplied for it too.
#[test]
fn a_squared_distance_is_refused_as_a_metric() {
    on_a_deep_stack(|| {
        let outcome = instance_probe(&|d, p, n, args| {
            let vec = d.kernel().const_(p.vec, vec![]);
            // dist' := fun u v => RN.dot (RN.sub u v) (RN.sub u v) n
            let u_fv = d.fresh_fvar();
            let u = d.kernel().fvar(u_fv);
            let v_fv = d.fresh_fvar();
            let v = d.kernel().fvar(v_fv);
            let w = d.const_app(p.sub, &[u, v]);
            let body = d.const_app(p.dot, &[w, w, n]);
            let inner = d.lam_fv(v_fv, vec, body);
            args[crate::METRIC_DIST] = d.lam_fv(u_fv, vec, inner);
        });
        assert!(
            outcome.is_err(),
            "NEGATIVE CONTROL: the squared distance must NOT be admitted as a metric"
        );
    });
}

/// **A norm that violates positivity is refused.** Replace the distance by the
/// NEGATED norm — still a function of the right type, still symmetric, still
/// zero on the diagonal, but `0 ≤ d(a,b)` fails.
#[test]
fn a_negated_norm_is_refused_as_a_metric() {
    on_a_deep_stack(|| {
        let outcome = instance_probe(&|d, p, n, args| {
            let c = p.metric.cpoint.creal;
            let vec = d.kernel().const_(p.vec, vec![]);
            let u_fv = d.fresh_fvar();
            let u = d.kernel().fvar(u_fv);
            let v_fv = d.fresh_fvar();
            let v = d.kernel().fvar(v_fv);
            let w = d.const_app(p.sub, &[u, v]);
            let nrm = d.const_app(p.norm, &[w, n]);
            let body = d.const_app(c.neg, &[nrm]);
            let inner = d.lam_fv(v_fv, vec, body);
            args[crate::METRIC_DIST] = d.lam_fv(u_fv, vec, inner);
        });
        assert!(
            outcome.is_err(),
            "NEGATIVE CONTROL: a negated norm must NOT be admitted as a metric"
        );
    });
}

/// **The dimension in the equivalence has to be the dimension in the
/// distance.** Using `EqOn (succ n)` beside `dist n` breaks `distEquiv`: two
/// vectors at distance zero in ℝⁿ need not agree at index `n`.
#[test]
fn a_mismatched_dimension_is_refused() {
    on_a_deep_stack(|| {
        let outcome = instance_probe(&|d, p, n, args| {
            let sn = d.succ(n);
            args[crate::METRIC_EQUIV] = d.const_app(p.eq_on, &[sn]);
            args[crate::METRIC_EQUIV_REFL] = d.const_app(p.eq_on_refl, &[sn]);
            args[crate::METRIC_EQUIV_SYMM] = d.const_app(p.eq_on_symm, &[sn]);
            args[crate::METRIC_EQUIV_TRANS] = d.const_app(p.eq_on_trans, &[sn]);
        });
        assert!(
            outcome.is_err(),
            "NEGATIVE CONTROL: the equivalence's dimension must match the distance's"
        );
    });
}

/// **The setoid laws are about `EqOn`, not about `Eq`.** Handing the record a
/// reflexivity proof for the WRONG relation is refused, which is what makes
/// "ℝⁿ is a Bishop setoid" a checked claim rather than a naming convention.
#[test]
fn the_wrong_reflexivity_is_refused() {
    on_a_deep_stack(|| {
        let outcome = instance_probe(&|d, p, n, args| {
            // `RN.eqOn_refl (succ n)` proves reflexivity of a DIFFERENT relation.
            let sn = d.succ(n);
            args[crate::METRIC_EQUIV_REFL] = d.const_app(p.eq_on_refl, &[sn]);
        });
        assert!(
            outcome.is_err(),
            "NEGATIVE CONTROL: a reflexivity proof for another relation must be refused"
        );
    });
}

// ---------------------------------------------------------------------------
// Theorem controls: the statements themselves must be refutable.
// ---------------------------------------------------------------------------

/// Admit `theorem <fresh> : <ty> := <proof of the real statement>` and report
/// the verdict — used to check that a theorem's statement is not accidentally
/// so weak that a nearby FALSE statement would also have gone through.
fn statement_probe(
    build: &dyn Fn(&mut IntDev<'_>, RNPrelude) -> (ExprId, ExprId),
) -> Result<(), crate::KernelError> {
    let (mut kernel, p) = built();
    let int = p.metric.cpoint.creal.rat.int;
    let probe = {
        let root = kernel.anon();
        kernel.name_str(root, "RNStatementProbe")
    };
    let mut d = IntDev::new(&mut kernel, int);
    let (ty, value) = build(&mut d, p);
    d.kernel().add_declaration(Declaration::Theorem {
        name: probe,
        uparams: vec![],
        ty,
        value,
    })
}

/// **Cauchy-Schwarz does not hold with the inequality reversed.** The proof
/// term of the real theorem must not typecheck against the flipped statement —
/// if it did, `CReal.le` would be symmetric and the theorem would say nothing.
#[test]
fn cauchy_schwarz_does_not_prove_its_converse() {
    on_a_deep_stack(|| {
        assert!(
            statement_probe(&|d, p| {
                let c = p.metric.cpoint.creal;
                let vec = d.kernel().const_(p.vec, vec![]);
                let nat = d.nat_ty();
                let u_fv = d.fresh_fvar();
                let u = d.kernel().fvar(u_fv);
                let v_fv = d.fresh_fvar();
                let v = d.kernel().fvar(v_fv);
                let n_fv = d.fresh_fvar();
                let n = d.kernel().fvar(n_fv);
                let lhs = d.const_app(p.dot, &[u, v, n]);
                let nu = d.const_app(p.norm, &[u, n]);
                let nv = d.const_app(p.norm, &[v, n]);
                let rhs = d.const_app(c.mul, &[nu, nv]);
                // FLIPPED: `‖u‖·‖v‖ ≤ <u,v>`.
                let concl = d.const_app(c.le, &[rhs, lhs]);
                let ty = {
                    let t = d.pi_fv(n_fv, nat, concl);
                    let t = d.pi_fv(v_fv, vec, t);
                    d.pi_fv(u_fv, vec, t)
                };
                let value = d.kernel().const_(p.cauchy_schwarz, vec![]);
                (ty, value)
            })
            .is_err(),
            "NEGATIVE CONTROL: the Cauchy-Schwarz proof must not prove the reverse inequality"
        );
    });
}

/// The same guard for the triangle inequality: `norm_add_le`'s proof must not
/// discharge `‖u‖ + ‖v‖ ≤ ‖u+v‖`.
#[test]
fn minkowski_does_not_prove_its_converse() {
    on_a_deep_stack(|| {
        assert!(
            statement_probe(&|d, p| {
                let c = p.metric.cpoint.creal;
                let vec = d.kernel().const_(p.vec, vec![]);
                let nat = d.nat_ty();
                let u_fv = d.fresh_fvar();
                let u = d.kernel().fvar(u_fv);
                let v_fv = d.fresh_fvar();
                let v = d.kernel().fvar(v_fv);
                let n_fv = d.fresh_fvar();
                let n = d.kernel().fvar(n_fv);
                let w = d.const_app(p.add, &[u, v]);
                let lhs = d.const_app(p.norm, &[w, n]);
                let nu = d.const_app(p.norm, &[u, n]);
                let nv = d.const_app(p.norm, &[v, n]);
                let rhs = d.const_app(c.add, &[nu, nv]);
                let concl = d.const_app(c.le, &[rhs, lhs]);
                let ty = {
                    let t = d.pi_fv(n_fv, nat, concl);
                    let t = d.pi_fv(v_fv, vec, t);
                    d.pi_fv(u_fv, vec, t)
                };
                let value = d.kernel().const_(p.norm_add_le, vec![]);
                (ty, value)
            })
            .is_err(),
            "NEGATIVE CONTROL: Minkowski's proof must not prove the reverse inequality"
        );
    });
}

/// **The generic metric theorems apply.** `Metric.dist_quadrilateral` is stated
/// for an arbitrary metric space; instantiating it at `RN.metric n` must
/// typecheck, which is the whole reason for building the instance.
#[test]
fn the_generic_metric_theorems_apply_to_rn() {
    on_a_deep_stack(|| {
        assert!(
            statement_probe(&|d, p| {
                let c = p.metric.cpoint.creal;
                let vec = d.kernel().const_(p.vec, vec![]);
                let nat = d.nat_ty();
                let n_fv = d.fresh_fvar();
                let n = d.kernel().fvar(n_fv);
                let a_fv = d.fresh_fvar();
                let a = d.kernel().fvar(a_fv);
                let inst = d.const_app(p.metric_inst, &[n]);
                let sel = d
                    .kernel()
                    .const_(p.metric.record.sel(crate::METRIC_DIST), vec![]);
                let dist_aa = d.apply(sel, &[inst, a, a]);
                let z = d.kernel().const_(c.zero, vec![]);
                let concl = d.const_app(c.equiv, &[dist_aa, z]);
                let ty = {
                    let t = d.pi_fv(a_fv, vec, concl);
                    d.pi_fv(n_fv, nat, t)
                };
                let value = {
                    let body = d.lemma(p.metric.dist_self, &[inst, a]);
                    let t = d.lam_fv(a_fv, vec, body);
                    d.lam_fv(n_fv, nat, t)
                };
                (ty, value)
            })
            .is_ok(),
            "Metric.dist_self must instantiate at RN.metric n"
        );
    });
}

/// **The positive half of the two converse controls above.** Restating the real
/// Cauchy-Schwarz inequality and discharging it with `RN.cauchy_schwarz` must
/// SUCCEED — without this, `cauchy_schwarz_does_not_prove_its_converse` and
/// `minkowski_does_not_prove_its_converse` would both "pass" if
/// `statement_probe` were broken in any way at all, and neither would be
/// telling you anything about `CReal.le`.
#[test]
fn the_statement_probe_accepts_the_real_cauchy_schwarz() {
    on_a_deep_stack(|| {
        assert!(
            statement_probe(&|d, p| {
                let c = p.metric.cpoint.creal;
                let vec = d.kernel().const_(p.vec, vec![]);
                let nat = d.nat_ty();
                let u_fv = d.fresh_fvar();
                let u = d.kernel().fvar(u_fv);
                let v_fv = d.fresh_fvar();
                let v = d.kernel().fvar(v_fv);
                let n_fv = d.fresh_fvar();
                let n = d.kernel().fvar(n_fv);
                let lhs = d.const_app(p.dot, &[u, v, n]);
                let nu = d.const_app(p.norm, &[u, n]);
                let nv = d.const_app(p.norm, &[v, n]);
                let rhs = d.const_app(c.mul, &[nu, nv]);
                let concl = d.const_app(c.le, &[lhs, rhs]);
                let ty = {
                    let t = d.pi_fv(n_fv, nat, concl);
                    let t = d.pi_fv(v_fv, vec, t);
                    d.pi_fv(u_fv, vec, t)
                };
                let value = d.kernel().const_(p.cauchy_schwarz, vec![]);
                (ty, value)
            })
            .is_ok(),
            "the statement probe must accept the inequality RN.cauchy_schwarz actually proves"
        );
    });
}
