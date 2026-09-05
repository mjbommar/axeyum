//! `IntSpace.Bundled` — **an integrable function and its integrability witness
//! are now one object** (ADR-1613, unblocking what ADR-1612 recorded).
//!
//! ADR-1612's obstruction, quoted from `intspace.rs`'s own module doc: an
//! "integrable set" cannot be bundled into one object, *because `Sigma` and
//! `Subtype` are absent from this kernel*. That absence is why
//! `IntSpace.Integrable` is `Sort 1` data rather than a `Prop` side condition,
//! and why `IntSpace.integral` takes its witness as a separate explicit
//! argument:
//!
//! ```text
//! IntSpace.Integrable : Π (S : IntSpace), S.carrier → Sort 1
//! IntSpace.integral   : Π (S : IntSpace) (f : S.carrier), S.Integrable f → CReal
//! ```
//!
//! A metric needs a **total** `dist : carrier → carrier → CReal`, so
//! `S.carrier` can never be the carrier of an L¹ metric: `integral` is not
//! total on it. `Sigma` fixes exactly that, and nothing else:
//!
//! ```text
//! IntSpace.Bundled S := Sigma.{0,0} S.carrier (IntSpace.Integrable S)
//! ```
//!
//! Universe check, which is the whole reason this needs `Sigma` and not
//! `Subtype`: `S.carrier : Sort 1 = Type 0`, so `u = 0`; `S.Integrable S f :
//! Sort 1 = Type 0` — **data, not a proposition** — so `v = 0` and
//! `Sigma.{0,0} … : Type (max 0 0) = Sort 1`. That is precisely the universe
//! `declare_record` fixes a carrier at, so `IntSpace.Bundled S` is a legal
//! carrier for a `Metric`. `Subtype` would not do here: its second field must
//! be `Prop`-valued, and `Integrable` deliberately is not.
//!
//! # What is declared
//!
//! | name | type |
//! | --- | --- |
//! | `IntSpace.Bundled` | `IntSpace → Sort 1` |
//! | `IntSpace.bundle` | `Π S (f : S.carrier), S.Integrable f → S.Bundled` |
//! | `IntSpace.bundledFun` | `Π S, S.Bundled → S.carrier` |
//! | `IntSpace.bundledWitness` | `Π S (b : S.Bundled), S.Integrable (S.bundledFun b)` |
//! | `IntSpace.bundledIntegral` | `Π S, S.Bundled → CReal` — **∫ as a TOTAL function** |
//! | `IntSpace.bundledIntegral_bundle` | `∀ S f h, S.bundledIntegral (S.bundle f h) = S.integral f h` |
//! | `IntSpace.bundledDist` | `Π S, S.Bundled → S.Bundled → CReal` |
//!
//! `bundledIntegral_bundle` is an `Eq`, closed by `Eq.refl`: `Sigma.fst`/`snd`
//! ι-reduce on the literal constructor, so bundling and then integrating IS
//! integrating. That equation is what makes the bundle faithful rather than a
//! wrapper that loses the connection to `IntSpace.integral`.
//!
//! # What this is NOT: it is not L¹
//!
//! `IntSpace.bundledDist S b₁ b₂ := |∫b₁ − ∫b₂|` is a genuine
//! `Bundled S → Bundled S → CReal`, and it is declared here for one reason
//! only: to demonstrate that a function of the shape `Metric.dist` demands is
//! now *writable* on this carrier, which it was not before. **It is not the L¹
//! seminorm**, which is `‖f − g‖₁ = ∫|f − g|` — a different function, and
//! generally larger than this one.
//!
//! The L¹ seminorm remains blocked, and on something this file does not touch:
//! `IntSpace` has `fadd` and `fscale` (so `f − g` is `fadd f (fscale (−1) g)`)
//! but **no absolute value on the carrier**, and no integrability witness for
//! `|f|` given one for `f`. That is exactly the lattice/`|·|`-closure gap
//! `intspace.rs` already records as standing between `IntSpace` and a
//! Petrakis–Zeuner pre-integration space. `Sigma` was one of the two missing
//! pieces; it is no longer missing, and the remaining one is named.
//!
//! Nor is `bundledDist` claimed to satisfy the metric axioms — it does not
//! separate points (two different functions with the same integral are at
//! distance zero), so it is a pseudometric at best. Building the `Metric`
//! instance is a separate task with real proof cost; establishing that the
//! carrier and the distance function are *expressible* is this file's whole
//! claim.

use super::{
    INTEGRABLE, INTEGRAL, IntSpacePrelude, definition, field, generic_space, radd, rneg, rty,
    theorem,
};
use crate::KernelError;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;
use crate::{Kernel, LevelId};

/// The interned names this file owns.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BundledNames {
    /// `IntSpace.Bundled : IntSpace → Sort 1` — `Sigma S.carrier S.Integrable`,
    /// the function bundled with its integrability datum.
    pub bundled: NameId,
    /// `IntSpace.bundle : Π S (f : S.carrier), S.Integrable f → S.Bundled`.
    pub bundle: NameId,
    /// `IntSpace.bundledFun : Π S, S.Bundled → S.carrier`.
    pub bundled_fun: NameId,
    /// `IntSpace.bundledWitness : Π S (b : S.Bundled),
    /// S.Integrable (S.bundledFun b)`.
    pub bundled_witness: NameId,
    /// `IntSpace.bundledIntegral : Π S, S.Bundled → CReal` — the integral as a
    /// **total** function of one argument, which is what a metric needs.
    pub bundled_integral: NameId,
    /// `IntSpace.bundledIntegral_bundle : ∀ S f h,
    /// Eq CReal (S.bundledIntegral (S.bundle f h)) (S.integral f h)`.
    pub bundled_integral_bundle: NameId,
    /// `IntSpace.bundledDist : Π S, S.Bundled → S.Bundled → CReal` —
    /// `|∫b₁ − ∫b₂|`. A function of the shape `Metric.dist` demands, on the
    /// bundled carrier. **Not** the L¹ seminorm; see the module doc.
    pub bundled_dist: NameId,
}

impl BundledNames {
    /// Every name this file owns, for the inventory tests. Derived from the
    /// struct's own fields, never from a literal list somewhere else.
    pub fn all(&self) -> Vec<(&'static str, NameId)> {
        vec![
            ("IntSpace.Bundled", self.bundled),
            ("IntSpace.bundle", self.bundle),
            ("IntSpace.bundledFun", self.bundled_fun),
            ("IntSpace.bundledWitness", self.bundled_witness),
            ("IntSpace.bundledIntegral", self.bundled_integral),
            (
                "IntSpace.bundledIntegral_bundle",
                self.bundled_integral_bundle,
            ),
            ("IntSpace.bundledDist", self.bundled_dist),
        ]
    }
}

pub(super) fn intern(kernel: &mut Kernel, intspace: NameId) -> BundledNames {
    BundledNames {
        bundled: kernel.name_str(intspace, "Bundled"),
        bundle: kernel.name_str(intspace, "bundle"),
        bundled_fun: kernel.name_str(intspace, "bundledFun"),
        bundled_witness: kernel.name_str(intspace, "bundledWitness"),
        bundled_integral: kernel.name_str(intspace, "bundledIntegral"),
        bundled_integral_bundle: kernel.name_str(intspace, "bundledIntegral_bundle"),
        bundled_dist: kernel.name_str(intspace, "bundledDist"),
    }
}

/// The two universe levels every `Sigma` application here is at: both `0`,
/// because `S.carrier` and `S.Integrable S f` are both `Sort 1 = Type 0`.
fn sigma_levels(d: &mut IntDev<'_>) -> (LevelId, LevelId) {
    let zero = d.kernel().level_zero();
    (zero, zero)
}

/// `IntSpace.Bundled S`, by name (not unfolded).
fn bundled_ty(d: &mut IntDev<'_>, p: IntSpacePrelude, s: ExprId) -> ExprId {
    let name = p.bundled.bundled;
    d.const_app(name, &[s])
}

/// `IntSpace.Bundled : IntSpace → Sort 1`.
fn declare_bundled(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let logic = p.creal.rat.int.logic;
    let g = generic_space(d, p);
    let (u, v) = sigma_levels(d);

    let integrable = field(d, p, g.s, INTEGRABLE);
    let value = {
        let head = d.kernel().const_(logic.sigma.sigma, vec![u, v]);
        let body = d.apply(head, &[g.carrier, integrable]);
        d.lam_fv(g.s_fv, g.space_ty, body)
    };
    let ty = {
        let one = d.kernel().level_succ(u);
        let sort_one = d.kernel().sort(one);
        d.pi_fv(g.s_fv, g.space_ty, sort_one)
    };
    definition(d, p.bundled.bundled, ty, value)
}

/// `IntSpace.bundle : Π S (f : S.carrier), S.Integrable f → S.Bundled`.
fn declare_bundle(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let logic = p.creal.rat.int.logic;
    let g = generic_space(d, p);
    let (u, v) = sigma_levels(d);

    let integrable = field(d, p, g.s, INTEGRABLE);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let witness_ty = d.apply(integrable, &[f]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let body = {
        let head = d.kernel().const_(logic.sigma.sigma_mk, vec![u, v]);
        d.apply(head, &[g.carrier, integrable, f, h])
    };
    let value = {
        let with_h = d.lam_fv(h_fv, witness_ty, body);
        let with_f = d.lam_fv(f_fv, g.carrier, with_h);
        d.lam_fv(g.s_fv, g.space_ty, with_f)
    };
    let ty = {
        let target = bundled_ty(d, p, g.s);
        let with_h = d.pi_fv(h_fv, witness_ty, target);
        let with_f = d.pi_fv(f_fv, g.carrier, with_h);
        d.pi_fv(g.s_fv, g.space_ty, with_f)
    };
    definition(d, p.bundled.bundle, ty, value)
}

/// `IntSpace.bundledFun : Π S, S.Bundled → S.carrier`.
fn declare_bundled_fun(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let logic = p.creal.rat.int.logic;
    let g = generic_space(d, p);
    let (u, v) = sigma_levels(d);

    let integrable = field(d, p, g.s, INTEGRABLE);
    let carrier_of_bundle = bundled_ty(d, p, g.s);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let body = {
        let head = d.kernel().const_(logic.sigma.sigma_fst, vec![u, v]);
        d.apply(head, &[g.carrier, integrable, b])
    };
    let value = {
        let with_b = d.lam_fv(b_fv, carrier_of_bundle, body);
        d.lam_fv(g.s_fv, g.space_ty, with_b)
    };
    let ty = {
        let inner = d.arrow(carrier_of_bundle, g.carrier);
        d.pi_fv(g.s_fv, g.space_ty, inner)
    };
    definition(d, p.bundled.bundled_fun, ty, value)
}

/// `IntSpace.bundledWitness : Π S (b : S.Bundled),
/// S.Integrable (S.bundledFun b)`.
///
/// A `Definition`, not a `Theorem`: `Integrable` is `Sort 1` data (ADR-1612),
/// so this projects a value, not a proof.
fn declare_bundled_witness(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let logic = p.creal.rat.int.logic;
    let g = generic_space(d, p);
    let (u, v) = sigma_levels(d);

    let integrable = field(d, p, g.s, INTEGRABLE);
    let carrier_of_bundle = bundled_ty(d, p, g.s);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let body = {
        let head = d.kernel().const_(logic.sigma.sigma_snd, vec![u, v]);
        d.apply(head, &[g.carrier, integrable, b])
    };
    let value = {
        let with_b = d.lam_fv(b_fv, carrier_of_bundle, body);
        d.lam_fv(g.s_fv, g.space_ty, with_b)
    };
    let ty = {
        let name = p.bundled.bundled_fun;
        let projected = d.const_app(name, &[g.s, b]);
        let claim = d.apply(integrable, &[projected]);
        let with_b = d.pi_fv(b_fv, carrier_of_bundle, claim);
        d.pi_fv(g.s_fv, g.space_ty, with_b)
    };
    definition(d, p.bundled.bundled_witness, ty, value)
}

/// `IntSpace.bundledIntegral : Π S, S.Bundled → CReal`.
///
/// **This is the deliverable.** `IntSpace.integral` needs two arguments and is
/// therefore not a function of the carrier alone; on the bundled carrier it is.
fn declare_bundled_integral(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let c = p.creal;
    let g = generic_space(d, p);
    let carrier_of_bundle = bundled_ty(d, p, g.s);
    let real = rty(d, c);

    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let body = {
        let fun_name = p.bundled.bundled_fun;
        let witness_name = p.bundled.bundled_witness;
        let projected = d.const_app(fun_name, &[g.s, b]);
        let witness = d.const_app(witness_name, &[g.s, b]);
        let integral = field(d, p, g.s, INTEGRAL);
        d.apply(integral, &[projected, witness])
    };
    let value = {
        let with_b = d.lam_fv(b_fv, carrier_of_bundle, body);
        d.lam_fv(g.s_fv, g.space_ty, with_b)
    };
    let ty = {
        let inner = d.arrow(carrier_of_bundle, real);
        d.pi_fv(g.s_fv, g.space_ty, inner)
    };
    definition(d, p.bundled.bundled_integral, ty, value)
}

/// `IntSpace.bundledIntegral_bundle : ∀ S f h,
/// Eq CReal (S.bundledIntegral (S.bundle f h)) (S.integral f h)`.
///
/// `Eq.refl`. Bundling and then integrating IS integrating: `Sigma.fst` and
/// `Sigma.snd` ι-reduce on the literal `Sigma.mk`, so the bundle loses nothing.
fn declare_bundled_integral_bundle(
    d: &mut IntDev<'_>,
    p: IntSpacePrelude,
) -> Result<(), KernelError> {
    let c = p.creal;
    let logic = c.rat.int.logic;
    let g = generic_space(d, p);
    let real = rty(d, c);
    let zero = d.kernel().level_zero();
    let one = d.kernel().level_succ(zero);

    let integrable = field(d, p, g.s, INTEGRABLE);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let witness_ty = d.apply(integrable, &[f]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let rhs = {
        let integral = field(d, p, g.s, INTEGRAL);
        d.apply(integral, &[f, h])
    };
    let lhs = {
        let bundle_name = p.bundled.bundle;
        let bundled = d.const_app(bundle_name, &[g.s, f, h]);
        let integral_name = p.bundled.bundled_integral;
        d.const_app(integral_name, &[g.s, bundled])
    };
    let stmt = {
        let head = d.kernel().const_(logic.eq, vec![one]);
        d.apply(head, &[real, lhs, rhs])
    };
    let proof = {
        let head = d.kernel().const_(logic.eq_refl, vec![one]);
        d.apply(head, &[real, rhs])
    };
    let ty = {
        let with_h = d.pi_fv(h_fv, witness_ty, stmt);
        let with_f = d.pi_fv(f_fv, g.carrier, with_h);
        d.pi_fv(g.s_fv, g.space_ty, with_f)
    };
    let value = {
        let with_h = d.lam_fv(h_fv, witness_ty, proof);
        let with_f = d.lam_fv(f_fv, g.carrier, with_h);
        d.lam_fv(g.s_fv, g.space_ty, with_f)
    };
    theorem(d, p.bundled.bundled_integral_bundle, ty, value)
}

/// `IntSpace.bundledDist : Π S, S.Bundled → S.Bundled → CReal
///   := fun S b₁ b₂ => CReal.abs (∫b₁ + −∫b₂)`.
///
/// The shape `Metric.dist` demands, on the bundled carrier. Read the module
/// doc before treating this as L¹: it is not.
fn declare_bundled_dist(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let c = p.creal;
    let g = generic_space(d, p);
    let carrier_of_bundle = bundled_ty(d, p, g.s);
    let real = rty(d, c);

    let left_fv = d.fresh_fvar();
    let left = d.kernel().fvar(left_fv);
    let right_fv = d.fresh_fvar();
    let right = d.kernel().fvar(right_fv);

    let body = {
        let name = p.bundled.bundled_integral;
        let a = d.const_app(name, &[g.s, left]);
        let b = d.const_app(name, &[g.s, right]);
        let negated = rneg(d, c, b);
        let difference = radd(d, c, a, negated);
        d.const_app(c.abs, &[difference])
    };
    let value = {
        let with_right = d.lam_fv(right_fv, carrier_of_bundle, body);
        let with_left = d.lam_fv(left_fv, carrier_of_bundle, with_right);
        d.lam_fv(g.s_fv, g.space_ty, with_left)
    };
    let ty = {
        let inner = d.arrow(carrier_of_bundle, real);
        let outer = d.arrow(carrier_of_bundle, inner);
        d.pi_fv(g.s_fv, g.space_ty, outer)
    };
    definition(d, p.bundled.bundled_dist, ty, value)
}

/// Land every declaration this file owns, in dependency order.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_all(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    declare_bundled(d, p)?;
    declare_bundle(d, p)?;
    declare_bundled_fun(d, p)?;
    declare_bundled_witness(d, p)?;
    declare_bundled_integral(d, p)?;
    declare_bundled_integral_bundle(d, p)?;
    declare_bundled_dist(d, p)
}
