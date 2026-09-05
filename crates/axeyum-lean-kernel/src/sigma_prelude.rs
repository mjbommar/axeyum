//! **Dependent pairs and subtypes**: `Sigma`, `PSigma` and `Subtype`, declared
//! into the logical prelude through the same trusted `add_inductive` gate as
//! `And`, `Or`, `Eq`, `Exists` and `Acc` (ADR-1613).
//!
//! # Why this module exists
//!
//! Three ADRs hit the same wall on one day. ADR-1595 found the *classical*
//! first-isomorphism statement `G/ker f ≅ Im f` needs a **subtype** for the
//! image, because the image is a predicate on the codomain and this kernel has
//! no way to turn a predicate into a carrier. ADR-1602 found a metric
//! **subspace** needs the same thing, because `Metric.dist` is total on its
//! carrier and a subspace's distance is the ambient one *restricted*. ADR-1612
//! found L¹ needs a **`Sigma`** to bundle an integrability witness with the
//! function it is about, because `Metric.dist` is total but `Integrable` is a
//! side condition. ADR-1606 rejected a `Fin n → CReal` carrier for ℝⁿ on the
//! same ground.
//!
//! None of that is an axiom. A dependent pair is an ordinary one-constructor
//! inductive, and this kernel already admits **two specializations of exactly
//! this shape**: `Nat.Fin` (`⟨val : Nat, isLt : val < n⟩`, a `Type 0` family
//! with a data field and a dependent `Prop` field over it) and `CReal`
//! (`⟨seq, regular⟩`). What was missing was only the **universe-polymorphic**
//! form, whose result universe is a `max`. So the real question this module
//! answers by trying is whether ADR-1495's constructor-field universe guard
//! (`KernelError::ConstructorFieldUniverseTooBig`) refuses a `Sort (max u v)`
//! result level. **It does not**, and the reason is worth stating precisely,
//! because the guard is the one thing standing between this kernel and
//! Girard's paradox and it must not be weakened by accident:
//!
//! The guard rejects a constructor field whose type's universe is *strictly
//! above* the family's own result universe (`Prop` exempt, being
//! impredicative). Every field of every inductive below sits **at or below**
//! its family's result universe by construction, and `Kernel::level_leq`
//! discharges each obligation *symbolically*, with no instantiation:
//!
//! | family | result universe | field | field universe | why `≤` holds |
//! | --- | --- | --- | --- | --- |
//! | `Sigma.{u,v}` | `Sort (max u v + 1)` | `α : Type u` | `Sort (u+1)` | `u ≤ max u v` |
//! | | | `β fst : Type v` | `Sort (v+1)` | `v ≤ max u v` |
//! | `PSigma.{u,v}` | `Sort (max 1 u v)` | `α : Sort u` | `Sort u` | `u ≤ max 1 u v` |
//! | | | `β fst : Sort v` | `Sort v` | `v ≤ max 1 u v` |
//! | `Subtype.{u}` | `Sort (max 1 u)` | `α : Sort u` | `Sort u` | `u ≤ max 1 u` |
//! | | | `p val : Prop` | `Sort 0` | `0 ≤ anything` |
//!
//! Nothing here stores its own universe, which is the shape ADR-1495 actually
//! forbids (`mk : Sort 1 → U` with `U : Sort 1`). The guard is untouched: this
//! module only shows that the shape it rejects and the shape a dependent pair
//! needs are different shapes.
//!
//! # Large elimination, and the one place this kernel diverged from Lean
//!
//! `Kernel::add_mutual_inductive` grants large elimination (a recursor with its
//! own motive universe parameter) when the family's result universe is
//! *provably* non-zero, or when the family is a single-constructor one whose
//! non-`Prop` fields all appear in the result type. All three families here
//! clear that bar — a successor for `Sigma`, a `max` with a literal `1` in it
//! for `PSigma` and `Subtype` — so each gets `Sigma.rec.{w,u,v}`,
//! `PSigma.rec.{w,u,v}`, `Subtype.rec.{w,u}` and its projections.
//!
//! **`PSigma`'s result universe is `Sort (max 1 u v)`, and the `1` is not
//! decoration.** The obvious spelling is `Sort (max u v)`, which is what this
//! module was written with first. This kernel ADMITS that, and handles it
//! soundly: `max u v` is zero at `u = v = 0`, so `PSigma.{0,0}` genuinely is a
//! `Prop`, the kernel cannot prove the result universe non-zero, and it
//! therefore refuses large elimination — leaving a `Prop`-only recursor and no
//! projections. That is a correct verdict, and it is also **more permissive
//! than real Lean**, which rejects the declaration outright:
//!
//! ```text
//! error: Invalid universe polymorphic resulting type: The resulting universe
//! is not `Prop`, but it may be `Prop` for some parameter values:
//!   Sort (max u v)
//! Hint: A possible solution is to use levels of the form `max 1 _` or `_ + 1`
//! ```
//!
//! That is Lean 4.34.0-rc1's own message, produced by
//! `tests/real_lean_shared_prelude_crosscheck.rs` — the gate that elaborates
//! this prelude's exported module in the pinned real Lean. It is the only
//! divergence the three families produced, it was found by measurement rather
//! than by reading, and it is resolved by following Lean: `PSigma` is declared
//! at `Sort (max 1 u v)`, exactly Lean's own, and consequently DOES get large
//! elimination and both projections.
//!
//! # What is declared
//!
//! ```text
//! inductive Sigma.{u,v} (α : Type u) (β : α → Type v) : Type (max u v)
//!   | mk : (fst : α) → (snd : β fst) → Sigma α β
//! Sigma.fst.{u,v}    : Π (α) (β) (s : Sigma α β), α
//! Sigma.snd.{u,v}    : Π (α) (β) (s : Sigma α β), β (Sigma.fst α β s)
//! Sigma.fst_mk.{u,v} : ∀ α β (a : α) (b : β a), Sigma.fst α β (Sigma.mk α β a b) = a
//! Sigma.snd_mk.{u,v} : ∀ α β (a : α) (b : β a), Sigma.snd α β (Sigma.mk α β a b) = b
//! Sigma.mk_eta.{u,v} : ∀ α β (s : Sigma α β), Sigma.mk α β (Sigma.fst α β s) (Sigma.snd α β s) = s
//!
//! inductive PSigma.{u,v} (α : Sort u) (β : α → Sort v) : Sort (max 1 u v)
//!   | mk : (fst : α) → (snd : β fst) → PSigma α β
//! PSigma.fst.{u,v}   : Π (α) (β) (p : PSigma α β), α
//! PSigma.snd.{u,v}   : Π (α) (β) (p : PSigma α β), β (PSigma.fst α β p)
//!
//! inductive Subtype.{u} (α : Sort u) (p : α → Prop) : Sort (max 1 u)
//!   | mk : (val : α) → (property : p val) → Subtype α p
//! Subtype.val.{u}      : Π (α) (p) (s : Subtype α p), α
//! Subtype.property.{u} : ∀ α p (s : Subtype α p), p (Subtype.val α p s)
//! Subtype.val_mk.{u}   : ∀ α p (a : α) (h : p a), Subtype.val α p (Subtype.mk α p a h) = a
//! Subtype.mk_eta.{u}   : ∀ α p (s : Subtype α p),
//!                          Subtype.mk α p (Subtype.val α p s) (Subtype.property α p s) = s
//! ```
//!
//! `Sigma.fst`/`Sigma.snd`/`PSigma.fst`/`PSigma.snd`/`Subtype.val` are
//! [`Declaration::Definition`]s (their
//! codomains are data, not `Prop`); everything else with a `=` in it is a
//! [`Declaration::Theorem`]. Every one of them is proved from the generated
//! recursor and `Eq.refl` — **no axiom is added by this module**, and
//! `Kernel::axiom_footprint` is empty for each (asserted in
//! `sigma_prelude_tests`).
//!
//! `mk_eta` is a *theorem*, not a kernel eta rule: the recursor's ι-reduction
//! on the literal constructor `mk a b` turns the statement into
//! `mk a b = mk a b`, closed by `Eq.refl`. That is the same route
//! `Nat.Fin.val_mk` takes.
//!
//! # What is deliberately NOT declared
//!
//! **`Fin`.** It already exists, as `Nat.Fin` (`nat_prelude/finite.rs`), with
//! `Nat.Fin.val`, `Nat.Fin.isLt` and the evaluation theorem `Nat.Fin.val_mk` —
//! and it is *already* the subtype form, `⟨val : Nat, isLt : val < n⟩`. A
//! second, generic `Fin` would be a duplicate carrier with no consumer, and the
//! interesting statement (`Nat.Fin n ≃ Subtype Nat (· < n)`) is a bridge that
//! belongs next to `Nat.Fin`, in `nat_prelude`, not here.

use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::name::NameId;
use crate::{BinderInfo, Kernel, KernelError};

#[cfg(test)]
mod sigma_prelude_tests;

/// The interned names [`declare_sigma_family`] produces.
///
/// Handles belong to the kernel they were built in; do not mix them across
/// kernels.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SigmaNames {
    /// `Sigma.{u,v} : Π (α : Type u), (α → Type v) → Type (max u v)`.
    pub sigma: NameId,
    /// `Sigma.mk.{u,v} : Π (α) (β) (fst : α), β fst → Sigma α β`.
    pub sigma_mk: NameId,
    /// `Sigma.rec.{w,u,v}` — the generated large-eliminating recursor.
    pub sigma_rec: NameId,
    /// `Sigma.fst.{u,v} : Π (α) (β) (s : Sigma α β), α`.
    pub sigma_fst: NameId,
    /// `Sigma.snd.{u,v} : Π (α) (β) (s : Sigma α β), β (Sigma.fst α β s)` —
    /// the **dependent** second projection.
    pub sigma_snd: NameId,
    /// `Sigma.fst_mk.{u,v}` — `fst (mk a b) = a`.
    pub sigma_fst_mk: NameId,
    /// `Sigma.snd_mk.{u,v}` — `snd (mk a b) = b`, at the carrier `β a`.
    pub sigma_snd_mk: NameId,
    /// `Sigma.mk_eta.{u,v}` — `mk (fst s) (snd s) = s`, proved by ι-reduction
    /// on the constructor, not assumed as a kernel eta rule.
    pub sigma_mk_eta: NameId,
    /// The universe parameter `u` shared by the whole `Sigma` family.
    pub sigma_uparam_u: NameId,
    /// The universe parameter `v` shared by the whole `Sigma` family.
    pub sigma_uparam_v: NameId,

    /// `PSigma.{u,v} : Π (α : Sort u), (α → Sort v) → Sort (max 1 u v)` — the
    /// `Sort`-level dependent pair, at Lean's own result universe.
    pub psigma: NameId,
    /// `PSigma.mk.{u,v} : Π (α) (β) (fst : α), β fst → PSigma α β`.
    pub psigma_mk: NameId,
    /// `PSigma.rec.{w,u,v}` — the generated large-eliminating recursor.
    pub psigma_rec: NameId,
    /// `PSigma.fst.{u,v} : Π (α) (β) (p : PSigma α β), α`.
    pub psigma_fst: NameId,
    /// `PSigma.snd.{u,v} : Π (α) (β) (p : PSigma α β), β (PSigma.fst α β p)`.
    pub psigma_snd: NameId,
    /// The universe parameter `u` shared by the `PSigma` family.
    pub psigma_uparam_u: NameId,
    /// The universe parameter `v` shared by the `PSigma` family.
    pub psigma_uparam_v: NameId,

    /// `Subtype.{u} : Π (α : Sort u), (α → Prop) → Sort (max 1 u)`.
    pub subtype: NameId,
    /// `Subtype.mk.{u} : Π (α) (p) (val : α), p val → Subtype α p`.
    pub subtype_mk: NameId,
    /// `Subtype.rec.{w,u}` — the generated large-eliminating recursor.
    pub subtype_rec: NameId,
    /// `Subtype.val.{u} : Π (α) (p) (s : Subtype α p), α`.
    pub subtype_val: NameId,
    /// `Subtype.property.{u} : ∀ α p (s : Subtype α p), p (Subtype.val α p s)`.
    pub subtype_property: NameId,
    /// `Subtype.val_mk.{u}` — `val (mk a h) = a`.
    pub subtype_val_mk: NameId,
    /// `Subtype.mk_eta.{u}` — `mk (val s) (property s) = s`.
    pub subtype_mk_eta: NameId,
    /// The universe parameter `u` shared by the whole `Subtype` family.
    pub subtype_uparam: NameId,
}

/// `f a₁ … aₙ`.
fn apply_all(kernel: &mut Kernel, mut function: ExprId, arguments: &[ExprId]) -> ExprId {
    for &argument in arguments {
        function = kernel.app(function, argument);
    }
    function
}

/// `Π (x : ty), body` with `x` the free variable `fvar` occurring in `body`.
fn pi_fvar(kernel: &mut Kernel, fvar: u64, ty: ExprId, body: ExprId) -> ExprId {
    let body = kernel.abstract_fvars(body, &[fvar]);
    let anon = kernel.anon();
    kernel.pi(anon, ty, body, BinderInfo::Default)
}

/// `fun (x : ty) => body` with `x` the free variable `fvar` occurring in `body`.
fn lam_fvar(kernel: &mut Kernel, fvar: u64, ty: ExprId, body: ExprId) -> ExprId {
    let body = kernel.abstract_fvars(body, &[fvar]);
    let anon = kernel.anon();
    kernel.lam(anon, ty, body, BinderInfo::Default)
}

/// `Eq.{level} carrier lhs rhs`.
fn eq_app(
    kernel: &mut Kernel,
    eq: NameId,
    level: LevelId,
    carrier: ExprId,
    lhs: ExprId,
    rhs: ExprId,
) -> ExprId {
    let head = kernel.const_(eq, vec![level]);
    apply_all(kernel, head, &[carrier, lhs, rhs])
}

/// `Eq.refl.{level} carrier value`.
fn eq_refl_app(
    kernel: &mut Kernel,
    eq_refl: NameId,
    level: LevelId,
    carrier: ExprId,
    value: ExprId,
) -> ExprId {
    let head = kernel.const_(eq_refl, vec![level]);
    apply_all(kernel, head, &[carrier, value])
}

// Free-variable identifiers. `prelude.rs` uses the 19_000–24_999 band; this
// module takes a disjoint one so a term never accidentally shares an fvar with
// a neighbouring declaration.
const SIGMA_ALPHA: u64 = 71_000;
const SIGMA_BETA: u64 = 71_001;
const SIGMA_PAIR: u64 = 71_002;
const SIGMA_A: u64 = 71_003;
const SIGMA_B: u64 = 71_004;
const SIGMA_Y: u64 = 71_005;
const PSIGMA_ALPHA: u64 = 71_050;
const PSIGMA_BETA: u64 = 71_051;
const PSIGMA_PAIR: u64 = 71_052;
const PSIGMA_A: u64 = 71_053;
const PSIGMA_B: u64 = 71_054;
const PSIGMA_Y: u64 = 71_055;
const SUBTYPE_ALPHA: u64 = 71_100;
const SUBTYPE_P: u64 = 71_101;
const SUBTYPE_S: u64 = 71_102;
const SUBTYPE_A: u64 = 71_103;
const SUBTYPE_H: u64 = 71_104;
const SUBTYPE_Y: u64 = 71_105;

/// Declare `Sigma`, `PSigma` and `Subtype` (with `Sigma`/`Subtype`'s
/// projections and their defining equations) into `kernel`.
///
/// `eq` and `eq_refl` are the logical prelude's `Eq`/`Eq.refl`, which must
/// already be declared — every theorem here is an equation proved by
/// ι-reduction plus `Eq.refl`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. In particular a
/// [`KernelError::ConstructorFieldUniverseTooBig`] here would be ADR-1495's
/// universe guard refusing a `max`-valued result universe; see the module doc
/// for why it does not fire.
#[allow(clippy::too_many_lines)]
pub(crate) fn declare_sigma_family(
    kernel: &mut Kernel,
    eq: NameId,
    eq_refl: NameId,
) -> Result<SigmaNames, KernelError> {
    let anon = kernel.anon();

    let sigma_uparam_u = kernel.name_str(anon, "u");
    let sigma_uparam_v = kernel.name_str(anon, "v");
    let sigma = kernel.name_str(anon, "Sigma");
    let sigma_mk = kernel.name_str(sigma, "mk");

    // --- Sigma.{u,v} (α : Type u) (β : α → Type v) : Type (max u v) ---------
    {
        let u_lvl = kernel.level_param(sigma_uparam_u);
        let v_lvl = kernel.level_param(sigma_uparam_v);
        let type_u = {
            let succ_u = kernel.level_succ(u_lvl);
            kernel.sort(succ_u)
        };
        let type_v = {
            let succ_v = kernel.level_succ(v_lvl);
            kernel.sort(succ_v)
        };
        let result_sort = {
            let max_uv = kernel.level_max(u_lvl, v_lvl);
            let succ_max = kernel.level_succ(max_uv);
            kernel.sort(succ_max)
        };
        let sigma_const = kernel.const_(sigma, vec![u_lvl, v_lvl]);

        // ty := Π (α : Type u) (β : α → Type v), Type (max u v).
        //   `β`'s domain `α` = BVar 0 under the α binder.
        let sigma_ty = {
            let a0 = kernel.bvar(0);
            let beta_ty = kernel.pi(anon, a0, type_v, BinderInfo::Default);
            let inner = kernel.pi(anon, beta_ty, result_sort, BinderInfo::Default);
            kernel.pi(anon, type_u, inner, BinderInfo::Default)
        };

        // mk : Π (α) (β) (fst : α) (snd : β fst), Sigma α β.
        //   binders outer→inner: α, β, fst, snd.
        //   result under all four: α = BVar 3, β = BVar 2.
        //   `snd : β fst` under α, β, fst: β = BVar 1, fst = BVar 0.
        //   `fst : α`     under α, β:      α = BVar 1.
        let mk_ty = {
            let a3 = kernel.bvar(3);
            let b2 = kernel.bvar(2);
            let sigma_ab = {
                let e = kernel.app(sigma_const, a3);
                kernel.app(e, b2)
            };
            let b1 = kernel.bvar(1);
            let f0 = kernel.bvar(0);
            let beta_fst = kernel.app(b1, f0);
            let inner_snd = kernel.pi(anon, beta_fst, sigma_ab, BinderInfo::Default);
            let a1 = kernel.bvar(1);
            let inner_fst = kernel.pi(anon, a1, inner_snd, BinderInfo::Default);
            let a0 = kernel.bvar(0);
            let beta_ty = kernel.pi(anon, a0, type_v, BinderInfo::Default);
            let inner_beta = kernel.pi(anon, beta_ty, inner_fst, BinderInfo::Default);
            kernel.pi(anon, type_u, inner_beta, BinderInfo::Default)
        };

        kernel.add_inductive(
            sigma,
            &[sigma_uparam_u, sigma_uparam_v],
            2,
            sigma_ty,
            &[(sigma_mk, mk_ty)],
        )?;
    }
    let sigma_rec = kernel.name_str(sigma, "rec");
    let sigma_fst = kernel.name_str(sigma, "fst");
    let sigma_snd = kernel.name_str(sigma, "snd");
    let sigma_fst_mk = kernel.name_str(sigma, "fst_mk");
    let sigma_snd_mk = kernel.name_str(sigma, "snd_mk");
    let sigma_mk_eta = kernel.name_str(sigma, "mk_eta");

    // --- Sigma.fst.{u,v} : Π (α) (β) (s : Sigma α β), α --------------------
    // := fun α β s => Sigma.rec.{u+1, u, v} α β (fun _ => α) (fun a b => a) s.
    {
        let u_lvl = kernel.level_param(sigma_uparam_u);
        let v_lvl = kernel.level_param(sigma_uparam_v);
        let succ_u = kernel.level_succ(u_lvl);
        let succ_v = kernel.level_succ(v_lvl);
        let type_u = kernel.sort(succ_u);
        let type_v = kernel.sort(succ_v);

        let alpha = kernel.fvar(SIGMA_ALPHA);
        let beta = kernel.fvar(SIGMA_BETA);
        let beta_ty = pi_fvar(kernel, SIGMA_A, alpha, type_v);
        let sigma_const = kernel.const_(sigma, vec![u_lvl, v_lvl]);
        let sigma_ab = apply_all(kernel, sigma_const, &[alpha, beta]);

        let motive = lam_fvar(kernel, SIGMA_PAIR, sigma_ab, alpha);
        let minor = {
            let a = kernel.fvar(SIGMA_A);
            let beta_a = kernel.app(beta, a);
            let inner = lam_fvar(kernel, SIGMA_B, beta_a, a);
            lam_fvar(kernel, SIGMA_A, alpha, inner)
        };
        let pair = kernel.fvar(SIGMA_PAIR);
        let rec_const = kernel.const_(sigma_rec, vec![succ_u, u_lvl, v_lvl]);
        let body = apply_all(kernel, rec_const, &[alpha, beta, motive, minor, pair]);

        let value = {
            let with_pair = lam_fvar(kernel, SIGMA_PAIR, sigma_ab, body);
            let with_beta = lam_fvar(kernel, SIGMA_BETA, beta_ty, with_pair);
            lam_fvar(kernel, SIGMA_ALPHA, type_u, with_beta)
        };
        let ty = {
            let with_pair = pi_fvar(kernel, SIGMA_PAIR, sigma_ab, alpha);
            let with_beta = pi_fvar(kernel, SIGMA_BETA, beta_ty, with_pair);
            pi_fvar(kernel, SIGMA_ALPHA, type_u, with_beta)
        };
        kernel.add_declaration(Declaration::Definition {
            name: sigma_fst,
            uparams: vec![sigma_uparam_u, sigma_uparam_v],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // --- Sigma.snd.{u,v} : Π (α) (β) (s : Sigma α β), β (Sigma.fst α β s) ---
    // := fun α β s => Sigma.rec.{v+1, u, v} α β
    //                   (fun y => β (Sigma.fst α β y)) (fun a b => b) s.
    // The minor's expected type is `β (Sigma.fst α β (Sigma.mk α β a b))`,
    // which ι- then δ-reduces to `β a` — exactly `b`'s type.
    {
        let u_lvl = kernel.level_param(sigma_uparam_u);
        let v_lvl = kernel.level_param(sigma_uparam_v);
        let succ_u = kernel.level_succ(u_lvl);
        let succ_v = kernel.level_succ(v_lvl);
        let type_u = kernel.sort(succ_u);
        let type_v = kernel.sort(succ_v);

        let alpha = kernel.fvar(SIGMA_ALPHA);
        let beta = kernel.fvar(SIGMA_BETA);
        let beta_ty = pi_fvar(kernel, SIGMA_A, alpha, type_v);
        let sigma_const = kernel.const_(sigma, vec![u_lvl, v_lvl]);
        let sigma_ab = apply_all(kernel, sigma_const, &[alpha, beta]);

        let fst_const = kernel.const_(sigma_fst, vec![u_lvl, v_lvl]);
        let motive = {
            let y = kernel.fvar(SIGMA_Y);
            let fst_y = apply_all(kernel, fst_const, &[alpha, beta, y]);
            let claim = kernel.app(beta, fst_y);
            lam_fvar(kernel, SIGMA_Y, sigma_ab, claim)
        };
        let minor = {
            let a = kernel.fvar(SIGMA_A);
            let beta_a = kernel.app(beta, a);
            let b = kernel.fvar(SIGMA_B);
            let inner = lam_fvar(kernel, SIGMA_B, beta_a, b);
            lam_fvar(kernel, SIGMA_A, alpha, inner)
        };
        let pair = kernel.fvar(SIGMA_PAIR);
        let rec_const = kernel.const_(sigma_rec, vec![succ_v, u_lvl, v_lvl]);
        let body = apply_all(kernel, rec_const, &[alpha, beta, motive, minor, pair]);

        let value = {
            let with_pair = lam_fvar(kernel, SIGMA_PAIR, sigma_ab, body);
            let with_beta = lam_fvar(kernel, SIGMA_BETA, beta_ty, with_pair);
            lam_fvar(kernel, SIGMA_ALPHA, type_u, with_beta)
        };
        let ty = {
            let fst_pair = apply_all(kernel, fst_const, &[alpha, beta, pair]);
            let codomain = kernel.app(beta, fst_pair);
            let with_pair = pi_fvar(kernel, SIGMA_PAIR, sigma_ab, codomain);
            let with_beta = pi_fvar(kernel, SIGMA_BETA, beta_ty, with_pair);
            pi_fvar(kernel, SIGMA_ALPHA, type_u, with_beta)
        };
        kernel.add_declaration(Declaration::Definition {
            name: sigma_snd,
            uparams: vec![sigma_uparam_u, sigma_uparam_v],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // --- Sigma.fst_mk / Sigma.snd_mk ---------------------------------------
    // Both close by `Eq.refl`: the recursor ι-reduces on the literal
    // constructor `Sigma.mk α β a b`, the same route `Nat.Fin.val_mk` takes.
    {
        let u_lvl = kernel.level_param(sigma_uparam_u);
        let v_lvl = kernel.level_param(sigma_uparam_v);
        let succ_u = kernel.level_succ(u_lvl);
        let succ_v = kernel.level_succ(v_lvl);
        let type_u = kernel.sort(succ_u);
        let type_v = kernel.sort(succ_v);

        let alpha = kernel.fvar(SIGMA_ALPHA);
        let beta = kernel.fvar(SIGMA_BETA);
        let beta_ty = pi_fvar(kernel, SIGMA_A, alpha, type_v);
        let a = kernel.fvar(SIGMA_A);
        let beta_a = kernel.app(beta, a);
        let b = kernel.fvar(SIGMA_B);

        let mk_const = kernel.const_(sigma_mk, vec![u_lvl, v_lvl]);
        let mk_ab = apply_all(kernel, mk_const, &[alpha, beta, a, b]);
        let fst_const = kernel.const_(sigma_fst, vec![u_lvl, v_lvl]);
        let snd_const = kernel.const_(sigma_snd, vec![u_lvl, v_lvl]);

        // fst_mk : ∀ α β a b, Eq α (Sigma.fst α β (Sigma.mk α β a b)) a.
        {
            let lhs = apply_all(kernel, fst_const, &[alpha, beta, mk_ab]);
            let stmt = eq_app(kernel, eq, succ_u, alpha, lhs, a);
            let proof = eq_refl_app(kernel, eq_refl, succ_u, alpha, a);
            let ty = {
                let with_b = pi_fvar(kernel, SIGMA_B, beta_a, stmt);
                let with_a = pi_fvar(kernel, SIGMA_A, alpha, with_b);
                let with_beta = pi_fvar(kernel, SIGMA_BETA, beta_ty, with_a);
                pi_fvar(kernel, SIGMA_ALPHA, type_u, with_beta)
            };
            let value = {
                let with_b = lam_fvar(kernel, SIGMA_B, beta_a, proof);
                let with_a = lam_fvar(kernel, SIGMA_A, alpha, with_b);
                let with_beta = lam_fvar(kernel, SIGMA_BETA, beta_ty, with_a);
                lam_fvar(kernel, SIGMA_ALPHA, type_u, with_beta)
            };
            kernel.add_declaration(Declaration::Theorem {
                name: sigma_fst_mk,
                uparams: vec![sigma_uparam_u, sigma_uparam_v],
                ty,
                value,
            })?;
        }

        // snd_mk : ∀ α β a b, Eq (β a) (Sigma.snd α β (Sigma.mk α β a b)) b.
        // `Sigma.snd (mk a b)` has type `β (Sigma.fst (mk a b))`, definitionally
        // `β a` — so stating it at the carrier `β a` is well-typed, and that is
        // the whole content of a *dependent* second projection computing.
        {
            let lhs = apply_all(kernel, snd_const, &[alpha, beta, mk_ab]);
            let stmt = eq_app(kernel, eq, succ_v, beta_a, lhs, b);
            let proof = eq_refl_app(kernel, eq_refl, succ_v, beta_a, b);
            let ty = {
                let with_b = pi_fvar(kernel, SIGMA_B, beta_a, stmt);
                let with_a = pi_fvar(kernel, SIGMA_A, alpha, with_b);
                let with_beta = pi_fvar(kernel, SIGMA_BETA, beta_ty, with_a);
                pi_fvar(kernel, SIGMA_ALPHA, type_u, with_beta)
            };
            let value = {
                let with_b = lam_fvar(kernel, SIGMA_B, beta_a, proof);
                let with_a = lam_fvar(kernel, SIGMA_A, alpha, with_b);
                let with_beta = lam_fvar(kernel, SIGMA_BETA, beta_ty, with_a);
                lam_fvar(kernel, SIGMA_ALPHA, type_u, with_beta)
            };
            kernel.add_declaration(Declaration::Theorem {
                name: sigma_snd_mk,
                uparams: vec![sigma_uparam_u, sigma_uparam_v],
                ty,
                value,
            })?;
        }
    }

    // --- Sigma.mk_eta : ∀ α β s, Eq (Sigma α β) (mk (fst s) (snd s)) s ------
    // Proved by `Sigma.rec.{0,u,v}` with the equation as motive; the minor at
    // `mk a b` ι-reduces to `mk a b = mk a b`, closed by `Eq.refl`.
    {
        let u_lvl = kernel.level_param(sigma_uparam_u);
        let v_lvl = kernel.level_param(sigma_uparam_v);
        let succ_u = kernel.level_succ(u_lvl);
        let succ_v = kernel.level_succ(v_lvl);
        let zero_lvl = kernel.level_zero();
        let type_u = kernel.sort(succ_u);
        let type_v = kernel.sort(succ_v);
        let carrier_lvl = {
            let max_uv = kernel.level_max(u_lvl, v_lvl);
            kernel.level_succ(max_uv)
        };

        let alpha = kernel.fvar(SIGMA_ALPHA);
        let beta = kernel.fvar(SIGMA_BETA);
        let beta_ty = pi_fvar(kernel, SIGMA_A, alpha, type_v);
        let sigma_const = kernel.const_(sigma, vec![u_lvl, v_lvl]);
        let sigma_ab = apply_all(kernel, sigma_const, &[alpha, beta]);

        let mk_const = kernel.const_(sigma_mk, vec![u_lvl, v_lvl]);
        let fst_const = kernel.const_(sigma_fst, vec![u_lvl, v_lvl]);
        let snd_const = kernel.const_(sigma_snd, vec![u_lvl, v_lvl]);

        let rebuilt = |kernel: &mut Kernel, s: ExprId| {
            let fst_s = apply_all(kernel, fst_const, &[alpha, beta, s]);
            let snd_s = apply_all(kernel, snd_const, &[alpha, beta, s]);
            apply_all(kernel, mk_const, &[alpha, beta, fst_s, snd_s])
        };

        let motive = {
            let y = kernel.fvar(SIGMA_Y);
            let lhs = rebuilt(kernel, y);
            let claim = eq_app(kernel, eq, carrier_lvl, sigma_ab, lhs, y);
            lam_fvar(kernel, SIGMA_Y, sigma_ab, claim)
        };
        let minor = {
            let a = kernel.fvar(SIGMA_A);
            let beta_a = kernel.app(beta, a);
            let b = kernel.fvar(SIGMA_B);
            let mk_ab = apply_all(kernel, mk_const, &[alpha, beta, a, b]);
            let proof = eq_refl_app(kernel, eq_refl, carrier_lvl, sigma_ab, mk_ab);
            let inner = lam_fvar(kernel, SIGMA_B, beta_a, proof);
            lam_fvar(kernel, SIGMA_A, alpha, inner)
        };
        let pair = kernel.fvar(SIGMA_PAIR);
        let rec_const = kernel.const_(sigma_rec, vec![zero_lvl, u_lvl, v_lvl]);
        let body = apply_all(kernel, rec_const, &[alpha, beta, motive, minor, pair]);

        let ty = {
            let lhs = rebuilt(kernel, pair);
            let claim = eq_app(kernel, eq, carrier_lvl, sigma_ab, lhs, pair);
            let with_pair = pi_fvar(kernel, SIGMA_PAIR, sigma_ab, claim);
            let with_beta = pi_fvar(kernel, SIGMA_BETA, beta_ty, with_pair);
            pi_fvar(kernel, SIGMA_ALPHA, type_u, with_beta)
        };
        let value = {
            let with_pair = lam_fvar(kernel, SIGMA_PAIR, sigma_ab, body);
            let with_beta = lam_fvar(kernel, SIGMA_BETA, beta_ty, with_pair);
            lam_fvar(kernel, SIGMA_ALPHA, type_u, with_beta)
        };
        kernel.add_declaration(Declaration::Theorem {
            name: sigma_mk_eta,
            uparams: vec![sigma_uparam_u, sigma_uparam_v],
            ty,
            value,
        })?;
    }

    // --- PSigma.{u,v} (α : Sort u) (β : α → Sort v) : Sort (max u v) --------
    let psigma_uparam_u = kernel.name_str(anon, "u");
    let psigma_uparam_v = kernel.name_str(anon, "v");
    let psigma = kernel.name_str(anon, "PSigma");
    let psigma_mk = kernel.name_str(psigma, "mk");
    {
        let u_lvl = kernel.level_param(psigma_uparam_u);
        let v_lvl = kernel.level_param(psigma_uparam_v);
        let sort_u = kernel.sort(u_lvl);
        let sort_v = kernel.sort(v_lvl);
        // `Sort (max 1 u v)`, exactly Lean's own `PSigma`, and NOT
        // `Sort (max u v)`. See the module doc: this kernel admits the latter
        // and soundly denies it large elimination, but real Lean refuses the
        // declaration outright, and the shared-prelude crosscheck is what
        // measured that. We follow Lean.
        let result_sort = {
            let zero = kernel.level_zero();
            let one = kernel.level_succ(zero);
            let max_uv = kernel.level_max(u_lvl, v_lvl);
            let result_level = kernel.level_max(one, max_uv);
            kernel.sort(result_level)
        };
        let psigma_const = kernel.const_(psigma, vec![u_lvl, v_lvl]);

        let psigma_ty = {
            let a0 = kernel.bvar(0);
            let beta_ty = kernel.pi(anon, a0, sort_v, BinderInfo::Default);
            let inner = kernel.pi(anon, beta_ty, result_sort, BinderInfo::Default);
            kernel.pi(anon, sort_u, inner, BinderInfo::Default)
        };
        let mk_ty = {
            let a3 = kernel.bvar(3);
            let b2 = kernel.bvar(2);
            let psigma_ab = {
                let e = kernel.app(psigma_const, a3);
                kernel.app(e, b2)
            };
            let b1 = kernel.bvar(1);
            let f0 = kernel.bvar(0);
            let beta_fst = kernel.app(b1, f0);
            let inner_snd = kernel.pi(anon, beta_fst, psigma_ab, BinderInfo::Default);
            let a1 = kernel.bvar(1);
            let inner_fst = kernel.pi(anon, a1, inner_snd, BinderInfo::Default);
            let a0 = kernel.bvar(0);
            let beta_ty = kernel.pi(anon, a0, sort_v, BinderInfo::Default);
            let inner_beta = kernel.pi(anon, beta_ty, inner_fst, BinderInfo::Default);
            kernel.pi(anon, sort_u, inner_beta, BinderInfo::Default)
        };
        kernel.add_inductive(
            psigma,
            &[psigma_uparam_u, psigma_uparam_v],
            2,
            psigma_ty,
            &[(psigma_mk, mk_ty)],
        )?;
    }
    let psigma_rec = kernel.name_str(psigma, "rec");
    let psigma_fst = kernel.name_str(psigma, "fst");
    let psigma_snd = kernel.name_str(psigma, "snd");

    // --- PSigma.fst / PSigma.snd ------------------------------------------
    // The same two definitions as `Sigma`'s, one universe lower: `α : Sort u`
    // rather than `Type u`, so the motive levels are `u` and `v` themselves.
    {
        let u_lvl = kernel.level_param(psigma_uparam_u);
        let v_lvl = kernel.level_param(psigma_uparam_v);
        let sort_u = kernel.sort(u_lvl);
        let sort_v = kernel.sort(v_lvl);

        let alpha = kernel.fvar(PSIGMA_ALPHA);
        let beta = kernel.fvar(PSIGMA_BETA);
        let beta_ty = pi_fvar(kernel, PSIGMA_A, alpha, sort_v);
        let psigma_const = kernel.const_(psigma, vec![u_lvl, v_lvl]);
        let psigma_ab = apply_all(kernel, psigma_const, &[alpha, beta]);

        // fst := fun α β p => PSigma.rec.{u,u,v} α β (fun _ => α) (fun a b => a) p.
        {
            let motive = lam_fvar(kernel, PSIGMA_PAIR, psigma_ab, alpha);
            let minor = {
                let a = kernel.fvar(PSIGMA_A);
                let beta_a = kernel.app(beta, a);
                let inner = lam_fvar(kernel, PSIGMA_B, beta_a, a);
                lam_fvar(kernel, PSIGMA_A, alpha, inner)
            };
            let pair = kernel.fvar(PSIGMA_PAIR);
            let rec_const = kernel.const_(psigma_rec, vec![u_lvl, u_lvl, v_lvl]);
            let body = apply_all(kernel, rec_const, &[alpha, beta, motive, minor, pair]);
            let value = {
                let with_pair = lam_fvar(kernel, PSIGMA_PAIR, psigma_ab, body);
                let with_beta = lam_fvar(kernel, PSIGMA_BETA, beta_ty, with_pair);
                lam_fvar(kernel, PSIGMA_ALPHA, sort_u, with_beta)
            };
            let ty = {
                let with_pair = pi_fvar(kernel, PSIGMA_PAIR, psigma_ab, alpha);
                let with_beta = pi_fvar(kernel, PSIGMA_BETA, beta_ty, with_pair);
                pi_fvar(kernel, PSIGMA_ALPHA, sort_u, with_beta)
            };
            kernel.add_declaration(Declaration::Definition {
                name: psigma_fst,
                uparams: vec![psigma_uparam_u, psigma_uparam_v],
                ty,
                value,
                hint: ReducibilityHint::Regular(1),
            })?;
        }

        // snd := fun α β p => PSigma.rec.{v,u,v} α β
        //          (fun y => β (PSigma.fst α β y)) (fun a b => b) p.
        {
            let fst_const = kernel.const_(psigma_fst, vec![u_lvl, v_lvl]);
            let motive = {
                let y = kernel.fvar(PSIGMA_Y);
                let fst_y = apply_all(kernel, fst_const, &[alpha, beta, y]);
                let claim = kernel.app(beta, fst_y);
                lam_fvar(kernel, PSIGMA_Y, psigma_ab, claim)
            };
            let minor = {
                let a = kernel.fvar(PSIGMA_A);
                let beta_a = kernel.app(beta, a);
                let b = kernel.fvar(PSIGMA_B);
                let inner = lam_fvar(kernel, PSIGMA_B, beta_a, b);
                lam_fvar(kernel, PSIGMA_A, alpha, inner)
            };
            let pair = kernel.fvar(PSIGMA_PAIR);
            let rec_const = kernel.const_(psigma_rec, vec![v_lvl, u_lvl, v_lvl]);
            let body = apply_all(kernel, rec_const, &[alpha, beta, motive, minor, pair]);
            let value = {
                let with_pair = lam_fvar(kernel, PSIGMA_PAIR, psigma_ab, body);
                let with_beta = lam_fvar(kernel, PSIGMA_BETA, beta_ty, with_pair);
                lam_fvar(kernel, PSIGMA_ALPHA, sort_u, with_beta)
            };
            let ty = {
                let fst_pair = apply_all(kernel, fst_const, &[alpha, beta, pair]);
                let codomain = kernel.app(beta, fst_pair);
                let with_pair = pi_fvar(kernel, PSIGMA_PAIR, psigma_ab, codomain);
                let with_beta = pi_fvar(kernel, PSIGMA_BETA, beta_ty, with_pair);
                pi_fvar(kernel, PSIGMA_ALPHA, sort_u, with_beta)
            };
            kernel.add_declaration(Declaration::Definition {
                name: psigma_snd,
                uparams: vec![psigma_uparam_u, psigma_uparam_v],
                ty,
                value,
                hint: ReducibilityHint::Regular(1),
            })?;
        }
    }

    // --- Subtype.{u} (α : Sort u) (p : α → Prop) : Sort (max 1 u) ----------
    let subtype_uparam = kernel.name_str(anon, "u");
    let subtype = kernel.name_str(anon, "Subtype");
    let subtype_mk = kernel.name_str(subtype, "mk");
    {
        let u_lvl = kernel.level_param(subtype_uparam);
        let sort_u = kernel.sort(u_lvl);
        let prop = kernel.sort_zero();
        let result_sort = {
            let zero = kernel.level_zero();
            let one = kernel.level_succ(zero);
            let max_1u = kernel.level_max(one, u_lvl);
            kernel.sort(max_1u)
        };
        let subtype_const = kernel.const_(subtype, vec![u_lvl]);

        // ty := Π (α : Sort u) (p : α → Prop), Sort (max 1 u).
        let subtype_ty = {
            let a0 = kernel.bvar(0);
            let p_ty = kernel.pi(anon, a0, prop, BinderInfo::Default);
            let inner = kernel.pi(anon, p_ty, result_sort, BinderInfo::Default);
            kernel.pi(anon, sort_u, inner, BinderInfo::Default)
        };
        // mk : Π (α) (p) (val : α) (property : p val), Subtype α p.
        let mk_ty = {
            let a3 = kernel.bvar(3);
            let p2 = kernel.bvar(2);
            let subtype_ap = {
                let e = kernel.app(subtype_const, a3);
                kernel.app(e, p2)
            };
            let p1 = kernel.bvar(1);
            let v0 = kernel.bvar(0);
            let p_val = kernel.app(p1, v0);
            let inner_property = kernel.pi(anon, p_val, subtype_ap, BinderInfo::Default);
            let a1 = kernel.bvar(1);
            let inner_val = kernel.pi(anon, a1, inner_property, BinderInfo::Default);
            let a0 = kernel.bvar(0);
            let p_ty = kernel.pi(anon, a0, prop, BinderInfo::Default);
            let inner_p = kernel.pi(anon, p_ty, inner_val, BinderInfo::Default);
            kernel.pi(anon, sort_u, inner_p, BinderInfo::Default)
        };
        kernel.add_inductive(
            subtype,
            &[subtype_uparam],
            2,
            subtype_ty,
            &[(subtype_mk, mk_ty)],
        )?;
    }
    let subtype_rec = kernel.name_str(subtype, "rec");
    let subtype_val = kernel.name_str(subtype, "val");
    let subtype_property = kernel.name_str(subtype, "property");
    let subtype_val_mk = kernel.name_str(subtype, "val_mk");
    let subtype_mk_eta = kernel.name_str(subtype, "mk_eta");

    // --- Subtype.val.{u} : Π (α) (p) (s : Subtype α p), α ------------------
    // := fun α p s => Subtype.rec.{u, u} α p (fun _ => α) (fun v _ => v) s.
    {
        let u_lvl = kernel.level_param(subtype_uparam);
        let sort_u = kernel.sort(u_lvl);
        let prop = kernel.sort_zero();

        let alpha = kernel.fvar(SUBTYPE_ALPHA);
        let predicate = kernel.fvar(SUBTYPE_P);
        let p_ty = pi_fvar(kernel, SUBTYPE_A, alpha, prop);
        let subtype_const = kernel.const_(subtype, vec![u_lvl]);
        let subtype_ap = apply_all(kernel, subtype_const, &[alpha, predicate]);

        let motive = lam_fvar(kernel, SUBTYPE_S, subtype_ap, alpha);
        let minor = {
            let a = kernel.fvar(SUBTYPE_A);
            let p_a = kernel.app(predicate, a);
            let inner = lam_fvar(kernel, SUBTYPE_H, p_a, a);
            lam_fvar(kernel, SUBTYPE_A, alpha, inner)
        };
        let s = kernel.fvar(SUBTYPE_S);
        let rec_const = kernel.const_(subtype_rec, vec![u_lvl, u_lvl]);
        let body = apply_all(kernel, rec_const, &[alpha, predicate, motive, minor, s]);

        let value = {
            let with_s = lam_fvar(kernel, SUBTYPE_S, subtype_ap, body);
            let with_p = lam_fvar(kernel, SUBTYPE_P, p_ty, with_s);
            lam_fvar(kernel, SUBTYPE_ALPHA, sort_u, with_p)
        };
        let ty = {
            let with_s = pi_fvar(kernel, SUBTYPE_S, subtype_ap, alpha);
            let with_p = pi_fvar(kernel, SUBTYPE_P, p_ty, with_s);
            pi_fvar(kernel, SUBTYPE_ALPHA, sort_u, with_p)
        };
        kernel.add_declaration(Declaration::Definition {
            name: subtype_val,
            uparams: vec![subtype_uparam],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // --- Subtype.property.{u} : ∀ α p s, p (Subtype.val α p s) -------------
    // := fun α p s => Subtype.rec.{0, u} α p (fun y => p (val α p y))
    //                   (fun v h => h) s.
    {
        let u_lvl = kernel.level_param(subtype_uparam);
        let zero_lvl = kernel.level_zero();
        let sort_u = kernel.sort(u_lvl);
        let prop = kernel.sort_zero();

        let alpha = kernel.fvar(SUBTYPE_ALPHA);
        let predicate = kernel.fvar(SUBTYPE_P);
        let p_ty = pi_fvar(kernel, SUBTYPE_A, alpha, prop);
        let subtype_const = kernel.const_(subtype, vec![u_lvl]);
        let subtype_ap = apply_all(kernel, subtype_const, &[alpha, predicate]);
        let val_const = kernel.const_(subtype_val, vec![u_lvl]);

        let motive = {
            let y = kernel.fvar(SUBTYPE_Y);
            let val_y = apply_all(kernel, val_const, &[alpha, predicate, y]);
            let claim = kernel.app(predicate, val_y);
            lam_fvar(kernel, SUBTYPE_Y, subtype_ap, claim)
        };
        let minor = {
            let a = kernel.fvar(SUBTYPE_A);
            let p_a = kernel.app(predicate, a);
            let h = kernel.fvar(SUBTYPE_H);
            let inner = lam_fvar(kernel, SUBTYPE_H, p_a, h);
            lam_fvar(kernel, SUBTYPE_A, alpha, inner)
        };
        let s = kernel.fvar(SUBTYPE_S);
        let rec_const = kernel.const_(subtype_rec, vec![zero_lvl, u_lvl]);
        let body = apply_all(kernel, rec_const, &[alpha, predicate, motive, minor, s]);

        let ty = {
            let val_s = apply_all(kernel, val_const, &[alpha, predicate, s]);
            let claim = kernel.app(predicate, val_s);
            let with_s = pi_fvar(kernel, SUBTYPE_S, subtype_ap, claim);
            let with_p = pi_fvar(kernel, SUBTYPE_P, p_ty, with_s);
            pi_fvar(kernel, SUBTYPE_ALPHA, sort_u, with_p)
        };
        let value = {
            let with_s = lam_fvar(kernel, SUBTYPE_S, subtype_ap, body);
            let with_p = lam_fvar(kernel, SUBTYPE_P, p_ty, with_s);
            lam_fvar(kernel, SUBTYPE_ALPHA, sort_u, with_p)
        };
        kernel.add_declaration(Declaration::Theorem {
            name: subtype_property,
            uparams: vec![subtype_uparam],
            ty,
            value,
        })?;
    }

    // --- Subtype.val_mk / Subtype.mk_eta -----------------------------------
    {
        let u_lvl = kernel.level_param(subtype_uparam);
        let zero_lvl = kernel.level_zero();
        let sort_u = kernel.sort(u_lvl);
        let prop = kernel.sort_zero();
        let carrier_lvl = {
            let zero = kernel.level_zero();
            let one = kernel.level_succ(zero);
            kernel.level_max(one, u_lvl)
        };

        let alpha = kernel.fvar(SUBTYPE_ALPHA);
        let predicate = kernel.fvar(SUBTYPE_P);
        let p_ty = pi_fvar(kernel, SUBTYPE_A, alpha, prop);
        let subtype_const = kernel.const_(subtype, vec![u_lvl]);
        let subtype_ap = apply_all(kernel, subtype_const, &[alpha, predicate]);
        let mk_const = kernel.const_(subtype_mk, vec![u_lvl]);
        let val_const = kernel.const_(subtype_val, vec![u_lvl]);
        let property_const = kernel.const_(subtype_property, vec![u_lvl]);

        // val_mk : ∀ α p a (h : p a), Eq α (val α p (mk α p a h)) a.
        {
            let a = kernel.fvar(SUBTYPE_A);
            let p_a = kernel.app(predicate, a);
            let h = kernel.fvar(SUBTYPE_H);
            let mk_ah = apply_all(kernel, mk_const, &[alpha, predicate, a, h]);
            let lhs = apply_all(kernel, val_const, &[alpha, predicate, mk_ah]);
            let stmt = eq_app(kernel, eq, u_lvl, alpha, lhs, a);
            let proof = eq_refl_app(kernel, eq_refl, u_lvl, alpha, a);
            let ty = {
                let with_h = pi_fvar(kernel, SUBTYPE_H, p_a, stmt);
                let with_a = pi_fvar(kernel, SUBTYPE_A, alpha, with_h);
                let with_p = pi_fvar(kernel, SUBTYPE_P, p_ty, with_a);
                pi_fvar(kernel, SUBTYPE_ALPHA, sort_u, with_p)
            };
            let value = {
                let with_h = lam_fvar(kernel, SUBTYPE_H, p_a, proof);
                let with_a = lam_fvar(kernel, SUBTYPE_A, alpha, with_h);
                let with_p = lam_fvar(kernel, SUBTYPE_P, p_ty, with_a);
                lam_fvar(kernel, SUBTYPE_ALPHA, sort_u, with_p)
            };
            kernel.add_declaration(Declaration::Theorem {
                name: subtype_val_mk,
                uparams: vec![subtype_uparam],
                ty,
                value,
            })?;
        }

        // mk_eta : ∀ α p s, Eq (Subtype α p) (mk (val s) (property s)) s.
        {
            let rebuilt = |kernel: &mut Kernel, s: ExprId| {
                let val_s = apply_all(kernel, val_const, &[alpha, predicate, s]);
                let prop_s = apply_all(kernel, property_const, &[alpha, predicate, s]);
                apply_all(kernel, mk_const, &[alpha, predicate, val_s, prop_s])
            };
            let motive = {
                let y = kernel.fvar(SUBTYPE_Y);
                let lhs = rebuilt(kernel, y);
                let claim = eq_app(kernel, eq, carrier_lvl, subtype_ap, lhs, y);
                lam_fvar(kernel, SUBTYPE_Y, subtype_ap, claim)
            };
            let minor = {
                let a = kernel.fvar(SUBTYPE_A);
                let p_a = kernel.app(predicate, a);
                let h = kernel.fvar(SUBTYPE_H);
                let mk_ah = apply_all(kernel, mk_const, &[alpha, predicate, a, h]);
                let proof = eq_refl_app(kernel, eq_refl, carrier_lvl, subtype_ap, mk_ah);
                let inner = lam_fvar(kernel, SUBTYPE_H, p_a, proof);
                lam_fvar(kernel, SUBTYPE_A, alpha, inner)
            };
            let s = kernel.fvar(SUBTYPE_S);
            let rec_const = kernel.const_(subtype_rec, vec![zero_lvl, u_lvl]);
            let body = apply_all(kernel, rec_const, &[alpha, predicate, motive, minor, s]);

            let ty = {
                let lhs = rebuilt(kernel, s);
                let claim = eq_app(kernel, eq, carrier_lvl, subtype_ap, lhs, s);
                let with_s = pi_fvar(kernel, SUBTYPE_S, subtype_ap, claim);
                let with_p = pi_fvar(kernel, SUBTYPE_P, p_ty, with_s);
                pi_fvar(kernel, SUBTYPE_ALPHA, sort_u, with_p)
            };
            let value = {
                let with_s = lam_fvar(kernel, SUBTYPE_S, subtype_ap, body);
                let with_p = lam_fvar(kernel, SUBTYPE_P, p_ty, with_s);
                lam_fvar(kernel, SUBTYPE_ALPHA, sort_u, with_p)
            };
            kernel.add_declaration(Declaration::Theorem {
                name: subtype_mk_eta,
                uparams: vec![subtype_uparam],
                ty,
                value,
            })?;
        }
    }

    Ok(SigmaNames {
        sigma,
        sigma_mk,
        sigma_rec,
        sigma_fst,
        sigma_snd,
        sigma_fst_mk,
        sigma_snd_mk,
        sigma_mk_eta,
        sigma_uparam_u,
        sigma_uparam_v,
        psigma,
        psigma_mk,
        psigma_rec,
        psigma_fst,
        psigma_snd,
        psigma_uparam_u,
        psigma_uparam_v,
        subtype,
        subtype_mk,
        subtype_rec,
        subtype_val,
        subtype_property,
        subtype_val_mk,
        subtype_mk_eta,
        subtype_uparam,
    })
}
