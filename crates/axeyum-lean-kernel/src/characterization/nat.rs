//! The **Peano characterization of `Nat`**: the three Peano axioms, the
//! universal property (initiality) of `Nat` as an iteration algebra, and the
//! categoricity theorem that pins our `Nat` to *the* natural numbers up to a
//! unique isomorphism.
//!
//! Every statement here is built in this module and handed to the kernel's
//! trusted gate together with its proof, so a statement that drifts is a
//! rejection rather than a silently weaker claim.

// Proof scripts are long, straight-line term constructions over short
// mathematical names; splitting them would obscure the derivation they mirror,
// and the near-identical binder names (`hzs`/`hsi`, `f_up`/`g_up`) are the
// statement's own vocabulary.
#![allow(
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_lines,
    clippy::type_complexity
)]

use crate::KernelError;
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::name::NameId;
use crate::nat_prelude::NatOps;

use super::Weakening;
use super::ops::CharDev;

/// Delta height for `Nat.Peano.iter`: above every `Nat`/`Int` definition in the
/// environment, as the reducibility contract requires.
const ITER_HEIGHT: u16 = 40;

/// The interned names of the `Nat` characterization package.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NatCharacterization {
    /// The `Nat.Peano` namespace root.
    pub root: NameId,
    /// The universe parameter `u` shared by the carrier-generic declarations.
    pub uparam: NameId,
    /// **Peano 1** — `∀ (n : Nat), Not (Eq Nat Nat.zero (Nat.succ n))`.
    pub zero_ne_succ: NameId,
    /// **Peano 2** — `∀ (m n : Nat), Eq Nat (succ m) (succ n) → Eq Nat m n`.
    pub succ_injective: NameId,
    /// **Peano 3** — `∀ (P : Nat → Prop), P zero → (∀ n, P n → P (succ n)) → ∀ n, P n`,
    /// discharged by the kernel-generated recursor `Nat.rec`.
    pub induction: NameId,
    /// `Nat.Peano.iter.{u} : ∀ (A : Sort u), A → (A → A) → Nat → A` — the
    /// iterator, i.e. the *existence* half of the universal property.
    pub iter: NameId,
    /// `iter A a f zero = a`.
    pub iter_zero: NameId,
    /// `iter A a f (succ n) = f (iter A a f n)`.
    pub iter_succ: NameId,
    /// The *uniqueness* half: any `h` with the same two equations equals `iter`.
    pub iter_unique: NameId,
    /// The comparison map into any Peano structure is surjective.
    pub surjective: NameId,
    /// The comparison map into any Peano structure is injective.
    pub injective: NameId,
    /// **Categoricity** — for every Peano structure `(N, z, s)`, `iter N z s` is
    /// a structure-preserving bijection `Nat → N`.
    pub categorical: NameId,
}

/// Apply `Nat.Peano.iter.{u} ty z s x`.
fn iter_app(
    dev: &mut CharDev<'_>,
    iter: ExprId,
    ty: ExprId,
    z: ExprId,
    s: ExprId,
    x: ExprId,
) -> ExprId {
    dev.apply(iter, &[ty, z, s, x])
}

/// Declare the whole `Nat.Peano` package.
///
/// # Errors
///
/// Returns the trusted gate's rejection. Every `Err` here means the kernel
/// **refused** one of the characterization proofs.
#[allow(clippy::too_many_lines)]
pub(super) fn declare(
    dev: &mut CharDev<'_>,
    weaken: Weakening,
) -> Result<NatCharacterization, KernelError> {
    let anon = dev.anon_name();
    let nat_name = dev.int_prelude().nat.nat;
    let root = dev.kernel().name_str(nat_name, "Peano");
    let names = NatCharacterization {
        root,
        uparam: dev.kernel().name_str(anon, "u"),
        zero_ne_succ: dev.kernel().name_str(root, "zero_ne_succ"),
        succ_injective: dev.kernel().name_str(root, "succ_injective"),
        induction: dev.kernel().name_str(root, "induction"),
        iter: dev.kernel().name_str(root, "iter"),
        iter_zero: dev.kernel().name_str(root, "iter_zero"),
        iter_succ: dev.kernel().name_str(root, "iter_succ"),
        iter_unique: dev.kernel().name_str(root, "iter_unique"),
        surjective: dev.kernel().name_str(root, "surjective"),
        injective: dev.kernel().name_str(root, "injective"),
        categorical: dev.kernel().name_str(root, "categorical"),
    };

    let nat = dev.nat_ty();
    let prop = dev.prop_ty();
    let one = dev.level_one();
    let zero_lvl = dev.level_zero();
    let u_lvl = dev.level_of(names.uparam);
    let sort_u = dev.sort_at(u_lvl);
    let zero = dev.zero();

    // ---- Peano 1: zero is not a successor -----------------------------------
    //
    // The discriminator is the standard one: a `Prop`-valued recursion sending
    // `zero` to `True` and every successor to `False`, so transporting
    // `True.intro` along `zero = succ n` lands in `False`.
    {
        let discriminator = {
            let motive = dev.lam_const(nat, prop);
            let true_ty = dev.true_ty();
            let false_ty = dev.false_ty();
            let succ_case = {
                let inner = dev.lam_const(prop, false_ty);
                dev.lam_const(nat, inner)
            };
            let rec_name = dev.prelude().rec;
            let rec = dev.kernel().const_(rec_name, vec![one]);
            dev.apply(rec, &[motive, true_ty, succ_case])
        };

        let n_fv = dev.fresh_fvar();
        let n = dev.kernel().fvar(n_fv);
        let succ_n = dev.succ(n);
        // The equation the hypothesis carries. The reversed variant is a
        // negative control: the transport below is oriented, so it must fail.
        let hypothesis = if weaken == Weakening::ZeroNeSuccReversed {
            dev.eq(succ_n, zero)
        } else {
            dev.eq(zero, succ_n)
        };
        let statement = {
            let negated = dev.not_of(hypothesis);
            dev.pi_fv(n_fv, nat, negated)
        };

        let h_fv = dev.fresh_fvar();
        let h = dev.kernel().fvar(h_fv);
        let motive = dev.eq_motive(zero, &|d, x| d.apply(discriminator, &[x]));
        let true_intro = dev.true_intro();
        let contradiction = dev.transport(zero, motive, true_intro, succ_n, h);
        let value = {
            let inner = dev.lam_fv(h_fv, hypothesis, contradiction);
            dev.lam_fv(n_fv, nat, inner)
        };
        dev.declare_theorem_u(names.zero_ne_succ, vec![], statement, value)?;
    }

    // ---- Peano 2: successor is injective ------------------------------------
    //
    // Stated here and discharged by the prelude's own theorem, so the kernel
    // checks that `Nat.succ_injective` really has the Peano statement.
    {
        let m_fv = dev.fresh_fvar();
        let m = dev.kernel().fvar(m_fv);
        let n_fv = dev.fresh_fvar();
        let n = dev.kernel().fvar(n_fv);
        let succ_m = dev.succ(m);
        let succ_n = dev.succ(n);
        let hypothesis = dev.eq(succ_m, succ_n);
        let conclusion = dev.eq(m, n);
        let body = dev.arrow(hypothesis, conclusion);
        let statement = dev.close_pi(&[(m_fv, nat), (n_fv, nat)], body);
        let existing = dev.prelude().succ_injective;
        let value = dev.kernel().const_(existing, vec![]);
        dev.declare_theorem_u(names.succ_injective, vec![], statement, value)?;
    }

    // ---- Peano 3: induction, from the kernel-generated recursor -------------
    {
        let p_ty = dev.arrow(nat, prop);
        let p_fv = dev.fresh_fvar();
        let p = dev.kernel().fvar(p_fv);
        // The base point the hypothesis is demanded at. `succ zero` is a
        // negative control: `Nat.rec`'s zero minor premise is at `zero`.
        let base_point = if weaken == Weakening::InductionBaseAtOne {
            dev.succ(zero)
        } else {
            zero
        };
        let base_ty = dev.apply(p, &[base_point]);
        let step_ty = {
            let k_fv = dev.fresh_fvar();
            let k = dev.kernel().fvar(k_fv);
            let p_k = dev.apply(p, &[k]);
            let succ_k = dev.succ(k);
            let p_succ_k = dev.apply(p, &[succ_k]);
            let body = dev.arrow(p_k, p_succ_k);
            dev.pi_fv(k_fv, nat, body)
        };
        let base_fv = dev.fresh_fvar();
        let base = dev.kernel().fvar(base_fv);
        let step_fv = dev.fresh_fvar();
        let step = dev.kernel().fvar(step_fv);
        let n_fv = dev.fresh_fvar();
        let n = dev.kernel().fvar(n_fv);
        let binders = [
            (p_fv, p_ty),
            (base_fv, base_ty),
            (step_fv, step_ty),
            (n_fv, nat),
        ];
        let conclusion = dev.apply(p, &[n]);
        let statement = dev.close_pi(&binders, conclusion);
        let rec_name = dev.prelude().rec;
        let rec = dev.kernel().const_(rec_name, vec![zero_lvl]);
        let body = dev.apply(rec, &[p, base, step, n]);
        let value = dev.close_lam(&binders, body);
        dev.declare_theorem_u(names.induction, vec![], statement, value)?;
    }

    // ---- The universal property: existence ----------------------------------
    //
    // `iter A a f` is the unique arrow from `(Nat, zero, succ)` into the
    // iteration algebra `(A, a, f)`. Existence is a definition by `Nat.rec`;
    // the two computation rules below hold definitionally.
    {
        let a_fv = dev.fresh_fvar();
        let a_ty = dev.kernel().fvar(a_fv);
        let point_fv = dev.fresh_fvar();
        let point = dev.kernel().fvar(point_fv);
        let f_ty = dev.arrow(a_ty, a_ty);
        let f_fv = dev.fresh_fvar();
        let f = dev.kernel().fvar(f_fv);
        let n_fv = dev.fresh_fvar();
        let n = dev.kernel().fvar(n_fv);
        let motive = dev.lam_const(nat, a_ty);
        let step = {
            let j_fv = dev.fresh_fvar();
            let ih_fv = dev.fresh_fvar();
            let ih = dev.kernel().fvar(ih_fv);
            let body = dev.apply(f, &[ih]);
            let inner = dev.lam_fv(ih_fv, a_ty, body);
            dev.lam_fv(j_fv, nat, inner)
        };
        let rec_name = dev.prelude().rec;
        let rec = dev.kernel().const_(rec_name, vec![u_lvl]);
        let body = dev.apply(rec, &[motive, point, step, n]);
        let binders = [(a_fv, sort_u), (point_fv, a_ty), (f_fv, f_ty), (n_fv, nat)];
        let ty = dev.close_pi(&binders, a_ty);
        let value = dev.close_lam(&binders, body);
        dev.declare_definition_u(names.iter, vec![names.uparam], ty, value, ITER_HEIGHT)?;
    }

    let iter_const = dev.kernel().const_(names.iter, vec![u_lvl]);

    // ---- The two computation rules ------------------------------------------
    {
        let a_fv = dev.fresh_fvar();
        let a_ty = dev.kernel().fvar(a_fv);
        let point_fv = dev.fresh_fvar();
        let point = dev.kernel().fvar(point_fv);
        let f_ty = dev.arrow(a_ty, a_ty);
        let f_fv = dev.fresh_fvar();
        let f = dev.kernel().fvar(f_fv);
        let head = [(a_fv, sort_u), (point_fv, a_ty), (f_fv, f_ty)];

        let applied_zero = iter_app(dev, iter_const, a_ty, point, f, zero);
        let equation = dev.eq_at(u_lvl, a_ty, applied_zero, point);
        let statement = dev.close_pi(&head, equation);
        let proof = dev.refl_at(u_lvl, a_ty, point);
        let value = dev.close_lam(&head, proof);
        dev.declare_theorem_u(names.iter_zero, vec![names.uparam], statement, value)?;

        let n_fv = dev.fresh_fvar();
        let n = dev.kernel().fvar(n_fv);
        let succ_n = dev.succ(n);
        let applied_succ = iter_app(dev, iter_const, a_ty, point, f, succ_n);
        let applied_n = iter_app(dev, iter_const, a_ty, point, f, n);
        let stepped = dev.apply(f, &[applied_n]);
        let equation = dev.eq_at(u_lvl, a_ty, applied_succ, stepped);
        let binders = [(a_fv, sort_u), (point_fv, a_ty), (f_fv, f_ty), (n_fv, nat)];
        let statement = dev.close_pi(&binders, equation);
        let proof = dev.refl_at(u_lvl, a_ty, stepped);
        let value = dev.close_lam(&binders, proof);
        dev.declare_theorem_u(names.iter_succ, vec![names.uparam], statement, value)?;
    }

    // ---- The universal property: uniqueness ---------------------------------
    {
        let a_fv = dev.fresh_fvar();
        let a_ty = dev.kernel().fvar(a_fv);
        let point_fv = dev.fresh_fvar();
        let point = dev.kernel().fvar(point_fv);
        let f_ty = dev.arrow(a_ty, a_ty);
        let f_fv = dev.fresh_fvar();
        let f = dev.kernel().fvar(f_fv);
        let h_ty = dev.arrow(nat, a_ty);
        let h_fv = dev.fresh_fvar();
        let h = dev.kernel().fvar(h_fv);

        let h_zero = dev.apply(h, &[zero]);
        let true_ty = dev.true_ty();
        // Dropping the zero equation is a negative control: the base case of
        // the induction below is exactly that hypothesis.
        let hz_ty = if weaken == Weakening::IterUniqueDropZeroHypothesis {
            true_ty
        } else {
            dev.eq_at(u_lvl, a_ty, h_zero, point)
        };
        let hz_fv = dev.fresh_fvar();
        let hz = dev.kernel().fvar(hz_fv);
        let hs_ty = {
            let k_fv = dev.fresh_fvar();
            let k = dev.kernel().fvar(k_fv);
            let succ_k = dev.succ(k);
            let h_succ_k = dev.apply(h, &[succ_k]);
            let h_k = dev.apply(h, &[k]);
            let f_h_k = dev.apply(f, &[h_k]);
            let body = dev.eq_at(u_lvl, a_ty, h_succ_k, f_h_k);
            dev.pi_fv(k_fv, nat, body)
        };
        let hs_fv = dev.fresh_fvar();
        let hs = dev.kernel().fvar(hs_fv);
        let n_fv = dev.fresh_fvar();
        let n = dev.kernel().fvar(n_fv);

        let motive = |d: &mut CharDev<'_>, x: ExprId| {
            let left = d.apply(h, &[x]);
            let right = iter_app(d, iter_const, a_ty, point, f, x);
            d.eq_at(u_lvl, a_ty, left, right)
        };
        let proof = dev.induct(
            &motive,
            &|_d| hz,
            &|d, k, ih| {
                let succ_k = d.succ(k);
                let h_succ_k = d.apply(h, &[succ_k]);
                let h_k = d.apply(h, &[k]);
                let f_h_k = d.apply(f, &[h_k]);
                let iter_k = iter_app(d, iter_const, a_ty, point, f, k);
                let f_iter_k = d.apply(f, &[iter_k]);
                let congruence = d.congr_at(u_lvl, a_ty, u_lvl, a_ty, h_k, iter_k, ih, &|d2, x| {
                    d2.apply(f, &[x])
                });
                let stepped = d.apply(hs, &[k]);
                d.trans_at(u_lvl, a_ty, h_succ_k, f_h_k, f_iter_k, stepped, congruence)
            },
            n,
        );

        let binders = [
            (a_fv, sort_u),
            (point_fv, a_ty),
            (f_fv, f_ty),
            (h_fv, h_ty),
            (hz_fv, hz_ty),
            (hs_fv, hs_ty),
            (n_fv, nat),
        ];
        let conclusion = motive(dev, n);
        let statement = dev.close_pi(&binders, conclusion);
        let value = dev.close_lam(&binders, proof);
        dev.declare_theorem_u(names.iter_unique, vec![names.uparam], statement, value)?;
    }

    // ---- Categoricity: the comparison map is a bijection --------------------
    //
    // A "Peano structure" is a carrier `N` with a point `z`, an endomorphism
    // `s`, and the three Peano axioms. `iter N z s` preserves the structure
    // definitionally; the content is that it is injective and surjective.
    let carrier_fv = dev.fresh_fvar();
    let carrier = dev.kernel().fvar(carrier_fv);
    let point_fv = dev.fresh_fvar();
    let point = dev.kernel().fvar(point_fv);
    let step_ty = dev.arrow(carrier, carrier);
    let step_fv = dev.fresh_fvar();
    let step = dev.kernel().fvar(step_fv);
    let true_ty = dev.true_ty();

    // `∀ (n : N), Not (Eq N z (s n))`
    let hzs_ty = {
        let n_fv = dev.fresh_fvar();
        let n = dev.kernel().fvar(n_fv);
        let s_n = dev.apply(step, &[n]);
        let equation = dev.eq_at(u_lvl, carrier, point, s_n);
        let negated = dev.not_of(equation);
        dev.pi_fv(n_fv, carrier, negated)
    };
    // `∀ (m n : N), Eq N (s m) (s n) → Eq N m n`
    let hsi_ty = {
        let m_fv = dev.fresh_fvar();
        let m = dev.kernel().fvar(m_fv);
        let n_fv = dev.fresh_fvar();
        let n = dev.kernel().fvar(n_fv);
        let s_m = dev.apply(step, &[m]);
        let s_n = dev.apply(step, &[n]);
        let hypothesis = dev.eq_at(u_lvl, carrier, s_m, s_n);
        let conclusion = dev.eq_at(u_lvl, carrier, m, n);
        let body = dev.arrow(hypothesis, conclusion);
        dev.close_pi(&[(m_fv, carrier), (n_fv, carrier)], body)
    };
    // `∀ (P : N → Prop), P z → (∀ n, P n → P (s n)) → ∀ n, P n`
    let hind_ty = {
        let p_ty = dev.arrow(carrier, prop);
        let p_fv = dev.fresh_fvar();
        let p = dev.kernel().fvar(p_fv);
        let base_ty = dev.apply(p, &[point]);
        let inner_step_ty = {
            let n_fv = dev.fresh_fvar();
            let n = dev.kernel().fvar(n_fv);
            let p_n = dev.apply(p, &[n]);
            let s_n = dev.apply(step, &[n]);
            let p_s_n = dev.apply(p, &[s_n]);
            let body = dev.arrow(p_n, p_s_n);
            dev.pi_fv(n_fv, carrier, body)
        };
        let tail = {
            let n_fv = dev.fresh_fvar();
            let n = dev.kernel().fvar(n_fv);
            let body = dev.apply(p, &[n]);
            dev.pi_fv(n_fv, carrier, body)
        };
        let after_step = dev.arrow(inner_step_ty, tail);
        let after_base = dev.arrow(base_ty, after_step);
        dev.pi_fv(p_fv, p_ty, after_base)
    };

    let hzs_fv = dev.fresh_fvar();
    let hzs = dev.kernel().fvar(hzs_fv);
    let hsi_fv = dev.fresh_fvar();
    let hsi = dev.kernel().fvar(hsi_fv);
    let hind_fv = dev.fresh_fvar();
    let hind = dev.kernel().fvar(hind_fv);

    // `∀ k m, iter N z s k = iter N z s m → k = m`
    let injective_tail = {
        let k_fv = dev.fresh_fvar();
        let k = dev.kernel().fvar(k_fv);
        let m_fv = dev.fresh_fvar();
        let m = dev.kernel().fvar(m_fv);
        let left = iter_app(dev, iter_const, carrier, point, step, k);
        let right = iter_app(dev, iter_const, carrier, point, step, m);
        let hypothesis = dev.eq_at(u_lvl, carrier, left, right);
        let conclusion = dev.eq(k, m);
        let body = dev.arrow(hypothesis, conclusion);
        dev.close_pi(&[(k_fv, nat), (m_fv, nat)], body)
    };
    // `∀ y, ∃ k, iter N z s k = y`
    let surjective_tail = {
        let y_fv = dev.fresh_fvar();
        let y = dev.kernel().fvar(y_fv);
        let k_fv = dev.fresh_fvar();
        let k = dev.kernel().fvar(k_fv);
        let applied = iter_app(dev, iter_const, carrier, point, step, k);
        let equation = dev.eq_at(u_lvl, carrier, applied, y);
        let predicate = dev.lam_fv(k_fv, nat, equation);
        let body = dev.exists_at(one, nat, predicate);
        dev.pi_fv(y_fv, carrier, body)
    };

    // ---- surjectivity --------------------------------------------------------
    {
        let hind_ty_here = if weaken == Weakening::SurjectiveDropInduction {
            true_ty
        } else {
            hind_ty
        };
        let y_fv = dev.fresh_fvar();
        let y = dev.kernel().fvar(y_fv);

        // `Q := fun y => ∃ k, iter N z s k = y`
        let reachable = |d: &mut CharDev<'_>, target: ExprId| {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let applied = iter_app(d, iter_const, carrier, point, step, k);
            let equation = d.eq_at(u_lvl, carrier, applied, target);
            let predicate = d.lam_fv(k_fv, nat, equation);
            (predicate, d.exists_at(one, nat, predicate))
        };
        let reachable_predicate = |d: &mut CharDev<'_>, target: ExprId| reachable(d, target).0;
        let reachable_prop = |d: &mut CharDev<'_>, target: ExprId| reachable(d, target).1;

        let motive = {
            let m_fv = dev.fresh_fvar();
            let m = dev.kernel().fvar(m_fv);
            let body = reachable_prop(dev, m);
            dev.lam_fv(m_fv, carrier, body)
        };
        let base = {
            let predicate = reachable_predicate(dev, point);
            let proof = dev.refl_at(u_lvl, carrier, point);
            dev.exists_intro_at(one, nat, predicate, zero, proof)
        };
        let inductive_step = {
            let m_fv = dev.fresh_fvar();
            let m = dev.kernel().fvar(m_fv);
            let ih_ty = reachable_prop(dev, m);
            let s_m = dev.apply(step, &[m]);
            let target = reachable_prop(dev, s_m);
            let predicate_m = reachable_predicate(dev, m);
            let predicate_s_m = reachable_predicate(dev, s_m);
            let minor = {
                let k_fv = dev.fresh_fvar();
                let k = dev.kernel().fvar(k_fv);
                let applied = iter_app(dev, iter_const, carrier, point, step, k);
                let hk_ty = dev.eq_at(u_lvl, carrier, applied, m);
                let hk_fv = dev.fresh_fvar();
                let hk = dev.kernel().fvar(hk_fv);
                let lifted =
                    dev.congr_at(u_lvl, carrier, u_lvl, carrier, applied, m, hk, &|d, x| {
                        d.apply(step, &[x])
                    });
                let succ_k = dev.succ(k);
                let witnessed = dev.exists_intro_at(one, nat, predicate_s_m, succ_k, lifted);
                let inner = dev.lam_fv(hk_fv, hk_ty, witnessed);
                dev.lam_fv(k_fv, nat, inner)
            };
            let ih_fv = dev.fresh_fvar();
            let ih = dev.kernel().fvar(ih_fv);
            let eliminated = dev.exists_elim_at(one, nat, predicate_m, target, minor, ih);
            let inner = dev.lam_fv(ih_fv, ih_ty, eliminated);
            dev.lam_fv(m_fv, carrier, inner)
        };
        let body = dev.apply(hind, &[motive, base, inductive_step, y]);
        let binders = [
            (carrier_fv, sort_u),
            (point_fv, carrier),
            (step_fv, step_ty),
            (hind_fv, hind_ty_here),
            (y_fv, carrier),
        ];
        let conclusion = reachable_prop(dev, y);
        let statement = dev.close_pi(&binders, conclusion);
        let value = dev.close_lam(&binders, body);
        dev.declare_theorem_u(names.surjective, vec![names.uparam], statement, value)?;
    }

    // ---- injectivity ---------------------------------------------------------
    {
        let hzs_ty_here = if weaken == Weakening::InjectiveDropZeroNeSucc {
            true_ty
        } else {
            hzs_ty
        };
        let hsi_ty_here = if weaken == Weakening::InjectiveDropSuccInjective {
            true_ty
        } else {
            hsi_ty
        };
        let structure = PeanoStructure {
            iter: iter_const,
            carrier,
            point,
            step,
            level: u_lvl,
            zero_ne_succ: hzs,
            succ_injective: hsi,
        };
        let k_fv = dev.fresh_fvar();
        let k = dev.kernel().fvar(k_fv);
        let m_fv = dev.fresh_fvar();
        let m = dev.kernel().fvar(m_fv);
        let phi_k = iter_app(dev, iter_const, carrier, point, step, k);
        let phi_m = iter_app(dev, iter_const, carrier, point, step, m);
        let h_ty = dev.eq_at(u_lvl, carrier, phi_k, phi_m);
        let h_fv = dev.fresh_fvar();
        let h = dev.kernel().fvar(h_fv);

        let proof = dev.induct(
            &|d, i| injective_motive(d, structure, i),
            &|d| injective_at(d, structure, zero, None),
            &|d, i, ih| {
                let succ_i = d.succ(i);
                injective_at(d, structure, succ_i, Some((i, ih)))
            },
            k,
        );
        let applied = dev.apply(proof, &[m, h]);
        let binders = [
            (carrier_fv, sort_u),
            (point_fv, carrier),
            (step_fv, step_ty),
            (hzs_fv, hzs_ty_here),
            (hsi_fv, hsi_ty_here),
            (k_fv, nat),
            (m_fv, nat),
            (h_fv, h_ty),
        ];
        let conclusion = dev.eq(k, m);
        let statement = dev.close_pi(&binders, conclusion);
        let value = dev.close_lam(&binders, applied);
        dev.declare_theorem_u(names.injective, vec![names.uparam], statement, value)?;
    }

    // ---- the packaged categoricity statement --------------------------------
    {
        let hom_zero = {
            let applied = iter_app(dev, iter_const, carrier, point, step, zero);
            dev.eq_at(u_lvl, carrier, applied, point)
        };
        let hom_succ = {
            let k_fv = dev.fresh_fvar();
            let k = dev.kernel().fvar(k_fv);
            let succ_k = dev.succ(k);
            let left = iter_app(dev, iter_const, carrier, point, step, succ_k);
            let inner = iter_app(dev, iter_const, carrier, point, step, k);
            let right = dev.apply(step, &[inner]);
            let body = dev.eq_at(u_lvl, carrier, left, right);
            dev.pi_fv(k_fv, nat, body)
        };
        let preserves = dev.and_of(hom_zero, hom_succ);
        let bijective = dev.and_of(injective_tail, surjective_tail);
        let conclusion = dev.and_of(preserves, bijective);
        let binders = [
            (carrier_fv, sort_u),
            (point_fv, carrier),
            (step_fv, step_ty),
            (hzs_fv, hzs_ty),
            (hsi_fv, hsi_ty),
            (hind_fv, hind_ty),
        ];
        let statement = dev.close_pi(&binders, conclusion);

        let hom_zero_proof = dev.refl_at(u_lvl, carrier, point);
        let hom_succ_proof = {
            let k_fv = dev.fresh_fvar();
            let k = dev.kernel().fvar(k_fv);
            let inner = iter_app(dev, iter_const, carrier, point, step, k);
            let right = dev.apply(step, &[inner]);
            let body = dev.refl_at(u_lvl, carrier, right);
            dev.lam_fv(k_fv, nat, body)
        };
        let preserves_proof = dev.and_intro(hom_zero, hom_succ, hom_zero_proof, hom_succ_proof);
        let injective_proof = {
            let head = dev.kernel().const_(names.injective, vec![u_lvl]);
            dev.apply(head, &[carrier, point, step, hzs, hsi])
        };
        let surjective_proof = {
            let head = dev.kernel().const_(names.surjective, vec![u_lvl]);
            dev.apply(head, &[carrier, point, step, hind])
        };
        let bijective_proof = dev.and_intro(
            injective_tail,
            surjective_tail,
            injective_proof,
            surjective_proof,
        );
        let body = dev.and_intro(preserves, bijective, preserves_proof, bijective_proof);
        let value = dev.close_lam(&binders, body);
        dev.declare_theorem_u(names.categorical, vec![names.uparam], statement, value)?;
    }

    Ok(names)
}

/// The data of a Peano structure `(N, z, s)` together with the two
/// discrimination hypotheses, threaded through the injectivity proof.
#[derive(Debug, Clone, Copy)]
struct PeanoStructure {
    /// `Nat.Peano.iter.{u}` as a constant term.
    iter: ExprId,
    /// The carrier `N`.
    carrier: ExprId,
    /// The point `z : N`.
    point: ExprId,
    /// The endomorphism `s : N -> N`.
    step: ExprId,
    /// The universe level of the carrier.
    level: LevelId,
    /// A proof of `forall n, Not (Eq N z (s n))`.
    zero_ne_succ: ExprId,
    /// A proof of `forall m n, Eq N (s m) (s n) -> Eq N m n`.
    succ_injective: ExprId,
}

/// The comparison map `iter N z s x`.
fn phi(dev: &mut CharDev<'_>, s: PeanoStructure, x: ExprId) -> ExprId {
    iter_app(dev, s.iter, s.carrier, s.point, s.step, x)
}

/// `iter i = iter j -> i = j`, the inner statement at a fixed `i`.
fn injective_step_statement(
    dev: &mut CharDev<'_>,
    s: PeanoStructure,
    i: ExprId,
    j: ExprId,
) -> ExprId {
    let left = phi(dev, s, i);
    let right = phi(dev, s, j);
    let hypothesis = dev.eq_at(s.level, s.carrier, left, right);
    let conclusion = dev.eq(i, j);
    dev.arrow(hypothesis, conclusion)
}

/// `P i := forall j, iter i = iter j -> i = j`, the outer induction motive.
fn injective_motive(dev: &mut CharDev<'_>, s: PeanoStructure, i: ExprId) -> ExprId {
    let j_fv = dev.fresh_fvar();
    let j = dev.kernel().fvar(j_fv);
    let body = injective_step_statement(dev, s, i, j);
    let nat = dev.nat_ty();
    dev.pi_fv(j_fv, nat, body)
}

/// A proof of `P i`, by an inner induction on the second argument.
///
/// `predecessor` is `None` when `i` is `Nat.zero` and `Some((p, ih))` when `i`
/// is `Nat.succ p` and `ih : P p` is the outer induction hypothesis. Passing
/// the predecessor explicitly (rather than recovering it with `Nat.pred`) keeps
/// every obligation syntactically the one the kernel expects.
fn injective_at(
    dev: &mut CharDev<'_>,
    s: PeanoStructure,
    i: ExprId,
    predecessor: Option<(ExprId, ExprId)>,
) -> ExprId {
    let nat = dev.nat_ty();
    let zero = dev.zero();
    let j_fv = dev.fresh_fvar();
    let j = dev.kernel().fvar(j_fv);
    let inner = dev.induct(
        &|d, x| injective_step_statement(d, s, i, x),
        &|d| {
            // Second argument is `zero`.
            let left = phi(d, s, i);
            let right = phi(d, s, zero);
            let hyp_ty = d.eq_at(s.level, s.carrier, left, right);
            let h_fv = d.fresh_fvar();
            let hypothesis = d.kernel().fvar(h_fv);
            let body = if let Some((p, _)) = predecessor {
                // `i = succ p`, so `iter i = s (iter p)` and `iter zero = z`:
                // flipping the equation contradicts `z != s _`.
                let target = d.eq(i, zero);
                let flipped = d.symm_at(s.level, s.carrier, left, right, hypothesis);
                let phi_p = phi(d, s, p);
                let contradiction = d.apply(s.zero_ne_succ, &[phi_p, flipped]);
                d.absurd(target, contradiction)
            } else {
                // `i = zero`: reflexivity.
                d.refl(zero)
            };
            d.lam_fv(h_fv, hyp_ty, body)
        },
        &|d, jj, _inner_ih| {
            // Second argument is `succ jj`.
            let succ_j = d.succ(jj);
            let left = phi(d, s, i);
            let right = phi(d, s, succ_j);
            let hyp_ty = d.eq_at(s.level, s.carrier, left, right);
            let h_fv = d.fresh_fvar();
            let hypothesis = d.kernel().fvar(h_fv);
            let body = if let Some((p, ih)) = predecessor {
                // Both sides are successors: strip them and use the outer IH.
                let phi_p = phi(d, s, p);
                let phi_j = phi(d, s, jj);
                let stripped = d.apply(s.succ_injective, &[phi_p, phi_j, hypothesis]);
                let equal = d.apply(ih, &[jj, stripped]);
                d.congr(p, jj, equal, &|d2, x| d2.succ(x))
            } else {
                // `i = zero`: `z = s (iter jj)` contradicts Peano 1.
                let target = d.eq(zero, succ_j);
                let phi_j = phi(d, s, jj);
                let contradiction = d.apply(s.zero_ne_succ, &[phi_j, hypothesis]);
                d.absurd(target, contradiction)
            };
            d.lam_fv(h_fv, hyp_ty, body)
        },
        j,
    );
    dev.lam_fv(j_fv, nat, inner)
}
