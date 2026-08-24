//! `Int.factorial`, the self-inverse analysis Wilson's theorem needs, and
//! `Int.factorial_pos` — the assembly slice toward Wilson's theorem
//! (`p` prime ⟹ `(p-1)! ≡ -1 [p]`).
//!
//! ## What lands here, and what does not
//!
//! `Int.factorial` (a `prodRange` instance) and `Int.self_inverse_mod_prime`
//! (the genuinely prime-theoretic heart: `a*a ≡ 1 [p]` forces `a ≡ ±1 [p]`,
//! via `Int.euclid_lemma` deciding which factor of `(a-1)(a+1)` `p` divides —
//! a real constructive disjunction, not excluded middle) are both proved
//! here, axiom-free.
//!
//! Wilson's theorem itself is **not** declared, and the reason has narrowed
//! twice since this module was written. The classical proof collapses
//! `prodRange` over `2..p-2` by pairing each survivor with its distinct
//! inverse — a permutation argument. `Int.prodRange : (Nat → Int) → Nat → Int`
//! folds over a fixed *initial segment* `{0,…,n-1}`; the set of not-yet-paired
//! survivors is in general not an initial segment (the partner of a small
//! index can be a large one), so the induction hypothesis the collapse needs —
//! "the product over the remaining unpaired elements is `1`" — cannot even be
//! *stated* as a `prodRange` term, let alone proved by it.
//!
//! What is missing is the rearrangement principle
//! `prodRange f n = prodRange (f ∘ σ) n` for `σ` a permutation of
//! `{0,…,n-1}`.
//!
//! **An earlier revision of this paragraph said the kernel has "no `Finset`,
//! no `Fin n`, no `Equiv`, and no notion of a bijection of a finite range at
//! all". That is no longer true** (2026-08-23). `Nat.Fin`,
//! `Nat.injectiveOn` / `surjectiveOn` / `mapsInto`, and the pigeonhole
//! principle connecting them (`Nat.injective_on_imp_surjective_on`) are all
//! declared and axiom-free; `Int.prodRange_swap_adjacent` proves the
//! adjacent-transposition case of the rearrangement, and (2026-08-24)
//! `Int.prodRange_swap` extends that to **any** two indices `i < j`, via
//! `prod.rs`'s `point_swap` (a `Nat.ble`-cascaded explicit swap function,
//! never `Nat.beq`) and a conjugation induction
//! `(j' j)(i j')(j' j) = (i j)` on the gap `j - i`.
//!
//! What is STILL missing is the full permutation, not just one transposition —
//! but the gap is now three named assembly steps, not a missing construction.
//!
//! **Earlier revisions of this paragraph said the recursive call needs `σ`
//! restricted with `i0` removed and REINDEXED DOWNWARD
//! (`σ'(k) := if k < i0 then σ(k) else σ(k+1)`). That turned out to be
//! unnecessary** (2026-08-24), and it is worth recording because three
//! successive drafts named it as the blocker. Applying `point_swap` to
//! `g := f ∘ σ` at `(i0, n)` — rather than to `σ` — reduces the recursive
//! obligation to `prodRange (f ∘ τ) n = prodRange f n` where `τ` is an
//! **override at `i0`**, not a shift: once the trivial `i0 = n` case is peeled
//! off, `i0` is already `< n`, so there is nothing to reindex.
//!
//! `Nat.restrict_injective` and `Nat.restrict_maps_into` (both in
//! `nat_prelude/finite.rs`, axiom-free) supply exactly that override's two
//! closure properties. What remains for `prodRange_permute`:
//!
//! 1. The `i0 = n` branch, which needs no restriction at all — just
//!    bound-weakening `injectiveOn σ (n+1) → injectiveOn σ n`, since `σ`
//!    already fixes `n`.
//! 2. The `i0 < n` branch: the `point_swap`-on-`g` application, threading the
//!    two restriction lemmas into the induction hypothesis.
//! 3. The `Exists`-elimination on the pigeonhole's result and the two-way case
//!    split on `i0` versus `n`, assembling both branches.
//!
//! Note the induction generalises over **σ, not over `f`** — unlike every
//! earlier proof in this chain, whose recursive calls took a different
//! function. Here the hypothesis reuses the same `f` and only `σ` becomes `τ`,
//! so `f` is quantified outside the `Nat.rec` with motive
//! `∀ σ, injectiveOn σ x → mapsInto σ x → prodRange f x = prodRange (f ∘ σ) x`.
//! Copying the earlier shape yields a motive that does not close.

use super::defs::POW_HEIGHT;
use super::ops::IntDev;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

/// Delta height for `Int.factorial`, which calls `Int.prodRange` (itself
/// `POW_HEIGHT + 1`, `prod.rs`'s private `PROD_RANGE_HEIGHT`); strictly
/// greater so unfolding order stays fixed.
const FACTORIAL_HEIGHT: u16 = POW_HEIGHT + 2;

/// Admit `Int.factorial : Nat → Int := Int.prodRange (fun k => Int.ofNat (Nat.succ k))`.
///
/// Mirrors `Nat.factorial`'s own convention exactly (`nat_prelude/defs.rs`):
/// the new factor is multiplied onto the **right** of the prior product, so
/// `factorial (succ n) ≡ factorial n * ofNat (succ n)` — the same shape as
/// `Nat.factorial (succ n) ≡ factorial n * succ n`, transported to `ℤ`.
///
/// # Errors
///
/// Returns the kernel's rejection if the generated definition does not
/// type-check or the name is already taken.
pub(super) fn declare_factorial(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let int_ty = d.int_ty();

    // f := fun (k : Nat) => Int.ofNat (Nat.succ k)
    let f = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let sk = d.succ(k);
        let body = d.of_nat(sk);
        d.lam_fv(k_fv, nat, body)
    };
    let prod_range = d.kernel().const_(p.prod_range, vec![]);
    let value = d.apply(prod_range, &[f]);
    let ty = d.arrow(nat, int_ty);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.factorial,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(FACTORIAL_HEIGHT),
    })
}

/// `factorial_zero : Eq Int (factorial zero) one` and
/// `factorial_succ : ∀ n, Eq Int (factorial (succ n)) (mul (factorial n) (ofNat (succ n)))`.
///
/// Both close by `Eq.refl` alone: `Int.factorial` unfolds to `Int.prodRange f`
/// for a fixed `f`, and `prodRange`'s own defining equations
/// (`prod.rs::declare_prod_range_equations`) are themselves `Eq.refl` proofs,
/// so the composition reduces all the way through with no rewrite needed —
/// the same signal `prodRange_zero`/`prodRange_succ` report for
/// `Int.prodRange` itself.
///
/// # Errors
///
/// Returns the trusted gate's rejection if a generated proof does not check.
pub(super) fn declare_factorial_equations(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();

    // factorial_zero : Eq Int (factorial zero) one
    {
        let zero = d.zero();
        let lhs = d.const_app(p.factorial, &[zero]);
        let one = d.ione();
        let stmt = d.ieq(lhs, one);
        let proof = d.irefl(one);
        d.declare_theorem(p.factorial_zero, stmt, proof)?;
    }

    // factorial_succ :
    //   ∀ (n : Nat), Eq Int (factorial (succ n)) (mul (factorial n) (ofNat (succ n))).
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let sn = d.succ(n);
        let lhs = d.const_app(p.factorial, &[sn]);
        let prior = d.const_app(p.factorial, &[n]);
        let sn_i = d.of_nat(sn);
        let rhs = d.imul(prior, sn_i);
        let stmt = d.ieq(lhs, rhs);
        let proof = d.irefl(rhs);

        let ty = d.pi_fv(n_fv, nat, stmt);
        let value = d.lam_fv(n_fv, nat, proof);
        d.declare_theorem(p.factorial_succ, ty, value)?;
    }
    Ok(())
}

/// `2 ≤ magnitude ∧ ∀ (x : Nat), x ∣ magnitude → Eq Nat x 1 ∨ Eq Nat x magnitude` —
/// the same inline primality convention `Int.euclid_lemma` uses (this
/// prelude has no `Prime` name over either carrier). Spelled out again here
/// rather than imported: `gcd.rs`'s copy (`int_prime_condition`) is not
/// `pub(super)`, and this is five lines.
fn prime_condition(d: &mut IntDev<'_>, magnitude: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let two_nat = d.num(2);
    let one_nat = d.num(1);
    let two_le = d.le(two_nat, magnitude);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let hyp = d.dvd(x, magnitude);
    let is_one = d.eq(x, one_nat);
    let is_whole = d.eq(x, magnitude);
    let disjunction = d.or(is_one, is_whole);
    let inner = d.arrow(hyp, disjunction);
    let clause = d.pi_fv(x_fv, nat, inner);
    d.and(two_le, clause)
}

/// `Eq Int (mul (sub a one) (add a one)) (sub (mul a a) one)` — the
/// difference of squares `(a-1)(a+1) = a*a - 1`.
///
/// Expansion: commute to `(a+1)*(a-1)`, distribute the subtraction via
/// `mul_sub`, expand `(a+1)*a` via `mul_comm`/`left_distrib`/`mul_one` into
/// `a*a+a`, collapse `(a+1)*1` to `a+1` via `mul_one`, commute that `a+1` to
/// `1+a`, and finish with
/// [`super::modeq::cancel_common_addend`]`(a*a, one, a)`, which is exactly
/// the `(X+r)-(Y+r) = X-Y` shape the last step needs.
fn diff_of_squares(d: &mut IntDev<'_>, a: ExprId) -> ExprId {
    let p = d.int();
    let one_i = d.ione();
    let aa = d.imul(a, a);
    let sub_a1 = d.isub(a, one_i);
    let add_a1 = d.iadd(a, one_i);
    let diff = d.isub(aa, one_i);

    let start = d.imul(sub_a1, add_a1);

    // (a-1)*(a+1) = (a+1)*(a-1)
    let t1 = d.imul(add_a1, sub_a1);
    let p1 = d.const_app(p.mul_comm, &[sub_a1, add_a1]);

    // (a+1)*(a-1) = (a+1)*a - (a+1)*1
    let m_add_a = d.imul(add_a1, a);
    let m_add_one = d.imul(add_a1, one_i);
    let t2 = d.isub(m_add_a, m_add_one);
    let p2 = d.const_app(p.mul_sub, &[add_a1, a, one_i]);

    // (a+1)*a = a*(a+1)
    let m_a_add = d.imul(a, add_a1);
    let t3 = d.isub(m_a_add, m_add_one);
    let p3_eq = d.const_app(p.mul_comm, &[add_a1, a]);
    let p3 = d.icongr(m_add_a, m_a_add, p3_eq, &|d, t| d.isub(t, m_add_one));

    // a*(a+1) = a*a + a*1
    let a_one = d.imul(a, one_i);
    let sum4 = d.iadd(aa, a_one);
    let t4 = d.isub(sum4, m_add_one);
    let p4_eq = d.const_app(p.left_distrib, &[a, a, one_i]);
    let p4 = d.icongr(m_a_add, sum4, p4_eq, &|d, t| d.isub(t, m_add_one));

    // a*1 = a
    let sum5 = d.iadd(aa, a);
    let t5 = d.isub(sum5, m_add_one);
    let p5_eq = d.const_app(p.mul_one, &[a]);
    let p5 = d.icongr(a_one, a, p5_eq, &|d, t| {
        let s = d.iadd(aa, t);
        d.isub(s, m_add_one)
    });

    // (a+1)*1 = a+1
    let t6 = d.isub(sum5, add_a1);
    let p6_eq = d.const_app(p.mul_one, &[add_a1]);
    let p6 = d.icongr(m_add_one, add_a1, p6_eq, &|d, t| d.isub(sum5, t));

    // a+1 = 1+a
    let one_add_a = d.iadd(one_i, a);
    let t7 = d.isub(sum5, one_add_a);
    let p7_eq = d.const_app(p.add_comm, &[a, one_i]);
    let p7 = d.icongr(add_a1, one_add_a, p7_eq, &|d, t| d.isub(sum5, t));

    // (a*a+a) - (1+a) = a*a - 1
    let p8 = super::modeq::cancel_common_addend(d, aa, one_i, a);

    let (_, proof) = d.ichain(
        start,
        &[
            (t1, p1),
            (t2, p2),
            (t3, p3),
            (t4, p4),
            (t5, p5),
            (t6, p6),
            (t7, p7),
            (diff, p8),
        ],
    );
    proof
}

/// `Int.self_inverse_mod_prime :
/// ∀ p a,
///   (2 ≤ natAbs p ∧ ∀ d, d ∣ natAbs p → d = 1 ∨ d = natAbs p) →
///   0 < p → 1 ≤ a → a ≤ p - 1 →
///   ModEq p (a*a) one →
///   Or (ModEq p a one) (ModEq p a (p - one))`
///
/// The genuinely prime-theoretic content Wilson's theorem needs: an element
/// that is its own modular inverse is congruent to `1` or `-1` (here `p-1`).
/// `0 < p` is threaded explicitly rather than derived — every `ModEq`
/// congruence in this development needs it for the same reason
/// (`modeq.rs`'s header), and deriving it from `1 ≤ a ≤ p-1` alone would cost
/// more order arithmetic than the lemma's actual content.
///
/// Route: `a*a ≡ 1 [p]` gives `p ∣ (a*a - 1)` (`ModEq.symm` +
/// `modEq_iff_dvd`); `a*a - 1 = (a-1)(a+1)` ([`diff_of_squares`]) transports
/// that into `p ∣ (a-1)(a+1)`; `Int.euclid_lemma` — fed the *same* inline
/// primality clause it already uses — **constructively** decides which
/// factor `p` divides (Euclid's lemma, not excluded middle). Each branch
/// converts back to a `ModEq` via `modEq_iff_dvd`'s `mpr`: the `a-1` branch
/// directly; the `a+1` branch through `ModEq p (-1) a` (relying on the
/// kernel reducing `neg (neg one)` to `one` on the concrete literal, exactly
/// as `gcd.rs`'s own `neg_neg` helper does) and then a `ModEq p (-1) (p-1)`
/// bridge built from `Int.dvd_refl p` transported along
/// [`super::modeq::cancel_neg_add`]`(p, one)`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_self_inverse_mod_prime(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.self_inverse_mod_prime, 2, &|d, v| {
        let (p_var, a) = (v[0], v[1]);
        let big_p = {
            let f = d.int().nat_abs;
            d.const_app(f, &[p_var])
        };
        let prime_ty = prime_condition(d, big_p);
        let zero = d.izero();
        let pos_ty = d.ilt(zero, p_var);
        let one_i = d.ione();
        let one_lb = d.ile(one_i, a);
        let p_minus_one = d.isub(p_var, one_i);
        let ub = d.ile(a, p_minus_one);
        let aa = d.imul(a, a);
        let sq_ty = super::modeq::imodeq(d, p_var, aa, one_i);
        let modeq_a_one = super::modeq::imodeq(d, p_var, a, one_i);
        let modeq_a_pm1 = super::modeq::imodeq(d, p_var, a, p_minus_one);
        let concl = d.or(modeq_a_one, modeq_a_pm1);

        let stmt = {
            let inner = d.arrow(sq_ty, concl);
            let with_ub = d.arrow(ub, inner);
            let with_lb = d.arrow(one_lb, with_ub);
            let with_pos = d.arrow(pos_ty, with_lb);
            d.arrow(prime_ty, with_pos)
        };

        let prime_fv = d.fresh_fvar();
        let h_prime = d.kernel().fvar(prime_fv);
        let pos_fv = d.fresh_fvar();
        let h_pos = d.kernel().fvar(pos_fv);
        let lb_fv = d.fresh_fvar();
        // Unused in the proof: primality + `0 < p` already force `p ≥ 2`, and
        // the algebra below never needs the concrete bound on `a` — kept
        // because the brief's statement carries it (`1 ≤ a ≤ p-1`), matching
        // the classical range Wilson's theorem quantifies `a` over.
        let _h_lb = d.kernel().fvar(lb_fv);
        let ub_fv = d.fresh_fvar();
        let _h_ub = d.kernel().fvar(ub_fv);
        let sq_fv = d.fresh_fvar();
        let h_sq = d.kernel().fvar(sq_fv);

        // Step 1: p ∣ (a*a - 1), from h_sq via ModEq.symm + modEq_iff_dvd.
        let symm_sq = d.const_app(p.mod_eq_symm, &[p_var, aa, one_i, h_sq]);
        let diff = d.isub(aa, one_i);
        let dvd_diff_ty = super::dvd::idvd(d, p_var, diff);
        let modeq_one_aa = super::modeq::imodeq(d, p_var, one_i, aa);
        let iff1 = d.const_app(p.mod_eq_iff_dvd, &[p_var, one_i, aa, h_pos]);
        let mp1 = d.const_app(p.logic.iff_mp, &[modeq_one_aa, dvd_diff_ty, iff1]);
        let dvd_diff = d.apply(mp1, &[symm_sq]);

        // Step 2: a*a - 1 = (a-1)*(a+1), transported.
        let sub_a1 = d.isub(a, one_i);
        let add_a1 = d.iadd(a, one_i);
        let prod = d.imul(sub_a1, add_a1);
        let prod_eq_start = diff_of_squares(d, a); // Eq Int prod diff
        let prod_eq = d.isymm(prod, diff, prod_eq_start); // Eq Int diff prod
        let motive = d.ieq_motive(diff, &|d, x| super::dvd::idvd(d, p_var, x));
        let dvd_prod = d.itransport(diff, motive, dvd_diff, prod, prod_eq);

        // Step 3: Euclid's lemma decides which factor `p` divides.
        let disj = d.const_app(p.euclid_lemma, &[p_var, sub_a1, add_a1, h_prime, dvd_prod]);
        let left_ty = super::dvd::idvd(d, p_var, sub_a1);
        let right_ty = super::dvd::idvd(d, p_var, add_a1);

        let on_left = &|d: &mut IntDev<'_>, h: ExprId| -> ExprId {
            let modeq_one_a_ty = super::modeq::imodeq(d, p_var, one_i, a);
            let dvd_l_ty = super::dvd::idvd(d, p_var, sub_a1);
            let iff_l = d.const_app(p.mod_eq_iff_dvd, &[p_var, one_i, a, h_pos]);
            let mpr_l = d.const_app(p.logic.iff_mpr, &[modeq_one_a_ty, dvd_l_ty, iff_l]);
            let modeq_one_a = d.apply(mpr_l, &[h]);
            let modeq_a_one_pf = d.const_app(p.mod_eq_symm, &[p_var, one_i, a, modeq_one_a]);
            d.or_inl(modeq_a_one, modeq_a_pm1, modeq_a_one_pf)
        };

        let on_right = &|d: &mut IntDev<'_>, h: ExprId| -> ExprId {
            let neg_one = d.ineg(one_i);

            // ModEq p (-1) a, from h : p ∣ (a+1), via `neg (neg one) = one`.
            let modeq_negone_a_ty = super::modeq::imodeq(d, p_var, neg_one, a);
            let a_minus_negone = d.isub(a, neg_one);
            let dvd_r1_ty = super::dvd::idvd(d, p_var, a_minus_negone);
            let iff_r1 = d.const_app(p.mod_eq_iff_dvd, &[p_var, neg_one, a, h_pos]);
            let mpr_r1 = d.const_app(p.logic.iff_mpr, &[modeq_negone_a_ty, dvd_r1_ty, iff_r1]);
            let modeq_negone_a = d.apply(mpr_r1, &[h]);
            let modeq_a_negone = d.const_app(p.mod_eq_symm, &[p_var, neg_one, a, modeq_negone_a]);

            // ModEq p (-1) (p-1), from `Int.dvd_refl p` transported along
            // `cancel_neg_add p one : (p + (-1)) + 1 = p`.
            let dvd_refl_p = d.const_app(p.dvd_refl, &[p_var]);
            let cna = super::modeq::cancel_neg_add(d, p_var, one_i);
            let cna_lhs = {
                let inner = d.iadd(p_var, neg_one);
                d.iadd(inner, one_i)
            };
            let reversed = d.isymm(cna_lhs, p_var, cna);
            let motive2 = d.ieq_motive(p_var, &|d, x| super::dvd::idvd(d, p_var, x));
            let result_r2 = d.itransport(p_var, motive2, dvd_refl_p, cna_lhs, reversed);

            let modeq_negone_pm1_ty = super::modeq::imodeq(d, p_var, neg_one, p_minus_one);
            let pm1_minus_negone = d.isub(p_minus_one, neg_one);
            let dvd_r2_ty = super::dvd::idvd(d, p_var, pm1_minus_negone);
            let iff_r2 = d.const_app(p.mod_eq_iff_dvd, &[p_var, neg_one, p_minus_one, h_pos]);
            let mpr_r2 = d.const_app(p.logic.iff_mpr, &[modeq_negone_pm1_ty, dvd_r2_ty, iff_r2]);
            let modeq_negone_pm1 = d.apply(mpr_r2, &[result_r2]);

            let modeq_a_pm1_pf = d.const_app(
                p.mod_eq_trans,
                &[
                    p_var,
                    a,
                    neg_one,
                    p_minus_one,
                    modeq_a_negone,
                    modeq_negone_pm1,
                ],
            );
            d.or_inr(modeq_a_one, modeq_a_pm1, modeq_a_pm1_pf)
        };

        let proof_body = d.or_elim(left_ty, right_ty, concl, disj, on_left, on_right);

        let with_sq = d.lam_fv(sq_fv, sq_ty, proof_body);
        let with_ub = d.lam_fv(ub_fv, ub, with_sq);
        let with_lb = d.lam_fv(lb_fv, one_lb, with_ub);
        let with_pos = d.lam_fv(pos_fv, pos_ty, with_lb);
        let proof = d.lam_fv(prime_fv, prime_ty, with_pos);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.factorial_pos : ∀ (n : Nat), 0 < factorial n`.
///
/// Induction on `n`: the base case is `0 < factorial zero`, defeq to
/// `zero_lt_one` (`factorial_zero` is `Eq.refl`); the step needs
/// `0 < ofNat (succ j)`, built from `Int.lt_of_nat_add zero j : 0 < 0 +
/// ofNat (succ j)` transported past `add_comm`/`add_zero`, then
/// `Int.mul_pos` closes `0 < factorial j * ofNat (succ j)`, defeq to
/// `0 < factorial (succ j)` (`factorial_succ` is `Eq.refl` too).
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_factorial_pos(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let zero_i = d.izero();

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let motive = |d: &mut IntDev<'_>, x: ExprId| {
        let f = d.const_app(p.factorial, &[x]);
        d.ilt(zero_i, f)
    };
    let stmt = motive(d, n);

    let proof_body = d.induct(
        &motive,
        &|d| d.const_app(p.zero_lt_one, &[]),
        &|d, j, ih| {
            let sj = d.succ(j);
            let sj_i = d.of_nat(sj);
            let base_lt = d.const_app(p.lt_of_nat_add, &[zero_i, j]); // 0 < 0 + sj_i
            let sum = d.iadd(zero_i, sj_i);
            let sj0 = d.iadd(sj_i, zero_i);
            let comm = d.const_app(p.add_comm, &[zero_i, sj_i]);
            let addz = d.const_app(p.add_zero, &[sj_i]);
            let (_, sum_eq_sji) = d.ichain(sum, &[(sj0, comm), (sj_i, addz)]);
            let motive2 = d.ieq_motive(sum, &|d, x| d.ilt(zero_i, x));
            let pos_sj = d.itransport(sum, motive2, base_lt, sj_i, sum_eq_sji);
            let factorial_j = d.const_app(p.factorial, &[j]);
            d.const_app(p.mul_pos, &[factorial_j, sj_i, ih, pos_sj])
        },
        n,
    );

    let ty = d.pi_fv(n_fv, nat, stmt);
    let value = d.lam_fv(n_fv, nat, proof_body);
    d.declare_theorem(p.factorial_pos, ty, value)
}
