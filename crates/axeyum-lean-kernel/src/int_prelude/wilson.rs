//! `Int.factorial`, the self-inverse analysis Wilson's theorem needs, and
//! `Int.factorial_pos` — the assembly slice toward Wilson's theorem
//! (`p` prime ⟹ `(p-1)! ≡ -1 [p]`). Also, since 2026-08-24, the coprime form
//! of Fermat's little theorem (`Int.pow_prime_sub_one_modeq_one`,
//! `p ∤ a ⟹ a^(p−1) ≡ 1 [p]`) and its bridging lemma `Int.of_nat_pow`.
//!
//! ## What lands here, and what does not
//!
//! `Int.factorial` (a `prodRange` instance) and `Int.self_inverse_mod_prime`
//! (the genuinely prime-theoretic heart: `a*a ≡ 1 [p]` forces `a ≡ ±1 [p]`,
//! via `Int.euclid_lemma` deciding which factor of `(a-1)(a+1)` `p` divides —
//! a real constructive disjunction, not excluded middle) are both proved
//! here, axiom-free. So is `Int.pow_prime_sub_one_modeq_one`
//! (`declare_pow_prime_sub_one_modeq_one`, below) — the headline form of
//! Fermat every application actually wants, as opposed to the unrestricted
//! `Nat.pow_prime_modeq_self : prime p → a^p ≡ a [p]` this whole chain rests
//! on.
//!
//! ## What Wilson is blocked on now, measured 2026-08-24
//!
//! The rearrangement principle is done, so the remaining gap has moved. To use
//! `prodRange_permute` the pairing needs a **concrete `σ : Nat → Nat`** — the
//! `injectiveOn`/`mapsInto` predicates quantify over a function, not over a
//! proof that one exists. Two routes, and the obvious one does not work:
//!
//! - **Bézout cannot supply it.** `Int.gcd_eq_gcd_ab` and `Nat.gcd_bezout`
//!   produce EXISTENTIAL witnesses, extracted by `exists_elim` inside a proof.
//!   They never yield a closed-form function, so they cannot instantiate `σ`.
//!   This is the same wall `CReal.inv` and `pos_bound_of_lt` hit: a `Prop`-level
//!   existential does not eliminate into a `Type` target.
//! - **The Fermat route can**, because `σ(k) := a^(p-2) mod p` is closed form.
//!
//! Taking that route needed three pieces. Two are now landed and reusable —
//! `Int.modEq_of_nat_modEq` (the `Nat.modEq → Int.ModEq` transport,
//! `modeq.rs`) and `Nat.coprime_of_lt_prime` (`prime p → 0 < a < p →
//! Coprime a p`, `nat_prelude/primes.rs`) — and this file now also has
//! `Int.pow_prime_sub_one_modeq_one`
//! (`declare_pow_prime_sub_one_modeq_one`, below), the assembled
//! `a^(p-1) ≡ 1 [p]`, proved from exactly those two plus
//! `Nat.pow_prime_modeq_self` and `Int.modEq_cancel`. What is **not** yet
//! built is `σ` itself: splitting one more factor off
//! (`a^(p-1) = a^(p-2) · a`, so `a · a^(p-2) ≡ 1 [p]`) to get an *executable*
//! inverse, and the `Nat → Nat` closed form `σ(k) := a^(p-2) mod p` built from
//! it — plus the `p = 2` edge case, where `p - 2 = 0` under TRUNCATED
//! `Nat.sub` and the range is empty.
//!
//! The indexing, settled: `a := ofNat(k+1)` for `k < n` with
//! `n := natAbs(p) - 1`, so `{0,…,p-2}` maps onto `{1,…,p-1}` and `n` is the
//! same `Nat` that `Int.factorial` already consumes for `(p-1)!` — no
//! reindexing gap against the rest of the chain.
//!
//! Wilson's theorem itself is **not** declared here — that is its own slice —
//! but the rearrangement principle it needs is now fully proved and
//! axiom-free: `Int.prodRange_permute`
//! (`prod.rs`) : `∀ f σ n, InjectiveOn σ n → MapsInto σ n →
//! prodRange f n = prodRange (fun k => f (σ k)) n`. The classical proof of
//! Wilson's theorem collapses `prodRange` over `2..p-2` by pairing each
//! survivor with its distinct inverse — a permutation argument — and
//! `prodRange_permute` is exactly the rearrangement step that argument needs:
//! `Int.prodRange : (Nat → Int) → Nat → Int` folds over a fixed *initial
//! segment* `{0,…,n-1}`, so reasoning about "the product over the remaining
//! unpaired elements" has to go through a `σ` that moves each survivor's
//! partner into its slot, and `prodRange_permute` is what licenses that move
//! for an arbitrary `InjectiveOn`/`MapsInto` self-map, not just one swap.
//!
//! It was built in three stages, the last landing 2026-08-24:
//! `Nat.Fin`, `Nat.injectiveOn` / `surjectiveOn` / `mapsInto`, and the
//! pigeonhole principle connecting them
//! (`Nat.injective_on_imp_surjective_on`, `nat_prelude/finite.rs`);
//! `Int.prodRange_swap_adjacent` (one adjacent transposition) and
//! `Int.prodRange_swap` (any two indices `i < j`, via `prod.rs`'s
//! `point_swap` — a `Nat.ble`-cascaded explicit swap function, never
//! `Nat.beq` — and a conjugation induction `(j' j)(i j')(j' j) = (i j)` on the
//! gap `j - i`); and finally `prodRange_permute` itself, induction on `n`
//! with `f` quantified OUTSIDE the `Nat.rec` and the motive generalized over
//! **`σ`, not `f`** (motive `∀ σ, injectiveOn σ x → mapsInto σ x →
//! prodRange f x = prodRange (f ∘ σ) x`; three earlier drafts generalized over
//! `f` instead, copying every earlier proof in this chain, and that shape does
//! not close — the recursive call here reuses the same `f` and only `σ`
//! changes). At `n+1` the pigeonhole locates `i0 < n+1` with `σ i0 = n`: the
//! `i0 = n` branch is pure bound-weakening (`σ` already fixes `n`), and the
//! `i0 < n` branch applies `point_swap` to `g := f ∘ σ` at `(i0, n)` — not to
//! `σ` — reducing the recursive obligation to `prodRange (f ∘ τ) n =
//! prodRange f n` for the OVERRIDE `τ := point_override σ i0 (σ n)` (never a
//! downward reindex: once `i0 = n` is peeled off, `i0` is already `< n`, so
//! there is nothing to shift), with `Nat.restrict_injective` /
//! `Nat.restrict_maps_into` (`nat_prelude/finite.rs`) supplying `τ`'s two
//! closure properties.

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

// ============================================================================
// The coprime form of Fermat's little theorem, and the executable-inverse
// bridge it unlocks. `p ∤ a ⟹ a^(p−1) ≡ 1 [p]` — every ingredient below it
// (`Nat.pow_prime_modeq_self`, `Nat.coprime_of_lt_prime`,
// `Int.modEq_of_nat_modEq`, `Int.modEq_cancel`) landed the same day; this is
// the assembly.
// ============================================================================

/// `2 ≤ magnitude`, `∀ x, x ∣ magnitude → x = 1 ∨ x = magnitude` — the two
/// conjuncts [`prime_condition`] ANDs together, split out so `and_left` can
/// project `2 ≤ magnitude` back out of a primality proof. A deliberate
/// duplicate of `prime_condition`'s own construction (not a refactor of it):
/// identical builder calls in identical order intern to the identical
/// `ExprId`, so `and_left(two_le, clause, prime_proof)` type-checks against a
/// `prime_proof` built via [`prime_condition`] without either function
/// depending on the other's internals.
fn prime_parts(d: &mut IntDev<'_>, magnitude: ExprId) -> (ExprId, ExprId) {
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
    (two_le, clause)
}

/// `prime magnitude → Nat.le 1 magnitude` — usable directly (via defeq,
/// `Nat.lt` unfolding to a `succ`-shifted `Nat.le`) wherever `0 < magnitude`
/// is wanted too. Mirrors `nat_prelude/fermat.rs`'s private `prime_pos`
/// exactly (that copy is not reachable from `int_prelude`), extracting
/// `2 ≤ magnitude` via `and_left` and weakening `1 ≤ 2 ≤ magnitude`.
fn nat_prime_pos(d: &mut IntDev<'_>, magnitude: ExprId, prime_proof: ExprId) -> ExprId {
    let p = d.int();
    let (two_le_ty, clause_ty) = prime_parts(d, magnitude);
    let two_le = d.and_left(two_le_ty, clause_ty, prime_proof);
    let one = d.num(1);
    let two = d.num(2);
    let one_le_two = d.lemma(p.nat.le_succ, &[one]);
    d.lemma(p.nat.le_trans, &[one, two, magnitude, one_le_two, two_le])
}

/// `(ofNat (pow base exp), pow (ofNat base) exp)` — the two sides
/// [`declare_of_nat_pow`]'s statement (and induction step) equates.
fn of_nat_pow_sides(d: &mut IntDev<'_>, base: ExprId, exp: ExprId) -> (ExprId, ExprId) {
    let pow_nat = d.pow(base, exp);
    let lhs = d.of_nat(pow_nat);
    let of_base = d.of_nat(base);
    let rhs = d.ipow(of_base, exp);
    (lhs, rhs)
}

/// `Int.of_nat_pow : ∀ (a n : Nat), Eq Int (ofNat (pow a n)) (pow (ofNat a) n)`.
///
/// `Int.ofNat` is a ring homomorphism on `+`/`*` at even a *symbolic* pair of
/// naturals — `Int.add`/`Int.mul` pattern-match on the outer `ofNat`/`negSucc`
/// constructor of their `Int` arguments, which is already determined for
/// `ofNat _` regardless of what is nested inside, so the `ofNat`-branch
/// reduction is `Eq.refl`-transparent even for free variables (the same fact
/// [`declare_modeq_of_nat_modeq`](super::modeq::declare_modeq_of_nat_modeq)'s
/// doc comment relies on). `Int.pow` does not get this for free: its
/// recursion is on the *exponent*, via `Nat.rec`, and a free-variable exponent
/// is not a constructor application, so no amount of unfolding reaches a
/// normal form. Hence this needs a genuine induction on `n`, not a `refl`.
///
/// Base (`n = zero`): both sides reduce, independently, to `ofNat 1`
/// (`Nat.pow_zero` then `Int.one := ofNat 1`; `Int.pow_zero` directly) — an
/// `Eq.refl`-shaped closure, same pattern as `factorial_zero`.
///
/// Step (`n = succ j`, `ih : Eq Int (ofNat (pow a j)) (pow (ofNat a) j)`):
/// `icongr ih (fun x => mul x (ofNat a))` gives `Eq Int (mul (ofNat (pow a j))
/// (ofNat a)) (mul (pow (ofNat a) j) (ofNat a))`; its left side is defeq to
/// `ofNat (pow a (succ j))` (`Nat.pow_succ`, then the same ofNat-branch
/// reduction as the base case) and its right side is defeq to `pow (ofNat a)
/// (succ j)` (`Int.pow_succ`) — so the `icongr` term, unadjusted, already has
/// the goal's type up to defeq.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_of_nat_pow(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.theorem(p.of_nat_pow, 2, &|d, v| {
        let (a, n) = (v[0], v[1]);
        let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
            let (lhs, rhs) = of_nat_pow_sides(d, a, x);
            d.ieq(lhs, rhs)
        };
        let stmt = motive(d, n);

        let proof = d.induct(
            &motive,
            &|d| {
                let one_i = d.ione();
                d.irefl(one_i)
            },
            &|d, j, ih| {
                let (lhs_j, rhs_j) = of_nat_pow_sides(d, a, j);
                let of_a = d.of_nat(a);
                d.icongr(lhs_j, rhs_j, ih, &|d, x| d.imul(x, of_a))
            },
            n,
        );
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.pow_prime_sub_one_modeq_one :
/// ∀ p a, (2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p) → 0 < a → a < p →
///   ModEq (ofNat p) (pow (ofNat a) (p-1)) one`
///
/// The coprime form of Fermat's little theorem: `p ∤ a ⟹ a^(p−1) ≡ 1 [p]`.
/// Kept over `ℤ` (not `ℕ`) because the one step this needs that `ℕ` cannot
/// supply is cancellation — `Int.modEq_cancel` — and the transport is
/// `ℕ → ℤ` only ([`super::modeq::declare_modeq_of_nat_modeq`]'s doc), so
/// carrying primality and the two range hypotheses in `ℕ` (matching
/// `Nat.pow_prime_modeq_self`/`Nat.coprime_of_lt_prime` exactly, no
/// `natAbs` detour) and casting only the *derived* congruence is the cheaper
/// split: it needed one bridging lemma ([`declare_of_nat_pow`]) instead of
/// redoing primality/order over `ℤ`.
///
/// Route:
/// 1. `Nat.pow_prime_modeq_self` gives `ModEq p (pow a p) a` over `ℕ`.
/// 2. `Nat.sub_add_cancel 1 p (1 ≤ p)` gives `Eq Nat (add (p-1) 1) p`, defeq
///    `Eq Nat (succ (p-1)) p` (`add x 1` reduces to `succ x` by the same
///    `add_succ`/`add_zero` `Eq.refl` pair `Nat.add`'s own equations use).
///    `Nat.pow_succ` at `p-1` gives `pow a (succ (p-1)) = pow a (p-1) * a`;
///    composing rewrites `pow a p` (step 1's exponent) into `pow a (p-1) * a`,
///    entirely over `ℕ`.
/// 3. `Int.modEq_of_nat_modEq` casts the rewritten congruence,
///    `ModEq p (pow a (p-1) * a) a`, to `ℤ` — landing (via the ofNat-branch
///    defeq [`declare_of_nat_pow`]'s doc comment describes) at
///    `ModEq (ofNat p) (mul (ofNat (pow a (p-1))) (ofNat a)) (ofNat a)`.
/// 4. [`declare_of_nat_pow`] reshapes `ofNat (pow a (p-1))` into
///    `pow (ofNat a) (p-1)` inside that congruence.
/// 5. `Int.mul_comm`/`Int.mul_one` reshape the congruence into
///    `ModEq (ofNat p) (mul (ofNat a) (pow (ofNat a) (p-1))) (mul (ofNat a) one)`
///    — the `c*x ≡ c*y` shape `Int.modEq_cancel` needs, `c := ofNat a`.
/// 6. `Nat.coprime_of_lt_prime` gives `Eq Nat (gcd a p) 1`, defeq to
///    `Coprime (ofNat a) (ofNat p)` (`Int.gcd`/`Int.natAbs` both reduce
///    transparently on an `ofNat` argument, symbolic or not). `Int.modEq_cancel`
///    then cancels the factor of `a`, landing exactly on the goal.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_pow_prime_sub_one_modeq_one(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.theorem(p.pow_prime_sub_one_modeq_one, 2, &|d, v| {
        let (pp, aa) = (v[0], v[1]);
        let prime_ty = prime_condition(d, pp);
        let zero = d.zero();
        let pos_ty = d.lt(zero, aa);
        let ub_ty = d.lt(aa, pp);

        let one_nat = d.num(1);
        let pm1 = d.sub(pp, one_nat);
        let big_p = d.of_nat(pp);
        let big_a = d.of_nat(aa);
        let pow_int = d.ipow(big_a, pm1);
        let one_i = d.ione();
        let concl = super::modeq::imodeq(d, big_p, pow_int, one_i);

        let stmt = {
            let inner = d.arrow(ub_ty, concl);
            let with_pos = d.arrow(pos_ty, inner);
            d.arrow(prime_ty, with_pos)
        };

        let prime_fv = d.fresh_fvar();
        let prime_proof = d.kernel().fvar(prime_fv);
        let pos_fv = d.fresh_fvar();
        let pos_proof = d.kernel().fvar(pos_fv);
        let ub_fv = d.fresh_fvar();
        let ub_proof = d.kernel().fvar(ub_fv);

        // Step 0: 1 ≤ p (also usable as 0 < p, `Nat.lt` unfolding to a
        // succ-shifted `Nat.le`).
        let one_le_pp = nat_prime_pos(d, pp, prime_proof);

        // Step 2: succ(p-1) = p.
        let cancel = d.lemma(p.nat.sub_add_cancel, &[one_nat, pp, one_le_pp]);
        let succ_pm1 = d.succ(pm1);

        // Step 1: Nat.ModEq p (pow a p) a.
        let nat_fermat_fn = d.lemma(p.nat.pow_prime_modeq_self, &[pp, aa]);
        let nat_fermat = d.apply(nat_fermat_fn, &[prime_proof]);

        // Step 2 (continued): pow a p = pow a (p-1) * a, over Nat.
        let pow_aa_pp = d.pow(aa, pp);
        let pow_aa_succpm1 = d.pow(aa, succ_pm1);
        let pow_aa_pm1 = d.pow(aa, pm1);
        let mul_term = d.mul(pow_aa_pm1, aa);
        let pow_succ_pm1 = d.lemma(p.nat.pow_succ, &[aa, pm1]);
        let congr_exp = d.congr(succ_pm1, pp, cancel, &|d, x| d.pow(aa, x));
        let rev_congr_exp = d.symm(pow_aa_succpm1, pow_aa_pp, congr_exp);
        let pow_pp_eq = d.trans(
            pow_aa_pp,
            pow_aa_succpm1,
            mul_term,
            rev_congr_exp,
            pow_succ_pm1,
        );

        let motive_nat = d.eq_motive(pow_aa_pp, &|d, x| d.mod_eq(pp, x, aa));
        let nat_rewritten = d.transport(pow_aa_pp, motive_nat, nat_fermat, mul_term, pow_pp_eq);

        // Step 3: cast to Int.
        let int_pre = d.const_app(p.mod_eq_of_nat_mod_eq, &[pp, mul_term, aa]);
        let int_form = d.apply(int_pre, &[nat_rewritten, one_le_pp]);

        // Step 4: reshape ofNat(pow a (p-1)) into pow (ofNat a) (p-1).
        let of_nat_powpm1 = d.of_nat(pow_aa_pm1);
        let bridge = d.const_app(p.of_nat_pow, &[aa, pm1]);
        let step4 = d.int_eq_rewrite(of_nat_powpm1, pow_int, bridge, int_form, &|d, x| {
            let mulx = d.imul(x, big_a);
            super::modeq::imodeq(d, big_p, mulx, big_a)
        });

        // Step 5: commute, then turn the trailing `a` into `a*1`.
        let mul_comm_pf = d.const_app(p.mul_comm, &[pow_int, big_a]);
        let lhs5 = d.imul(pow_int, big_a);
        let rhs5 = d.imul(big_a, pow_int);
        let step5a = d.int_eq_rewrite(lhs5, rhs5, mul_comm_pf, step4, &|d, x| {
            super::modeq::imodeq(d, big_p, x, big_a)
        });

        let mul_one_pf = d.const_app(p.mul_one, &[big_a]);
        let a_times_one = d.imul(big_a, one_i);
        let rev_mul_one = d.isymm(a_times_one, big_a, mul_one_pf);
        let step5b = d.int_eq_rewrite(big_a, a_times_one, rev_mul_one, step5a, &|d, x| {
            let lhs = d.imul(big_a, pow_int);
            super::modeq::imodeq(d, big_p, lhs, x)
        });

        // Step 6: coprimality, then cancel.
        let coprime_fn = d.lemma(p.nat.coprime_of_lt_prime, &[pp, aa]);
        let coprime_proof = d.apply(coprime_fn, &[prime_proof, pos_proof, ub_proof]);

        let cancel_fn = d.const_app(p.mod_eq_cancel, &[big_p, big_a, pow_int, one_i]);
        let final_proof = d.apply(cancel_fn, &[one_le_pp, coprime_proof, step5b]);

        let with_ub = d.lam_fv(ub_fv, ub_ty, final_proof);
        let with_pos = d.lam_fv(pos_fv, pos_ty, with_ub);
        let proof = d.lam_fv(prime_fv, prime_ty, with_pos);
        (stmt, proof)
    })?;
    Ok(())
}
