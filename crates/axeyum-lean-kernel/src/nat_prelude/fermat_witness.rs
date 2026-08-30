//! Fermat's little theorem, run backwards: a computable compositeness
//! certificate (ADR-0603 row 1 + row 3 for a graded family that needs no
//! row 2 at all).
//!
//! [`super::fermat`]'s `Nat.pow_prime_modeq_self : Prime p → a^p ≡ a [p]` is
//! unconditional in `a` and needs no restriction beyond primality of `p`.
//! Its CONTRAPOSITIVE — "if `a^p` and `a` disagree mod `p`, then `p` is not
//! prime" — is the Fermat primality test's whole engine, and is a genuine
//! new proposition this prelude did not previously state: nothing here
//! previously connected `pow_prime_modeq_self` to a *negative* primality
//! conclusion.
//!
//! [`declare_mod_eq_iff_mod_eq`] is the bridge that makes this EXECUTABLE
//! rather than merely propositional: `Nat.modEq d a b` is the existential
//! balanced-witness congruence (`∃ u v, a+d*u = b+d*v`), which is not
//! itself something a concrete instantiation can refute by `Eq.refl` (its
//! negation quantifies over all naturals `u, v`). `Nat.mod_eq_iff_mod_eq`
//! rewrites it to `Eq (modulo a d) (modulo b d)` — an equation between two
//! EXECUTABLE `Nat.mod` values — by composing two already-landed theorems:
//! `Nat.mod_eq_iff_div_mod_remainder_eq` (`modular.rs`, stated against the
//! *relational* `Nat.divMod`) instantiated at the *executable* projections
//! via `Nat.div_mod_exec` (`division.rs`) supplied as the `divMod` witness
//! for both sides. No new induction: this is pure composition of landed
//! lemmas, in the same spirit as `int_prelude/euler_theorem.rs`'s
//! `Int.prodRangeIf_permute` getting its hard part for free by routing
//! through an already-proved theorem instead of re-deriving one.
//!
//! `Nat.div_mod_exec` is stated with the divisor SYNTACTICALLY `succ`-shaped
//! (`∀ pred_divisor dividend, divMod (succ pred_divisor) dividend …`,
//! `division.rs`), because `divMod`'s own remainder bound `Lt r divisor` is
//! false at `divisor = 0`. So `mod_eq_iff_mod_eq` carries an explicit
//! `0 < d` hypothesis and is built entirely in terms of `n := succ (pred d)`
//! (via `pos_implies_succ_pred`, exactly [`super::fermat`]'s own convention
//! for the same reason — see that module's doc), transported back to `d`
//! only at the very end.
//!
//! [`declare_not_prime_of_pow_mod_ne`] is then the row-1 statement itself,
//! `Nat.not_prime_of_pow_mod_ne : ∀ p a, Not (Eq (modulo (pow a p) p)
//! (modulo a p)) → Not (Prime p)` — general, unconditional, needs no
//! decidability principle beyond what the two lemmas above already supply
//! (the `0 < p` hypothesis `mod_eq_iff_mod_eq` needs comes for free from
//! `Prime p` via `prime_pos`), and does not touch `Nat.least_number`/LNP or
//! any excluded-middle question at all: it is a single modus-tollens step.
//! There is no row 2 to extract here (see the module-level argument in
//! `docs/plan/status/graded-families-number-theory.md`): a direct logical
//! inference on an unconditional theorem has no comparison or unbounded
//! search to reduce to a boundary.
//!
//! Row 3 (the decidable/exact fragment) is the evaluation test in
//! `nat_prelude_tests.rs`: `not_prime_of_pow_mod_ne` instantiated at
//! `p := 4`, `a := 3` gives a fully kernel-checked, executable
//! compositeness certificate for `4` (`3^4 mod 4 = 1 ≠ 3 mod 4 = 3`),
//! discriminated against a positive control at the genuine prime `p := 5`
//! (`3^5 mod 5 = 3 = 3 mod 5`, so the hypothesis is false there and the
//! theorem correctly proves nothing false).

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::expr::ExprId;

// ============================================================================
// `(2 ≤ x) ∧ (∀ c, c ∣ x → c = 1 ∨ c = x)` — per-file local copy of the same
// helper `fermat.rs`/`totient.rs`/`perfect.rs` each carry (this
// development's own convention for a proposition with no named constant).
// ============================================================================

fn prime_parts(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId) -> (ExprId, ExprId) {
    let nat = d.nat_ty();
    let two = d.num(2);
    let one = d.num(1);
    let two_le = d.le(two, x);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let hyp = d.dvd(c, x);
    let is_one = d.eq(c, one);
    let is_x = d.eq(c, x);
    let disjunction = d.const_app(p.logic.or, &[is_one, is_x]);
    let inner = d.arrow(hyp, disjunction);
    let divisor_clause = d.pi_fv(c_fv, nat, inner);
    (two_le, divisor_clause)
}

fn prime_ty(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId) -> ExprId {
    let (two_le, divisor_clause) = prime_parts(d, p, x);
    d.const_app(p.logic.and, &[two_le, divisor_clause])
}

/// `prime x → Lt zero x` — a local copy of `fermat.rs`'s private
/// `prime_pos` (same convention: extract `2 ≤ x` from the packed proof,
/// weaken via `le_succ`/`le_trans`).
fn prime_pos(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId, prime_proof: ExprId) -> ExprId {
    let (two_le_ty, divisor_clause_ty) = prime_parts(d, p, x);
    let two_le = super::helpers::and_left(d, two_le_ty, divisor_clause_ty, prime_proof);
    let one = d.num(1);
    let two = d.num(2);
    let one_le_two = d.lemma(p.le_succ, &[one]);
    d.lemma(p.le_trans, &[one, two, x, one_le_two, two_le])
}

// ============================================================================
// `Nat.mod_eq_iff_mod_eq` — the executable bridge.
// ============================================================================

/// `Nat.mod_eq_iff_mod_eq : ∀ d a b, 0 < d → Iff (ModEq d a b) (Eq (modulo a
/// d) (modulo b d))`.
///
/// Built at `n := succ (pred d)` (`div_mod_exec` needs a syntactically
/// `succ`-shaped divisor), then transported back to `d` via the positivity
/// hypothesis, mirroring `fermat.rs`'s `pos_implies_succ_pred` pattern.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_mod_eq_iff_mod_eq(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.mod_eq_iff_mod_eq, 3, &|d, v| {
        let (dd, a, b) = (v[0], v[1], v[2]);
        let zero = d.zero();
        let pos_ty = d.lt(zero, dd);
        let pos_fv = d.fresh_fvar();
        let pos_proof = d.kernel().fvar(pos_fv);

        // eq_d_n : Eq dd n, where n := succ (pred dd).
        let eq_d_n_fn = d.lemma(p.succ_pred_of_pos, &[dd]);
        let eq_d_n = d.apply(eq_d_n_fn, &[pos_proof]);
        let pred_dd = d.pred(dd);
        let n = d.succ(pred_dd);
        let eq_n_d = d.symm(dd, n, eq_d_n);

        // Build the whole Iff at n (succ-shaped), where div_mod_exec applies.
        let iff_at = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
            let congruence_ty = d.mod_eq(x, a, b);
            let mod_a = d.modulo(a, x);
            let mod_b = d.modulo(b, x);
            let remainder_eq_ty = d.eq(mod_a, mod_b);
            d.const_app(p.logic.iff, &[congruence_ty, remainder_eq_ty])
        };
        let target = iff_at(d, dd);

        let proof_at_n = {
            let mod_a = d.modulo(a, n);
            let mod_b = d.modulo(b, n);
            let div_a = d.div(a, n);
            let div_b = d.div(b, n);
            let dm_a = d.lemma(p.div_mod_exec, &[pred_dd, a]);
            let dm_b = d.lemma(p.div_mod_exec, &[pred_dd, b]);
            d.lemma(
                p.mod_eq_iff_div_mod_remainder_eq,
                &[n, a, b, div_a, mod_a, div_b, mod_b, dm_a, dm_b],
            )
        };
        let motive = d.eq_motive(n, &|d, x| iff_at(d, x));
        let proof_at_d = d.transport(n, motive, proof_at_n, dd, eq_n_d);

        let stmt = d.arrow(pos_ty, target);
        let proof = d.lam_fv(pos_fv, pos_ty, proof_at_d);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.not_prime_of_pow_mod_ne` — the row-1 statement.
// ============================================================================

/// `Nat.not_prime_of_pow_mod_ne : ∀ p a, Not (Eq (modulo (pow a p) p)
/// (modulo a p)) → Not (Prime p)` — the contrapositive of
/// `Nat.pow_prime_modeq_self`, composed through [`declare_mod_eq_iff_mod_eq`].
///
/// Proof: `fun hne hp => hne (mp (mod_eq_iff_mod_eq p (pow a p) a
/// (prime_pos p hp)) (pow_prime_modeq_self p a hp))`. No induction, no case
/// split — a single modus-tollens step, fully symbolic in `p` and `a`
/// throughout.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_not_prime_of_pow_mod_ne(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.not_prime_of_pow_mod_ne, 2, &|d, v| {
        let (pp, a) = (v[0], v[1]);
        let pow_a_pp = d.pow(a, pp);
        let mod_pow = d.modulo(pow_a_pp, pp);
        let mod_a = d.modulo(a, pp);
        let eq_ty = d.eq(mod_pow, mod_a);
        let ne_ty = d.const_app(p.logic.not, &[eq_ty]);

        let prime_ty_pp = prime_ty(d, &p, pp);
        let not_prime_ty = d.const_app(p.logic.not, &[prime_ty_pp]);
        let stmt = d.arrow(ne_ty, not_prime_ty);

        let hne_fv = d.fresh_fvar();
        let hne = d.kernel().fvar(hne_fv);
        let hp_fv = d.fresh_fvar();
        let hp = d.kernel().fvar(hp_fv);

        let modeq_ty = d.mod_eq(pp, pow_a_pp, a);
        let modeq = d.lemma(p.pow_prime_modeq_self, &[pp, a, hp]);

        let pos_pp = prime_pos(d, &p, pp, hp);
        let iff_fn = d.lemma(p.mod_eq_iff_mod_eq, &[pp, pow_a_pp, a]);
        let iff_pp = d.apply(iff_fn, &[pos_pp]);
        let mp_fn = d.const_app(p.logic.iff_mp, &[modeq_ty, eq_ty, iff_pp]);
        let eq_proof = d.apply(mp_fn, &[modeq]);
        let absurd = d.apply(hne, &[eq_proof]);

        let inner = d.lam_fv(hp_fv, prime_ty_pp, absurd);
        let proof = d.lam_fv(hne_fv, ne_ty, inner);
        (stmt, proof)
    })?;
    Ok(())
}

/// Declare `Nat.mod_eq_iff_mod_eq` and `Nat.not_prime_of_pow_mod_ne`, in
/// dependency order.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_fermat_witness_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_mod_eq_iff_mod_eq(d, p)?;
    declare_not_prime_of_pow_mod_ne(d, p)?;
    Ok(())
}
