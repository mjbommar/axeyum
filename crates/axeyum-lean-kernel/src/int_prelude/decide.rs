//! Decidable integer equality (ADR-0106), derived rather than assumed.
//!
//! `Int.eq_em : ∀ a b, Or (Eq Int a b) (Not (Eq Int a b))` is the
//! integer-specific decision the equality-partition reconstruction route needs.
//! It is *not* propositional excluded middle and must not be obtained from it —
//! the logic prelude is intuitionistic and carries no axioms, which is exactly
//! what would be lost.
//!
//! Deriving it needs the two facts a constructor presentation gives and an
//! opaque carrier cannot:
//!
//! - **Injectivity.** `Int.magnitudeOf` (built here, not declared) projects a
//!   constructor's `Nat` field, so `Eq Int (ofNat m) (ofNat n)` rewrites into
//!   `Eq Nat m n`.
//! - **Discrimination.** A `Prop`-valued `Int.rec` that returns `True` on one
//!   constructor and `False` on the other turns `Eq Int (ofNat m) (negSucc n)`
//!   into `False` by transporting `True.intro` across it.
//!
//! The `Nat` half is decided by `Nat.beq`, whose soundness and completeness the
//! `Nat` prelude already proves, so the whole thing stays axiom-free.

use super::ops::{IntDev, Shape, case_split};
use super::statements;
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

/// `Int.rec.{1} (fun _ => Nat) (fun n => n) (fun n => n) x` — the `Nat` field of
/// whichever constructor `x` is. ι-reduces to `m` on both `ofNat m` and
/// `negSucc m`, which is what makes it an injectivity witness for each
/// constructor separately.
fn magnitude(d: &mut IntDev<'_>, x: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let int_ty = d.int_ty();
    let anon = d.anon_name();
    let one = d.level_one();
    let motive = d.kernel().lam(anon, int_ty, nat, BinderInfo::Default);
    let identity = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        d.lam_fv(n_fv, nat, n)
    };
    let rec_name = d.int().rec;
    let rec = d.kernel().const_(rec_name, vec![one]);
    d.apply(rec, &[motive, identity, identity, x])
}

/// `Int.rec.{1} (fun _ => Prop) <on ofNat> <on negSucc> x` — a `Prop` that
/// separates the two constructors definitionally.
fn sign_predicate(d: &mut IntDev<'_>, x: ExprId, on_of_nat: ExprId, on_neg_succ: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let int_ty = d.int_ty();
    let anon = d.anon_name();
    let one = d.level_one();
    let prop = d.kernel().sort_zero();
    let motive = d.kernel().lam(anon, int_ty, prop, BinderInfo::Default);
    let constant = |d: &mut IntDev<'_>, value: ExprId| {
        let fv = d.fresh_fvar();
        d.lam_fv(fv, nat, value)
    };
    let minor_of_nat = constant(d, on_of_nat);
    let minor_neg_succ = constant(d, on_neg_succ);
    let rec_name = d.int().rec;
    let rec = d.kernel().const_(rec_name, vec![one]);
    d.apply(rec, &[motive, minor_of_nat, minor_neg_succ, x])
}

/// `h : Eq Int p q` between terms with **different** constructors ⊢ `False`.
///
/// `positive_is_left` says whether `p` is the `Int.ofNat` one; the predicate is
/// chosen so that it is `True` at `p` and `False` at `q`.
fn discriminate(
    d: &mut IntDev<'_>,
    p: ExprId,
    q: ExprId,
    h: ExprId,
    positive_is_left: bool,
) -> ExprId {
    let true_ty = d.true_ty();
    let false_ty = d.false_ty();
    let (on_of_nat, on_neg_succ) = if positive_is_left {
        (true_ty, false_ty)
    } else {
        (false_ty, true_ty)
    };
    let witness = d.true_intro();
    d.int_eq_rewrite(p, q, h, witness, &|d, y| {
        sign_predicate(d, y, on_of_nat, on_neg_succ)
    })
}

/// `h : Eq Int p q` ⊢ `Eq Nat (magnitude p) (magnitude q)`.
fn project_equality(d: &mut IntDev<'_>, p: ExprId, q: ExprId, h: ExprId) -> ExprId {
    let left = magnitude(d, p);
    let witness = d.refl(left);
    d.int_eq_rewrite(p, q, h, witness, &|d, y| {
        let right = magnitude(d, y);
        d.eq(left, right)
    })
}

/// `Or (Eq Bool c Bool.true) (Eq Bool c Bool.false)` for `c := Nat.beq m n`.
///
/// The minor premises are ordered `true` then `false`, matching the recursor
/// this environment generates for `Bool`.
fn beq_is_true_or_false(d: &mut IntDev<'_>, m: ExprId, n: ExprId) -> ExprId {
    let bool_ty = d.bool_ty();
    let scrutinee = d.beq(m, n);

    let disjunction = |d: &mut IntDev<'_>, c: ExprId| {
        let yes = {
            let value = d.bool_true();
            d.bool_eq(c, value)
        };
        let no = {
            let value = d.bool_false();
            d.bool_eq(c, value)
        };
        (yes, no)
    };

    let motive = {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let (yes, no) = disjunction(d, c);
        let body = d.or(yes, no);
        d.lam_fv(c_fv, bool_ty, body)
    };
    let minor_true = {
        let c = d.bool_true();
        let (yes, no) = disjunction(d, c);
        let witness = d.bool_refl(c);
        d.or_inl(yes, no, witness)
    };
    let minor_false = {
        let c = d.bool_false();
        let (yes, no) = disjunction(d, c);
        let witness = d.bool_refl(c);
        d.or_inr(yes, no, witness)
    };
    let zero = d.kernel().level_zero();
    let bool_rec = d.int().logic.bool_rec;
    let rec = d.kernel().const_(bool_rec, vec![zero]);
    d.apply(rec, &[motive, minor_false, minor_true, scrutinee])
}

/// `Or (Eq Nat m n) (Not (Eq Nat m n))` — decidable natural equality, from
/// `Nat.beq`'s proved soundness and completeness.
fn nat_decidable_equality(d: &mut IntDev<'_>, m: ExprId, n: ExprId) -> ExprId {
    let scrutinee = d.beq(m, n);
    let true_value = d.bool_true();
    let false_value = d.bool_false();
    let is_true = d.bool_eq(scrutinee, true_value);
    let is_false = d.bool_eq(scrutinee, false_value);
    let equal = d.eq(m, n);
    let distinct = d.not(equal);
    let goal = d.or(equal, distinct);
    let decision = beq_is_true_or_false(d, m, n);

    d.or_elim(
        is_true,
        is_false,
        goal,
        decision,
        &|d, holds| {
            let sound = d.int().nat.eq_of_beq_eq_true;
            let witness = d.const_app(sound, &[m, n, holds]);
            d.or_inl(equal, distinct, witness)
        },
        &|d, fails| {
            // `Nat.beq m n = false` refutes `m = n`: completeness would make it
            // `true`, and `Bool.false = Bool.true` is uninhabited.
            let fv = d.fresh_fvar();
            let assumed = d.kernel().fvar(fv);
            let complete = d.int().nat.beq_eq_true_of_eq;
            let forced = d.const_app(complete, &[m, n, assumed]);
            let reversed = d.bool_symm(scrutinee, false_value, fails);
            let clash = d.bool_trans(false_value, scrutinee, true_value, reversed, forced);
            let false_ty = d.false_ty();
            let contradiction = d.false_true_elim(false_ty, clash);
            let refutation = d.lam_fv(fv, equal, contradiction);
            d.or_inr(equal, distinct, refutation)
        },
    )
}

/// Declare `Int.eq_em`.
pub(super) fn declare_decidable_equality(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.eq_em, 2, &|d, v| {
        let stmt = statements::eq_em(d, v);
        let proof = case_split(d, v, &statements::eq_em, &|d, b| {
            let left = d.branch_term(b[0]);
            let right = d.branch_term(b[1]);
            let equality = d.ieq(left, right);
            let distinct = d.not(equality);
            let (m, n) = (b[0].1, b[1].1);
            match (b[0].0, b[1].0) {
                (Shape::OfNat, Shape::NegSucc) | (Shape::NegSucc, Shape::OfNat) => {
                    let positive_is_left = b[0].0 == Shape::OfNat;
                    let fv = d.fresh_fvar();
                    let assumed = d.kernel().fvar(fv);
                    let contradiction = discriminate(d, left, right, assumed, positive_is_left);
                    let refutation = d.lam_fv(fv, equality, contradiction);
                    d.or_inr(equality, distinct, refutation)
                }
                (Shape::OfNat, Shape::OfNat) | (Shape::NegSucc, Shape::NegSucc) => {
                    let constructor = b[0].0;
                    let decision = nat_decidable_equality(d, m, n);
                    let equal = d.eq(m, n);
                    let unequal = d.not(equal);
                    let goal = d.or(equality, distinct);
                    d.or_elim(
                        equal,
                        unequal,
                        goal,
                        decision,
                        &|d, holds| {
                            let lifted = d.nat_eq_to_int(m, n, holds, &|d, x| match constructor {
                                Shape::OfNat => d.of_nat(x),
                                Shape::NegSucc => d.neg_succ(x),
                            });
                            d.or_inl(equality, distinct, lifted)
                        },
                        &|d, fails| {
                            let fv = d.fresh_fvar();
                            let assumed = d.kernel().fvar(fv);
                            let projected = project_equality(d, left, right, assumed);
                            let contradiction = d.kernel().app(fails, projected);
                            let refutation = d.lam_fv(fv, equality, contradiction);
                            d.or_inr(equality, distinct, refutation)
                        },
                    )
                }
            }
        });
        (stmt, proof)
    })?;
    Ok(())
}
