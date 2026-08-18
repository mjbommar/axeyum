//! **ℝ, constructed**: a Bishop setoid of regular sequences of rationals over
//! the proved `ℚ`, with equality carried by a *defined* relation rather than by
//! `Eq`, and costing **zero** trusted declarations.
//!
//! This is ADR-0468
//! (`docs/research/09-decisions/adr-0468-real-is-constructed-as-a-setoid-over-the-rationals.md`)
//! phase R1, and it is what `examples/creal_shape_probe.rs` measured the shape
//! of before `ℚ` had an order. The probe admitted
//! `CReal.Of (reg : (Nat → Rat) → Prop)` — the carrier *parametric* in its
//! regularity predicate, because `Rat.le` did not exist. It does now, so the
//! predicate is a definition and the carrier is concrete.
//!
//! ## Why a setoid, in one line
//!
//! ADR-0456 priced the two textbook routes and found both closed here: a Cauchy
//! **quotient** needs `Quot.sound`, which this kernel's four-declaration
//! quotient package does not contain, and **Dedekind cuts** need `funext` and
//! `propext`, neither of which exists. The missing option was that equality
//! need not be `Eq`. `CReal.Equiv` is a `Prop`-valued definition, so the whole
//! construction is ordinary definitions and theorems.
//!
//! `Eq CReal` is **not** the equality of real numbers, and nothing here pretends
//! it is. `0.999… ` and `1` are distinct `CReal`s and `CReal.Equiv`-equal, which
//! is the correct and intended state of affairs.
//!
//! ## The three shapes this module is built out of
//!
//! - **`|a| ≤ b` is a pair.** [`Within`](CRealPrelude::within) is
//!   `−b ≤ a ∧ a ≤ b`, so `Rat.abs` is never needed — no sign case split, no
//!   congruence lemma, no monotonicity theory.
//! - **Every bound is one `Rat.natDivSucc`.** `1/(m+1)`, `2/(n+1)` and `6/(j+1)`
//!   are the same construction at different numerators, which is what lets the
//!   six-term estimate in [`Equiv.trans`](CRealPrelude::equiv_trans) fuse.
//! - **Regularity is a fixed modulus, not an existential.** Bishop's
//!   `|f m − f n| ≤ 1/(m+1) + 1/(n+1)` keeps the representative a plain
//!   function: the modulus never has to be extracted, and completeness will
//!   later be provable without countable choice. That is the trap a bare-Cauchy
//!   development falls into and the reason the HoTT book reaches for a higher
//!   inductive type.
//!
//! ## What transitivity costs, and where it is paid
//!
//! Chaining two closeness hypotheses directly gives `|x_n − z_n| ≤ 4/(n+1)`,
//! which is not the `≤ 2/(n+1)` the relation asks for, and no rearrangement
//! fixes that. Bishop compares at an arbitrary third index `j`:
//!
//! ```text
//! |x_n − z_n| ≤ |x_n − x_j| + |x_j − y_j| + |y_j − z_j| + |z_j − z_n|
//!             ≤ (1/(n+1) + 1/(j+1)) + 2/(j+1) + 2/(j+1) + (1/(j+1) + 1/(n+1))
//!              = 2/(n+1) + 6/(j+1)
//! ```
//!
//! and the `6/(j+1)` is discharged by
//! [`Rat.le_of_le_add_natDivSucc`](crate::RatPrelude::le_of_le_add_natDivSucc)
//! — the **Archimedean property of ℚ**, a statement about rationals that this
//! module only consumes. That is the price of the fixed modulus, and it is paid
//! once.

// Proof scripts are long, straight-line term constructions with short
// mathematical names, exactly as in `rat_prelude`.
#![allow(
    clippy::doc_markdown,
    clippy::large_types_passed_by_value,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_arguments,
    clippy::too_many_lines
)]

use crate::BinderInfo;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::group::{rsub, rsum, rsum_append, rsum_perm};
use crate::rat_prelude::ops::{radd, rat_eq_rewrite, rat_ty, rchain, rcongr, rneg, rsymm, rzero};
use crate::rat_prelude::{RatPrelude, build_rat_prelude};
use crate::{Kernel, KernelError};

/// Delta heights for the real definitions: above every `Rat` definition.
const LEAF_HEIGHT: u16 = 40;
/// Height for a definition that calls a leaf one.
const DERIVED_HEIGHT: u16 = 41;

/// The interned names produced by [`build_creal_prelude`]: the carrier, its
/// constructor and recursor, the two projections, the setoid relation, and its
/// three equivalence laws — plus the embedded [`RatPrelude`] the whole thing is
/// constructed over.
///
/// Handles belong to the kernel they were built in; do not mix them across
/// kernels.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CRealPrelude {
    /// The rational development `CReal` is constructed over. Its axiom
    /// footprint is empty, which is what makes every law below empty too.
    pub rat: RatPrelude,

    /// `CReal.Within : Rat → Rat → Prop` — `Within r q := −q ≤ r ∧ r ≤ q`.
    ///
    /// ADR-0468's encoding of `|r| ≤ q`, chosen so that `Rat.abs` never has to
    /// exist. Every bound in this module is stated through it.
    pub within: NameId,
    /// `CReal.Regular : (Nat → Rat) → Prop` — Bishop regularity with the
    /// **fixed** modulus `|f m − f n| ≤ 1/(m+1) + 1/(n+1)`.
    pub regular_pred: NameId,
    /// `CReal : Type` — a one-constructor inductive. **Not** a quotient: this
    /// kernel has no `Quot.sound` (ADR-0456), and does not need one.
    pub creal: NameId,
    /// `CReal.mk : (f : Nat → Rat) → CReal.Regular f → CReal`.
    pub mk: NameId,
    /// `CReal.rec` — the kernel-generated recursor.
    pub rec: NameId,
    /// `CReal.seq : CReal → Nat → Rat` — the representative, by **large
    /// elimination** out of a `Type`-valued inductive with a `Prop` field.
    pub seq: NameId,
    /// `CReal.regular : ∀ x, CReal.Regular (CReal.seq x)` — the regularity
    /// field, projected.
    pub regular: NameId,
    /// `CReal.Equiv : CReal → CReal → Prop` —
    /// `∀ n, Within (seq x n − seq y n) (2/(n+1))`.
    ///
    /// **This, and not `Eq CReal`, is the equality of real numbers.**
    pub equiv: NameId,
    /// `CReal.Equiv.refl : ∀ x, CReal.Equiv x x`.
    pub equiv_refl: NameId,
    /// `CReal.Equiv.symm : ∀ x y, CReal.Equiv x y → CReal.Equiv y x`.
    pub equiv_symm: NameId,
    /// `CReal.Equiv.trans : ∀ x y z, CReal.Equiv x y → CReal.Equiv y z → CReal.Equiv x z`.
    ///
    /// The one proof in the construction that is not routine — see the module
    /// documentation. It is the only consumer of the Archimedean property.
    pub equiv_trans: NameId,

    // --- the carrier is inhabited, and `Equiv` discriminates ------------------
    /// `CReal.ofRat : Rat → CReal` — the embedding `ℚ ↪ ℝ`, the constant
    /// sequence.
    ///
    /// It is also the **non-vacuity** witness. Everything above is a statement
    /// about the inhabitants of `CReal`, so if `CReal.Regular` had no solutions
    /// the carrier would be empty and `refl`, `symm` and `trans` would all be
    /// true and worthless — and an empty axiom footprint would not notice.
    pub of_rat: NameId,
    /// `CReal.Equiv.not_zero_one : Not (CReal.Equiv (ofRat Rat.zero) (ofRat Rat.one))`.
    ///
    /// The **discrimination** witness. `Equiv` being an equivalence relation is
    /// worth nothing if `Equiv` is the total relation; this exhibits two
    /// `CReal`s it separates, and it separates them *by computation* — the
    /// witness index is `3`, and `−1/2 ≤ −1` reduces to `Nat.le 1 0`.
    pub not_zero_one: NameId,

    // --- the additive structure (ADR-0468 phase R2, partial) -----------------
    /// `CReal.zero : CReal` — `ofRat Rat.zero`.
    pub zero: NameId,
    /// `CReal.one : CReal` — `ofRat Rat.one`.
    pub one: NameId,
    /// `CReal.Equiv.of_pointwise : ∀ x y, (∀ n, Eq Rat (seq x n) (seq y n)) → Equiv x y`.
    ///
    /// The bridge from `Eq` to `Equiv`, and the reason the *pointwise* laws
    /// below are cheap: an operation whose two sides agree at every index is
    /// `Equiv`-equal without any analytic argument at all. It is one-way, and
    /// deliberately: the converse is false, which is the whole reason `CReal`
    /// is a setoid.
    pub equiv_of_pointwise: NameId,
    /// `CReal.neg : CReal → CReal` — pointwise negation. **No index shift**:
    /// negation does not degrade the modulus, which is why it lands before
    /// `add` does.
    pub neg: NameId,
    /// `CReal.neg_congr : ∀ x y, Equiv x y → Equiv (neg x) (neg y)` — the first
    /// of the setoid's congruence obligations, which ADR-0468 counts as the
    /// construction's real tax.
    pub neg_congr: NameId,
    /// `CReal.add : CReal → CReal → CReal`, with **Bishop's index shift**:
    /// `(x + y)_n := x_{2n+1} + y_{2n+1}`.
    ///
    /// The shift is not decoration. Adding two regular sequences doubles the
    /// error, so the naive pointwise sum is *not* regular; sampling at `2n+1`
    /// halves each modulus first, and
    /// [`Rat.natDivSucc_halve`](crate::RatPrelude::nat_div_succ_halve) is the
    /// identity that cashes the trade.
    pub add: NameId,
    /// `CReal.add_congr : ∀ x x' y y', Equiv x x' → Equiv y y' →
    /// Equiv (add x y) (add x' y')` — the second congruence obligation.
    pub add_congr: NameId,
    /// `CReal.add_comm : ∀ x y, Equiv (add x y) (add y x)` — one of the 22, in
    /// `Equiv` form. Both sides sample at the same index, so it is *pointwise*
    /// and costs one `Rat.add_comm`.
    pub add_comm: NameId,
    /// `CReal.add_neg : ∀ x, Equiv (add x (neg x)) zero` — one of the 22, in
    /// `Equiv` form, and pointwise for the same reason.
    pub add_neg: NameId,
    /// `CReal.add_zero : ∀ x, Equiv (add x zero) x` — one of the 22, and the
    /// first that is **not** pointwise: `add x zero` samples `x` at `2n+1`
    /// where `x` samples it at `n`, so the two sides are not equal at any
    /// index and `Equiv.of_pointwise` does not apply. Regularity closes the
    /// gap, and the slack is paid by [`shifted_bound_le`].
    pub add_zero: NameId,
    /// `CReal.le : CReal → CReal → Prop` —
    /// `le x y := ∀ n, seq x n − seq y n ≤ 2/(n+1)`.
    ///
    /// Bishop's order, and the **one-sided** reading of `Equiv`: `Equiv x y`
    /// is exactly `le x y ∧ le y x` unfolded. That is not a coincidence to be
    /// exploited later, it is why the order laws cost so little here — every
    /// estimate `Equiv` needed is already one-sided inside, and the two-sided
    /// version was the expensive packaging.
    ///
    /// **`le` is not decidable and no totality law is stated.** `le_or_lt`
    /// holds for `ℚ` and does not lift: `∀ x y, le x y ∨ le y x` over the reals
    /// is not constructively provable, and nothing below assumes it.
    pub le: NameId,
    /// `CReal.le_refl : ∀ x, le x x` — one of the 22, and verbatim: it
    /// mentions no `Eq`, so unlike the additive laws it does not have to be
    /// restated over `Equiv`.
    pub le_refl: NameId,
    /// `CReal.le_trans : ∀ x y z, le x y → le y z → le x z` — one of the 22,
    /// verbatim, and the **upper half of `Equiv.trans`**: the same four-term
    /// estimate at an arbitrary index `j`, the same
    /// [`telescope_four`]/[`six_term_bound`], the same Archimedean lemma —
    /// with `Rat.add_le_add` in place of `Rat.bounds_add` and no negated
    /// branch at all.
    pub le_trans: NameId,
    /// `CReal.add_le_add : ∀ x x' y y', le x x' → le y y' →
    /// le (add x y) (add x' y')` — one of the 22, verbatim. Exact, like
    /// `add_congr`: two `2/(2n+2)` bounds sum to `2/(n+1)` with no slack.
    pub add_le_add: NameId,
    /// `CReal.le_of_equiv : ∀ x y, Equiv x y → le x y`.
    ///
    /// Half of the coherence between the order and the setoid's equality, and
    /// it is a projection: `Equiv` *is* the two-sided bound whose upper half is
    /// `le`.
    pub le_of_equiv: NameId,
    /// `CReal.equiv_of_le_le : ∀ x y, le x y → le y x → Equiv x y`.
    ///
    /// The other half — **antisymmetry up to `Equiv`** — and the reason the
    /// three order laws are laws about *this* order rather than about some
    /// coarser relation that happens to satisfy them. A `le` weakened to
    /// `≤ 100/(n+1)` would still be reflexive, transitive and additive; it
    /// would not close this.
    pub equiv_of_le_le: NameId,
    /// `CReal.not_le_one_zero : Not (le one zero)`.
    ///
    /// The **discrimination** witness for the order, and the reason the three
    /// laws above are worth anything: `le_refl`, `le_trans` and `add_le_add`
    /// all hold, footprint-free, of the relation that relates everything. This
    /// exhibits a pair `le` separates, by computation — at index `3` the claim
    /// is `1 ≤ 1/2`, which unfolds through `Int.le` to `Nat.le 2 1`.
    pub not_le_one_zero: NameId,
    /// `CReal.add_assoc : ∀ x y z, Equiv (add (add x y) z) (add x (add y z))`
    /// — one of the 22, and the analytic one: `(x+y)+z` samples `x` at
    /// `2(2n+1)+1` while `x+(y+z)` samples it at `2n+1`, and `z` the other way
    /// round. `y` is sampled at the same index on both sides and cancels, so
    /// the whole difference is `(x_M − x_N) + (z_N − z_M)` — two regularity
    /// bounds, and then the *same* inequality `add_zero` needs.
    pub add_assoc: NameId,
}

fn intern_names(kernel: &mut Kernel, rat: RatPrelude) -> CRealPrelude {
    let anon = kernel.anon();
    let creal = kernel.name_str(anon, "CReal");
    let equiv = kernel.name_str(creal, "Equiv");
    CRealPrelude {
        rat,
        within: kernel.name_str(creal, "Within"),
        regular_pred: kernel.name_str(creal, "Regular"),
        creal,
        mk: kernel.name_str(creal, "mk"),
        rec: kernel.name_str(creal, "rec"),
        seq: kernel.name_str(creal, "seq"),
        regular: kernel.name_str(creal, "regular"),
        equiv,
        equiv_refl: kernel.name_str(equiv, "refl"),
        equiv_symm: kernel.name_str(equiv, "symm"),
        equiv_trans: kernel.name_str(equiv, "trans"),
        of_rat: kernel.name_str(creal, "ofRat"),
        not_zero_one: kernel.name_str(equiv, "not_zero_one"),
        zero: kernel.name_str(creal, "zero"),
        one: kernel.name_str(creal, "one"),
        equiv_of_pointwise: kernel.name_str(equiv, "of_pointwise"),
        neg: kernel.name_str(creal, "neg"),
        neg_congr: kernel.name_str(creal, "neg_congr"),
        add: kernel.name_str(creal, "add"),
        add_congr: kernel.name_str(creal, "add_congr"),
        add_comm: kernel.name_str(creal, "add_comm"),
        add_neg: kernel.name_str(creal, "add_neg"),
        add_zero: kernel.name_str(creal, "add_zero"),
        add_assoc: kernel.name_str(creal, "add_assoc"),
        le: kernel.name_str(creal, "le"),
        le_refl: kernel.name_str(creal, "le_refl"),
        le_trans: kernel.name_str(creal, "le_trans"),
        add_le_add: kernel.name_str(creal, "add_le_add"),
        le_of_equiv: kernel.name_str(creal, "le_of_equiv"),
        equiv_of_le_le: kernel.name_str(creal, "equiv_of_le_le"),
        not_le_one_zero: kernel.name_str(creal, "not_le_one_zero"),
    }
}

/// Build the real prelude: `ℝ` as a Bishop setoid over the constructed `ℚ`,
/// **asserting nothing**.
///
/// Idempotent on a kernel that already carries it. A failure rolls the
/// environment back to the pre-call state.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub fn build_creal_prelude(kernel: &mut Kernel) -> Result<CRealPrelude, KernelError> {
    let rat = build_rat_prelude(kernel)?;
    let prelude = intern_names(kernel, rat);
    if kernel.environment().get(prelude.creal).is_some() {
        return Ok(prelude);
    }
    let checkpoint = kernel.prelude_checkpoint();
    let built = (|| -> Result<(), KernelError> {
        let mut d = IntDev::new(kernel, rat.int);
        declare_predicates(&mut d, prelude)?;
        declare_carrier(&mut d, prelude)?;
        declare_projections(&mut d, prelude)?;
        declare_equiv(&mut d, prelude)?;
        declare_reflexivity(&mut d, prelude)?;
        declare_symmetry(&mut d, prelude)?;
        declare_transitivity(&mut d, prelude)?;
        declare_of_rat(&mut d, prelude)?;
        declare_discrimination(&mut d, prelude)?;
        declare_constants(&mut d, prelude)?;
        declare_pointwise(&mut d, prelude)?;
        declare_negation(&mut d, prelude)?;
        declare_addition(&mut d, prelude)?;
        declare_additive_laws(&mut d, prelude)?;
        declare_order(&mut d, prelude)
    })();
    match built {
        Ok(()) => Ok(prelude),
        Err(error) => {
            kernel.rollback_prelude(checkpoint);
            Err(error)
        }
    }
}

// --- term builders ----------------------------------------------------------

/// `Nat → Rat`, the representative type. Its own sort is `Type 0`, so a field of
/// this type does not push the carrier up a universe.
fn seq_ty(d: &mut IntDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    d.arrow(nat, carrier)
}

/// `CReal`.
fn creal_ty(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    d.kernel().const_(p.creal, vec![])
}

/// `CReal.Within r q`.
fn within(d: &mut IntDev<'_>, p: CRealPrelude, r: ExprId, q: ExprId) -> ExprId {
    d.const_app(p.within, &[r, q])
}

/// `CReal.seq x n`.
fn sample(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.seq, &[x, n])
}

/// `Rat.natDivSucc k j`, with `k` a literal.
fn div_succ(d: &mut IntDev<'_>, p: CRealPrelude, k: u32, j: ExprId) -> ExprId {
    let numerator = d.num(k);
    d.const_app(p.rat.nat_div_succ, &[numerator, j])
}

/// `Rat.add (natDivSucc 1 m) (natDivSucc 1 n)` — the regularity modulus,
/// written inline rather than behind a constant so the rearrangement in
/// [`declare_transitivity`] sees the two summands.
fn modulus(d: &mut IntDev<'_>, p: CRealPrelude, m: ExprId, n: ExprId) -> ExprId {
    let left = div_succ(d, p, 1, m);
    let right = div_succ(d, p, 1, n);
    radd(d, left, right)
}

/// `CReal.Equiv x y`.
fn equiv(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.equiv, &[x, y])
}

/// `And.intro`, at two `Prop`s.
fn and_intro(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    left: ExprId,
    right: ExprId,
    lp: ExprId,
    rp: ExprId,
) -> ExprId {
    let intro = p.rat.int.logic.and_intro;
    d.const_app(intro, &[left, right, lp, rp])
}

/// The lower and upper halves of a `Within r q` proof.
fn halves(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    r: ExprId,
    q: ExprId,
    proof: ExprId,
) -> (ExprId, ExprId) {
    let rat = p.rat;
    let negated = rneg(d, q);
    let lower = crate::rat_prelude::ops::rle(d, rat, negated, r);
    let upper = crate::rat_prelude::ops::rle(d, rat, r, q);
    let left = d.and_left(lower, upper, proof);
    let right = d.and_right(lower, upper, proof);
    (left, right)
}

/// Widen a two-sided bound: from `Within r q` and `q ≤ q'`, `Within r q'`.
///
/// The one thing the `−b ≤ a ∧ a ≤ b` encoding needs that an `abs` operator
/// would give for free, and it is four lines: the upper half is `le_trans`
/// outright, the lower half is `le_trans` after `neg_le_neg` turns `q ≤ q'`
/// into `−q' ≤ −q`.
fn weaken(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    r: ExprId,
    bound: ExprId,
    wider: ExprId,
    proof: ExprId,
    order: ExprId,
) -> ExprId {
    let rat = p.rat;
    let rle = crate::rat_prelude::ops::rle;
    let (lower, upper) = halves(d, p, r, bound, proof);
    let widened = d.lemma(rat.le_trans, &[r, bound, wider, upper, order]);
    let negated_wide = rneg(d, wider);
    let negated_bound = rneg(d, bound);
    let flipped = d.lemma(rat.neg_le_neg, &[bound, wider, order]);
    let deepened = d.lemma(
        rat.le_trans,
        &[negated_wide, negated_bound, r, flipped, lower],
    );
    let lower_ty = rle(d, rat, negated_wide, r);
    let upper_ty = rle(d, rat, r, wider);
    and_intro(d, p, lower_ty, upper_ty, deepened, widened)
}

/// `1/(2n+2) + 1/(n+1) ≤ 2/(n+1)` — the single inequality that both `add_zero`
/// and `add_assoc` reduce to.
///
/// Both laws compare a sample at Bishop's shifted index `2n+1` with one at `n`,
/// and regularity bounds that difference by `1/(2n+2) + 1/(n+1)` where the
/// setoid asks for `2/(n+1)`. Read at the common denominator `2n+2` — which is
/// what [`Rat.natDivSucc_halve`](crate::RatPrelude::nat_div_succ_halve)
/// supplies, `1/(n+1) = 2/(2n+2)` — the two sides are `3/(2n+2)` and `4/(2n+2)`,
/// so the gap is one `1/(2n+2)` and closing it needs only nonnegativity. **No
/// monotonicity of `natDivSucc` in its index is required**, which is what makes
/// these two laws cost a helper rather than a new rational development.
///
/// Returns a proof of `Rat.le (modulus (2n+1) n) (natDivSucc 2 n)`.
fn shifted_bound_le(d: &mut IntDev<'_>, p: CRealPrelude, n: ExprId) -> ExprId {
    let rat = p.rat;
    let rle = crate::rat_prelude::ops::rle;
    let s = shift(d, n);
    let one_s = div_succ(d, p, 1, s);
    let two_s = div_succ(d, p, 2, s);
    let three_s = div_succ(d, p, 3, s);
    let four_s = div_succ(d, p, 4, s);
    let one_n = div_succ(d, p, 1, n);
    let two_n = div_succ(d, p, 2, n);
    let one_nat = d.num(1);
    let two_nat = d.num(2);
    let three_nat = d.num(3);

    // `1/(n+1) = 2/(2n+2)`: the halving identity, read backwards.
    let halve = d.lemma(rat.nat_div_succ_halve, &[n]);
    let deepen = rsymm(d, two_s, one_n, halve);

    // Left: `1/(2n+2) + 1/(n+1) = 1/(2n+2) + 2/(2n+2) = 3/(2n+2)`.
    let start = radd(d, one_s, one_n);
    let staged = radd(d, one_s, two_s);
    let step = rcongr(d, one_n, two_s, deepen, &|d, t| radd(d, one_s, t));
    let fuse_left = d.lemma(rat.nat_div_succ_add, &[one_nat, two_nat, s]);
    let (_, left_chain) = rchain(d, start, &[(staged, step), (three_s, fuse_left)]);

    // Right: `2/(n+1) = 1/(n+1) + 1/(n+1) = 2/(2n+2) + 2/(2n+2) = 4/(2n+2)`.
    let split = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, n]);
    let doubled_n = radd(d, one_n, one_n);
    let unsplit = rsymm(d, doubled_n, two_n, split);
    let first = rcongr(d, one_n, two_s, deepen, &|d, t| radd(d, t, one_n));
    let mixed = radd(d, two_s, one_n);
    let second = rcongr(d, one_n, two_s, deepen, &|d, t| radd(d, two_s, t));
    let doubled_s = radd(d, two_s, two_s);
    let fuse_right = d.lemma(rat.nat_div_succ_add, &[two_nat, two_nat, s]);
    let (_, right_chain) = rchain(
        d,
        two_n,
        &[
            (doubled_n, unsplit),
            (mixed, first),
            (doubled_s, second),
            (four_s, fuse_right),
        ],
    );

    // `3/(2n+2) ≤ 3/(2n+2) + 1/(2n+2) = 4/(2n+2)`.
    let zero = rzero(d, rat);
    let nonneg = d.lemma(rat.zero_le_nat_div_succ, &[one_nat, s]);
    let reflexive = d.lemma(rat.le_refl, &[three_s]);
    let padded = d.lemma(
        rat.add_le_add,
        &[three_s, three_s, zero, one_s, reflexive, nonneg],
    );
    let with_zero = radd(d, three_s, zero);
    let sum = radd(d, three_s, one_s);
    let collapse = d.lemma(rat.add_zero, &[three_s]);
    let trimmed = rat_eq_rewrite(d, with_zero, three_s, collapse, padded, &|d, t| {
        rle(d, rat, t, sum)
    });
    let fuse_gap = d.lemma(rat.nat_div_succ_add, &[three_nat, one_nat, s]);
    let core = rat_eq_rewrite(d, sum, four_s, fuse_gap, trimmed, &|d, t| {
        rle(d, rat, three_s, t)
    });

    // Read both endpoints back at their original denominators.
    let widen_left = rsymm(d, start, three_s, left_chain);
    let moved = rat_eq_rewrite(d, three_s, start, widen_left, core, &|d, t| {
        rle(d, rat, t, four_s)
    });
    let widen_right = rsymm(d, two_n, four_s, right_chain);
    rat_eq_rewrite(d, four_s, two_n, widen_right, moved, &|d, t| {
        rle(d, rat, start, t)
    })
}

/// The **quantity** half of Bishop's four-term estimate:
/// `(a − p) + ((p − q) + ((q − r) + (r − b))) = a − b`, three applications of
/// the telescoping identity from the inside out.
///
/// Returns `(start, target, proof)` with `proof : Eq Rat start target`. Nothing
/// here is a rearrangement — the four differences are combined right-nested
/// precisely so that they chain — and nothing here depends on *which* bound
/// each difference carries, which is why the two-sided `Equiv.trans` and the
/// one-sided [`CReal.le_trans`](CRealPrelude::le_trans) share it verbatim.
fn telescope_four(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    head: ExprId,
    first_mid: ExprId,
    second_mid: ExprId,
    third_mid: ExprId,
    tail: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let rat = p.rat;
    let u1 = rsub(d, rat, head, first_mid);
    let u2 = rsub(d, rat, first_mid, second_mid);
    let u3 = rsub(d, rat, second_mid, third_mid);
    let u4 = rsub(d, rat, third_mid, tail);
    let q34 = radd(d, u3, u4);
    let q234 = radd(d, u2, q34);
    let q1234 = radd(d, u1, q234);
    let target = rsub(d, rat, head, tail);

    let mid_second = rsub(d, rat, second_mid, tail);
    let mid_first = rsub(d, rat, first_mid, tail);
    let step34 = d.lemma(rat.sub_add_sub, &[second_mid, third_mid, tail]);
    let step234 = d.lemma(rat.sub_add_sub, &[first_mid, second_mid, tail]);
    let step1234 = d.lemma(rat.sub_add_sub, &[head, first_mid, tail]);
    let q234_reduced = radd(d, u2, mid_second);
    let staged = radd(d, u1, q234_reduced);
    let first = rcongr(d, q34, mid_second, step34, &|d, t| {
        let inner = radd(d, u2, t);
        radd(d, u1, inner)
    });
    let second = rcongr(d, q234_reduced, mid_first, step234, &|d, t| radd(d, u1, t));
    let q1234_reduced = radd(d, u1, mid_first);
    let (_, quantity) = rchain(
        d,
        q1234,
        &[(staged, first), (q1234_reduced, second), (target, step1234)],
    );
    (q1234, target, quantity)
}

/// The **bound** half of Bishop's four-term estimate:
/// `(1/(n+1) + 1/(j+1)) + (2/(j+1) + (2/(j+1) + (1/(j+1) + 1/(n+1))))` fused
/// into `2/(n+1) + 6/(j+1)`, which is the form the Archimedean lemma consumes.
///
/// Returns `(start, target, proof)` with `proof : Eq Rat start target`. Six
/// summands over two denominators; `rsum_perm` sorts them and
/// `Rat.natDivSucc_add` fuses each group, and the sort is done by the shared
/// helper rather than inline because that is where a proof of this size goes
/// wrong silently.
fn six_term_bound(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    n: ExprId,
    j: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let rat = p.rat;
    let b1 = modulus(d, p, n, j);
    let b2 = div_succ(d, p, 2, j);
    let b3 = div_succ(d, p, 2, j);
    let b4 = modulus(d, p, j, n);
    let c34 = radd(d, b3, b4);
    let c234 = radd(d, b2, c34);
    let c1234 = radd(d, b1, c234);
    // The bound rearranges: (A+Bj) + (Cj + (Cj + (Bj+A))) = 2/(n+1) + 6/(j+1).
    let a_atom = div_succ(d, p, 1, n);
    let b_atom = div_succ(d, p, 1, j);
    let c_atom = div_succ(d, p, 2, j);
    let flat_atoms = [a_atom, b_atom, c_atom, c_atom, b_atom, a_atom];
    let sorted_atoms = [a_atom, a_atom, b_atom, c_atom, c_atom, b_atom];
    let flatten = rsum_append(d, rat, &flat_atoms[..2], &flat_atoms[2..]);
    let flat = rsum(d, rat, &flat_atoms);
    let permute = rsum_perm(d, rat, &flat_atoms, &sorted_atoms);
    let sorted = rsum(d, rat, &sorted_atoms);

    let one_nat = d.num(1);
    let two_nat = d.num(2);
    let three = div_succ(d, p, 3, j);
    let five = div_succ(d, p, 5, j);
    let six = div_succ(d, p, 6, j);
    let fuse_inner = d.lemma(rat.nat_div_succ_add, &[two_nat, one_nat, j]);
    let cb = radd(d, c_atom, b_atom);
    let after_inner = rcongr(d, cb, three, fuse_inner, &|d, t| {
        let level1 = radd(d, c_atom, t);
        let level2 = radd(d, b_atom, level1);
        let level3 = radd(d, a_atom, level2);
        radd(d, a_atom, level3)
    });
    let sorted_1 = {
        let level1 = radd(d, c_atom, three);
        let level2 = radd(d, b_atom, level1);
        let level3 = radd(d, a_atom, level2);
        radd(d, a_atom, level3)
    };
    let three_nat = d.num(3);
    let fuse_mid = d.lemma(rat.nat_div_succ_add, &[two_nat, three_nat, j]);
    let c3 = radd(d, c_atom, three);
    let after_mid = rcongr(d, c3, five, fuse_mid, &|d, t| {
        let level2 = radd(d, b_atom, t);
        let level3 = radd(d, a_atom, level2);
        radd(d, a_atom, level3)
    });
    let sorted_2 = {
        let level2 = radd(d, b_atom, five);
        let level3 = radd(d, a_atom, level2);
        radd(d, a_atom, level3)
    };
    let five_nat = d.num(5);
    let fuse_outer = d.lemma(rat.nat_div_succ_add, &[one_nat, five_nat, j]);
    let b5 = radd(d, b_atom, five);
    let after_outer = rcongr(d, b5, six, fuse_outer, &|d, t| {
        let level3 = radd(d, a_atom, t);
        radd(d, a_atom, level3)
    });
    let sorted_3 = {
        let level3 = radd(d, a_atom, six);
        radd(d, a_atom, level3)
    };
    let regroup = {
        let forward = d.lemma(rat.add_assoc, &[a_atom, a_atom, six]);
        let flat_pair = {
            let aa = radd(d, a_atom, a_atom);
            radd(d, aa, six)
        };
        rsymm(d, flat_pair, sorted_3, forward)
    };
    let aa = radd(d, a_atom, a_atom);
    let flat_pair = radd(d, aa, six);
    let fuse_head = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, n]);
    let head_bound = div_succ(d, p, 2, n);
    let after_head = rcongr(d, aa, head_bound, fuse_head, &|d, t| radd(d, t, six));
    let final_bound = radd(d, head_bound, six);
    let (_, bound_chain) = rchain(
        d,
        c1234,
        &[
            (flat, flatten),
            (sorted, permute),
            (sorted_1, after_inner),
            (sorted_2, after_mid),
            (sorted_3, after_outer),
            (flat_pair, regroup),
            (final_bound, after_head),
        ],
    );
    (c1234, final_bound, bound_chain)
}

// --- the definitions --------------------------------------------------------

/// `CReal.Within` and `CReal.Regular`.
fn declare_predicates(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = rat_ty(d);
    let prop = d.kernel().sort_zero();

    // Within r q := And (Rat.le (Rat.neg q) r) (Rat.le r q)
    {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let negated = rneg(d, q);
        let lower = crate::rat_prelude::ops::rle(d, rat, negated, r);
        let upper = crate::rat_prelude::ops::rle(d, rat, r, q);
        let body = d.and(lower, upper);
        let value = {
            let with_q = d.lam_fv(q_fv, carrier, body);
            d.lam_fv(r_fv, carrier, with_q)
        };
        let ty = {
            let inner = d.arrow(carrier, prop);
            d.arrow(carrier, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.within,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(LEAF_HEIGHT),
        })?;
    }

    // Regular f := ∀ (m n : Nat), Within (Rat.sub (f m) (f n)) (1/(m+1) + 1/(n+1))
    {
        let nat = d.nat_ty();
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let left = d.apply(f, &[m]);
        let right = d.apply(f, &[n]);
        let difference = rsub(d, rat, left, right);
        let bound = modulus(d, p, m, n);
        let claim = within(d, p, difference, bound);
        let body = {
            let over_n = d.pi_fv(n_fv, nat, claim);
            d.pi_fv(m_fv, nat, over_n)
        };
        let sequences = seq_ty(d);
        let value = d.lam_fv(f_fv, sequences, body);
        let ty = d.arrow(sequences, prop);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.regular_pred,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(DERIVED_HEIGHT),
        })?;
    }
    Ok(())
}

/// The carrier: a one-constructor inductive in `Type 0` with a function field
/// and a dependent `Prop` field over it.
fn declare_carrier(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let sequences = seq_ty(d);
    let one = d.level_one();
    let type0 = d.kernel().sort(one);

    let mk_ty = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let regular = d.const_app(p.regular_pred, &[f]);
        let result = creal_ty(d, p);
        let body = d.arrow(regular, result);
        d.pi_fv(f_fv, sequences, body)
    };
    d.kernel()
        .add_inductive(p.creal, &[], 0, type0, &[(p.mk, mk_ty)])
}

/// The two projections: the representative (large elimination, into `Type 0`)
/// and its regularity proof (into `Prop`).
fn declare_projections(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let sequences = seq_ty(d);
    let one = d.level_one();
    let zero_level = d.kernel().level_zero();
    let anon = d.anon_name();
    let carrier = creal_ty(d, p);

    // seq x := CReal.rec (fun _ => Nat → Rat) (fun f _ => f) x
    {
        let motive = d
            .kernel()
            .lam(anon, carrier, sequences, BinderInfo::Default);
        let minor = {
            let f_fv = d.fresh_fvar();
            let f = d.kernel().fvar(f_fv);
            let regular = d.const_app(p.regular_pred, &[f]);
            let inner = d.kernel().lam(anon, regular, f, BinderInfo::Default);
            d.lam_fv(f_fv, sequences, inner)
        };
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let rec = d.kernel().const_(p.rec, vec![one]);
        let body = d.apply(rec, &[motive, minor, x]);
        let value = d.lam_fv(x_fv, carrier, body);
        let ty = d.arrow(carrier, sequences);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.seq,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 1),
        })?;
    }

    // regular x : Regular (seq x) := CReal.rec (fun y => Regular (seq y)) (fun f h => h) x
    {
        let claim = |d: &mut IntDev<'_>, y: ExprId| {
            let representative = d.const_app(p.seq, &[y]);
            d.const_app(p.regular_pred, &[representative])
        };
        let motive = {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let body = claim(d, y);
            d.lam_fv(y_fv, carrier, body)
        };
        let minor = {
            let f_fv = d.fresh_fvar();
            let f = d.kernel().fvar(f_fv);
            let regular = d.const_app(p.regular_pred, &[f]);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let inner = d.lam_fv(h_fv, regular, h);
            d.lam_fv(f_fv, sequences, inner)
        };
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let rec = d.kernel().const_(p.rec, vec![zero_level]);
        let body = d.apply(rec, &[motive, minor, x]);
        let value = d.lam_fv(x_fv, carrier, body);
        let ty = {
            let inner = claim(d, x);
            d.pi_fv(x_fv, carrier, inner)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.regular,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// `CReal.Equiv x y := ∀ n, Within (seq x n − seq y n) (2/(n+1))`.
fn declare_equiv(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let prop = d.kernel().sort_zero();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let left = sample(d, p, x, n);
    let right = sample(d, p, y, n);
    let difference = rsub(d, p.rat, left, right);
    let bound = div_succ(d, p, 2, n);
    let claim = within(d, p, difference, bound);
    let body = d.pi_fv(n_fv, nat, claim);
    let value = {
        let with_y = d.lam_fv(y_fv, carrier, body);
        d.lam_fv(x_fv, carrier, with_y)
    };
    let ty = {
        let inner = d.arrow(carrier, prop);
        d.arrow(carrier, inner)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.equiv,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 2),
    })
}

/// `Equiv.refl`: `seq x n − seq x n = 0`, and `0` is inside every bound.
fn declare_reflexivity(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let point = sample(d, p, x, n);
    let difference = rsub(d, rat, point, point);
    let bound = div_succ(d, p, 2, n);
    let zero = rzero(d, rat);
    let negated = rneg(d, bound);

    let collapse = d.lemma(rat.sub_self, &[point]);
    let back = rsymm(d, difference, zero, collapse);
    let two = d.num(2);
    let nonneg = d.lemma(rat.zero_le_nat_div_succ, &[two, n]);
    let nonpos = d.lemma(rat.neg_nonpos_of_nonneg, &[bound, nonneg]);
    let lower = rat_eq_rewrite(d, zero, difference, back, nonpos, &|d, t| {
        crate::rat_prelude::ops::rle(d, rat, negated, t)
    });
    let upper = rat_eq_rewrite(d, zero, difference, back, nonneg, &|d, t| {
        crate::rat_prelude::ops::rle(d, rat, t, bound)
    });
    let lower_ty = crate::rat_prelude::ops::rle(d, rat, negated, difference);
    let upper_ty = crate::rat_prelude::ops::rle(d, rat, difference, bound);
    let pair = and_intro(d, p, lower_ty, upper_ty, lower, upper);
    let value = {
        let over_n = d.lam_fv(n_fv, nat, pair);
        d.lam_fv(x_fv, carrier, over_n)
    };
    let ty = {
        let inner = equiv(d, p, x, x);
        d.pi_fv(x_fv, carrier, inner)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.equiv_refl,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Equiv.symm`: negate the two-sided bound, then `−(a − b) = b − a`.
fn declare_symmetry(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let hypothesis = equiv(d, p, x, y);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let a = sample(d, p, x, n);
    let b = sample(d, p, y, n);
    let forward = rsub(d, rat, a, b);
    let backward = rsub(d, rat, b, a);
    let bound = div_succ(d, p, 2, n);
    let instance = d.apply(h, &[n]);
    let (lower, upper) = halves(d, p, forward, bound, instance);
    let flipped = d.lemma(rat.bounds_neg, &[forward, bound, lower, upper]);
    let negated_forward = rneg(d, forward);
    let rewrite = d.lemma(rat.neg_sub, &[a, b]);
    let body = rat_eq_rewrite(d, negated_forward, backward, rewrite, flipped, &|d, t| {
        within(d, p, t, bound)
    });
    let value = {
        let over_n = d.lam_fv(n_fv, nat, body);
        let with_h = d.lam_fv(h_fv, hypothesis, over_n);
        let with_y = d.lam_fv(y_fv, carrier, with_h);
        d.lam_fv(x_fv, carrier, with_y)
    };
    let ty = {
        let conclusion = equiv(d, p, y, x);
        let inner = d.arrow(hypothesis, conclusion);
        let with_y = d.pi_fv(y_fv, carrier, inner);
        d.pi_fv(x_fv, carrier, with_y)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.equiv_symm,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Equiv.trans`: Bishop's four-term estimate at an arbitrary index `j`,
/// closed by the Archimedean property of `ℚ`.
fn declare_transitivity(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let rle = crate::rat_prelude::ops::rle;

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let first_ty = equiv(d, p, x, y);
    let second_ty = equiv(d, p, y, z);
    let hxy_fv = d.fresh_fvar();
    let hxy = d.kernel().fvar(hxy_fv);
    let hyz_fv = d.fresh_fvar();
    let hyz = d.kernel().fvar(hyz_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let head = sample(d, p, x, n);
    let tail = sample(d, p, z, n);
    let target = rsub(d, rat, head, tail);
    let goal_bound = div_succ(d, p, 2, n);

    // The estimate at an arbitrary index `j`, as a function of `j`.
    let estimate = |d: &mut IntDev<'_>, j: ExprId| -> (ExprId, ExprId) {
        let xj = sample(d, p, x, j);
        let yj = sample(d, p, y, j);
        let zj = sample(d, p, z, j);
        let u1 = rsub(d, rat, head, xj);
        let u2 = rsub(d, rat, xj, yj);
        let u3 = rsub(d, rat, yj, zj);
        let u4 = rsub(d, rat, zj, tail);
        let b1 = modulus(d, p, n, j);
        let b2 = div_succ(d, p, 2, j);
        let b3 = div_succ(d, p, 2, j);
        let b4 = modulus(d, p, j, n);

        let w1 = d.lemma(p.regular, &[x, n, j]);
        let w2 = d.apply(hxy, &[j]);
        let w3 = d.apply(hyz, &[j]);
        let w4 = d.lemma(p.regular, &[z, j, n]);

        let (l1, r1) = halves(d, p, u1, b1, w1);
        let (l2, r2) = halves(d, p, u2, b2, w2);
        let (l3, r3) = halves(d, p, u3, b3, w3);
        let (l4, r4) = halves(d, p, u4, b4, w4);

        // Combine right-nested, so the quantities telescope in the same order.
        let w34 = d.lemma(rat.bounds_add, &[u3, b3, u4, b4, l3, r3, l4, r4]);
        let q34 = radd(d, u3, u4);
        let c34 = radd(d, b3, b4);
        let (l34, r34) = halves(d, p, q34, c34, w34);
        let w234 = d.lemma(rat.bounds_add, &[u2, b2, q34, c34, l2, r2, l34, r34]);
        let q234 = radd(d, u2, q34);
        let c234 = radd(d, b2, c34);
        let (l234, r234) = halves(d, p, q234, c234, w234);
        let w1234 = d.lemma(rat.bounds_add, &[u1, b1, q234, c234, l1, r1, l234, r234]);
        let q1234 = radd(d, u1, q234);
        let c1234 = radd(d, b1, c234);

        // The quantity telescopes and the bound fuses — both are functions of
        // the five sample points and of `(n, j)` alone, so both are shared with
        // `CReal.le_trans`, which runs the *upper half* of this same estimate.
        let (_, _, quantity) = telescope_four(d, p, head, xj, yj, zj, tail);
        let (_, final_bound, bound_chain) = six_term_bound(d, p, n, j);

        let at_quantity = rat_eq_rewrite(d, q1234, target, quantity, w1234, &|d, t| {
            within(d, p, t, c1234)
        });
        let moved = rat_eq_rewrite(d, c1234, final_bound, bound_chain, at_quantity, &|d, t| {
            within(d, p, target, t)
        });
        (final_bound, moved)
    };

    // Upper half: `∀ j, target ≤ 2/(n+1) + 6/(j+1)`, then the Archimedean lemma.
    let six_nat = d.num(6);
    let upper_hypothesis = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let (bound, proof) = estimate(d, j);
        let (_, upper) = halves(d, p, target, bound, proof);
        d.lam_fv(j_fv, nat, upper)
    };
    let upper = d.lemma(
        rat.le_of_le_add_nat_div_succ,
        &[target, goal_bound, six_nat, upper_hypothesis],
    );

    // Lower half: negate the estimate, run the same lemma, and negate back.
    let negated_target = rneg(d, target);
    let lower_hypothesis = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let (bound, proof) = estimate(d, j);
        let (low, high) = halves(d, p, target, bound, proof);
        let flipped = d.lemma(rat.bounds_neg, &[target, bound, low, high]);
        let negated_bound = rneg(d, bound);
        let inner_lower = rle(d, rat, negated_bound, negated_target);
        let inner_upper = rle(d, rat, negated_target, bound);
        let body = d.and_right(inner_lower, inner_upper, flipped);
        d.lam_fv(j_fv, nat, body)
    };
    let lower_raw = d.lemma(
        rat.le_of_le_add_nat_div_succ,
        &[negated_target, goal_bound, six_nat, lower_hypothesis],
    );
    let lower_negated = d.lemma(rat.neg_le_neg, &[negated_target, goal_bound, lower_raw]);
    let twice = rneg(d, negated_target);
    let cancel = d.lemma(rat.neg_neg, &[target]);
    let negated_goal = rneg(d, goal_bound);
    let lower = rat_eq_rewrite(d, twice, target, cancel, lower_negated, &|d, t| {
        rle(d, rat, negated_goal, t)
    });

    let lower_ty = rle(d, rat, negated_goal, target);
    let upper_ty = rle(d, rat, target, goal_bound);
    let pair = and_intro(d, p, lower_ty, upper_ty, lower, upper);
    let value = {
        let over_n = d.lam_fv(n_fv, nat, pair);
        let with_second = d.lam_fv(hyz_fv, second_ty, over_n);
        let with_first = d.lam_fv(hxy_fv, first_ty, with_second);
        let with_z = d.lam_fv(z_fv, carrier, with_first);
        let with_y = d.lam_fv(y_fv, carrier, with_z);
        d.lam_fv(x_fv, carrier, with_y)
    };
    let ty = {
        let conclusion = equiv(d, p, x, z);
        let after_second = d.arrow(second_ty, conclusion);
        let after_first = d.arrow(first_ty, after_second);
        let with_z = d.pi_fv(z_fv, carrier, after_first);
        let with_y = d.pi_fv(y_fv, carrier, with_z);
        d.pi_fv(x_fv, carrier, with_y)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.equiv_trans,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.ofRat q` — the constant sequence, and with it the proof that the
/// carrier is **inhabited**.
///
/// The regularity obligation is `Within (q − q) (1/(m+1) + 1/(n+1))`, and
/// `q − q` is `0` by `Rat.sub_self`, so it reduces to "`0` is inside a
/// nonnegative bound".
fn declare_of_rat(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = rat_ty(d);
    let nat = d.nat_ty();
    let rle = crate::rat_prelude::ops::rle;

    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let sequences = seq_ty(d);
    let constant = {
        let anon = d.anon_name();
        d.kernel().lam(anon, nat, q, BinderInfo::Default)
    };
    let regularity = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let difference = rsub(d, rat, q, q);
        let bound = modulus(d, p, m, n);
        let zero = rzero(d, rat);
        let negated = rneg(d, bound);
        let one_nat = d.num(1);
        let left_nonneg = d.lemma(rat.zero_le_nat_div_succ, &[one_nat, m]);
        let right_nonneg = d.lemma(rat.zero_le_nat_div_succ, &[one_nat, n]);
        let left_atom = div_succ(d, p, 1, m);
        let right_atom = div_succ(d, p, 1, n);
        let nonneg = d.lemma(
            rat.add_nonneg,
            &[left_atom, right_atom, left_nonneg, right_nonneg],
        );
        let nonpos = d.lemma(rat.neg_nonpos_of_nonneg, &[bound, nonneg]);
        let collapse = d.lemma(rat.sub_self, &[q]);
        let back = rsymm(d, difference, zero, collapse);
        let lower = rat_eq_rewrite(d, zero, difference, back, nonpos, &|d, t| {
            rle(d, rat, negated, t)
        });
        let upper = rat_eq_rewrite(d, zero, difference, back, nonneg, &|d, t| {
            rle(d, rat, t, bound)
        });
        let lower_ty = rle(d, rat, negated, difference);
        let upper_ty = rle(d, rat, difference, bound);
        let pair = and_intro(d, p, lower_ty, upper_ty, lower, upper);
        let over_n = d.lam_fv(n_fv, nat, pair);
        d.lam_fv(m_fv, nat, over_n)
    };
    let constructor = d.kernel().const_(p.mk, vec![]);
    let body = d.apply(constructor, &[constant, regularity]);
    let value = d.lam_fv(q_fv, carrier, body);
    let result = creal_ty(d, p);
    let ty = d.arrow(carrier, result);
    let _ = sequences;
    d.kernel().add_declaration(Declaration::Definition {
        name: p.of_rat,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 3),
    })
}

/// `Not (CReal.Equiv (ofRat 0) (ofRat 1))` — `Equiv` is not the total relation.
///
/// Read at index `3`, the hypothesis' lower half says `−1/2 ≤ 0 − 1`, i.e.
/// `−1/2 ≤ −1`. Every term in that is closed, so `Rat.le` unfolds through
/// `Int.le` to `Nat.le 1 0` by pure reduction and `Nat.not_succ_le_zero`
/// finishes it. Nothing in the proof is specific to the construction beyond
/// `CReal.seq (ofRat q) n` reducing to `q`, which is the point.
fn declare_discrimination(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat = rat.int.nat;

    let zero_rat = rzero(d, rat);
    let one_rat = d.kernel().const_(rat.one, vec![]);
    let left = d.const_app(p.of_rat, &[zero_rat]);
    let right = d.const_app(p.of_rat, &[one_rat]);
    let claim = equiv(d, p, left, right);
    let stmt = d.not(claim);

    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let index = d.num(3);
    let instance = d.apply(h, &[index]);
    let a = sample(d, p, left, index);
    let b = sample(d, p, right, index);
    let difference = rsub(d, rat, a, b);
    let bound = div_succ(d, p, 2, index);
    let (lower, _upper) = halves(d, p, difference, bound, instance);
    // `lower : Rat.le (-1/2) (-1)`, which reduces to `Nat.le 1 0`.
    let zero_nat = d.zero();
    let absurd = d.lemma(nat.not_succ_le_zero, &[zero_nat, lower]);
    let value = d.lam_fv(h_fv, claim, absurd);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.not_zero_one,
        uparams: vec![],
        ty: stmt,
        value,
    })
}

#[cfg(test)]
mod creal_tests;

// --- the additive structure -------------------------------------------------

/// `CReal.zero` and `CReal.one`, as constant sequences.
fn declare_constants(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let result = creal_ty(d, p);
    let constant = |d: &mut IntDev<'_>, name: NameId, source: NameId| -> Result<(), KernelError> {
        let value_rat = d.kernel().const_(source, vec![]);
        let value = d.const_app(p.of_rat, &[value_rat]);
        d.kernel().add_declaration(Declaration::Definition {
            name,
            uparams: vec![],
            ty: result,
            value,
            hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 4),
        })
    };
    constant(d, p.zero, rat.zero)?;
    constant(d, p.one, rat.one)
}

/// `Equiv.of_pointwise`: two reals whose representatives agree at every index
/// are `Equiv`-equal.
///
/// The converse is **false** — `CReal.Equiv` relates sequences that are merely
/// asymptotically close — which is exactly why the carrier is a setoid and not
/// a quotient. This direction is what makes the pointwise laws free.
fn declare_pointwise(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let rle = crate::rat_prelude::ops::rle;

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let hypothesis = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let left = sample(d, p, x, n);
        let right = sample(d, p, y, n);
        let claim = crate::rat_prelude::ops::req(d, left, right);
        d.pi_fv(n_fv, nat, claim)
    };
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let a = sample(d, p, x, n);
    let b = sample(d, p, y, n);
    let difference = rsub(d, rat, a, b);
    let bound = div_succ(d, p, 2, n);
    let zero = rzero(d, rat);
    let negated = rneg(d, bound);

    let pointwise = d.apply(h, &[n]);
    let degenerate = rsub(d, rat, b, b);
    let step = rcongr(d, a, b, pointwise, &|d, t| rsub(d, rat, t, b));
    let collapse = d.lemma(rat.sub_self, &[b]);
    let (_, to_zero) = rchain(d, difference, &[(degenerate, step), (zero, collapse)]);
    let back = rsymm(d, difference, zero, to_zero);
    let two = d.num(2);
    let nonneg = d.lemma(rat.zero_le_nat_div_succ, &[two, n]);
    let nonpos = d.lemma(rat.neg_nonpos_of_nonneg, &[bound, nonneg]);
    let lower = rat_eq_rewrite(d, zero, difference, back, nonpos, &|d, t| {
        rle(d, rat, negated, t)
    });
    let upper = rat_eq_rewrite(d, zero, difference, back, nonneg, &|d, t| {
        rle(d, rat, t, bound)
    });
    let lower_ty = rle(d, rat, negated, difference);
    let upper_ty = rle(d, rat, difference, bound);
    let pair = and_intro(d, p, lower_ty, upper_ty, lower, upper);
    let value = {
        let over_n = d.lam_fv(n_fv, nat, pair);
        let with_h = d.lam_fv(h_fv, hypothesis, over_n);
        let with_y = d.lam_fv(y_fv, carrier, with_h);
        d.lam_fv(x_fv, carrier, with_y)
    };
    let ty = {
        let conclusion = equiv(d, p, x, y);
        let inner = d.arrow(hypothesis, conclusion);
        let with_y = d.pi_fv(y_fv, carrier, inner);
        d.pi_fv(x_fv, carrier, with_y)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.equiv_of_pointwise,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.neg`, and its `Equiv`-congruence.
///
/// Negation is the one operation that needs **no index shift**: it does not
/// degrade the modulus, because `(−x_m) − (−x_n)` is `x_n − x_m` and the
/// regularity bound is symmetric in its two indices. `CReal.add` will not be so
/// lucky — Bishop's `(x+y)_n := x_{2n+1} + y_{2n+1}` exists precisely because
/// adding two regular sequences doubles the error.
fn declare_negation(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let sequences = seq_ty(d);
    let rle = crate::rat_prelude::ops::rle;

    // neg x := mk (fun n => Rat.neg (seq x n)) _
    {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let representative = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let point = sample(d, p, x, n);
            let body = rneg(d, point);
            d.lam_fv(n_fv, nat, body)
        };
        let regularity = {
            let m_fv = d.fresh_fvar();
            let m = d.kernel().fvar(m_fv);
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let xm = sample(d, p, x, m);
            let xn = sample(d, p, x, n);
            let negated_m = rneg(d, xm);
            let negated_n = rneg(d, xn);
            let goal_quantity = rsub(d, rat, negated_m, negated_n);
            let goal_bound = modulus(d, p, m, n);

            // `regular x n m` bounds `x_n − x_m` by `1/(n+1) + 1/(m+1)`.
            let source = d.lemma(p.regular, &[x, n, m]);
            let source_quantity = rsub(d, rat, xn, xm);
            let source_bound = modulus(d, p, n, m);
            let swap_quantity = {
                let forward = d.lemma(rat.sub_neg_sub, &[xm, xn]);
                rsymm(d, goal_quantity, source_quantity, forward)
            };
            let left_atom = div_succ(d, p, 1, n);
            let right_atom = div_succ(d, p, 1, m);
            let swap_bound = d.lemma(rat.add_comm, &[left_atom, right_atom]);
            let at_quantity = rat_eq_rewrite(
                d,
                source_quantity,
                goal_quantity,
                swap_quantity,
                source,
                &|d, t| within(d, p, t, source_bound),
            );
            let moved = rat_eq_rewrite(
                d,
                source_bound,
                goal_bound,
                swap_bound,
                at_quantity,
                &|d, t| within(d, p, goal_quantity, t),
            );
            let over_n = d.lam_fv(n_fv, nat, moved);
            d.lam_fv(m_fv, nat, over_n)
        };
        let constructor = d.kernel().const_(p.mk, vec![]);
        let body = d.apply(constructor, &[representative, regularity]);
        let value = d.lam_fv(x_fv, carrier, body);
        let ty = d.arrow(carrier, carrier);
        let _ = sequences;
        d.kernel().add_declaration(Declaration::Definition {
            name: p.neg,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 5),
        })?;
    }

    // neg_congr : Equiv x y → Equiv (neg x) (neg y).
    {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let hypothesis = equiv(d, p, x, y);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);

        let a = sample(d, p, x, n);
        let b = sample(d, p, y, n);
        let forward = rsub(d, rat, a, b);
        let bound = div_succ(d, p, 2, n);
        let instance = d.apply(h, &[n]);
        let (lower, upper) = halves(d, p, forward, bound, instance);
        let flipped = d.lemma(rat.bounds_neg, &[forward, bound, lower, upper]);
        let negated_forward = rneg(d, forward);
        let negated_a = rneg(d, a);
        let negated_b = rneg(d, b);
        let target = rsub(d, rat, negated_a, negated_b);
        // `−(a − b) = b − a = (−a) − (−b)`.
        let swapped = rsub(d, rat, b, a);
        let first = d.lemma(rat.neg_sub, &[a, b]);
        let second = {
            let forward_eq = d.lemma(rat.sub_neg_sub, &[a, b]);
            rsymm(d, target, swapped, forward_eq)
        };
        let (_, chained) = rchain(d, negated_forward, &[(swapped, first), (target, second)]);
        let body = rat_eq_rewrite(d, negated_forward, target, chained, flipped, &|d, t| {
            within(d, p, t, bound)
        });
        let _ = rle;
        let value = {
            let over_n = d.lam_fv(n_fv, nat, body);
            let with_h = d.lam_fv(h_fv, hypothesis, over_n);
            let with_y = d.lam_fv(y_fv, carrier, with_h);
            d.lam_fv(x_fv, carrier, with_y)
        };
        let ty = {
            let left = d.const_app(p.neg, &[x]);
            let right = d.const_app(p.neg, &[y]);
            let conclusion = equiv(d, p, left, right);
            let inner = d.arrow(hypothesis, conclusion);
            let with_y = d.pi_fv(y_fv, carrier, inner);
            d.pi_fv(x_fv, carrier, with_y)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.neg_congr,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// `2·n + 1`, Bishop's shifted sampling index.
fn shift(d: &mut IntDev<'_>, n: ExprId) -> ExprId {
    let two = d.num(2);
    let doubled = NatOps::mul(d, two, n);
    d.succ(doubled)
}

/// `CReal.add`, and its `Equiv`-congruence.
///
/// Regularity is the whole content. `f m − f n` splits into the two component
/// errors by `Rat.sub_add_add`, each is bounded by `regular`, and the four
/// resulting summands sort into `(A+A) + (B+B) = 2/(2m+2) + 2/(2n+2)`, which
/// `Rat.natDivSucc_halve` turns into exactly `1/(m+1) + 1/(n+1)`.
fn declare_addition(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    // add x y := mk (fun n => x_{2n+1} + y_{2n+1}) _
    {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let representative = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let index = shift(d, n);
            let left = sample(d, p, x, index);
            let right = sample(d, p, y, index);
            let body = radd(d, left, right);
            d.lam_fv(n_fv, nat, body)
        };
        let regularity = {
            let m_fv = d.fresh_fvar();
            let m = d.kernel().fvar(m_fv);
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let sm = shift(d, m);
            let sn = shift(d, n);
            let a = sample(d, p, x, sm);
            let b = sample(d, p, y, sm);
            let c = sample(d, p, x, sn);
            let e = sample(d, p, y, sn);

            let wx = d.lemma(p.regular, &[x, sm, sn]);
            let wy = d.lemma(p.regular, &[y, sm, sn]);
            let dx = rsub(d, rat, a, c);
            let dy = rsub(d, rat, b, e);
            let component = modulus(d, p, sm, sn);
            let (lx, rx) = halves(d, p, dx, component, wx);
            let (ly, ry) = halves(d, p, dy, component, wy);
            let combined = d.lemma(
                rat.bounds_add,
                &[dx, component, dy, component, lx, rx, ly, ry],
            );
            let summed_quantity = radd(d, dx, dy);
            let summed_bound = radd(d, component, component);

            // The quantity: (a+b) − (c+e) = (a−c) + (b−e).
            let left_sum = radd(d, a, b);
            let right_sum = radd(d, c, e);
            let goal_quantity = rsub(d, rat, left_sum, right_sum);
            let split = d.lemma(rat.sub_add_add, &[a, b, c, e]);
            let back = rsymm(d, goal_quantity, summed_quantity, split);
            let at_quantity = rat_eq_rewrite(
                d,
                summed_quantity,
                goal_quantity,
                back,
                combined,
                &|d, t| within(d, p, t, summed_bound),
            );

            // The bound: (A+B) + (A+B) = (A+A) + (B+B) = 2/(2m+2) + 2/(2n+2)
            //                          = 1/(m+1) + 1/(n+1).
            let a_atom = div_succ(d, p, 1, sm);
            let b_atom = div_succ(d, p, 1, sn);
            let flat_atoms = [a_atom, b_atom, a_atom, b_atom];
            let sorted_atoms = [a_atom, a_atom, b_atom, b_atom];
            let flatten = rsum_append(d, rat, &flat_atoms[..2], &flat_atoms[2..]);
            let flat = rsum(d, rat, &flat_atoms);
            let permute = rsum_perm(d, rat, &flat_atoms, &sorted_atoms);
            let sorted = rsum(d, rat, &sorted_atoms);
            let paired = {
                let forward = rsum_append(d, rat, &sorted_atoms[..2], &sorted_atoms[2..]);
                let doubled_a = radd(d, a_atom, a_atom);
                let doubled_b = radd(d, b_atom, b_atom);
                let target = radd(d, doubled_a, doubled_b);
                rsymm(d, target, sorted, forward)
            };
            let doubled_a = radd(d, a_atom, a_atom);
            let doubled_b = radd(d, b_atom, b_atom);
            let pair_target = radd(d, doubled_a, doubled_b);
            let one_nat = d.num(1);
            let two_a = div_succ(d, p, 2, sm);
            let two_b = div_succ(d, p, 2, sn);
            let fuse_a = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, sm]);
            let fuse_b = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, sn]);
            let after_a = rcongr(d, doubled_a, two_a, fuse_a, &|d, t| radd(d, t, doubled_b));
            let staged_a = radd(d, two_a, doubled_b);
            let after_b = rcongr(d, doubled_b, two_b, fuse_b, &|d, t| radd(d, two_a, t));
            let staged_b = radd(d, two_a, two_b);
            let halve_m = d.lemma(rat.nat_div_succ_halve, &[m]);
            let halve_n = d.lemma(rat.nat_div_succ_halve, &[n]);
            let one_m = div_succ(d, p, 1, m);
            let one_n = div_succ(d, p, 1, n);
            let after_halve_m = rcongr(d, two_a, one_m, halve_m, &|d, t| radd(d, t, two_b));
            let staged_halve = radd(d, one_m, two_b);
            let after_halve_n = rcongr(d, two_b, one_n, halve_n, &|d, t| radd(d, one_m, t));
            let goal_bound = modulus(d, p, m, n);
            let (_, bound_chain) = rchain(
                d,
                summed_bound,
                &[
                    (flat, flatten),
                    (sorted, permute),
                    (pair_target, paired),
                    (staged_a, after_a),
                    (staged_b, after_b),
                    (staged_halve, after_halve_m),
                    (goal_bound, after_halve_n),
                ],
            );
            let moved = rat_eq_rewrite(
                d,
                summed_bound,
                goal_bound,
                bound_chain,
                at_quantity,
                &|d, t| within(d, p, goal_quantity, t),
            );
            let over_n = d.lam_fv(n_fv, nat, moved);
            d.lam_fv(m_fv, nat, over_n)
        };
        let constructor = d.kernel().const_(p.mk, vec![]);
        let body = d.apply(constructor, &[representative, regularity]);
        let value = {
            let with_y = d.lam_fv(y_fv, carrier, body);
            d.lam_fv(x_fv, carrier, with_y)
        };
        let ty = {
            let inner = d.arrow(carrier, carrier);
            d.arrow(carrier, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.add,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 6),
        })?;
    }

    // add_congr : Equiv x x' → Equiv y y' → Equiv (add x y) (add x' y').
    //
    // The two component bounds are `2/(2n+2)` each, and `2/(2n+2) = 1/(n+1)`,
    // so their sum is `2/(n+1)` exactly — no slack, and no weakening lemma.
    {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let x2_fv = d.fresh_fvar();
        let x2 = d.kernel().fvar(x2_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let y2_fv = d.fresh_fvar();
        let y2 = d.kernel().fvar(y2_fv);
        let first_ty = equiv(d, p, x, x2);
        let second_ty = equiv(d, p, y, y2);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);

        let index = shift(d, n);
        let a = sample(d, p, x, index);
        let b = sample(d, p, y, index);
        let c = sample(d, p, x2, index);
        let e = sample(d, p, y2, index);
        let dx = rsub(d, rat, a, c);
        let dy = rsub(d, rat, b, e);
        let component = div_succ(d, p, 2, index);
        let wx = d.apply(h1, &[index]);
        let wy = d.apply(h2, &[index]);
        let (lx, rx) = halves(d, p, dx, component, wx);
        let (ly, ry) = halves(d, p, dy, component, wy);
        let combined = d.lemma(
            rat.bounds_add,
            &[dx, component, dy, component, lx, rx, ly, ry],
        );
        let summed_quantity = radd(d, dx, dy);
        let summed_bound = radd(d, component, component);

        let left_sum = radd(d, a, b);
        let right_sum = radd(d, c, e);
        let goal_quantity = rsub(d, rat, left_sum, right_sum);
        let split = d.lemma(rat.sub_add_add, &[a, b, c, e]);
        let back = rsymm(d, goal_quantity, summed_quantity, split);
        let at_quantity = rat_eq_rewrite(
            d,
            summed_quantity,
            goal_quantity,
            back,
            combined,
            &|d, t| within(d, p, t, summed_bound),
        );

        // `2/(2n+2) + 2/(2n+2) = 1/(n+1) + 1/(n+1) = 2/(n+1)`.
        let halved = div_succ(d, p, 1, n);
        let halve = d.lemma(rat.nat_div_succ_halve, &[n]);
        let after_left = rcongr(d, component, halved, halve, &|d, t| radd(d, t, component));
        let staged = radd(d, halved, component);
        let after_right = rcongr(d, component, halved, halve, &|d, t| radd(d, halved, t));
        let doubled = radd(d, halved, halved);
        let one_nat = d.num(1);
        let fuse = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, n]);
        let goal_bound = div_succ(d, p, 2, n);
        let (_, bound_chain) = rchain(
            d,
            summed_bound,
            &[
                (staged, after_left),
                (doubled, after_right),
                (goal_bound, fuse),
            ],
        );
        let body = rat_eq_rewrite(
            d,
            summed_bound,
            goal_bound,
            bound_chain,
            at_quantity,
            &|d, t| within(d, p, goal_quantity, t),
        );
        let value = {
            let over_n = d.lam_fv(n_fv, nat, body);
            let with2 = d.lam_fv(h2_fv, second_ty, over_n);
            let with1 = d.lam_fv(h1_fv, first_ty, with2);
            let with_y2 = d.lam_fv(y2_fv, carrier, with1);
            let with_y = d.lam_fv(y_fv, carrier, with_y2);
            let with_x2 = d.lam_fv(x2_fv, carrier, with_y);
            d.lam_fv(x_fv, carrier, with_x2)
        };
        let ty = {
            let left = d.const_app(p.add, &[x, y]);
            let right = d.const_app(p.add, &[x2, y2]);
            let conclusion = equiv(d, p, left, right);
            let after2 = d.arrow(second_ty, conclusion);
            let after1 = d.arrow(first_ty, after2);
            let with_y2 = d.pi_fv(y2_fv, carrier, after1);
            let with_y = d.pi_fv(y_fv, carrier, with_y2);
            let with_x2 = d.pi_fv(x2_fv, carrier, with_y);
            d.pi_fv(x_fv, carrier, with_x2)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.add_congr,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// The **additive group**, in `Equiv` form: four of the 22 ordered-ring laws.
///
/// Two of them are *pointwise* — `add_comm` and `add_neg` sample both sides at
/// the same shifted index, so [`Equiv.of_pointwise`](CRealPrelude::equiv_of_pointwise)
/// reduces each to one `Rat` law and there is no analysis at all.
///
/// The other two are not, and they are where the setoid starts to earn its
/// keep. `add x zero` samples `x` at `2n+1` where `x` itself samples at `n`,
/// and `(x+y)+z` samples `x` at `2(2n+1)+1` where `x+(y+z)` samples it at
/// `2n+1` — so the two sides are equal at *no* index, and only `Equiv` can
/// relate them. Both reduce to regularity plus one inequality,
/// [`shifted_bound_le`], and in `add_assoc` the middle summand `y` is sampled
/// at the same index on both sides and cancels, leaving exactly two regularity
/// bounds. Neither needs `natDivSucc` to be monotone in its index.
fn declare_additive_laws(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    // add_comm : Equiv (add x y) (add y x).
    {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let left = d.const_app(p.add, &[x, y]);
        let right = d.const_app(p.add, &[y, x]);
        let pointwise = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let index = shift(d, n);
            let a = sample(d, p, x, index);
            let b = sample(d, p, y, index);
            let body = d.lemma(rat.add_comm, &[a, b]);
            d.lam_fv(n_fv, nat, body)
        };
        let body = d.lemma(p.equiv_of_pointwise, &[left, right, pointwise]);
        let value = {
            let with_y = d.lam_fv(y_fv, carrier, body);
            d.lam_fv(x_fv, carrier, with_y)
        };
        let ty = {
            let conclusion = equiv(d, p, left, right);
            let with_y = d.pi_fv(y_fv, carrier, conclusion);
            d.pi_fv(x_fv, carrier, with_y)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.add_comm,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // add_neg : Equiv (add x (neg x)) zero.
    {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let negated = d.const_app(p.neg, &[x]);
        let left = d.const_app(p.add, &[x, negated]);
        let right = d.kernel().const_(p.zero, vec![]);
        let pointwise = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let index = shift(d, n);
            let a = sample(d, p, x, index);
            let body = d.lemma(rat.add_neg, &[a]);
            d.lam_fv(n_fv, nat, body)
        };
        let body = d.lemma(p.equiv_of_pointwise, &[left, right, pointwise]);
        let value = d.lam_fv(x_fv, carrier, body);
        let ty = {
            let conclusion = equiv(d, p, left, right);
            d.pi_fv(x_fv, carrier, conclusion)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.add_neg,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // add_zero : Equiv (add x zero) x.
    //
    // The first law that is NOT pointwise. `(x + 0)_n` is `x_{2n+1} + 0`, and
    // `x_n` is `x_n`: the two sides disagree at every index, and regularity is
    // what says the disagreement is small. It bounds the gap by
    // `1/(2n+2) + 1/(n+1)` where the setoid asks for `2/(n+1)`, and
    // `shifted_bound_le` is the whole difference.
    {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let zero_real = d.kernel().const_(p.zero, vec![]);
        let left = d.const_app(p.add, &[x, zero_real]);
        let body = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let index = shift(d, n);
            let deep = sample(d, p, x, index);
            let shallow = sample(d, p, x, n);
            let difference = rsub(d, rat, deep, shallow);
            let bound = modulus(d, p, index, n);
            let goal_bound = div_succ(d, p, 2, n);
            let source = d.lemma(p.regular, &[x, index, n]);
            let order = shifted_bound_le(d, p, n);
            let widened = weaken(d, p, difference, bound, goal_bound, source, order);

            // `x_{2n+1}` is what the left side samples; `x_{2n+1} + 0` is what
            // it *writes*, because `CReal.zero` contributes a `Rat.zero`.
            let zero_rat = rzero(d, rat);
            let padded = radd(d, deep, zero_rat);
            let collapse = d.lemma(rat.add_zero, &[deep]);
            let restore = rsymm(d, padded, deep, collapse);
            let at_index = rat_eq_rewrite(d, deep, padded, restore, widened, &|d, t| {
                let quantity = rsub(d, rat, t, shallow);
                within(d, p, quantity, goal_bound)
            });
            d.lam_fv(n_fv, nat, at_index)
        };
        let value = d.lam_fv(x_fv, carrier, body);
        let ty = {
            let conclusion = equiv(d, p, left, x);
            d.pi_fv(x_fv, carrier, conclusion)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.add_zero,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // add_assoc : Equiv (add (add x y) z) (add x (add y z)).
    //
    // Write `N = 2n+1` and `M = 2N+1`. The left side samples
    // `(x_M + y_M) + z_N`, the right `x_N + (y_M + z_M)`: `y` is sampled at the
    // SAME index on both sides and cancels, and the whole difference is
    // `(x_M − x_N) + (z_N − z_M)` — two regularity bounds. Their sum is
    // `2/(M+1) + 2/(N+1)`, which halves twice into `1/(N+1) + 1/(n+1)`, the
    // same quantity `add_zero` weakens.
    {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let inner_left = d.const_app(p.add, &[x, y]);
        let left = d.const_app(p.add, &[inner_left, z]);
        let inner_right = d.const_app(p.add, &[y, z]);
        let right = d.const_app(p.add, &[x, inner_right]);
        let body = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let shallow_index = shift(d, n);
            let deep_index = shift(d, shallow_index);
            let xm = sample(d, p, x, deep_index);
            let ym = sample(d, p, y, deep_index);
            let zn = sample(d, p, z, shallow_index);
            let xn = sample(d, p, x, shallow_index);
            let zm = sample(d, p, z, deep_index);

            // The two regularity bounds, added.
            let dx = rsub(d, rat, xm, xn);
            let dz = rsub(d, rat, zn, zm);
            let bx = modulus(d, p, deep_index, shallow_index);
            let bz = modulus(d, p, shallow_index, deep_index);
            let wx = d.lemma(p.regular, &[x, deep_index, shallow_index]);
            let wz = d.lemma(p.regular, &[z, shallow_index, deep_index]);
            let (lx, rx) = halves(d, p, dx, bx, wx);
            let (lz, rz) = halves(d, p, dz, bz, wz);
            let combined = d.lemma(rat.bounds_add, &[dx, bx, dz, bz, lx, rx, lz, rz]);
            let summed_quantity = radd(d, dx, dz);
            let summed_bound = radd(d, bx, bz);

            // The bound: `(A+B) + (B+A) = (A+A) + (B+B) = 2/(M+1) + 2/(N+1)`,
            // and each doubling halves back one level — `2/(M+1) = 1/(N+1)`
            // and `2/(N+1) = 1/(n+1)`.
            let a_deep = div_succ(d, p, 1, deep_index);
            let a_shallow = div_succ(d, p, 1, shallow_index);
            let flat_atoms = [a_deep, a_shallow, a_shallow, a_deep];
            let sorted_atoms = [a_deep, a_deep, a_shallow, a_shallow];
            let flatten = rsum_append(d, rat, &flat_atoms[..2], &flat_atoms[2..]);
            let flat = rsum(d, rat, &flat_atoms);
            let permute = rsum_perm(d, rat, &flat_atoms, &sorted_atoms);
            let sorted = rsum(d, rat, &sorted_atoms);
            let doubled_deep = radd(d, a_deep, a_deep);
            let doubled_shallow = radd(d, a_shallow, a_shallow);
            let pair_target = radd(d, doubled_deep, doubled_shallow);
            let paired = {
                let forward = rsum_append(d, rat, &sorted_atoms[..2], &sorted_atoms[2..]);
                rsymm(d, pair_target, sorted, forward)
            };
            let one_nat = d.num(1);
            let two_deep = div_succ(d, p, 2, deep_index);
            let two_shallow = div_succ(d, p, 2, shallow_index);
            let a_flat = div_succ(d, p, 1, n);
            let fuse_deep = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, deep_index]);
            let after_deep = rcongr(d, doubled_deep, two_deep, fuse_deep, &|d, t| {
                radd(d, t, doubled_shallow)
            });
            let staged_deep = radd(d, two_deep, doubled_shallow);
            let halve_deep = d.lemma(rat.nat_div_succ_halve, &[shallow_index]);
            let after_halve_deep = rcongr(d, two_deep, a_shallow, halve_deep, &|d, t| {
                radd(d, t, doubled_shallow)
            });
            let staged_halved = radd(d, a_shallow, doubled_shallow);
            let fuse_shallow = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, shallow_index]);
            let after_shallow = rcongr(d, doubled_shallow, two_shallow, fuse_shallow, &|d, t| {
                radd(d, a_shallow, t)
            });
            let staged_shallow = radd(d, a_shallow, two_shallow);
            let halve_shallow = d.lemma(rat.nat_div_succ_halve, &[n]);
            let after_halve_shallow = rcongr(d, two_shallow, a_flat, halve_shallow, &|d, t| {
                radd(d, a_shallow, t)
            });
            let regularity_bound = modulus(d, p, shallow_index, n);
            let (_, bound_chain) = rchain(
                d,
                summed_bound,
                &[
                    (flat, flatten),
                    (sorted, permute),
                    (pair_target, paired),
                    (staged_deep, after_deep),
                    (staged_halved, after_halve_deep),
                    (staged_shallow, after_shallow),
                    (regularity_bound, after_halve_shallow),
                ],
            );
            let at_regularity = rat_eq_rewrite(
                d,
                summed_bound,
                regularity_bound,
                bound_chain,
                combined,
                &|d, t| within(d, p, summed_quantity, t),
            );
            let goal_bound = div_succ(d, p, 2, n);
            let order = shifted_bound_le(d, p, n);
            let widened = weaken(
                d,
                p,
                summed_quantity,
                regularity_bound,
                goal_bound,
                at_regularity,
                order,
            );

            // The quantity, in the `add`/`neg` form `Rat.sub` unfolds to:
            // `((x_M + y_M) + z_N) − (x_N + (y_M + z_M))` is six summands, of
            // which `y_M` and `−y_M` cancel.
            let neg_xn = rneg(d, xn);
            let neg_ym = rneg(d, ym);
            let neg_zm = rneg(d, zm);
            let lhs_sum = {
                let inner = radd(d, xm, ym);
                radd(d, inner, zn)
            };
            let rhs_inner = radd(d, ym, zm);
            let rhs_sum = radd(d, xn, rhs_inner);
            let neg_rhs = rneg(d, rhs_sum);
            let quantity = radd(d, lhs_sum, neg_rhs);
            let target = {
                let first = radd(d, xm, neg_xn);
                let second = radd(d, zn, neg_zm);
                radd(d, first, second)
            };

            let opened_left = rsum(d, rat, &[xm, ym, zn]);
            let assoc = d.lemma(rat.add_assoc, &[xm, ym, zn]);
            let step_assoc = rcongr(d, lhs_sum, opened_left, assoc, &|d, t| radd(d, t, neg_rhs));
            let staged_assoc = radd(d, opened_left, neg_rhs);
            let neg_inner = rneg(d, rhs_inner);
            let spread = d.lemma(rat.neg_add, &[xn, rhs_inner]);
            let spread_target = radd(d, neg_xn, neg_inner);
            let step_spread = rcongr(d, neg_rhs, spread_target, spread, &|d, t| {
                radd(d, opened_left, t)
            });
            let staged_spread = radd(d, opened_left, spread_target);
            let spread_inner = d.lemma(rat.neg_add, &[ym, zm]);
            let neg_pair = radd(d, neg_ym, neg_zm);
            let step_inner = rcongr(d, neg_inner, neg_pair, spread_inner, &|d, t| {
                let inner = radd(d, neg_xn, t);
                radd(d, opened_left, inner)
            });
            let opened_right = rsum(d, rat, &[neg_xn, neg_ym, neg_zm]);
            let staged_inner = radd(d, opened_left, opened_right);
            let six_atoms = [xm, ym, zn, neg_xn, neg_ym, neg_zm];
            let joined = rsum_append(d, rat, &six_atoms[..3], &six_atoms[3..]);
            let six = rsum(d, rat, &six_atoms);
            let sorted_six = [xm, neg_xn, zn, neg_zm, ym, neg_ym];
            let permute_six = rsum_perm(d, rat, &six_atoms, &sorted_six);
            let arranged = rsum(d, rat, &sorted_six);
            let zero_rat = rzero(d, rat);
            let pair_ym = radd(d, ym, neg_ym);
            let cancel = d.lemma(rat.add_neg, &[ym]);
            let step_cancel = rcongr(d, pair_ym, zero_rat, cancel, &|d, t| {
                let level1 = radd(d, neg_zm, t);
                let level2 = radd(d, zn, level1);
                let level3 = radd(d, neg_xn, level2);
                radd(d, xm, level3)
            });
            let cancelled = {
                let level1 = radd(d, neg_zm, zero_rat);
                let level2 = radd(d, zn, level1);
                let level3 = radd(d, neg_xn, level2);
                radd(d, xm, level3)
            };
            let padded_tail = radd(d, neg_zm, zero_rat);
            let trim = d.lemma(rat.add_zero, &[neg_zm]);
            let step_trim = rcongr(d, padded_tail, neg_zm, trim, &|d, t| {
                let level2 = radd(d, zn, t);
                let level3 = radd(d, neg_xn, level2);
                radd(d, xm, level3)
            });
            let four_atoms = [xm, neg_xn, zn, neg_zm];
            let four = rsum(d, rat, &four_atoms);
            let fold = {
                let forward = rsum_append(d, rat, &four_atoms[..2], &four_atoms[2..]);
                rsymm(d, target, four, forward)
            };
            let (_, quantity_chain) = rchain(
                d,
                quantity,
                &[
                    (staged_assoc, step_assoc),
                    (staged_spread, step_spread),
                    (staged_inner, step_inner),
                    (six, joined),
                    (arranged, permute_six),
                    (cancelled, step_cancel),
                    (four, step_trim),
                    (target, fold),
                ],
            );
            let restore = rsymm(d, quantity, target, quantity_chain);
            let at_quantity = rat_eq_rewrite(d, target, quantity, restore, widened, &|d, t| {
                within(d, p, t, goal_bound)
            });
            d.lam_fv(n_fv, nat, at_quantity)
        };
        let value = {
            let with_z = d.lam_fv(z_fv, carrier, body);
            let with_y = d.lam_fv(y_fv, carrier, with_z);
            d.lam_fv(x_fv, carrier, with_y)
        };
        let ty = {
            let conclusion = equiv(d, p, left, right);
            let with_z = d.pi_fv(z_fv, carrier, conclusion);
            let with_y = d.pi_fv(y_fv, carrier, with_z);
            d.pi_fv(x_fv, carrier, with_y)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.add_assoc,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// `CReal.le`, Bishop's order, and the three of the 22 order laws that do not
/// mention multiplication.
///
/// **These three restate verbatim**, which the additive laws did not: none of
/// `le_refl`, `le_trans`, `add_le_add` mentions `Eq`, so there is no equality
/// to replace by `Equiv` and the `Real` package's statement is the statement
/// proved here. That is ADR-0468's Measurement 2, cashed.
///
/// The order is *not* decidable and `le_total` is deliberately absent: it holds
/// for `ℚ`, and `∀ x y, le x y ∨ le y x` over the reals is not constructively
/// provable. Nothing here needs it — the one place a classical development
/// would say "suppose not" is `le_trans`, and that is a case split on nothing:
/// the estimate holds for every index `j`, and the Archimedean property of `ℚ`
/// turns "for every `j`" into the bound.
fn declare_order(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let rle = crate::rat_prelude::ops::rle;

    // le x y := ∀ n, Rat.le (seq x n − seq y n) (2/(n+1)).
    {
        let prop = d.kernel().sort_zero();
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let left = sample(d, p, x, n);
        let right = sample(d, p, y, n);
        let difference = rsub(d, rat, left, right);
        let bound = div_succ(d, p, 2, n);
        let claim = rle(d, rat, difference, bound);
        let body = d.pi_fv(n_fv, nat, claim);
        let value = {
            let with_y = d.lam_fv(y_fv, carrier, body);
            d.lam_fv(x_fv, carrier, with_y)
        };
        let ty = {
            let inner = d.arrow(carrier, prop);
            d.arrow(carrier, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.le,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 7),
        })?;
    }

    // le_refl : le x x. `x_n − x_n = 0`, and `0 ≤ 2/(n+1)`.
    {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let body = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let point = sample(d, p, x, n);
            let difference = rsub(d, rat, point, point);
            let bound = div_succ(d, p, 2, n);
            let zero = rzero(d, rat);
            let collapse = d.lemma(rat.sub_self, &[point]);
            let restore = rsymm(d, difference, zero, collapse);
            let two = d.num(2);
            let nonneg = d.lemma(rat.zero_le_nat_div_succ, &[two, n]);
            let at_index = rat_eq_rewrite(d, zero, difference, restore, nonneg, &|d, t| {
                rle(d, rat, t, bound)
            });
            d.lam_fv(n_fv, nat, at_index)
        };
        let value = d.lam_fv(x_fv, carrier, body);
        let ty = {
            let conclusion = d.const_app(p.le, &[x, x]);
            d.pi_fv(x_fv, carrier, conclusion)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.le_refl,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // le_trans : le x y → le y z → le x z.
    //
    // Chaining the two hypotheses at `n` gives `x_n − z_n ≤ 4/(n+1)`, which is
    // not what the order asks for and no rearrangement fixes. Bishop compares
    // at an arbitrary third index `j` instead, where the two hypotheses cost
    // `2/(j+1)` each and regularity pays the two round trips, and the
    // Archimedean property of `ℚ` discharges the resulting `6/(j+1)`. This is
    // `Equiv.trans` with the lower half deleted.
    {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let first_ty = d.const_app(p.le, &[x, y]);
        let second_ty = d.const_app(p.le, &[y, z]);
        let hxy_fv = d.fresh_fvar();
        let hxy = d.kernel().fvar(hxy_fv);
        let hyz_fv = d.fresh_fvar();
        let hyz = d.kernel().fvar(hyz_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);

        let head = sample(d, p, x, n);
        let tail = sample(d, p, z, n);
        let target = rsub(d, rat, head, tail);
        let goal_bound = div_succ(d, p, 2, n);

        let hypothesis = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let xj = sample(d, p, x, j);
            let yj = sample(d, p, y, j);
            let zj = sample(d, p, z, j);
            let u1 = rsub(d, rat, head, xj);
            let u2 = rsub(d, rat, xj, yj);
            let u3 = rsub(d, rat, yj, zj);
            let u4 = rsub(d, rat, zj, tail);
            let b1 = modulus(d, p, n, j);
            let b2 = div_succ(d, p, 2, j);
            let b3 = div_succ(d, p, 2, j);
            let b4 = modulus(d, p, j, n);

            // Only the UPPER half of each regularity bound is read; the two
            // hypotheses are one-sided already.
            let w1 = d.lemma(p.regular, &[x, n, j]);
            let w4 = d.lemma(p.regular, &[z, j, n]);
            let (_, r1) = halves(d, p, u1, b1, w1);
            let r2 = d.apply(hxy, &[j]);
            let r3 = d.apply(hyz, &[j]);
            let (_, r4) = halves(d, p, u4, b4, w4);

            // Right-nested, so the quantities telescope in the same order.
            let s34 = d.lemma(rat.add_le_add, &[u3, b3, u4, b4, r3, r4]);
            let q34 = radd(d, u3, u4);
            let c34 = radd(d, b3, b4);
            let s234 = d.lemma(rat.add_le_add, &[u2, b2, q34, c34, r2, s34]);
            let q234 = radd(d, u2, q34);
            let c234 = radd(d, b2, c34);
            let s1234 = d.lemma(rat.add_le_add, &[u1, b1, q234, c234, r1, s234]);
            let q1234 = radd(d, u1, q234);
            let c1234 = radd(d, b1, c234);

            let (_, _, quantity) = telescope_four(d, p, head, xj, yj, zj, tail);
            let (_, final_bound, bound_chain) = six_term_bound(d, p, n, j);
            let at_quantity = rat_eq_rewrite(d, q1234, target, quantity, s1234, &|d, t| {
                rle(d, rat, t, c1234)
            });
            let moved = rat_eq_rewrite(d, c1234, final_bound, bound_chain, at_quantity, &|d, t| {
                rle(d, rat, target, t)
            });
            d.lam_fv(j_fv, nat, moved)
        };
        let six_nat = d.num(6);
        let at_index = d.lemma(
            rat.le_of_le_add_nat_div_succ,
            &[target, goal_bound, six_nat, hypothesis],
        );
        let value = {
            let over_n = d.lam_fv(n_fv, nat, at_index);
            let with_second = d.lam_fv(hyz_fv, second_ty, over_n);
            let with_first = d.lam_fv(hxy_fv, first_ty, with_second);
            let with_z = d.lam_fv(z_fv, carrier, with_first);
            let with_y = d.lam_fv(y_fv, carrier, with_z);
            d.lam_fv(x_fv, carrier, with_y)
        };
        let ty = {
            let conclusion = d.const_app(p.le, &[x, z]);
            let after_second = d.arrow(second_ty, conclusion);
            let after_first = d.arrow(first_ty, after_second);
            let with_z = d.pi_fv(z_fv, carrier, after_first);
            let with_y = d.pi_fv(y_fv, carrier, with_z);
            d.pi_fv(x_fv, carrier, with_y)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.le_trans,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // add_le_add : le x x' → le y y' → le (add x y) (add x' y').
    //
    // Exact, like `add_congr`: both hypotheses are read at the shifted index
    // `2n+1` where each costs `2/(2n+2)`, and `2/(2n+2) = 1/(n+1)`, so the two
    // together are `2/(n+1)` with no slack and no weakening.
    {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let x2_fv = d.fresh_fvar();
        let x2 = d.kernel().fvar(x2_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let y2_fv = d.fresh_fvar();
        let y2 = d.kernel().fvar(y2_fv);
        let first_ty = d.const_app(p.le, &[x, x2]);
        let second_ty = d.const_app(p.le, &[y, y2]);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);

        let index = shift(d, n);
        let a = sample(d, p, x, index);
        let b = sample(d, p, y, index);
        let c = sample(d, p, x2, index);
        let e = sample(d, p, y2, index);
        let dx = rsub(d, rat, a, c);
        let dy = rsub(d, rat, b, e);
        let component = div_succ(d, p, 2, index);
        let wx = d.apply(h1, &[index]);
        let wy = d.apply(h2, &[index]);
        let combined = d.lemma(rat.add_le_add, &[dx, component, dy, component, wx, wy]);
        let summed_quantity = radd(d, dx, dy);
        let summed_bound = radd(d, component, component);

        let left_sum = radd(d, a, b);
        let right_sum = radd(d, c, e);
        let goal_quantity = rsub(d, rat, left_sum, right_sum);
        let split = d.lemma(rat.sub_add_add, &[a, b, c, e]);
        let restore = rsymm(d, goal_quantity, summed_quantity, split);
        let at_quantity = rat_eq_rewrite(
            d,
            summed_quantity,
            goal_quantity,
            restore,
            combined,
            &|d, t| rle(d, rat, t, summed_bound),
        );

        // `2/(2n+2) + 2/(2n+2) = 1/(n+1) + 1/(n+1) = 2/(n+1)`.
        let halved = div_succ(d, p, 1, n);
        let halve = d.lemma(rat.nat_div_succ_halve, &[n]);
        let after_left = rcongr(d, component, halved, halve, &|d, t| radd(d, t, component));
        let staged = radd(d, halved, component);
        let after_right = rcongr(d, component, halved, halve, &|d, t| radd(d, halved, t));
        let doubled = radd(d, halved, halved);
        let one_nat = d.num(1);
        let fuse = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, n]);
        let goal_bound = div_succ(d, p, 2, n);
        let (_, bound_chain) = rchain(
            d,
            summed_bound,
            &[
                (staged, after_left),
                (doubled, after_right),
                (goal_bound, fuse),
            ],
        );
        let at_index = rat_eq_rewrite(
            d,
            summed_bound,
            goal_bound,
            bound_chain,
            at_quantity,
            &|d, t| rle(d, rat, goal_quantity, t),
        );
        let value = {
            let over_n = d.lam_fv(n_fv, nat, at_index);
            let with2 = d.lam_fv(h2_fv, second_ty, over_n);
            let with1 = d.lam_fv(h1_fv, first_ty, with2);
            let with_y2 = d.lam_fv(y2_fv, carrier, with1);
            let with_y = d.lam_fv(y_fv, carrier, with_y2);
            let with_x2 = d.lam_fv(x2_fv, carrier, with_y);
            d.lam_fv(x_fv, carrier, with_x2)
        };
        let ty = {
            let left = d.const_app(p.add, &[x, y]);
            let right = d.const_app(p.add, &[x2, y2]);
            let conclusion = d.const_app(p.le, &[left, right]);
            let after2 = d.arrow(second_ty, conclusion);
            let after1 = d.arrow(first_ty, after2);
            let with_y2 = d.pi_fv(y2_fv, carrier, after1);
            let with_y = d.pi_fv(y_fv, carrier, with_y2);
            let with_x2 = d.pi_fv(x2_fv, carrier, with_y);
            d.pi_fv(x_fv, carrier, with_x2)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.add_le_add,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // le_of_equiv : Equiv x y → le x y, and equiv_of_le_le : the converse from
    // both directions.
    //
    // Together these say `le` is the order OF this setoid: `Equiv` is the
    // two-sided bound, `le` its upper half, and having both halves is having
    // `Equiv` back. Without them "three order laws hold" is a statement about
    // an unexamined relation — a `le` weakened to `≤ 100/(n+1)` satisfies all
    // three and closes neither of these.
    {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let a = sample(d, p, x, n);
        let b = sample(d, p, y, n);
        let forward = rsub(d, rat, a, b);
        let backward = rsub(d, rat, b, a);
        let bound = div_succ(d, p, 2, n);
        let negated = rneg(d, bound);

        // le_of_equiv: the upper half of the two-sided bound, projected.
        {
            let hypothesis = equiv(d, p, x, y);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let instance = d.apply(h, &[n]);
            let (_, upper) = halves(d, p, forward, bound, instance);
            let value = {
                let over_n = d.lam_fv(n_fv, nat, upper);
                let with_h = d.lam_fv(h_fv, hypothesis, over_n);
                let with_y = d.lam_fv(y_fv, carrier, with_h);
                d.lam_fv(x_fv, carrier, with_y)
            };
            let ty = {
                let conclusion = d.const_app(p.le, &[x, y]);
                let inner = d.arrow(hypothesis, conclusion);
                let with_y = d.pi_fv(y_fv, carrier, inner);
                d.pi_fv(x_fv, carrier, with_y)
            };
            d.kernel().add_declaration(Declaration::Theorem {
                name: p.le_of_equiv,
                uparams: vec![],
                ty,
                value,
            })?;
        }

        // equiv_of_le_le: the second hypothesis, negated, IS the lower half —
        // `−(y_n − x_n) = x_n − y_n` by `Rat.neg_sub`.
        {
            let first_ty = d.const_app(p.le, &[x, y]);
            let second_ty = d.const_app(p.le, &[y, x]);
            let h1_fv = d.fresh_fvar();
            let h1 = d.kernel().fvar(h1_fv);
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);
            let upper = d.apply(h1, &[n]);
            let reverse = d.apply(h2, &[n]);
            let flipped = d.lemma(rat.neg_le_neg, &[backward, bound, reverse]);
            let negated_backward = rneg(d, backward);
            let rewrite = d.lemma(rat.neg_sub, &[b, a]);
            let lower = rat_eq_rewrite(d, negated_backward, forward, rewrite, flipped, &|d, t| {
                rle(d, rat, negated, t)
            });
            let lower_ty = rle(d, rat, negated, forward);
            let upper_ty = rle(d, rat, forward, bound);
            let pair = and_intro(d, p, lower_ty, upper_ty, lower, upper);
            let value = {
                let over_n = d.lam_fv(n_fv, nat, pair);
                let with2 = d.lam_fv(h2_fv, second_ty, over_n);
                let with1 = d.lam_fv(h1_fv, first_ty, with2);
                let with_y = d.lam_fv(y_fv, carrier, with1);
                d.lam_fv(x_fv, carrier, with_y)
            };
            let ty = {
                let conclusion = equiv(d, p, x, y);
                let after2 = d.arrow(second_ty, conclusion);
                let after1 = d.arrow(first_ty, after2);
                let with_y = d.pi_fv(y_fv, carrier, after1);
                d.pi_fv(x_fv, carrier, with_y)
            };
            d.kernel().add_declaration(Declaration::Theorem {
                name: p.equiv_of_le_le,
                uparams: vec![],
                ty,
                value,
            })?;
        }
    }

    // not_le_one_zero : Not (le one zero) — the order discriminates.
    //
    // At index `3` the hypothesis says `1 − 0 ≤ 2/4`, i.e. `1 ≤ 1/2`. Every
    // term in that is closed, so `Rat.le` unfolds through `Int.le` to
    // `Nat.le 2 1` by pure reduction, and two Nat lemmas finish it.
    {
        let nat_p = rat.int.nat;
        let one_real = d.kernel().const_(p.one, vec![]);
        let zero_real = d.kernel().const_(p.zero, vec![]);
        let claim = d.const_app(p.le, &[one_real, zero_real]);
        let stmt = d.not(claim);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let index = d.num(3);
        let instance = d.apply(h, &[index]);
        let one_nat = d.num(1);
        let zero_nat = d.zero();
        let stripped = d.lemma(nat_p.le_of_succ_le_succ, &[one_nat, zero_nat, instance]);
        let absurd = d.lemma(nat_p.not_succ_le_zero, &[zero_nat, stripped]);
        let value = d.lam_fv(h_fv, claim, absurd);
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.not_le_one_zero,
            uparams: vec![],
            ty: stmt,
            value,
        })?;
    }
    Ok(())
}
