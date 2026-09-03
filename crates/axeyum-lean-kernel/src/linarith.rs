//! `linarith` — a decision procedure for quantifier-free linear arithmetic
//! that **emits kernel proof terms**.
//!
//! Every proof in this kernel is a hand-built term. This module is the first
//! *producer* in the sense of
//! [ADR-0601](../../../docs/research/09-decisions/adr-0601-three-producers-one-trust-anchor.md):
//! untrusted search, trusted small checking. It searches for a **Farkas
//! certificate** — a list of `(hypothesis, nonnegative coefficient)` pairs
//! whose sum derives the goal — and then *emits a kernel term* built entirely
//! from lemmas that already exist in the prelude. Nothing here is trusted: the
//! emitted term goes through
//! [`Kernel::add_declaration`](crate::Kernel::add_declaration) (or
//! [`Kernel::infer`](crate::Kernel::infer)) exactly like a hand-written proof,
//! and the module's own tests assert that a **corrupted** certificate is
//! rejected *by the kernel*, not by the procedure.
//!
//! ## The fragment
//!
//! Goals and hypotheses of the form `t₁ ≤ t₂`, `t₁ < t₂`, `t₁ = t₂` and
//! `¬(t₁ ≤ t₂)`, where each `t` is built from variables, numerals, `+`, `succ`
//! and multiplication by a numeral constant. This is quantifier-free
//! Presburger — what `omega` decides — minus the divisibility predicates.
//! A product of two non-constant terms is **not** in the fragment; the parser
//! treats it as an opaque atom, which is sound (an atom is just an unknown
//! natural) but means nothing is learned from its internal structure.
//!
//! ## Why the search is a bounded Farkas enumeration and not Fourier–Motzkin
//!
//! Fourier–Motzkin computes a *projection*; what the emitter needs is *cone
//! membership* — a specific nonnegative combination of the hypotheses that
//! reaches the goal, with the leftover slack made explicit. Recovering the
//! multipliers from an FM refutation requires dividing through by the negated
//! goal's own multiplier, which is rational and can reintroduce exactly the
//! large numerals the emitter must avoid: **every numeral in this kernel is
//! unary**, so a certificate with coefficient 40 is a term that forms `40` as
//! `succ⁴⁰ zero`. So the search enumerates small nonnegative multiplier
//! vectors directly, in order of increasing total weight, and declines rather
//! than growing a coefficient past [`MAX_MULTIPLIER`].
//!
//! That makes the procedure **incomplete by construction**, and the bound is
//! the honest statement of how incomplete: a goal needing a multiplier above
//! [`MAX_MULTIPLIER`], or more than [`MAX_HYPOTHESES`] hypotheses, gets
//! [`Decline::SearchBudget`] and not a wrong answer.

// Proof-term construction is dense in one-letter mathematical names (`a`, `b`,
// `c` for the three sides of a transitivity step, `d` for the development).
// Renaming them to `left`/`middle`/`right` makes the correspondence with the
// lemma statements harder to check, which is the only thing keeping these
// terms honest before the kernel sees them.
// `type_complexity`: the declaration helpers take
// `&dyn Fn(&mut D, &[ExprId]) -> (Vec<ExprId>, ExprId)` builders, the same
// shape `NatOps`'s own helpers use; a type alias mentioning the generic `D`
// would hide the signature rather than clarify it.
#![allow(
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::type_complexity
)]

use std::collections::BTreeMap;

pub mod nat;

#[cfg(test)]
mod tests;

/// Certificate and linear-form coefficients. Signed even over ℕ: a *goal*
/// `t₁ ≤ t₂` becomes the form `t₂ − t₁ ≥ 0`, whose intermediate coefficients
/// are freely negative even though every atom denotes a natural.
pub type Coeff = i64;

/// The largest multiplier the certificate search will consider.
///
/// Deliberately small: see the module docs. Every numeral here is unary.
pub const MAX_MULTIPLIER: Coeff = 4;

/// The most hypotheses the search will enumerate over.
///
/// The enumeration is `(MAX_MULTIPLIER + 1)^n`, so this bound is what keeps
/// the search in the microsecond range.
pub const MAX_HYPOTHESES: usize = 8;

/// A linear form `Σ cᵢ·atomᵢ + k` over atom indices into a problem's atom
/// table.
///
/// Zero coefficients are never stored, so two forms are equal as maps exactly
/// when they are equal as linear functions.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct LinForm {
    coeffs: BTreeMap<usize, Coeff>,
    constant: Coeff,
}

impl LinForm {
    /// The zero form.
    #[must_use]
    pub fn zero() -> Self {
        Self::default()
    }

    /// The constant form `k`.
    #[must_use]
    pub fn constant(k: Coeff) -> Self {
        Self {
            coeffs: BTreeMap::new(),
            constant: k,
        }
    }

    /// The form `1·atom`.
    #[must_use]
    pub fn atom(index: usize) -> Self {
        let mut coeffs = BTreeMap::new();
        coeffs.insert(index, 1);
        Self {
            coeffs,
            constant: 0,
        }
    }

    /// The coefficient of `index` (zero when absent).
    #[must_use]
    pub fn coeff(&self, index: usize) -> Coeff {
        self.coeffs.get(&index).copied().unwrap_or(0)
    }

    /// The constant term.
    #[must_use]
    pub fn const_term(&self) -> Coeff {
        self.constant
    }

    /// The atoms with a nonzero coefficient, in index order.
    pub fn atoms(&self) -> impl Iterator<Item = (usize, Coeff)> + '_ {
        self.coeffs.iter().map(|(&i, &c)| (i, c))
    }

    /// Set (or clear) one coefficient.
    fn set(&mut self, index: usize, value: Coeff) {
        if value == 0 {
            self.coeffs.remove(&index);
        } else {
            self.coeffs.insert(index, value);
        }
    }

    /// `self + other`, or `None` on coefficient overflow.
    #[must_use]
    pub fn checked_add(&self, other: &Self) -> Option<Self> {
        let mut out = self.clone();
        out.constant = out.constant.checked_add(other.constant)?;
        for (&i, &c) in &other.coeffs {
            let v = out.coeff(i).checked_add(c)?;
            out.set(i, v);
        }
        Some(out)
    }

    /// `self − other`, or `None` on coefficient overflow.
    #[must_use]
    pub fn checked_sub(&self, other: &Self) -> Option<Self> {
        let neg = other.checked_scale(-1)?;
        self.checked_add(&neg)
    }

    /// `factor · self`, or `None` on coefficient overflow.
    #[must_use]
    pub fn checked_scale(&self, factor: Coeff) -> Option<Self> {
        let mut out = Self {
            coeffs: BTreeMap::new(),
            constant: self.constant.checked_mul(factor)?,
        };
        if factor != 0 {
            for (&i, &c) in &self.coeffs {
                out.coeffs.insert(i, c.checked_mul(factor)?);
            }
        }
        Some(out)
    }

    /// Whether every coefficient **and** the constant are `≥ 0`.
    ///
    /// Over a carrier whose atoms are all nonnegative (ℕ), such a form is
    /// nonnegative at every valuation, so it is admissible slack.
    #[must_use]
    pub fn is_nonneg_cone(&self) -> bool {
        self.constant >= 0 && self.coeffs.values().all(|&c| c >= 0)
    }

    /// Whether every coefficient is `≤ 0` and the constant is `< 0`.
    ///
    /// Over ℕ such a form is *negative* at every valuation, so deriving it as
    /// `≥ 0` is a contradiction.
    #[must_use]
    pub fn is_neg_cone(&self) -> bool {
        self.constant < 0 && self.coeffs.values().all(|&c| c <= 0)
    }

    /// Whether the form mentions no atom.
    #[must_use]
    pub fn is_constant(&self) -> bool {
        self.coeffs.is_empty()
    }
}

/// Why the procedure produced no term.
///
/// Every variant is a *decline*, never an error: `linarith` returning
/// `Decline` says the search did not reach the goal, not that the goal is
/// false and not that anything went wrong.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Decline {
    /// The goal's shape is not `≤` / `<` / `=` / `¬(≤)` over the carrier.
    GoalNotAtomic,
    /// A term in the goal is outside the linear fragment — specifically, a
    /// product of two non-constant subterms, which the parser refuses rather
    /// than silently abstracting when it appears in a *goal*.
    NonLinear,
    /// The search found no nonnegative combination reaching the goal within
    /// the bounds. The goal may still be true.
    NoCertificate,
    /// More hypotheses than [`MAX_HYPOTHESES`], or a coefficient overflow.
    SearchBudget,
}

/// A Farkas certificate: nonnegative multipliers for the hypotheses, plus the
/// nonnegative slack left over.
///
/// The defining identity, with `Fⱼ` the hypothesis forms (each asserted `≥ 0`)
/// and `G` the goal form (to be shown `≥ 0`):
///
/// ```text
///     G  =  Σⱼ multipliers[j] · Fⱼ  +  residual
/// ```
///
/// with `residual` in the nonnegative cone. That identity is what the emitter
/// turns into a term, and it is checked here before the emitter runs — but the
/// check is *not* what makes the result sound. The kernel is.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Certificate {
    /// One nonnegative multiplier per hypothesis, in hypothesis order.
    pub multipliers: Vec<Coeff>,
    /// The leftover slack, with every coefficient `≥ 0`.
    pub residual: LinForm,
}

impl Certificate {
    /// The hypotheses actually used, as `(index, multiplier)` pairs.
    pub fn used(&self) -> impl Iterator<Item = (usize, Coeff)> + '_ {
        self.multipliers
            .iter()
            .enumerate()
            .filter(|&(_, &m)| m > 0)
            .map(|(i, &m)| (i, m))
    }

    /// The largest multiplier in the certificate.
    #[must_use]
    pub fn max_multiplier(&self) -> Coeff {
        self.multipliers.iter().copied().max().unwrap_or(0)
    }
}

/// Search for a certificate deriving `goal ≥ 0` from `hyps` (each `≥ 0`).
///
/// Enumerates multiplier vectors in order of increasing total weight, so the
/// certificate returned is one with the smallest coefficient sum — which is
/// also the smallest emitted term, since a multiplier `λ` costs `λ`
/// applications of `add_le_add`.
///
/// # Errors
///
/// [`Decline::SearchBudget`] when there are more than [`MAX_HYPOTHESES`]
/// hypotheses or a coefficient overflows; [`Decline::NoCertificate`] when no
/// vector within the bounds works.
pub fn find_certificate(hyps: &[LinForm], goal: &LinForm) -> Result<Certificate, Decline> {
    find_combination(hyps, goal, LinForm::is_nonneg_cone)
}

/// Search for a certificate whose combination of `hyps` is *negative* at every
/// valuation — a refutation of the hypothesis set over a nonnegative carrier.
///
/// The `residual` of the returned certificate is the nonnegative form `N` in
/// `Σⱼ λⱼ Fⱼ = −m − N` with `m ≥ 1`; the emitter reads `m` back off it.
///
/// # Errors
///
/// As [`find_certificate`].
pub fn find_refutation(hyps: &[LinForm]) -> Result<Certificate, Decline> {
    let goal = LinForm::zero();
    // Σ λⱼ Fⱼ must be negative everywhere, i.e. `0 − Σ λⱼ Fⱼ` must have every
    // coefficient ≥ 0 and a constant > 0.
    let cert = find_combination(hyps, &goal, |residual| {
        residual.constant > 0 && residual.coeffs.values().all(|&c| c >= 0)
    })?;
    if cert.multipliers.iter().all(|&m| m == 0) {
        return Err(Decline::NoCertificate);
    }
    Ok(cert)
}

/// The shared enumeration: find `λ ≥ 0` with `accept(goal − Σ λⱼ Fⱼ)`.
fn find_combination(
    hyps: &[LinForm],
    goal: &LinForm,
    accept: impl Fn(&LinForm) -> bool,
) -> Result<Certificate, Decline> {
    if hyps.len() > MAX_HYPOTHESES {
        return Err(Decline::SearchBudget);
    }
    let n = hyps.len();
    let max_total = MAX_MULTIPLIER * Coeff::try_from(n).unwrap_or(0);
    for total in 0..=max_total {
        let mut lambda = vec![0; n];
        if let Some(cert) = enumerate(hyps, goal, &accept, &mut lambda, 0, total)? {
            return Ok(cert);
        }
    }
    Err(Decline::NoCertificate)
}

/// Assign `remaining` weight across `lambda[position..]`, testing each full
/// assignment. Weight-ordered, so the first hit has the smallest coefficient
/// sum.
fn enumerate(
    hyps: &[LinForm],
    goal: &LinForm,
    accept: &impl Fn(&LinForm) -> bool,
    lambda: &mut Vec<Coeff>,
    position: usize,
    remaining: Coeff,
) -> Result<Option<Certificate>, Decline> {
    if position == lambda.len() {
        if remaining != 0 {
            return Ok(None);
        }
        let mut combination = LinForm::zero();
        for (h, &m) in hyps.iter().zip(lambda.iter()) {
            if m == 0 {
                continue;
            }
            let scaled = h.checked_scale(m).ok_or(Decline::SearchBudget)?;
            combination = combination
                .checked_add(&scaled)
                .ok_or(Decline::SearchBudget)?;
        }
        let residual = goal
            .checked_sub(&combination)
            .ok_or(Decline::SearchBudget)?;
        if accept(&residual) {
            return Ok(Some(Certificate {
                multipliers: lambda.clone(),
                residual,
            }));
        }
        return Ok(None);
    }
    let slots = Coeff::try_from(lambda.len() - position).unwrap_or(1);
    let upper = remaining.min(MAX_MULTIPLIER);
    for value in 0..=upper {
        // Prune: the remaining slots cannot carry more than MAX_MULTIPLIER each.
        if remaining - value > MAX_MULTIPLIER * (slots - 1) {
            continue;
        }
        lambda[position] = value;
        if let Some(cert) = enumerate(hyps, goal, accept, lambda, position + 1, remaining - value)?
        {
            return Ok(Some(cert));
        }
        lambda[position] = 0;
    }
    Ok(None)
}

#[cfg(test)]
mod core_tests {
    use super::*;

    #[test]
    fn a_goal_implied_by_one_hypothesis_gets_multiplier_one() {
        // hyp: m − n ≥ 0   goal: (m + 1) − n ≥ 0
        let hyp = LinForm::atom(1).checked_sub(&LinForm::atom(0)).unwrap();
        let goal = hyp.checked_add(&LinForm::constant(1)).unwrap();
        let cert = find_certificate(&[hyp], &goal).unwrap();
        assert_eq!(cert.multipliers, vec![1]);
        assert_eq!(cert.residual, LinForm::constant(1));
    }

    #[test]
    fn a_goal_needing_two_copies_gets_multiplier_two() {
        // hyp: b − a ≥ 0   goal: 2b − 2a ≥ 0
        let hyp = LinForm::atom(1).checked_sub(&LinForm::atom(0)).unwrap();
        let goal = hyp.checked_scale(2).unwrap();
        let cert = find_certificate(&[hyp], &goal).unwrap();
        assert_eq!(cert.multipliers, vec![2]);
        assert_eq!(cert.residual, LinForm::zero());
    }

    #[test]
    fn a_false_goal_declines_with_no_certificate() {
        // no hypotheses, goal: −1 ≥ 0
        let goal = LinForm::constant(-1);
        assert_eq!(find_certificate(&[], &goal), Err(Decline::NoCertificate));
    }

    #[test]
    fn a_goal_beyond_the_multiplier_bound_declines_rather_than_growing() {
        let hyp = LinForm::atom(1).checked_sub(&LinForm::atom(0)).unwrap();
        let goal = hyp.checked_scale(MAX_MULTIPLIER + 1).unwrap();
        assert_eq!(find_certificate(&[hyp], &goal), Err(Decline::NoCertificate));
    }

    #[test]
    fn contradictory_hypotheses_yield_a_refutation() {
        // a ≥ b and b ≥ a + 1
        let h0 = LinForm::atom(0).checked_sub(&LinForm::atom(1)).unwrap();
        let h1 = LinForm::atom(1)
            .checked_sub(&LinForm::atom(0))
            .unwrap()
            .checked_sub(&LinForm::constant(1))
            .unwrap();
        let cert = find_refutation(&[h0, h1]).unwrap();
        assert_eq!(cert.multipliers, vec![1, 1]);
        assert_eq!(cert.residual, LinForm::constant(1));
    }

    #[test]
    fn a_satisfiable_hypothesis_set_has_no_refutation() {
        let h0 = LinForm::atom(0).checked_sub(&LinForm::atom(1)).unwrap();
        assert_eq!(find_refutation(&[h0]), Err(Decline::NoCertificate));
    }

    #[test]
    fn more_hypotheses_than_the_bound_decline_on_budget() {
        let hyps = vec![LinForm::zero(); MAX_HYPOTHESES + 1];
        assert_eq!(
            find_certificate(&hyps, &LinForm::zero()),
            Err(Decline::SearchBudget)
        );
    }
}
