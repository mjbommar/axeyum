//! The ℚ instantiation of [`super`]: goals `Rat.le lhs rhs` over the
//! `RatPrelude`.
//!
//! ## Why ℚ and not `CReal`
//!
//! Both carriers have the four lemmas the emitted term rests on —
//! `sq_nonneg`, `mul_nonneg`, `add_nonneg`, `add_le_add` — and both are
//! axiom-free. ℚ is chosen for one reason the brief's alternative does not
//! have: **`crate::ring::rat` exists**. The certificate's identity
//! `M·(rhs − lhs) = Σ …` is the crux of every proof this producer emits, and
//! `ring::rat::prove_eq` is the only ring normalizer in this kernel that
//! closes such an identity at a field carrier. `CReal`'s equality is the
//! *defined* relation `CReal.Equiv`, so the same construction there needs a
//! setoid ring normalizer (the `ordered_ring::setoid` machinery in
//! `axeyum-solver` is the analogous thing one level up) that this kernel does
//! not have as a producer. Nothing about the design is ℚ-specific: the search,
//! the certificate and the division step are all carrier-agnostic and live in
//! [`super`]; only this file names `Rat`.
//!
//! ## The emitted term, step by step
//!
//! Goal `Rat.le a b`, certificate `M·(b − a) = Σₖ (kₖ copies of atomₖ)`:
//!
//! 1. `hₖ : le 0 atomₖ` — `sq_nonneg ℓₖ` for a square, `mul_nonneg hᵢ hⱼ` for a
//!    hypothesis product.
//! 2. `hS : le 0 S` — the left-associated `add_nonneg` fold over the atoms,
//!    each repeated `kₖ` times.
//! 3. `idS : Eq Rat S T`, where `T` is `t = b + (−a)` repeated `M` times —
//!    proved by `crate::ring::rat::prove_eq`, never asserted.
//! 4. `hT : le 0 T` — `hS` transported along `idS`.
//! 5. `hDiff : le 0 t` — `divide_by_scale`, the only step that is not a
//!    one-liner; see its own docs.
//! 6. `le (a + 0) (a + t)` by `add_le_add a a 0 t (le_refl a) hDiff`, rewritten
//!    to `le a (a + t)` by `add_zero`, and then to `le a b` along the second
//!    ring identity `a + (b + (−a)) = b`.
//!
//! Every lemma named there is a `RatPrelude` **theorem**, so the emitted term's
//! axiom footprint is whatever `Rat`'s own is — measured empty.

#![cfg_attr(not(test), allow(dead_code))]
// `RatPrelude` is a `Copy` handle carrying the whole `IntPrelude`/`NatPrelude`
// chain plus ~460 of its own names, so it is large and every function below
// trips `large_types_passed_by_value`. Same shape, same suppression and the
// same reason as `rn.rs`, `creal.rs` and `metric.rs`: these are straight-line
// term constructions and the handle is a `Copy` snapshot by design. The
// carrier-agnostic half in `super` uses `&self`/`Copy` scalars and needs none
// of this.
#![allow(
    clippy::large_types_passed_by_value,
    clippy::many_single_char_names,
    clippy::similar_names
)]

use crate::ExprNode;
use crate::RatPrelude;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::ops::{radd, req_motive, rle, rlt, rmul, rneg, rone, rtransport, rzero};
use crate::ring;

use super::{Atom, Certificate, Decline, DualWitness, Poly, Q};

/// The context a [`prove`] call needs.
pub(crate) struct Ctx<'a> {
    /// The `Rat` prelude every lemma is drawn from.
    pub prelude: RatPrelude,
    /// Hypotheses, each a `(statement, proof)` pair whose statement is
    /// `Rat.le Rat.zero h`. Only used by the Positivstellensatz product shape;
    /// an empty slice is the pure-SOS producer.
    pub assumptions: &'a [(ExprId, ExprId)],
    /// An optional non-SOS witness for the goal's difference. The producer
    /// never searches for one; when supplied it is CHECKED, and a witness that
    /// checks turns the refusal into [`Decline::PsdNotSos`].
    pub dual: Option<&'a DualWitness>,
}

// ---------------------------------------------------------------------------
// parsing
// ---------------------------------------------------------------------------

/// The atom table shared by the goal and every hypothesis, so one variable has
/// one index everywhere.
struct Parser {
    prelude: RatPrelude,
    atoms: Vec<ExprId>,
}

impl Parser {
    fn new(prelude: RatPrelude) -> Self {
        Self {
            prelude,
            atoms: Vec::new(),
        }
    }

    fn atom_index(&mut self, e: ExprId) -> usize {
        if let Some(i) = self.atoms.iter().position(|&a| a == e) {
            return i;
        }
        self.atoms.push(e);
        self.atoms.len() - 1
    }

    /// The application spine of `e`: its head and its arguments, left to right.
    fn spine(d: &mut IntDev<'_>, e: ExprId) -> (ExprId, Vec<ExprId>) {
        let mut args = Vec::new();
        let mut head = e;
        loop {
            let node = d.kernel().expr_node(head).clone();
            let ExprNode::App(f, a) = node else { break };
            args.push(a);
            head = f;
        }
        args.reverse();
        (head, args)
    }

    fn head_const(d: &mut IntDev<'_>, e: ExprId) -> Option<crate::NameId> {
        match d.kernel().expr_node(e).clone() {
            ExprNode::Const(n, _) => Some(n),
            _ => None,
        }
    }

    /// Parse `e` into a polynomial over the shared atom table.
    ///
    /// `Rat.zero`/`Rat.one` are the literals; `Rat.add`/`Rat.mul`/`Rat.neg` are
    /// the operations; anything else is an atom — which is exactly
    /// `ring::rat`'s own fragment, and deliberately so: a subterm this parser
    /// treats as an atom is one the ring normalizer that closes the
    /// certificate's identity also treats as an atom, so the two agree.
    fn parse(&mut self, d: &mut IntDev<'_>, e: ExprId) -> Result<Poly, Decline> {
        let p = self.prelude;
        if let Some(name) = Self::head_const(d, e) {
            if name == p.zero {
                return Ok(Poly::zero());
            }
            if name == p.one {
                return Ok(Poly::constant(Q::integer(1)));
            }
        }
        let (head, args) = Self::spine(d, e);
        if let Some(name) = Self::head_const(d, head) {
            let (add, mul, neg) = (d.int().rat_add, d.int().rat_mul, d.int().rat_neg);
            if name == add && args.len() == 2 {
                let a = self.parse(d, args[0])?;
                let b = self.parse(d, args[1])?;
                return a.add(&b).ok_or(Decline::Overflow);
            }
            if name == mul && args.len() == 2 {
                let a = self.parse(d, args[0])?;
                let b = self.parse(d, args[1])?;
                return a.mul(&b).ok_or(Decline::Overflow);
            }
            if name == neg && args.len() == 1 {
                let a = self.parse(d, args[0])?;
                return a.neg().ok_or(Decline::Overflow);
            }
        }
        Ok(Poly::var(self.atom_index(e)))
    }

    /// Parse a goal `Rat.le lhs rhs` into its two sides.
    fn parse_le_goal(d: &mut IntDev<'_>, p: RatPrelude, e: ExprId) -> Option<(ExprId, ExprId)> {
        let (head, args) = Self::spine(d, e);
        let name = Self::head_const(d, head)?;
        if name == p.le && args.len() == 2 {
            return Some((args[0], args[1]));
        }
        None
    }

    /// Parse a hypothesis statement `Rat.le Rat.zero h` into `h`.
    fn parse_nonneg(d: &mut IntDev<'_>, p: RatPrelude, e: ExprId) -> Option<ExprId> {
        let (lhs, rhs) = Self::parse_le_goal(d, p, e)?;
        if Self::head_const(d, lhs)? == p.zero {
            Some(rhs)
        } else {
            None
        }
    }
}

// ---------------------------------------------------------------------------
// term building
// ---------------------------------------------------------------------------

/// `t` repeated `count` times, left-associated: `((t + t) + t) + …`.
///
/// `count` must be `≥ 1`. Shared by the certificate's right-hand side and
/// `divide_by_scale`'s fold, so the two are the same expression by
/// construction rather than by hope — the kernel hash-conses, so "the same
/// expression" is `==`, not a defeq the normalizer might paper over.
fn repeat_add(d: &mut IntDev<'_>, t: ExprId, count: i128) -> ExprId {
    let mut acc = t;
    for _ in 1..count {
        acc = radd(d, acc, t);
    }
    acc
}

/// The kernel term for a cleared linear form `constant + Σ cᵢ xᵢ`, built as
/// repeated addition of signed atoms.
///
/// Repeated addition, not `Rat.mul` by a numeral: `ring::rat` recognizes only
/// the literals `{-1, 0, 1}` and has no numeral-scaling reduction (see
/// [`super`]'s module docs), so a coefficient has to arrive as summands or the
/// identity will not close.
fn form_term(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    atoms: &[ExprId],
    constant: i128,
    linear: &[(usize, i128)],
) -> ExprId {
    let mut summands: Vec<ExprId> = Vec::new();
    if constant != 0 {
        let one = rone(d, p);
        let signed = if constant < 0 { rneg(d, one) } else { one };
        for _ in 0..constant.abs() {
            summands.push(signed);
        }
    }
    for &(v, c) in linear {
        let base = atoms[v];
        let signed = if c < 0 { rneg(d, base) } else { base };
        for _ in 0..c.abs() {
            summands.push(signed);
        }
    }
    if summands.is_empty() {
        return rzero(d, p);
    }
    let mut acc = summands[0];
    for &s in &summands[1..] {
        acc = radd(d, acc, s);
    }
    acc
}

/// Build one certificate atom's kernel term together with its nonnegativity
/// proof.
fn atom_term_and_proof(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    atoms: &[ExprId],
    hypotheses: &[(ExprId, ExprId)],
    atom: &Atom,
) -> Option<(ExprId, ExprId)> {
    match atom {
        Atom::Square { constant, linear } => {
            let form = form_term(d, p, atoms, *constant, linear);
            let square = rmul(d, form, form);
            let proof = d.lemma(p.sq_nonneg, &[form]);
            Some((square, proof))
        }
        Atom::HypothesisProduct(i, j) => {
            let (a_term, a_proof) = *hypotheses.get(*i)?;
            let (b_term, b_proof) = *hypotheses.get(*j)?;
            let product = rmul(d, a_term, b_term);
            let proof = d.lemma(p.mul_nonneg, &[a_term, b_term, a_proof, b_proof]);
            Some((product, proof))
        }
    }
}

/// From `h_total : Rat.le 0 T` with `T` the `scale`-fold repeated sum of `t`,
/// derive `Rat.le 0 t`.
///
/// **The division step, and the only part of the emitted proof that is not a
/// single lemma application.** There is no `Rat` lemma taking `0 ≤ M·t` to
/// `0 ≤ t`, and routing through `Rat.inv` would need `inv_pos` plus a
/// `mul_inv_cancel` rearrangement; this route uses neither inverse nor
/// division. It case-splits on `le_or_lt 0 t`:
///
/// - **left** `0 ≤ t` — the goal, returned unchanged;
/// - **right** `t < 0` — fold `add_lt_add_of_le_of_lt` `scale − 1` times to
///   `T < 0` (each step rewriting `0 + 0` back to `0` by `zero_add`), contradict
///   it with `h_total` through `lt_of_le_of_lt` to get `0 < 0`, refute that with
///   `lt_irrefl 0`, and eliminate the resulting `False` into the goal.
///
/// `scale == 1` returns `h_total` untouched: `T` *is* `t`, and emitting a
/// case-split for it would be a proof of something already proved.
fn divide_by_scale(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    t: ExprId,
    scale: i128,
    h_total: ExprId,
) -> ExprId {
    if scale <= 1 {
        return h_total;
    }
    let zero = rzero(d, p);
    let goal = rle(d, p, zero, t);
    let left = goal;
    let right = rlt(d, p, t, zero);
    let disjunction = d.lemma(p.le_or_lt, &[zero, t]);
    d.or_elim(
        left,
        right,
        goal,
        disjunction,
        &|_d, hypothesis| hypothesis,
        &|d, negative| {
            // `negative : lt t zero`. Fold to `lt T zero`, the same left-associated
            // `T` `repeat_add` built.
            let mut acc_term = t;
            let mut acc_proof = negative;
            for _ in 1..scale {
                let weak = d.lemma(p.le_of_lt, &[acc_term, zero, acc_proof]);
                let step = d.lemma(
                    p.add_lt_add_of_le_of_lt,
                    &[acc_term, zero, t, zero, weak, negative],
                );
                // `step : lt (add acc_term t) (add zero zero)`; rewrite the
                // right-hand side back to `zero`.
                let sum = radd(d, acc_term, t);
                let zero_plus_zero = radd(d, zero, zero);
                let collapse = d.lemma(p.zero_add, &[zero]);
                let motive = req_motive(d, zero_plus_zero, &|d, x| rlt(d, p, sum, x));
                acc_proof = rtransport(d, zero_plus_zero, motive, step, zero, collapse);
                acc_term = sum;
            }
            let bad = d.lemma(
                p.lt_of_le_of_lt,
                &[zero, acc_term, zero, h_total, acc_proof],
            );
            let irreflexive = d.lemma(p.lt_irrefl, &[zero]);
            let contradiction = d.apply(irreflexive, &[bad]);
            d.absurd(goal, contradiction)
        },
    )
}

// ---------------------------------------------------------------------------
// the producer
// ---------------------------------------------------------------------------

/// Run the producer on `goal` (`Rat.le lhs rhs`), or decline.
///
/// The returned `ExprId` is an **unchecked** proof term, as every producer in
/// this crate returns — the caller pushes it through
/// [`Kernel::add_declaration`](crate::Kernel::add_declaration); this function
/// adds no trusted surface of its own.
///
/// # Errors
///
/// A [`Decline`] naming what the producer could not do. Two of its variants —
/// [`Decline::NotPsd`] and [`Decline::PsdNotSos`] — are findings rather than
/// mere refusals; see their docs.
pub(crate) fn prove(d: &mut IntDev<'_>, ctx: &Ctx<'_>, goal: ExprId) -> Result<ExprId, Decline> {
    let p = ctx.prelude;
    let (lhs, rhs) = Parser::parse_le_goal(d, p, goal).ok_or(Decline::GoalNotLe)?;

    let mut parser = Parser::new(p);
    let lhs_poly = parser.parse(d, lhs)?;
    let rhs_poly = parser.parse(d, rhs)?;
    let difference = rhs_poly.sub(&lhs_poly).ok_or(Decline::Overflow)?;

    // Hypotheses: `(term, proof)` pairs plus their polynomials, over the SAME
    // atom table as the goal.
    let mut hypothesis_terms: Vec<(ExprId, ExprId)> = Vec::new();
    let mut hypothesis_polys: Vec<Poly> = Vec::new();
    for &(statement, proof) in ctx.assumptions {
        let term = Parser::parse_nonneg(d, p, statement).ok_or(Decline::HypothesisNotNonneg)?;
        let poly = parser.parse(d, term)?;
        hypothesis_terms.push((term, proof));
        hypothesis_polys.push(poly);
    }

    let vars = parser.atoms.len();
    let certificate = match super::search_with_hypotheses(&difference, vars, &hypothesis_polys) {
        Ok(certificate) => certificate,
        Err(primary) => {
            // Only now consult a supplied non-SOS witness: a search that
            // SUCCEEDED needs no witness, and a witness that verifies against a
            // difference the search decomposed would mean one of the two is
            // wrong. Checking second keeps that impossible rather than merely
            // unlikely.
            let Some(witness) = ctx.dual else {
                return Err(primary);
            };
            return if witness.verifies(&difference, vars)? {
                Err(Decline::PsdNotSos)
            } else {
                Err(Decline::DualWitnessInvalid)
            };
        }
    };

    // The search's own re-derivation of the certificate: expand it back to a
    // polynomial and require it to equal `scale · (rhs − lhs)`. `ring::rat`
    // checks the same identity a second time, independently, in the kernel.
    let expanded = certificate
        .expand(&hypothesis_polys)
        .ok_or(Decline::Overflow)?;
    let target = difference
        .scale(Q::integer(certificate.scale))
        .ok_or(Decline::Overflow)?;
    if expanded != target {
        return Err(Decline::Ring(ring::Decline::NotAnIdentity));
    }

    emit(
        d,
        p,
        &parser.atoms,
        &hypothesis_terms,
        &certificate,
        lhs,
        rhs,
    )
}

/// Assemble the proof term for a certificate the search has already checked.
fn emit(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    atoms: &[ExprId],
    hypotheses: &[(ExprId, ExprId)],
    certificate: &Certificate,
    lhs: ExprId,
    rhs: ExprId,
) -> Result<ExprId, Decline> {
    emit_with(d, p, atoms, hypotheses, certificate, lhs, rhs, true)
}

/// [`emit`] with the ring producer's own normal-form check switched OFF.
///
/// Exposed for the corrupted-certificate test and nothing else: with the check
/// on, a wrong certificate is refused by `ring::rat` and the kernel never sees
/// it, so the test would be measuring the search rather than the trusted gate.
/// This is `ring::rat::prove_eq_unverified`'s reason for existing, reused.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn emit_unverified(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    atoms: &[ExprId],
    hypotheses: &[(ExprId, ExprId)],
    certificate: &Certificate,
    lhs: ExprId,
    rhs: ExprId,
) -> Result<ExprId, Decline> {
    emit_with(d, p, atoms, hypotheses, certificate, lhs, rhs, false)
}

#[allow(clippy::too_many_arguments)]
fn emit_with(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    atoms: &[ExprId],
    hypotheses: &[(ExprId, ExprId)],
    certificate: &Certificate,
    lhs: ExprId,
    rhs: ExprId,
    verify: bool,
) -> Result<ExprId, Decline> {
    let ring_eq = |d: &mut IntDev<'_>, a: ExprId, b: ExprId| {
        if verify {
            ring::rat::prove_eq(d, &p, a, b)
        } else {
            ring::rat::prove_eq_unverified(d, &p, a, b)
        }
    };
    // (1)-(2) the `add_nonneg` fold over every atom, each repeated `kₖ` times.
    let mut sum: Option<(ExprId, ExprId)> = None;
    for (multiplicity, atom) in &certificate.atoms {
        let (term, proof) = atom_term_and_proof(d, p, atoms, hypotheses, atom)
            .ok_or(Decline::CertificateTooLarge)?;
        for _ in 0..*multiplicity {
            sum = Some(match sum {
                None => (term, proof),
                Some((acc_term, acc_proof)) => {
                    let joined = radd(d, acc_term, term);
                    let joined_proof = d.lemma(p.add_nonneg, &[acc_term, term, acc_proof, proof]);
                    (joined, joined_proof)
                }
            });
        }
    }
    let (sum_term, sum_proof) = sum.ok_or(Decline::CertificateTooLarge)?;

    // (3) the certificate's identity `S = T`, proved by the ring producer.
    let negated_lhs = rneg(d, lhs);
    let difference_term = radd(d, rhs, negated_lhs);
    let total = repeat_add(d, difference_term, certificate.scale);
    let identity = ring_eq(d, sum_term, total).map_err(Decline::Ring)?;

    // (4) transport `0 ≤ S` along it to `0 ≤ T`.
    let zero = rzero(d, p);
    let motive = req_motive(d, sum_term, &|d, x| rle(d, p, zero, x));
    let total_nonneg = rtransport(d, sum_term, motive, sum_proof, total, identity);

    // (5) divide the scale back out.
    let difference_nonneg = divide_by_scale(d, p, difference_term, certificate.scale, total_nonneg);

    // (6) `0 ≤ b − a` ⟹ `a ≤ b`, in three steps that never mention the scale.
    let reflexive = d.lemma(p.le_refl, &[lhs]);
    let shifted = d.lemma(
        p.add_le_add,
        &[
            lhs,
            lhs,
            zero,
            difference_term,
            reflexive,
            difference_nonneg,
        ],
    );
    // `shifted : le (add lhs zero) (add lhs (b + (−a)))`; drop the `+ 0`.
    let lhs_plus_zero = radd(d, lhs, zero);
    let shifted_target = radd(d, lhs, difference_term);
    let drop_zero = d.lemma(p.add_zero, &[lhs]);
    let motive = req_motive(d, lhs_plus_zero, &|d, x| rle(d, p, x, shifted_target));
    let tidied = rtransport(d, lhs_plus_zero, motive, shifted, lhs, drop_zero);
    // `tidied : le lhs (add lhs (b + (−a)))`; the right side IS `b`, by ring.
    let collapse = ring_eq(d, shifted_target, rhs).map_err(Decline::Ring)?;
    let motive = req_motive(d, shifted_target, &|d, x| rle(d, p, lhs, x));
    Ok(rtransport(d, shifted_target, motive, tidied, rhs, collapse))
}

#[cfg(test)]
mod tests;
