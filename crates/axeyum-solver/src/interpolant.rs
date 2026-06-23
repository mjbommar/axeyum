//! Craig interpolation for conjunctive `QF_LRA`, read off the verified Farkas
//! certificate (Track 3, **T3.8.1**).
//!
//! Given an unsatisfiable conjunction `A ∧ B`, a **Craig interpolant** `I`
//! satisfies three conditions:
//!
//! 1. `A ⇒ I` (`A ∧ ¬I` is unsatisfiable);
//! 2. `I ∧ B ⇒ ⊥` (`I ∧ B` is unsatisfiable);
//! 3. `I` mentions only the *shared* symbols — those appearing in both `A` and
//!    `B`.
//!
//! For linear real arithmetic the interpolant is **not** a fresh search: it is
//! the `A`-side restriction of the Farkas refutation that axeyum already
//! produces and self-checks. If `λ` are the nonnegative Farkas multipliers that
//! collapse `A ∧ B` to a false constant relation, then
//!
//! ```text
//! I  :=  ( Σ_{atom i comes from A} λ_i · atom_i )  ⋈  0
//! ```
//!
//! where `⋈` is `<` when any used `A`-atom is strict, else `≤`. Each `A`-atom is
//! `eᵢ ⋈ᵢ 0`, so `A` directly entails `I` (condition 1). Adding the `B`-side
//! combination (each `B`-atom `≤ 0`, nonnegative multipliers) reproduces the
//! full refutation `K ⋈ 0` with `K > 0`, so `I ∧ B ⇒ ⊥` (condition 2).
//! Condition 3 holds **automatically**: in the full combination every variable
//! cancels, and a `B`-absent variable has coefficient `0` in the `B`-part, so its
//! `A`-part coefficient is `0` too — `A`-only variables vanish from `I`, leaving
//! only shared variables. (`McMillan`, *An interpolating theorem prover*.)
//!
//! Because the interpolant is a consequence of an already-checked proof it
//! inherits that assurance, but we do **not** trust the derivation: every
//! returned interpolant is re-verified by the three conditions as independent
//! `unsat`/vocabulary checks, and any failure declines to `Ok(None)` rather than
//! returning an unverified guess.

use std::collections::{BTreeMap, BTreeSet};

use axeyum_cnf::AletheCommand;
use axeyum_ir::{Rational, SymbolId, TermArena, TermId, TermNode};

use crate::{
    CheckResult, SolverError, check_with_lra, lra_farkas_certificate, prove_lra_unsat_alethe,
};

/// Produces a verified Craig interpolant for the unsatisfiable conjunction
/// `A ∧ B`, where `a_assertions` is `A` and `b_assertions` is `B` (each a
/// conjunctively-interpreted slice of linear-real constraints).
///
/// Returns `Ok(Some(I))` with a fully re-checked interpolant term `I`, or
/// `Ok(None)` when no Farkas interpolant is available — the conjunction is
/// satisfiable, only trivially false, outside conjunctive `QF_LRA`, an exact
/// `i128` overflow was hit while forming the combination, or the candidate fails
/// any of its three independent post-checks. It **never** returns an unverified
/// interpolant.
///
/// # Errors
///
/// Propagates [`SolverError`] from the underlying Farkas decision / the
/// verification `check_with_lra` calls (e.g. a `sat`-replay or self-check
/// soundness alarm). A term-builder failure is also surfaced as
/// [`SolverError::Backend`].
pub fn lra_interpolant(
    arena: &mut TermArena,
    a_assertions: &[TermId],
    b_assertions: &[TermId],
) -> Result<Option<TermId>, SolverError> {
    build_verified_interpolant(arena, a_assertions, b_assertions)
}

/// Builds the `A`-side Farkas interpolant `I` for the unsatisfiable conjunction
/// `A ∧ B`, re-verifies the three Craig conditions independently, and returns it
/// (or `None`). This is the single source of truth for the interpolant `I`;
/// [`lra_interpolant`] forwards to it directly and
/// [`lra_interpolant_certified`] reuses it, so the returned `I` is byte-identical
/// across both entry points.
fn build_verified_interpolant(
    arena: &mut TermArena,
    a_assertions: &[TermId],
    b_assertions: &[TermId],
) -> Result<Option<TermId>, SolverError> {
    // 1. Refute A ∧ B and take its (already self-checked) Farkas certificate.
    let mut combined = Vec::with_capacity(a_assertions.len() + b_assertions.len());
    combined.extend_from_slice(a_assertions);
    combined.extend_from_slice(b_assertions);
    let a_len = a_assertions.len();

    // Satisfiable, trivially false, or unsupported: no Farkas interpolant.
    let Some(cert) = lra_farkas_certificate(arena, &combined)? else {
        return Ok(None);
    };

    // 2. Sum the A-side combination  Σ_{origin(i) ∈ A} λ_i · atom_i.  By Farkas
    //    full-cancellation the A-only variables drop out here, so the result
    //    already mentions only shared variables. All arithmetic is overflow-
    //    checked: an overflow declines (never a wrong interpolant).
    let mut coeffs: BTreeMap<usize, Rational> = BTreeMap::new();
    let mut constant = Rational::zero();
    let mut strict = false;
    for ((atom, &multiplier), &origin) in
        cert.atoms.iter().zip(&cert.multipliers).zip(&cert.origins)
    {
        if origin >= a_len || multiplier.is_zero() {
            continue; // B-side atom, or unused by the refutation.
        }
        for &(index, coeff) in &atom.coeffs {
            let Some(scaled) = multiplier.checked_mul(coeff) else {
                return Ok(None);
            };
            let entry = coeffs.entry(index).or_insert_with(Rational::zero);
            let Some(sum) = entry.checked_add(scaled) else {
                return Ok(None);
            };
            *entry = sum;
        }
        let Some(scaled_const) = multiplier.checked_mul(atom.constant) else {
            return Ok(None);
        };
        let Some(next) = constant.checked_add(scaled_const) else {
            return Ok(None);
        };
        constant = next;
        if atom.strict {
            strict = true;
        }
    }

    // 3. Materialize  (Σ coeff·x + constant) ⋈ 0  as a typed real term.
    let Some(expr) = build_linear_term(arena, &coeffs, &cert.vars, constant) else {
        return Ok(None);
    };
    let zero = arena.real_const(Rational::zero());
    let interpolant = if strict {
        arena.real_lt(expr, zero)
    } else {
        arena.real_le(expr, zero)
    }
    .map_err(|e| SolverError::Backend(format!("interpolant term build failed: {e}")))?;

    // 4. Re-verify the three Craig conditions independently. Decline on any
    //    doubt — an unverified interpolant must never escape.
    if verify_interpolant(
        arena,
        a_assertions,
        b_assertions,
        interpolant,
        &coeffs,
        &cert.vars,
    )? {
        Ok(Some(interpolant))
    } else {
        Ok(None)
    }
}

/// A **certified** conjunctive `QF_LRA` Craig interpolant: the interpolant `I`
/// for an unsatisfiable `A ∧ B`, paired with two externally-checkable `Farkas`
/// refutations witnessing its two soundness conditions.
///
/// - [`a_refutation`](Self::a_refutation) is an Alethe `la_generic` proof of
///   `A ∧ ¬I ⊢ ⊥` (Craig condition 1, `A ⇒ I`);
/// - [`b_refutation`](Self::b_refutation) is an Alethe `la_generic` proof of
///   `I ∧ B ⊢ ⊥` (Craig condition 2).
///
/// Both proofs are self-validated through [`crate::check_alethe_lra`] before this
/// struct is constructed, and each is **independently** checkable by an external
/// checker — Carcara (`la_generic`, accepted when `valid && !holey`) or, via
/// [`crate::prove_unsat_to_lean_module`] on the same conjunction, the Lean kernel
/// (`infer` + `def_eq False`, no `sorryAx`). Because the interpolant `I` here is a
/// single linear inequality, both `A ∧ ¬I` and `I ∧ B` are **conjunctions** of
/// linear-real atoms (`¬I` is one inequality), so each is `Farkas`-refutable —
/// this is exactly the conjunctively-certifiable slice (see
/// [`lra_interpolant_certified`]).
#[derive(Debug, Clone)]
pub struct LraInterpolantCertificate {
    /// The verified interpolant term `I` (byte-identical to what
    /// [`lra_interpolant`] returns for the same `(A, B)`).
    pub interpolant: TermId,
    /// `A ∧ ¬I`, the conjunction the [`a_refutation`](Self::a_refutation) refutes
    /// (so a consumer can re-derive a Lean-kernel certificate from it).
    pub a_and_not_i: Vec<TermId>,
    /// `I ∧ B`, the conjunction the [`b_refutation`](Self::b_refutation) refutes.
    pub i_and_b: Vec<TermId>,
    /// Alethe `la_generic` refutation of `A ∧ ¬I` (Craig condition 1).
    pub a_refutation: Vec<AletheCommand>,
    /// Alethe `la_generic` refutation of `I ∧ B` (Craig condition 2).
    pub b_refutation: Vec<AletheCommand>,
}

/// Produces a **certified** Craig interpolant for the unsatisfiable conjunctive
/// `QF_LRA` partition `A = a_assertions`, `B = b_assertions`: the same verified
/// interpolant [`lra_interpolant`] returns, **plus** two `Farkas` certificates —
/// Alethe `la_generic` refutations of `A ∧ ¬I` and `I ∧ B` — that an independent
/// checker (Carcara, or the Lean kernel via
/// [`crate::prove_unsat_to_lean_module`]) can accept on its own.
///
/// This is the `Checked`-assurance upgrade of the `Validated` [`lra_interpolant`]:
/// the interpolant was already verify-before-return; here we additionally emit an
/// externally-checkable certificate for each of its two soundness conditions, and
/// return it **only** when both certificates are produced and self-check (through
/// [`crate::check_alethe_lra`]). Both refutations are conjunctive because the
/// interpolant `I` is a single linear inequality, so `¬I` is a single inequality
/// and each conjunction is `Farkas`-refutable.
///
/// # Boundary
///
/// Only the CONJUNCTIVE `QF_LRA` slice is certified here. A disjunctive or
/// Boolean-structured interpolant (the `lra_interpolant_cnf` shape) is **not**
/// emitted by this path and stays at `Validated`; this function declines
/// (`Ok(None)`) whenever [`lra_interpolant`] declines (satisfiable, trivially
/// false, outside conjunctive `QF_LRA`, an exact `i128` overflow, or a failed
/// post-check) or whenever either `Farkas` refutation cannot be emitted/validated
/// for the produced conjunction. A caller that gets `Ok(None)` should fall back to
/// the `Validated` [`lra_interpolant`] path — this function NEVER returns an
/// uncertified interpolant dressed as certified.
///
/// # Errors
///
/// Propagates [`SolverError`] from the underlying Farkas decision / verification
/// `check_with_lra` calls (a `sat`-replay or self-check soundness alarm), or a
/// term-builder failure ([`SolverError::Backend`]).
pub fn lra_interpolant_certified(
    arena: &mut TermArena,
    a_assertions: &[TermId],
    b_assertions: &[TermId],
) -> Result<Option<LraInterpolantCertificate>, SolverError> {
    // 1. The verified interpolant `I` (identical to `lra_interpolant`'s output).
    let Some(interpolant) = build_verified_interpolant(arena, a_assertions, b_assertions)? else {
        return Ok(None);
    };

    // 2. Form the two conjunctions whose UNSAT is the two Craig soundness
    //    conditions. `¬I` is one inequality (I is one inequality), so each
    //    conjunction is a conjunctive linear-real system — Farkas-refutable.
    //    We build `¬I` as the explicit DUAL comparison (`¬(e ≤ 0) = e > 0`,
    //    `¬(e < 0) = e ≥ 0`) rather than a `not`-wrapper, so the Alethe atom
    //    emitter (which lowers bare comparisons, not `not`) covers it.
    let Some(not_interpolant) = dual_comparison(arena, interpolant) else {
        return Ok(None);
    };
    let mut a_and_not_i: Vec<TermId> = a_assertions.to_vec();
    a_and_not_i.push(not_interpolant);
    let mut i_and_b: Vec<TermId> = Vec::with_capacity(b_assertions.len() + 1);
    i_and_b.push(interpolant);
    i_and_b.extend_from_slice(b_assertions);

    // 3. Emit a self-validated Alethe `la_generic` refutation for each. The
    //    emitter re-checks the proof through `check_alethe_lra` and yields `None`
    //    on any doubt; we then decline to the `Validated` path rather than return
    //    an uncertified interpolant. (The external Carcara/Lean acceptance of these
    //    two refutations is exercised by the cross-check tests.)
    let Some(a_refutation) = prove_lra_unsat_alethe(arena, &a_and_not_i) else {
        return Ok(None);
    };
    let Some(b_refutation) = prove_lra_unsat_alethe(arena, &i_and_b) else {
        return Ok(None);
    };

    Ok(Some(LraInterpolantCertificate {
        interpolant,
        a_and_not_i,
        i_and_b,
        a_refutation,
        b_refutation,
    }))
}

/// Builds the explicit dual (logical negation) of the interpolant comparison `I`
/// as a single bare comparison term, so the `la_generic` Alethe emitter — which
/// lowers bare comparisons but not a `not`-wrapper — can render it.
///
/// `I` is produced by [`build_verified_interpolant`] as exactly `real_le(e, 0)`
/// or `real_lt(e, 0)`, whose duals are `real_gt(e, 0)` and `real_ge(e, 0)`. Any
/// other shape (which this path never builds) returns `None` ⇒ decline.
fn dual_comparison(arena: &mut TermArena, interpolant: TermId) -> Option<TermId> {
    let (op, lhs, rhs) = match arena.node(interpolant) {
        TermNode::App { op, args } if args.len() == 2 => (*op, args[0], args[1]),
        _ => return None,
    };
    match op {
        axeyum_ir::Op::RealLe => arena.real_gt(lhs, rhs).ok(),
        axeyum_ir::Op::RealLt => arena.real_ge(lhs, rhs).ok(),
        _ => None,
    }
}

/// Builds the real term `Σ coeff·vars[index] + constant`, dropping zero
/// coefficients. Returns `None` if a referenced dense index is out of range for
/// `vars` (a malformed certificate — decline rather than panic).
fn build_linear_term(
    arena: &mut TermArena,
    coeffs: &BTreeMap<usize, Rational>,
    vars: &[SymbolId],
    constant: Rational,
) -> Option<TermId> {
    let mut terms: Vec<TermId> = Vec::new();
    for (&index, &coeff) in coeffs {
        if coeff.is_zero() {
            continue;
        }
        let symbol = *vars.get(index)?;
        let var = arena.var(symbol);
        let coeff_term = arena.real_const(coeff);
        let product = arena.real_mul(coeff_term, var).ok()?;
        terms.push(product);
    }
    // Keep the constant only when it is nonzero, or when there are no variable
    // terms at all (so the expression is well-formed, e.g. the `⊤`/`⊥` case).
    if !constant.is_zero() || terms.is_empty() {
        terms.push(arena.real_const(constant));
    }
    let mut acc = terms[0];
    for &term in &terms[1..] {
        acc = arena.real_add(acc, term).ok()?;
    }
    Some(acc)
}

/// Re-checks the three Craig conditions for `interpolant` over the partition
/// `A = a_assertions`, `B = b_assertions`, returning `true` iff all hold.
fn verify_interpolant(
    arena: &mut TermArena,
    a_assertions: &[TermId],
    b_assertions: &[TermId],
    interpolant: TermId,
    coeffs: &BTreeMap<usize, Rational>,
    vars: &[SymbolId],
) -> Result<bool, SolverError> {
    // (3) Vocabulary: every symbol used by I appears in both A and B.
    let a_symbols = symbols_of(arena, a_assertions);
    let b_symbols = symbols_of(arena, b_assertions);
    for (&index, &coeff) in coeffs {
        if coeff.is_zero() {
            continue;
        }
        let Some(&symbol) = vars.get(index) else {
            return Ok(false);
        };
        if !a_symbols.contains(&symbol) || !b_symbols.contains(&symbol) {
            return Ok(false);
        }
    }

    // (1) A ⇒ I  ≡  A ∧ ¬I unsat.
    let not_interpolant = arena
        .not(interpolant)
        .map_err(|e| SolverError::Backend(format!("interpolant negation failed: {e}")))?;
    let mut a_and_not_i: Vec<TermId> = a_assertions.to_vec();
    a_and_not_i.push(not_interpolant);
    if !matches!(check_with_lra(arena, &a_and_not_i)?, CheckResult::Unsat) {
        return Ok(false);
    }

    // (2) I ∧ B unsat.
    let mut i_and_b: Vec<TermId> = Vec::with_capacity(b_assertions.len() + 1);
    i_and_b.push(interpolant);
    i_and_b.extend_from_slice(b_assertions);
    if !matches!(check_with_lra(arena, &i_and_b)?, CheckResult::Unsat) {
        return Ok(false);
    }

    Ok(true)
}

/// Collects every free symbol appearing in any of `terms`.
fn symbols_of(arena: &TermArena, terms: &[TermId]) -> BTreeSet<SymbolId> {
    let mut out = BTreeSet::new();
    for &term in terms {
        collect_symbols(arena, term, &mut out);
    }
    out
}

fn collect_symbols(arena: &TermArena, term: TermId, out: &mut BTreeSet<SymbolId>) {
    match arena.node(term) {
        TermNode::Symbol(symbol) => {
            out.insert(*symbol);
        }
        TermNode::App { args, .. } => {
            for &arg in args {
                collect_symbols(arena, arg, out);
            }
        }
        _ => {}
    }
}
