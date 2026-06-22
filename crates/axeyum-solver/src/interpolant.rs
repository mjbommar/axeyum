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

use axeyum_ir::{Rational, SymbolId, TermArena, TermId, TermNode};

use crate::{CheckResult, SolverError, check_with_lra, lra_farkas_certificate};

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
