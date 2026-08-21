//! Kernel-checked reconstruction of a **string length / code-point** refutation.
//!
//! The certificate ([`crate::string_length_cert`]) abstracts every string term of
//! a query to an integer length or code point, names the theory lemmas the
//! argument uses, and closes with one nonnegative linear combination per
//! case-split branch. This module turns the **conjunctive** case of that
//! argument into a Lean term of type `False` that the trusted kernel
//! type-checks, over the **constructed integers** — `LraReconstructCtx::try_new_over_integers`
//! builds `build_int_prelude`, whose 30 ordered-ring declarations are theorems
//! and whose trusted surface is 0. Not `AxReal`, this repository's only nonzero
//! row (`axreal: axiom=30`), and not `CReal` either: lengths and code points are
//! integers, and `ℤ` models every law a Farkas combination uses.
//!
//! # What the kernel checks, and what it rests on
//!
//! The refutation is a linear combination, so the reconstruction is the ordinary
//! Farkas fold ([`super::try_general_farkas_atoms`] /
//! [`super::try_mixed_farkas_atoms`]) applied to the certificate's own facts:
//! every step is an ordered-ring law over terms built from those facts, and Lean
//! can reject it on the merits. The abstraction itself — that `(str.len yy)` is
//! an integer at all, that `|u . v| = |u| + |v|`, that `str.to_code` of a
//! singleton is in `[0, 0x2FFFF]` — is **not** reconstructed: there is no string
//! theory in the kernel to reconstruct it against.
//!
//! So the hypotheses of the emitted theorem are exactly the certificate's facts,
//! and each is one of two things, with nothing else able to enter:
//!
//! - a **premise conjunct**, i.e. an actual `(assert …)` line of the carried
//!   script (or one conjunct of one, after `and`-flattening); or
//! - a **named theory lemma instance** — one of the five schemas — whose side
//!   condition stage 1 of the checker bound to an actual `(assert …)` line.
//!
//! That binding is not taken on trust here. [`reconstruct_string_length`] gets
//! its facts **only** from [`checked_refutation`], which re-derives the sort
//! environment and the premise conjuncts from the carried commands and re-binds
//! every lemma before returning anything; there is no path that reads the
//! certificate's stored combination directly. The one entailment step this
//! reconstruction does not carry out in the kernel is the normalization
//! `lhs ⋈ rhs ↦ (lhs − rhs) ⋈ 0` that both the certificate's checker and this
//! module apply when they turn a source comparison into a linear atom; every
//! shipped arithmetic route in this crate has the same seam, and naming it is
//! the honest boundary rather than a disclaimer.
//!
//! # Declined, never approximated
//!
//! - **A case split.** Discharging an assumed disjunct needs `Or.elim` in the
//!   kernel, and refuting one arm of a several-arm split proves nothing about
//!   the query. A multi-branch certificate declines, and so does a
//!   single-disjunct `(or A)` one — `A` is a hypothesis the query does not
//!   state, only entails.
//! - **A combination too large to build.** The ordered-ring engine represents a
//!   constant `k` as `k` copies of `one`, so the cost of the fold is linear in
//!   the combined constant and in every multiplier — and the QUERY chooses that
//!   number. `r1_QF_SLIA_str-code-unsat-2` chooses `10^28 − 0x2FFFF` on one arm.
//!   Over [`MAX_UNARY_TERMS`] the reconstruction declines.

use std::collections::BTreeMap;

use axeyum_ir::Rational;
use axeyum_lean_kernel::ExprId;

use super::{LraReconstructCtx, ReconstructError};
use crate::FarkasAtom;
use crate::string_length_cert::{
    AbsVar, CheckedFact, FactRole, Rel, StringLengthRefutationCertificate, checked_refutation,
};

/// The rendered theorem name, matching the shared `axeyum_refutation` audit name
/// the real-Lean cross-check greps for in `#print axioms` output.
const LEAN_THEOREM: &str = "axeyum_refutation";

/// The budget on the ordered-ring fold's **unary** size: the total number of
/// `one`/variable generators the scaled-and-summed combination expands to, plus
/// the combined constant the closing `lt zero K` chain counts up to.
///
/// Not merely a resource guard. The fold builds a left-nested `add` chain and
/// the kernel walks it recursively, so an oversized combination does not run
/// slowly — it **overflows the stack and aborts the process**. Measured
/// 2026-08-20 on the `|x| <= -k` shape (cost `2k + 2`):
///
/// | cost | outcome |
/// |---:|---|
/// | 130 | 1.1 MB module |
/// | 258 | 3.6 MB module |
/// | 514 | 13.2 MB module |
/// | 1026 | **stack overflow, `SIGABRT`** |
///
/// The first version of this constant was `4_096`, which admits every row above
/// including the last: a guard calibrated to let through the failure it exists
/// to prevent. Only mutating it away and watching the test *abort* rather than
/// fail showed it. `128` is an 8× margin under the measured crash, and the two
/// committed corpus files need a cost of **4**.
///
/// Raising it needs the table re-measured, and on the smallest thread stack the
/// route can run on — the crash point is a stack depth, not a constant.
const MAX_UNARY_TERMS: i128 = 128;

/// Reconstruct a conjunctive string length/code-point refutation to `False`.
///
/// # Errors
///
/// [`ReconstructError::UnsupportedTerm`] when the certificate does not re-check,
/// when it needs case analysis, when the fold would exceed [`MAX_UNARY_TERMS`],
/// or when the Farkas engine declines the combination's shape;
/// [`ReconstructError::KernelRejected`] when an assembled term fails to `infer`
/// to `False` (an emitter bug, declined — never a wrong `False`).
pub(crate) fn reconstruct_string_length(
    ctx: &mut LraReconstructCtx,
    certificate: &StringLengthRefutationCertificate,
) -> Result<ExprId, ReconstructError> {
    // The SOLE source of facts, and therefore the sole gate: stage 1 re-derives
    // the premises from the carried commands and re-binds every lemma to the
    // conjunct that licenses it, stage 2 re-derives the combination. Nothing
    // below reads the certificate's stored combination.
    let checked =
        checked_refutation(certificate).ok_or_else(|| ReconstructError::UnsupportedTerm {
            term: "the string-length certificate does not re-check against its own carried \
                   commands; there is no refutation to reconstruct"
                .to_owned(),
        })?;

    let [facts] = checked.branches.as_slice() else {
        return Err(ReconstructError::UnsupportedTerm {
            term: format!(
                "string-length reconstruction handles the conjunctive form (one branch); \
                 this certificate splits into {} branches, and discharging an assumed \
                 disjunct needs kernel case analysis",
                checked.branches.len()
            ),
        });
    };
    if facts.iter().any(|f| matches!(f.role, FactRole::Arm(_))) {
        return Err(ReconstructError::UnsupportedTerm {
            term: "the single branch assumes a disjunct of an asserted `or`; the query states \
                   the disjunction, not the disjunct, so minting it as a hypothesis would \
                   assume something no assertion says"
                .to_owned(),
        });
    }

    // Dense indices, and a constant per abstraction variable NAMED after the
    // source it abstracts — `len_yy`, `code_x` — so the emitted hypotheses can be
    // read against the `.smt2` file. Seeded before any use, because the map is
    // first-write-wins.
    let mut index_of: BTreeMap<&AbsVar, usize> = BTreeMap::new();
    for (index, variable) in checked.variables.iter().enumerate() {
        index_of.insert(variable, index);
        ctx.var_const_named(index, &variable.lean_base());
    }

    // The engine's `a <= 0` / `a < 0` system, and the equality hypotheses that
    // must not be weakened into inequalities.
    let (atoms, multipliers, any_strict) = to_farkas_system(facts, &index_of)?;

    // The resource guard. Without it the fold below is linear in a constant the
    // query chose, and one committed corpus file chooses `10^28`.
    match unary_cost(&atoms, &multipliers) {
        Some(cost) if cost <= MAX_UNARY_TERMS => {}
        Some(cost) => {
            return Err(ReconstructError::UnsupportedTerm {
                term: format!(
                    "the ordered-ring fold would expand to {cost} unary terms, over the \
                     {MAX_UNARY_TERMS} budget; the engine counts a constant `k` as `k` copies \
                     of `one`"
                ),
            });
        }
        None => {
            return Err(ReconstructError::UnsupportedTerm {
                term: "the combination's size is not an integer this engine can bound (a \
                       non-integer coefficient, or `i128` overflow)"
                    .to_owned(),
            });
        }
    }

    let equalities = derive_equality_hypotheses(ctx, facts, &atoms)?;

    // A strict fact makes the whole sum strict, and the two engines own disjoint
    // shapes: `try_general_farkas_atoms` refuses any strict atom, and
    // `try_mixed_farkas_atoms` refuses a system with none.
    let minted_before = ctx.minted_hypothesis_count();
    let outcome = if any_strict {
        super::try_mixed_farkas_atoms(ctx, &atoms, &multipliers)?
    } else {
        super::try_general_farkas_atoms(ctx, &atoms, &multipliers)?
    };
    let Some(proof) = outcome else {
        return Err(ReconstructError::UnsupportedTerm {
            term: "the ordered-ring Farkas engine declined this combination's shape".to_owned(),
        });
    };

    // An override the engine never asked for is a SILENT fallback: the equality
    // is minted, ignored, and the inequality assumed beside it. The symptom is
    // arithmetic — the engine minted one axiom per non-equality fact and no
    // more — so check it rather than trust that the two sides built the same
    // proposition.
    //
    // Mutation-checked 2026-08-20, and the result is the interesting part.
    // Deleting THIS check alone kills nothing, because while both sides agree
    // the counts match. Deleting the REGISTRATION above kills seven tests —
    // through this check — and deleting both kills exactly one, the equality
    // test, with a quietly weaker module shipping past the other six. So the
    // check's value is measured, not asserted: it is what turns a silent
    // semantic weakening into a loud decline.
    let minted_by_engine = ctx.minted_hypothesis_count() - minted_before;
    let expected = facts.len() - equalities;
    if minted_by_engine != expected {
        return Err(ReconstructError::KernelRejected {
            rule: "string_length".to_owned(),
            detail: format!(
                "the fold minted {minted_by_engine} hypotheses where {expected} were expected;                  an equality fact was assumed as an inequality instead of derived from the                  equality this route mints"
            ),
        });
    }

    // Soundness gate, again, from outside the engine: the assembled term must
    // kernel-infer to `False`. The engine gates internally too, so
    // mutation-checking this kills no test — and that is the CORRECT result
    // rather than a missing fixture. It is a cross-check between two
    // implementations of the same obligation; a test can only kill it once one
    // of them is already wrong, which is exactly the state it exists to catch.
    let inferred = ctx
        .kernel_mut()
        .infer(proof)
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "string_length".to_owned(),
            detail: format!("string-length infer failed: {e:?}"),
        })?;
    let false_ = {
        let f = ctx.arith().logic.false_;
        ctx.kernel_mut().const_(f, vec![])
    };
    if ctx.kernel_mut().def_eq(inferred, false_) {
        Ok(proof)
    } else {
        Err(ReconstructError::KernelRejected {
            rule: "string_length".to_owned(),
            detail: "string-length refutation did not infer to False".to_owned(),
        })
    }
}

/// Turn the checked facts into the Farkas engines' `a ⋈ 0` system.
///
/// The engines want NONNEGATIVE multipliers, so `a = -E` with multiplier `λ`
/// whenever `λ > 0`, and `a = +E` with multiplier `-λ` for the negative
/// multiplier an EQUALITY licenses. Either way the contribution is `-λ·E`, so
/// the combined constant is the negation of the certificate's — which is what
/// turns "cancels to something negative" into the engines' "cancels to something
/// positive".
fn to_farkas_system(
    facts: &[CheckedFact],
    index_of: &BTreeMap<&AbsVar, usize>,
) -> Result<(Vec<FarkasAtom>, Vec<Rational>, bool), ReconstructError> {
    let mut atoms: Vec<FarkasAtom> = Vec::with_capacity(facts.len());
    let mut multipliers: Vec<Rational> = Vec::with_capacity(facts.len());
    let mut any_strict = false;
    let zero = Rational::zero();
    for fact in facts {
        let (negate, mu) = match fact.rel {
            // An inequality's multiplier is positive. That is enforced TWICE
            // around this line and neither copy is here: `checked_refutation`
            // refuses a non-positive multiplier on an inequality upstream, and
            // both Farkas engines refuse `mu.numerator() <= 0` downstream. A
            // third statement of it was written, mutated away, and killed no
            // test — so it is not here, rather than here and decorative.
            Rel::Ge | Rel::Gt => (true, fact.multiplier),
            Rel::Eq => {
                if fact.multiplier > zero {
                    (true, fact.multiplier)
                } else {
                    let Some(negated) = fact.multiplier.checked_neg() else {
                        return Err(overflowed());
                    };
                    (false, negated)
                }
            }
        };
        let sign = Rational::integer(if negate { -1 } else { 1 });
        let mut coeffs: Vec<(usize, Rational)> = Vec::with_capacity(fact.expr.coeffs.len());
        for (variable, coefficient) in &fact.expr.coeffs {
            let Some(&index) = index_of.get(variable) else {
                return Err(ReconstructError::UnsupportedTerm {
                    term: "a fact mentions a variable the checked refutation did not report"
                        .to_owned(),
                });
            };
            let Some(scaled) = coefficient.checked_mul(sign) else {
                return Err(overflowed());
            };
            coeffs.push((index, scaled));
        }
        coeffs.sort_by_key(|&(index, _)| index);
        let Some(constant) = fact.expr.constant.checked_mul(sign) else {
            return Err(overflowed());
        };
        let strict = fact.rel == Rel::Gt;
        any_strict |= strict;
        atoms.push(FarkasAtom {
            coeffs,
            constant,
            strict,
        });
        multipliers.push(mu);
    }
    Ok((atoms, multipliers, any_strict))
}

/// Mint each EQUALITY fact as an equality and derive the inequality the fold
/// wants, returning how many were derived.
///
/// The engines assume one `a <= 0` per atom, which is right for an asserted
/// inequality and wrong for an asserted equality: `a = 0` is strictly stronger,
/// so assuming only the `<=` half assumes something the source does not state.
/// The relation is the distinction the certificate itself turns on — an equality
/// is the only fact a negative multiplier may scale — so losing it here would be
/// the reconstruction quietly weakening what it claims to have reconstructed.
///
/// The derivation is `le_refl zero : le zero zero` transported along `zero = a`.
fn derive_equality_hypotheses(
    ctx: &mut LraReconstructCtx,
    facts: &[CheckedFact],
    atoms: &[FarkasAtom],
) -> Result<usize, ReconstructError> {
    let mut derived = 0usize;
    for (fact, atom) in facts.iter().zip(atoms) {
        if fact.rel != Rel::Eq {
            continue;
        }
        let lin = super::LinR {
            coeffs: atom.coeffs.clone(),
            constant: atom.constant,
        };
        let Some(gens) = LraReconstructCtx::lin_to_gens(&lin) else {
            return Err(ReconstructError::UnsupportedTerm {
                term: "an equality fact is not an integer linear form".to_owned(),
            });
        };
        let canonical = ctx.gens_to_expr(&gens);
        let zero = ctx.mk_zero();
        // The hypothesis the query licenses: `a = 0`.
        let equality = ctx.mk_eq_r(canonical, zero);
        let h = ctx.hyp_axiom(equality)?;
        let le_refl = ctx.kernel.const_(ctx.arith.le_refl, vec![]);
        let le_zero_zero = ctx.kernel.app(le_refl, zero);
        // `eq_symm_r(a, b, h : Eq a b) : Eq b a` — the argument order is the
        // HYPOTHESIS's, not the conclusion's.
        let eq_zero_canonical = ctx.eq_symm_r(canonical, zero, h);
        let inequality_proof =
            ctx.le_cast_left(zero, canonical, zero, le_zero_zero, eq_zero_canonical);
        let inequality = ctx.mk_le(canonical, zero);
        ctx.register_hyp_override(inequality, inequality_proof);
        derived += 1;
    }
    Ok(derived)
}

fn overflowed() -> ReconstructError {
    ReconstructError::UnsupportedTerm {
        term: "the combination overflows `i128` while being carried into the kernel".to_owned(),
    }
}

/// How many unary generators the ordered-ring fold will materialize.
///
/// The engine clears the multipliers' denominators to integers `μᵢ = λᵢ·L`, then
/// expands atom `i` into `μᵢ · (Σ|cᵢⱼ| + |kᵢ|)` generators and finally counts the
/// combined constant `K = Σ μᵢ·kᵢ` up from zero one `one` at a time. `None` when
/// a coefficient is not an integer (the engine declines those anyway, but then
/// the size is not defined) or when the estimate overflows `i128`.
fn unary_cost(atoms: &[FarkasAtom], multipliers: &[Rational]) -> Option<i128> {
    let mut lcm: i128 = 1;
    for m in multipliers {
        lcm = super::lcm_i128(lcm, m.denominator())?;
    }
    let factor = Rational::integer(lcm);
    let mut total: i128 = 0;
    let mut k_total: i128 = 0;
    for (atom, m) in atoms.iter().zip(multipliers) {
        let mu = m.checked_mul(factor)?;
        if mu.denominator() != 1 {
            return None;
        }
        let mu = mu.numerator().checked_abs()?;
        let mut weight: i128 = 0;
        for (_, c) in &atom.coeffs {
            if c.denominator() != 1 {
                return None;
            }
            weight = weight.checked_add(c.numerator().checked_abs()?)?;
        }
        if atom.constant.denominator() != 1 {
            return None;
        }
        let k = atom.constant.numerator();
        weight = weight.checked_add(k.checked_abs()?)?;
        total = total.checked_add(mu.checked_mul(weight)?)?;
        k_total = k_total.checked_add(mu.checked_mul(k)?)?;
    }
    total.checked_add(k_total.max(0))
}

/// Reconstruct a string length/code-point refutation to a self-contained,
/// kernel-checked Lean module over the **constructed integers**.
///
/// The certificate is re-checked from its own carried commands first (the sole
/// gate); the module is then rendered from a `False` term the kernel has already
/// `infer`ed and `def_eq`-compared.
///
/// # Errors
///
/// As [`reconstruct_string_length`], plus [`ReconstructError::KernelRejected`]
/// if the integer development does not build in a fresh kernel.
pub fn reconstruct_string_length_to_lean_module(
    certificate: &StringLengthRefutationCertificate,
) -> Result<String, ReconstructError> {
    let mut ctx = LraReconstructCtx::try_new_over_integers()?;
    let proof = reconstruct_string_length(&mut ctx, certificate)?;
    let false_ = {
        let f = ctx.arith().logic.false_;
        ctx.kernel_mut().const_(f, vec![])
    };
    Ok(ctx
        .kernel()
        .render_lean_module_compact(LEAN_THEOREM, false_, proof))
}

#[cfg(test)]
mod tests;
