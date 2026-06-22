//! Craig interpolation for conjunctive `QF_LIA` (linear integer arithmetic) by
//! interpolating the **rational relaxation** and verifying over the integers
//! (Track 3, integer companion of [`crate::lra_interpolant`]).
//!
//! Given an unsatisfiable conjunction `A ∧ B` of linear *integer* literals, a
//! [`Craig interpolant`](crate::lra_interpolant) `I` satisfies:
//!
//! 1. `A ⇒ I` (`A ∧ ¬I` is unsatisfiable);
//! 2. `I ∧ B ⇒ ⊥` (`I ∧ B` is unsatisfiable);
//! 3. `I` mentions only the *shared* integer symbols — those in both `A` and `B`.
//!
//! # Method
//!
//! The key fact: an interpolant of the **rational relaxation** of an
//! integer-unsat `A ∧ B` is a *valid integer interpolant* whenever the relaxation
//! is itself unsat (a `Farkas` refutation witnesses it). Reason: `A ⇒ I` and
//! `I ∧ B ⇒ ⊥` over all reals imply they hold over the integers (a subset). When
//! the rational relaxation is *satisfiable* (the unsat needs integer cuts, e.g.
//! `2x = 1`), this method **declines** — that case needs Omega/cut interpolation
//! (out of scope), so we return `Ok(None)` soundly.
//!
//! Steps:
//!
//! 1. **Map `Int`→`Real`.** Replace each `Int` symbol with a fresh `Real` symbol
//!    (one shared map across `A` and `B`, so a shared integer term maps to a
//!    shared real term) and each integer relation/op with its real counterpart.
//!    Keep a back-map real-symbol → original int-symbol.
//! 2. **Interpolate the relaxation** with [`crate::lra_interpolant`]. A satisfiable
//!    / non-conjunctive-`QF_LRA` relaxation yields `Ok(None)` / `Unsupported` ⇒
//!    decline.
//! 3. **Translate back, clearing denominators.** Parse the real interpolant atom
//!    `(Σ cⱼ·yⱼ + c0) ⋈ 0` into rational coefficients, map each real `yⱼ` back to
//!    its integer `xⱼ`, multiply through by the positive LCM of all denominators
//!    to get integer coefficients, and build the integer atom with the IR's
//!    integer builders, preserving the relation `⋈`.
//! 4. **Verify before return.** Re-check all three Craig conditions on the
//!    **original** integer partitions with the integer-complete decider
//!    [`crate::check_with_lia_simplex`], declining on any non-`Unsat`/doubt.
//!
//! The `Int`→`Real` mapping, the `Farkas` combination produced inside
//! [`crate::lra_interpolant`], and the denominator-clearing are **entirely
//! untrusted**: soundness comes *only* from the integer re-check in step 4. A
//! wrong interpolant is never returned; an over-eager `Ok(None)` is acceptable.

use std::collections::{BTreeMap, BTreeSet};

use axeyum_ir::{Op, Rational, Sort, SymbolId, TermArena, TermId, TermNode};

use crate::{CheckResult, SolverError, check_with_lia_simplex, lra_interpolant};

/// Produces a verified Craig interpolant for the unsatisfiable integer
/// conjunction `A ∧ B`, where `a_assertions` is `A` and `b_assertions` is `B`
/// (each a conjunctively-interpreted slice of linear-integer literals over
/// `Int`-sorted terms — `IntLt`/`IntLe`/`IntGt`/`IntGe`/`Eq`, possibly
/// `BoolNot`-negated).
///
/// Returns `Ok(Some(I))` with a fully re-checked integer interpolant term `I`,
/// or `Ok(None)` when no `Farkas` interpolant of the rational relaxation is
/// available — `A ∧ B` is satisfiable, the integer-unsat needs cuts the rational
/// relaxation cannot witness, the input is outside conjunctive `QF_LIA`, an exact
/// `i128` overflow was hit while clearing denominators, or the candidate fails
/// any of its three independent post-checks. It **never** returns an unverified
/// interpolant.
///
/// # Errors
///
/// Propagates [`SolverError`] from the underlying [`crate::lra_interpolant`] call
/// or from the verification [`crate::check_with_lia_simplex`] calls (e.g. a
/// self-check soundness alarm). A term-builder failure is surfaced as
/// [`SolverError::Backend`].
pub fn lia_interpolant(
    arena: &mut TermArena,
    a_assertions: &[TermId],
    b_assertions: &[TermId],
) -> Result<Option<TermId>, SolverError> {
    // 1. Build the rational relaxation: a fresh Real symbol per Int symbol (the
    //    SAME int symbol → the SAME real symbol across A and B), every integer
    //    relation/op reinterpreted over the reals. A construct with no clean real
    //    analogue (div/mod/abs/coercions/non-arith subterm) aborts → decline.
    let mut relax = Relax::default();
    let Some(a_real) = relax.translate_all(arena, a_assertions)? else {
        return Ok(None);
    };
    let Some(b_real) = relax.translate_all(arena, b_assertions)? else {
        return Ok(None);
    };

    // 2. Interpolate the relaxation. None (sat / trivially false / non-conjunctive)
    //    or Unsupported ⇒ the integer-unsat is not witnessed by a rational Farkas
    //    refutation (it needs cuts) ⇒ decline soundly.
    let real_interpolant = match lra_interpolant(arena, &a_real, &b_real) {
        Ok(Some(interpolant)) => interpolant,
        Ok(None) | Err(SolverError::Unsupported(_)) => return Ok(None),
        Err(other) => return Err(other),
    };

    // 3. Parse the real interpolant atom `(Σ cⱼ·yⱼ + c0) ⋈ 0` back into rational
    //    coefficients over the relaxation's real vars, then translate to integer
    //    coefficients by clearing denominators. Any shape we do not recognize, a
    //    real var with no integer pre-image, or an overflow ⇒ decline.
    let Some(real_atom) = parse_real_atom(arena, real_interpolant) else {
        return Ok(None);
    };
    let Some(int_atom) = relax.to_integer_atom(&real_atom) else {
        return Ok(None);
    };
    let IntAtom {
        coeffs: int_coeffs,
        constant: int_constant,
        relation,
    } = int_atom;

    let Some(interpolant) = build_integer_atom(arena, &int_coeffs, int_constant, relation)? else {
        return Ok(None);
    };

    // 4. VERIFY-BEFORE-RETURN over the ORIGINAL integer partitions with the
    //    integer-complete decider. Decline on any doubt.
    if verify_interpolant(arena, a_assertions, b_assertions, interpolant, &int_coeffs)? {
        Ok(Some(interpolant))
    } else {
        Ok(None)
    }
}

/// Re-checks the three Craig conditions for `interpolant` over the **integer**
/// partition `A = a_assertions`, `B = b_assertions`, returning `true` iff all
/// three hold. This is the sole soundness anchor: every prior step (Int→Real
/// mapping, `Farkas` combination, denominator-clearing) is untrusted.
fn verify_interpolant(
    arena: &mut TermArena,
    a_assertions: &[TermId],
    b_assertions: &[TermId],
    interpolant: TermId,
    int_coeffs: &BTreeMap<SymbolId, i128>,
) -> Result<bool, SolverError> {
    // (3) Vocabulary: every integer symbol used by I appears in both A and B.
    let a_symbols = symbols_of(arena, a_assertions);
    let b_symbols = symbols_of(arena, b_assertions);
    for (&symbol, &coeff) in int_coeffs {
        if coeff == 0 {
            continue;
        }
        if !a_symbols.contains(&symbol) || !b_symbols.contains(&symbol) {
            return Ok(false);
        }
    }
    // The interpolant must not introduce symbols beyond its linear coefficients
    // (e.g. via a malformed build): cross-check its full free-symbol set too.
    for symbol in symbols_of(arena, &[interpolant]) {
        if !a_symbols.contains(&symbol) || !b_symbols.contains(&symbol) {
            return Ok(false);
        }
    }

    // (1) A ⇒ I  ≡  A ∧ ¬I unsat (integer decider).
    let not_interpolant = arena
        .not(interpolant)
        .map_err(|e| SolverError::Backend(format!("interpolant negation failed: {e}")))?;
    let mut a_and_not_i: Vec<TermId> = a_assertions.to_vec();
    a_and_not_i.push(not_interpolant);
    if !matches!(
        check_with_lia_simplex(arena, &a_and_not_i)?,
        CheckResult::Unsat
    ) {
        return Ok(false);
    }

    // (2) I ∧ B unsat (integer decider).
    let mut i_and_b: Vec<TermId> = Vec::with_capacity(b_assertions.len() + 1);
    i_and_b.push(interpolant);
    i_and_b.extend_from_slice(b_assertions);
    if !matches!(check_with_lia_simplex(arena, &i_and_b)?, CheckResult::Unsat) {
        return Ok(false);
    }

    Ok(true)
}

/// The recognized comparison relation of an interpolant atom (`expr ⋈ 0`).
#[derive(Clone, Copy, PartialEq, Eq)]
enum Relation {
    /// `expr < 0`.
    Lt,
    /// `expr ≤ 0`.
    Le,
    /// `expr = 0`.
    Eq,
}

/// A parsed linear atom `(Σ coeff·var + constant) ⋈ 0` over real vars.
struct RealAtom {
    coeffs: BTreeMap<SymbolId, Rational>,
    constant: Rational,
    relation: Relation,
}

/// A linear atom `(Σ coeff·var + constant) ⋈ 0` with **integer** coefficients.
struct IntAtom {
    coeffs: BTreeMap<SymbolId, i128>,
    constant: i128,
    relation: Relation,
}

/// Parses the real interpolant term into a linear atom `(Σ cⱼ·yⱼ + c0) ⋈ 0`.
///
/// [`crate::lra_interpolant`] emits exactly `real_lt(expr, 0)` or
/// `real_le(expr, 0)`; we additionally accept `Eq(expr, 0)` defensively. Any
/// other shape (a non-atomic Boolean, a nonzero / non-constant right side, a
/// non-linear subterm) returns `None` so the caller declines.
fn parse_real_atom(arena: &TermArena, term: TermId) -> Option<RealAtom> {
    let TermNode::App { op, args } = arena.node(term) else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let (lhs, rhs) = (args[0], args[1]);
    let relation = match op {
        Op::RealLt => Relation::Lt,
        Op::RealLe => Relation::Le,
        Op::Eq => Relation::Eq,
        _ => return None,
    };

    // Move both sides into one linear form: lhs - rhs ⋈ 0.
    let mut linear = LinearReal::default();
    linear.add_term(arena, lhs, Rational::integer(1))?;
    linear.add_term(arena, rhs, Rational::integer(-1))?;
    Some(RealAtom {
        coeffs: linear.coeffs,
        constant: linear.constant,
        relation,
    })
}

/// Accumulator for a linear-real expression `Σ coeff·var + constant`.
#[derive(Default)]
struct LinearReal {
    coeffs: BTreeMap<SymbolId, Rational>,
    constant: Rational,
}

impl LinearReal {
    /// Adds `scale · term` into the accumulator, where `term` is a linear-real
    /// expression. Returns `None` on a non-linear / unsupported subterm or an
    /// `i128` overflow (the caller then declines).
    fn add_term(&mut self, arena: &TermArena, term: TermId, scale: Rational) -> Option<()> {
        match arena.node(term) {
            TermNode::RealConst(value) => {
                let scaled = scale.checked_mul(*value)?;
                self.constant = self.constant.checked_add(scaled)?;
                Some(())
            }
            TermNode::IntConst(value) => {
                let scaled = scale.checked_mul(Rational::integer(*value))?;
                self.constant = self.constant.checked_add(scaled)?;
                Some(())
            }
            TermNode::Symbol(symbol) => {
                let entry = self.coeffs.entry(*symbol).or_insert_with(Rational::zero);
                *entry = entry.checked_add(scale)?;
                Some(())
            }
            TermNode::App { op, args } => self.add_app(arena, *op, args, scale),
            _ => None,
        }
    }

    /// Adds `scale · op(args)` for a supported linear operator.
    fn add_app(
        &mut self,
        arena: &TermArena,
        op: Op,
        args: &[TermId],
        scale: Rational,
    ) -> Option<()> {
        match op {
            Op::RealAdd if args.len() == 2 => {
                self.add_term(arena, args[0], scale)?;
                self.add_term(arena, args[1], scale)
            }
            Op::RealSub if args.len() == 2 => {
                self.add_term(arena, args[0], scale)?;
                self.add_term(arena, args[1], scale.checked_neg()?)
            }
            Op::RealNeg if args.len() == 1 => self.add_term(arena, args[0], scale.checked_neg()?),
            // A product is linear only when one factor is a real constant.
            Op::RealMul if args.len() == 2 => {
                if let TermNode::RealConst(value) = arena.node(args[0]) {
                    self.add_term(arena, args[1], scale.checked_mul(*value)?)
                } else if let TermNode::RealConst(value) = arena.node(args[1]) {
                    self.add_term(arena, args[0], scale.checked_mul(*value)?)
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

/// The relaxation state: a deterministic `Int` symbol ↔ fresh `Real` symbol
/// bijection plus a translation memo.
#[derive(Default)]
struct Relax {
    /// Original integer symbol → fresh real symbol (same int → same real, so a
    /// shared integer term maps to a shared real term).
    int_to_real: BTreeMap<SymbolId, SymbolId>,
    /// Back-map real symbol → original integer symbol.
    real_to_int: BTreeMap<SymbolId, SymbolId>,
    /// Translated-term memo.
    memo: BTreeMap<TermId, Option<TermId>>,
}

impl Relax {
    /// Translates a whole assertion slice; `None` (decline) if any assertion has
    /// no clean real analogue.
    fn translate_all(
        &mut self,
        arena: &mut TermArena,
        assertions: &[TermId],
    ) -> Result<Option<Vec<TermId>>, SolverError> {
        let mut out = Vec::with_capacity(assertions.len());
        for &assertion in assertions {
            match self.translate(arena, assertion)? {
                Some(term) => out.push(term),
                None => return Ok(None),
            }
        }
        Ok(Some(out))
    }

    /// The fresh real symbol standing for `int_sym` (created on first use). The
    /// fresh `Real` symbol is declared in the caller's arena; it carries no
    /// integer model meaning — it exists only for the relaxation interpolant.
    fn real_of_int(
        &mut self,
        arena: &mut TermArena,
        int_sym: SymbolId,
    ) -> Result<TermId, SolverError> {
        if let Some(&real_sym) = self.int_to_real.get(&int_sym) {
            return Ok(arena.var(real_sym));
        }
        let name = format!("!lia-interp.relax.{}", int_sym.index());
        let real_sym = arena
            .declare(&name, Sort::Real)
            .map_err(|e| SolverError::Backend(e.to_string()))?;
        self.int_to_real.insert(int_sym, real_sym);
        self.real_to_int.insert(real_sym, int_sym);
        Ok(arena.var(real_sym))
    }

    /// Translates `t` to its faithful real analogue, or `None` if `t` contains a
    /// construct with no clean real reinterpretation.
    fn translate(
        &mut self,
        arena: &mut TermArena,
        t: TermId,
    ) -> Result<Option<TermId>, SolverError> {
        if let Some(&cached) = self.memo.get(&t) {
            return Ok(cached);
        }
        let out = self.translate_uncached(arena, t)?;
        self.memo.insert(t, out);
        Ok(out)
    }

    fn translate_uncached(
        &mut self,
        arena: &mut TermArena,
        t: TermId,
    ) -> Result<Option<TermId>, SolverError> {
        let err = |e: axeyum_ir::IrError| SolverError::Backend(e.to_string());
        let node = arena.node(t).clone();
        let out = match node {
            // Boolean / real constants pass through; a real subterm stays real.
            TermNode::BoolConst(_) | TermNode::RealConst(_) => t,
            // An integer constant `n` reinterprets as the real number `n`.
            TermNode::IntConst(n) => arena.real_const(Rational::integer(n)),
            // No real analogue.
            TermNode::BvConst { .. } | TermNode::WideBvConst(_) => return Ok(None),
            TermNode::Symbol(s) => match arena.sort_of(t) {
                Sort::Int => self.real_of_int(arena, s)?,
                Sort::Real | Sort::Bool => t,
                _ => return Ok(None),
            },
            TermNode::App { op, args } => {
                let mut low = Vec::with_capacity(args.len());
                for &a in &args {
                    match self.translate(arena, a)? {
                        Some(term) => low.push(term),
                        None => return Ok(None),
                    }
                }
                match op {
                    Op::IntNeg => arena.real_neg(low[0]).map_err(err)?,
                    Op::IntAdd => arena.real_add(low[0], low[1]).map_err(err)?,
                    Op::IntSub => arena.real_sub(low[0], low[1]).map_err(err)?,
                    Op::IntMul => arena.real_mul(low[0], low[1]).map_err(err)?,
                    Op::IntLt => arena.real_lt(low[0], low[1]).map_err(err)?,
                    Op::IntLe => arena.real_le(low[0], low[1]).map_err(err)?,
                    Op::IntGt => arena.real_gt(low[0], low[1]).map_err(err)?,
                    Op::IntGe => arena.real_ge(low[0], low[1]).map_err(err)?,
                    // Sort-polymorphic Boolean structure / already-real operators
                    // rebuild over the translated operands unchanged.
                    Op::Eq
                    | Op::Ite
                    | Op::BoolAnd
                    | Op::BoolOr
                    | Op::BoolNot
                    | Op::BoolXor
                    | Op::BoolImplies
                    | Op::RealNeg
                    | Op::RealAdd
                    | Op::RealSub
                    | Op::RealMul
                    | Op::RealLt
                    | Op::RealLe
                    | Op::RealGt
                    | Op::RealGe => axeyum_rewrite::build_app(arena, op, &low).map_err(err)?,
                    // div/mod/abs, coercions, bit-vectors, arrays, UFs, datatypes,
                    // quantifiers: no clean real analogue → abort.
                    _ => return Ok(None),
                }
            }
        };
        Ok(Some(out))
    }

    /// Translates a parsed real atom back to an integer atom over the original
    /// integer symbols, clearing denominators so the coefficients are integral.
    ///
    /// Returns `None` if any real var with a nonzero coefficient has no integer
    /// pre-image (a symbol that is not a relaxation surrogate — should not occur
    /// for a relaxation interpolant) or an `i128` overflow is hit while clearing
    /// denominators.
    fn to_integer_atom(&self, atom: &RealAtom) -> Option<IntAtom> {
        // The positive LCM of every coefficient and the constant denominator.
        let mut multiplier: i128 = 1;
        for coeff in atom.coeffs.values() {
            multiplier = lcm(multiplier, coeff.denominator())?;
        }
        multiplier = lcm(multiplier, atom.constant.denominator())?;

        let factor = Rational::integer(multiplier);

        let mut coeffs: BTreeMap<SymbolId, i128> = BTreeMap::new();
        for (&real_sym, &coeff) in &atom.coeffs {
            let scaled = coeff.checked_mul(factor)?;
            // After multiplying by the LCM of denominators the result is integral.
            if !scaled.is_integer() {
                return None;
            }
            let value = scaled.numerator();
            if value == 0 {
                continue;
            }
            let int_sym = *self.real_to_int.get(&real_sym)?;
            // A real surrogate maps to exactly one integer symbol; sum defensively.
            let entry = coeffs.entry(int_sym).or_insert(0);
            *entry = entry.checked_add(value)?;
        }
        // Prune any int symbol whose accumulated coefficient cancelled to zero.
        coeffs.retain(|_, &mut value| value != 0);

        let scaled_const = atom.constant.checked_mul(factor)?;
        if !scaled_const.is_integer() {
            return None;
        }
        let constant = scaled_const.numerator();

        Some(IntAtom {
            coeffs,
            constant,
            relation: atom.relation,
        })
    }
}

/// Builds the integer atom `(Σ coeff·sym + constant) ⋈ 0` from integer
/// coefficients, preserving the relation. Returns `Ok(None)` on a term-builder
/// failure (we never panic on a malformed candidate).
fn build_integer_atom(
    arena: &mut TermArena,
    coeffs: &BTreeMap<SymbolId, i128>,
    constant: i128,
    relation: Relation,
) -> Result<Option<TermId>, SolverError> {
    let mut terms: Vec<TermId> = Vec::new();
    for (&symbol, &coeff) in coeffs {
        if coeff == 0 {
            continue;
        }
        let var = arena.var(symbol);
        let coeff_term = arena.int_const(coeff);
        let Ok(product) = arena.int_mul(coeff_term, var) else {
            return Ok(None);
        };
        terms.push(product);
    }
    // Include the constant when it is nonzero, or when there are no variable
    // terms (so the expression is well-formed).
    if constant != 0 || terms.is_empty() {
        terms.push(arena.int_const(constant));
    }

    let mut acc = terms[0];
    for &term in &terms[1..] {
        let Ok(sum) = arena.int_add(acc, term) else {
            return Ok(None);
        };
        acc = sum;
    }

    let zero = arena.int_const(0);
    let atom = match relation {
        Relation::Lt => arena.int_lt(acc, zero),
        Relation::Le => arena.int_le(acc, zero),
        Relation::Eq => arena.eq(acc, zero),
    };
    match atom {
        Ok(term) => Ok(Some(term)),
        Err(e) => Err(SolverError::Backend(format!(
            "integer interpolant atom build failed: {e}"
        ))),
    }
}

/// The least common multiple of two `i128` values, overflow-checked. Both inputs
/// are denominators, always positive in a normalized [`Rational`]; returns `None`
/// on overflow.
fn lcm(a: i128, b: i128) -> Option<i128> {
    if a == 0 || b == 0 {
        return Some(0);
    }
    let g = gcd(a, b);
    // a / g is exact (g divides a); then (a/g) * b is the lcm.
    (a / g).checked_mul(b).map(i128::abs)
}

/// The greatest common divisor of two `i128` values (Euclid; uses absolute
/// values so it is well-defined for any sign).
fn gcd(first: i128, second: i128) -> i128 {
    let mut larger = first.unsigned_abs();
    let mut smaller = second.unsigned_abs();
    while smaller != 0 {
        let remainder = larger % smaller;
        larger = smaller;
        smaller = remainder;
    }
    i128::try_from(larger).unwrap_or(1)
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
