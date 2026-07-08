//! Disjunctive (CNF) Craig interpolation for `QF_LIA` — the integer mirror of
//! [`lra_interpolant_cnf`](crate::lra_interpolant_cnf) that lifts integer
//! interpolation beyond the conjunctive
//! [`lia_interpolant`](crate::lia_interpolant) to assertions with arbitrary
//! Boolean structure (`∧`/`∨`/`¬`/`ite`/`=`) over linear-integer order atoms
//! (Track 3, the disjunctive companion of the integer Farkas interpolator).
//!
//! [`lia_interpolant_cnf`] takes two slices of `QF_LIA` assertions `A` and `B`
//! (each interpreted as the **conjunction** of its members, but the members may
//! themselves be Boolean combinations of linear-integer order atoms — `<`, `<=`,
//! `>`, `>=`, `=`) whose conjunction `A ∧ B` is unsatisfiable over the integers,
//! and returns a verified Craig interpolant `I` (a Boolean [`TermId`] over the
//! shared integer symbols) such that `A ⇒ I`, `I ∧ B ⇒ ⊥`, and every integer
//! symbol of `I` is shared by `A` and `B`. It returns `Ok(None)` whenever
//! `A ∧ B` is satisfiable, the input is outside the supported fragment, the
//! construction cannot complete, or any re-check fails. It **never** returns an
//! unverified interpolant.
//!
//! # Method (relaxation + disjunctive real interpolation + integer re-check)
//!
//! The construction is the `McMillan` interpolating-SMT structure of
//! [`lra_interpolant_cnf`](crate::lra_interpolant_cnf), applied to the
//! **rational relaxation** of the integer query:
//!
//! 1. **Map `Int`→`Real`.** Each `Int` symbol is replaced by a fresh `Real`
//!    surrogate (one shared map across `A` and `B`, so a shared integer term
//!    maps to a shared real term) and each integer relation/op by its real
//!    counterpart, faithfully preserving the Boolean structure. A construct
//!    with no clean real analogue (div/mod/abs/coercions/non-arith subterm)
//!    declines.
//! 2. **Disjunctive real interpolation.**
//!    [`lra_interpolant_cnf`](crate::lra_interpolant_cnf) interpolates the
//!    relaxed partition. It internally Boolean-abstracts each distinct real
//!    order atom, harvests theory lemmas from the certified lazy-SMT decider,
//!    purifies mixed lemmas with the conjunctive Farkas
//!    [`lra_interpolant`](crate::lra_interpolant), and folds the propositional
//!    interpolant — returning a real interpolant or declining (`Ok(None)`).
//!    When the integer unsat needs cuts the rational relaxation cannot witness
//!    (e.g. `2x = 1`), the relaxation is *satisfiable*, so the lazy-SMT decider
//!    reports `sat` and the real interpolation declines — propagated here as a
//!    sound `Ok(None)` (the documented integer partiality caveat, the same one
//!    [`imc_lia`](crate::imc_lia) declines on).
//! 3. **Translate back, clearing denominators.** The real interpolant is a
//!    Boolean tree (`And`/`Or`/`Not` + `Top`/`Bot`) over linear-real order
//!    atoms whose variables are relaxation surrogates. Each atom is parsed into
//!    rational coefficients, each surrogate real var is mapped back to its
//!    integer symbol, the atom is multiplied through by the positive LCM of all
//!    its denominators, and the integer atom is rebuilt with the IR's integer
//!    builders. A surrogate-free real var, a non-linear atom, or an `i128`
//!    overflow declines.
//! 4. **Verify before return.** All three Craig conditions are re-checked on
//!    the **original** integer partitions with the disjunctive integer-complete
//!    decider [`check_with_lia_dpll`](crate::check_with_lia_dpll) (which routes
//!    Boolean structure over integer atoms through the integer simplex),
//!    declining on any non-`Unsat`/doubt.
//!
//! # Trust
//!
//! The `Int`→`Real` mapping, the entire disjunctive real construction inside
//! [`lra_interpolant_cnf`](crate::lra_interpolant_cnf), and the
//! denominator-clearing translate-back are **entirely untrusted**: soundness
//! comes only from [`verify_interpolant`], which re-checks all three Craig
//! conditions over ℤ (via the disjunctive integer decider
//! [`check_with_lia_dpll`](crate::check_with_lia_dpll)) before any interpolant
//! is returned. Any decision that is
//! not `unsat`, any shared-vocabulary violation, or any construction failure
//! yields `Ok(None)`.

use std::collections::{BTreeMap, BTreeSet};

use axeyum_ir::{Op, Rational, Sort, SymbolId, TermArena, TermId, TermNode};

use crate::backend::{CheckResult, SolverConfig, SolverError};
use crate::dpll_lia::check_with_lia_dpll;
use crate::lra_interpolant_cnf::lra_interpolant_cnf;

/// Produces a verified disjunctive (CNF) `QF_LIA` Craig interpolant for the
/// unsatisfiable integer conjunction `A ∧ B`, where `a_assertions` is `A` and
/// `b_assertions` is `B`. Unlike [`crate::lia_interpolant`], the assertions may
/// carry arbitrary Boolean structure (`∧`/`∨`/`¬`/`ite`/`=`) over linear-integer
/// order atoms.
///
/// Returns `Ok(Some(I))` with a fully re-checked integer interpolant term `I`,
/// or `Ok(None)` when `A ∧ B` is satisfiable over ℤ, the input is outside the
/// supported fragment, the integer unsat needs cuts the rational relaxation
/// cannot witness, an `i128` overflow is hit while clearing denominators, the
/// disjunctive real construction cannot complete, or the candidate fails any of
/// its three independent post-checks over ℤ. It **never** returns an unverified
/// interpolant.
///
/// # Errors
///
/// Propagates [`SolverError`] from the underlying disjunctive real
/// interpolation [`crate::lra_interpolant_cnf`] or from the integer
/// verification [`crate::check_with_lia_dpll`] calls (e.g. a self-check
/// soundness alarm). Ordinary unsupported input declines with `Ok(None)`.
pub fn lia_interpolant_cnf(
    arena: &mut TermArena,
    a_assertions: &[TermId],
    b_assertions: &[TermId],
) -> Result<Option<TermId>, SolverError> {
    // 1. Build the rational relaxation: a fresh Real surrogate per Int symbol
    //    (the SAME int symbol → the SAME real symbol across A and B), every
    //    integer relation/op reinterpreted over the reals, the Boolean structure
    //    preserved. A construct with no clean real analogue declines.
    let mut relax = Relax::default();
    let Some(a_real) = relax.translate_all(arena, a_assertions)? else {
        return Ok(None);
    };
    let Some(b_real) = relax.translate_all(arena, b_assertions)? else {
        return Ok(None);
    };

    // 2. Disjunctive real interpolation of the relaxation. A decline (sat —
    //    i.e. the integer unsat needs cuts — or out-of-fragment, or a failed
    //    construction) propagates as a sound `Ok(None)`.
    let Some(real_interpolant) = lra_interpolant_cnf(arena, &a_real, &b_real)? else {
        return Ok(None);
    };

    // 3. Translate the real interpolant (a Boolean tree over linear-real order
    //    atoms whose vars are relaxation surrogates) back to an integer term,
    //    clearing denominators per atom. A surrogate-free var, a non-linear
    //    atom, or an overflow declines.
    let Some(interpolant) = relax.to_integer_term(arena, real_interpolant) else {
        return Ok(None);
    };

    // 4. VERIFY-BEFORE-RETURN over the ORIGINAL integer partitions with the
    //    integer-complete decider. Decline on any doubt.
    if verify_interpolant(arena, a_assertions, b_assertions, interpolant)? {
        Ok(Some(interpolant))
    } else {
        Ok(None)
    }
}

/// Re-checks the three Craig conditions for `interpolant` against the
/// **original** disjunctive `QF_LIA` partitions with the disjunctive
/// integer-complete decider [`check_with_lia_dpll`] (which handles Boolean
/// structure over integer atoms — the conjunctive
/// [`check_with_lia_simplex`](crate::check_with_lia_simplex) cannot decide a
/// disjunctive `A`):
///
/// 1. `A ∧ ¬I` is `unsat` (i.e. `A ⇒ I`),
/// 2. `I ∧ B` is `unsat` (i.e. `I ∧ B ⇒ ⊥`),
/// 3. every integer symbol of `I` occurs in both `A` and `B`.
///
/// Returns `Ok(true)` only when all three hold; a vocabulary failure, a builder
/// error, an `Unsupported` decline of either query, or any non-`Unsat` decision
/// yields `Ok(false)`. This is the sole soundness anchor: the relaxation, the
/// disjunctive real construction, and the translate-back are all untrusted.
///
/// # Errors
///
/// Propagates a non-`Unsupported` [`SolverError`] from the integer decider (a
/// soundness alarm), never an ordinary decline.
fn verify_interpolant(
    arena: &mut TermArena,
    a_assertions: &[TermId],
    b_assertions: &[TermId],
    interpolant: TermId,
) -> Result<bool, SolverError> {
    // (3) Vocabulary: every symbol of I occurs in both A and B.
    let a_symbols = symbols_of(arena, a_assertions);
    let b_symbols = symbols_of(arena, b_assertions);
    for symbol in symbols_of(arena, &[interpolant]) {
        if !a_symbols.contains(&symbol) || !b_symbols.contains(&symbol) {
            return Ok(false);
        }
    }

    let config = SolverConfig::default();

    // (1) A ∧ ¬I unsat (disjunctive integer decider).
    let Ok(not_i) = arena.not(interpolant) else {
        return Ok(false);
    };
    let mut a_check: Vec<TermId> = a_assertions.to_vec();
    a_check.push(not_i);
    if !decided_unsat(arena, &a_check, &config)? {
        return Ok(false);
    }

    // (2) I ∧ B unsat (disjunctive integer decider).
    let mut b_check: Vec<TermId> = Vec::with_capacity(b_assertions.len() + 1);
    b_check.push(interpolant);
    b_check.extend_from_slice(b_assertions);
    if !decided_unsat(arena, &b_check, &config)? {
        return Ok(false);
    }

    Ok(true)
}

/// Decides `assertions` with the disjunctive integer decider, returning
/// `Ok(true)` only on a definite `unsat`. An `Unsupported` decline (input the
/// decider cannot classify) or any non-`unsat` result is a sound `Ok(false)`;
/// other [`SolverError`]s (a self-check soundness alarm) propagate.
fn decided_unsat(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<bool, SolverError> {
    match check_with_lia_dpll(arena, assertions, config) {
        Ok(CheckResult::Unsat) => Ok(true),
        Ok(_) | Err(SolverError::Unsupported(_)) => Ok(false),
        Err(other) => Err(other),
    }
}

/// The recognized comparison relation of an interpolant atom (`expr ⋈ 0`).
#[derive(Clone, Copy, PartialEq, Eq)]
enum Relation {
    /// `expr < 0`.
    Lt,
    /// `expr ≤ 0`.
    Le,
    /// `expr > 0`.
    Gt,
    /// `expr ≥ 0`.
    Ge,
    /// `expr = 0`.
    Eq,
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

/// The relaxation state: a deterministic `Int` symbol ↔ fresh `Real` surrogate
/// bijection plus a translation memo. Mirrors [`crate::lia_interpolant`]'s
/// relaxation so that the same integer term maps to the same real surrogate
/// across `A` and `B` (preserving the shared vocabulary the disjunctive real
/// interpolant ranges over).
#[derive(Default)]
struct Relax {
    /// Original integer symbol → fresh real symbol (same int → same real).
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

    /// The fresh real surrogate standing for `int_sym` (created on first use).
    /// It carries no integer model meaning — it exists only for the relaxation
    /// interpolant.
    fn real_of_int(
        &mut self,
        arena: &mut TermArena,
        int_sym: SymbolId,
    ) -> Result<TermId, SolverError> {
        if let Some(&real_sym) = self.int_to_real.get(&int_sym) {
            return Ok(arena.var(real_sym));
        }
        let name = format!("!lia-interp-cnf.relax.{}", int_sym.index());
        let real_sym = arena
            .declare_internal(&name, Sort::Real)
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

    /// Translates the real interpolant term — a Boolean tree (`And`/`Or`/`Not`,
    /// `Top`/`Bot`) over linear-real order atoms whose variables are relaxation
    /// surrogates — back to an integer term over the original integer symbols.
    /// Returns `None` on a surrogate-free real var, a non-linear / unrecognized
    /// atom, an `i128` overflow, or a builder failure.
    fn to_integer_term(&self, arena: &mut TermArena, term: TermId) -> Option<TermId> {
        let node = arena.node(term).clone();
        match node {
            TermNode::BoolConst(value) => Some(arena.bool_const(value)),
            TermNode::App { op, args } => match op {
                Op::BoolNot => {
                    let inner = self.to_integer_term(arena, args[0])?;
                    arena.not(inner).ok()
                }
                Op::BoolAnd => {
                    let lhs = self.to_integer_term(arena, args[0])?;
                    let rhs = self.to_integer_term(arena, args[1])?;
                    arena.and(lhs, rhs).ok()
                }
                Op::BoolOr => {
                    let lhs = self.to_integer_term(arena, args[0])?;
                    let rhs = self.to_integer_term(arena, args[1])?;
                    arena.or(lhs, rhs).ok()
                }
                Op::RealLt | Op::RealLe | Op::RealGt | Op::RealGe => {
                    self.translate_order_atom(arena, op, args[0], args[1])
                }
                Op::Eq if arena.sort_of(args[0]) == Sort::Real => {
                    self.translate_order_atom(arena, Op::Eq, args[0], args[1])
                }
                // Any other Boolean shape in a real interpolant (`ite`/`xor`/`=`
                // over Bool, etc.): the disjunctive real construction lifts only
                // `And`/`Or`/`Not` over atoms, so an unexpected shape declines.
                _ => None,
            },
            _ => None,
        }
    }

    /// Translates one linear-real order atom `lhs ⋈ rhs` back to the integer
    /// atom `(Σ coeff·sym + constant) ⋈ 0` over the original integer symbols,
    /// clearing denominators. Returns `None` on a surrogate-free var, a
    /// non-linear subterm, an overflow, or a builder failure.
    fn translate_order_atom(
        &self,
        arena: &mut TermArena,
        op: Op,
        lhs: TermId,
        rhs: TermId,
    ) -> Option<TermId> {
        let relation = match op {
            Op::RealLt => Relation::Lt,
            Op::RealLe => Relation::Le,
            Op::RealGt => Relation::Gt,
            Op::RealGe => Relation::Ge,
            Op::Eq => Relation::Eq,
            _ => return None,
        };
        // Move both sides into one linear form: lhs - rhs ⋈ 0.
        let mut linear = LinearReal::default();
        linear.add_term(arena, lhs, Rational::integer(1))?;
        linear.add_term(arena, rhs, Rational::integer(-1))?;

        let (coeffs, constant) = self.clear_denominators(&linear)?;
        build_integer_atom(arena, &coeffs, constant, relation)
    }

    /// Maps the relaxation-surrogate real coefficients of `linear` back to
    /// integer coefficients over the original integer symbols, multiplying
    /// through by the positive LCM of all denominators. Returns `None` on a
    /// surrogate-free var or an `i128` overflow.
    fn clear_denominators(&self, linear: &LinearReal) -> Option<(BTreeMap<SymbolId, i128>, i128)> {
        // The positive LCM of every coefficient and the constant denominator.
        let mut multiplier: i128 = 1;
        for coeff in linear.coeffs.values() {
            multiplier = lcm(multiplier, coeff.denominator())?;
        }
        multiplier = lcm(multiplier, linear.constant.denominator())?;
        let factor = Rational::integer(multiplier);

        let mut coeffs: BTreeMap<SymbolId, i128> = BTreeMap::new();
        for (&real_sym, &coeff) in &linear.coeffs {
            let scaled = coeff.checked_mul(factor)?;
            if !scaled.is_integer() {
                return None;
            }
            let value = scaled.numerator();
            if value == 0 {
                continue;
            }
            // A surrogate-free real var has no integer pre-image → decline.
            let int_sym = *self.real_to_int.get(&real_sym)?;
            let entry = coeffs.entry(int_sym).or_insert(0);
            *entry = entry.checked_add(value)?;
        }
        coeffs.retain(|_, &mut value| value != 0);

        let scaled_const = linear.constant.checked_mul(factor)?;
        if !scaled_const.is_integer() {
            return None;
        }
        Some((coeffs, scaled_const.numerator()))
    }
}

/// Builds the integer atom `(Σ coeff·sym + constant) ⋈ 0` from integer
/// coefficients, preserving the relation. Returns `None` on a term-builder
/// failure (we never panic on a malformed candidate).
fn build_integer_atom(
    arena: &mut TermArena,
    coeffs: &BTreeMap<SymbolId, i128>,
    constant: i128,
    relation: Relation,
) -> Option<TermId> {
    let mut terms: Vec<TermId> = Vec::new();
    for (&symbol, &coeff) in coeffs {
        if coeff == 0 {
            continue;
        }
        let var = arena.var(symbol);
        let coeff_term = arena.int_const(coeff);
        let product = arena.int_mul(coeff_term, var).ok()?;
        terms.push(product);
    }
    // Include the constant when nonzero, or when there are no variable terms (so
    // the expression is well-formed).
    if constant != 0 || terms.is_empty() {
        terms.push(arena.int_const(constant));
    }

    let mut acc = terms[0];
    for &term in &terms[1..] {
        acc = arena.int_add(acc, term).ok()?;
    }

    let zero = arena.int_const(0);
    match relation {
        Relation::Lt => arena.int_lt(acc, zero),
        Relation::Le => arena.int_le(acc, zero),
        Relation::Gt => arena.int_gt(acc, zero),
        Relation::Ge => arena.int_ge(acc, zero),
        Relation::Eq => arena.eq(acc, zero),
    }
    .ok()
}

/// The least common multiple of two `i128` values, overflow-checked. Both inputs
/// are denominators, always positive in a normalized [`Rational`]; returns
/// `None` on overflow.
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
    let mut stack = vec![term];
    let mut seen = BTreeSet::new();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match arena.node(t) {
            TermNode::Symbol(symbol) => {
                out.insert(*symbol);
            }
            TermNode::App { args, .. } => stack.extend(args.iter().copied()),
            _ => {}
        }
    }
}
