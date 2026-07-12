//! Independently checked certificates for supported satisfiable quantifiers.
//!
//! Search may propose a Skolem term for a supported positive existential, but
//! the term receives public `sat` credit only when this module re-matches the
//! original assertion and proves the witness with a small independent checker.
//! Unsupported shapes decline.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use axeyum_ir::{
    Assignment, IrError, Op, Rational, SymbolId, TermArena, TermId, TermNode, Value, eval,
};

use crate::{Model, SolverError};

/// A checked Skolem witness for one supported universally closed assertion.
///
/// The IDs refer only to atoms in the caller's original arena. The synthesized
/// affine expression is owned by the certificate, so it remains replayable when
/// solving occurred on an arena clone. [`check_quantified_skolem_sat`] re-derives
/// every structural fact from `assertion`; no field is trusted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuantifiedSkolemSatCertificate {
    /// The exact original quantified assertion covered by this certificate.
    pub assertion: TermId,
    /// The leading universal binders, outermost first.
    pub universals: Vec<SymbolId>,
    /// The single existential binder witnessed by `witness`.
    pub existential: SymbolId,
    /// An owned affine expression over original-arena atoms that witnesses the
    /// existential. For bit-vectors, only the exact identity encoding documented
    /// by [`AffineSkolemWitness`] is supported.
    pub witness: AffineSkolemWitness,
}

/// Arena-stable affine Skolem witness `sum(coeff_i * atom_i) + constant`.
///
/// `terms` must be strictly ordered by `TermId`, contain no zero coefficient,
/// and refer only to quantifier-free, same-sort atoms over the universal binders.
/// The checker validates those invariants before materializing the expression in
/// a private arena clone. For a bit-vector existential, the only defined recipe
/// is one same-width universal variable with coefficient one and constant zero.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AffineSkolemWitness {
    /// Deterministically ordered `(atom, coefficient)` pairs.
    pub terms: Vec<(TermId, Rational)>,
    /// The affine constant.
    pub constant: Rational,
}

/// Re-checks a Skolem certificate against its exact original assertion.
///
/// The checker clones the arena before substitution, so checking cannot mutate
/// caller state and original term IDs remain stable. It is intentionally partial:
/// prenex witnesses use syntactic reflexivity and Boolean combinations of
/// affine `Int`/`Real` tautologies and exact reflexive BV identity witnesses;
/// ADR-0098 additionally admits one exact guarded unit-gap theorem with a
/// positive nested existential.
#[must_use]
pub fn check_quantified_skolem_sat(
    arena: &TermArena,
    assertion: TermId,
    cert: &QuantifiedSkolemSatCertificate,
) -> bool {
    if cert.assertion != assertion {
        return false;
    }

    let mut universals = Vec::new();
    let mut cursor = assertion;
    while let TermNode::App {
        op: Op::Forall(var),
        args,
    } = arena.node(cursor)
    {
        if args.len() != 1 || universals.contains(var) {
            return false;
        }
        universals.push(*var);
        cursor = args[0];
    }
    if universals.is_empty() || universals != cert.universals {
        return false;
    }
    if let TermNode::App {
        op: Op::Exists(existential),
        args,
    } = arena.node(cursor)
    {
        let [body] = &**args else {
            return false;
        };
        if contains_quantifier(arena, *body)
            || *existential != cert.existential
            || universals.contains(existential)
        {
            return false;
        }
        let mut cloned = arena.clone();
        let Some(witness) =
            materialize_checked_witness(&mut cloned, &universals, *existential, &cert.witness)
        else {
            return false;
        };
        let existential_term = cloned.var(cert.existential);
        let mut memo = HashMap::new();
        let instantiated =
            substitute_term(&mut cloned, *body, existential_term, witness, &mut memo);
        return definitely_bool(&cloned, instantiated) == Some(true);
    }

    check_guarded_unit_gap(arena, cursor, &universals, cert)
}

fn materialize_checked_witness(
    arena: &mut TermArena,
    universals: &[SymbolId],
    existential: SymbolId,
    witness: &AffineSkolemWitness,
) -> Option<TermId> {
    let allowed: BTreeSet<_> = universals.iter().copied().collect();
    let sort = arena.symbol(existential).1;
    let mut previous = None;
    for &(term, coefficient) in &witness.terms {
        if coefficient.is_zero()
            || previous.is_some_and(|prior| prior >= term)
            || arena.term_by_index(term.index()) != Some(term)
            || arena.sort_of(term) != sort
            || contains_quantifier(arena, term)
            || symbols_in(arena, term)
                .iter()
                .any(|symbol| !allowed.contains(symbol))
        {
            return None;
        }
        previous = Some(term);
    }
    affine_witness_to_term(arena, witness, sort)
}

/// Checks the exact ADR-0098 theorem over the untouched original body:
///
/// `upper <= lower+1 or exists z. z>lower and z<upper`, witnessed by
/// `z := lower+1` over `Int` or `Real`.
fn check_guarded_unit_gap(
    arena: &TermArena,
    body: TermId,
    universals: &[SymbolId],
    cert: &QuantifiedSkolemSatCertificate,
) -> bool {
    let TermNode::App {
        op: Op::BoolOr,
        args,
    } = arena.node(body)
    else {
        return false;
    };
    let [left, right] = &**args else {
        return false;
    };
    let Some((guard, existential, inner)) = guarded_exists_side(arena, *left, *right)
        .or_else(|| guarded_exists_side(arena, *right, *left))
    else {
        return false;
    };
    let existential_sort = arena.symbol(existential).1;
    if !matches!(
        existential_sort,
        axeyum_ir::Sort::Int | axeyum_ir::Sort::Real
    ) || contains_quantifier(arena, guard)
        || contains_quantifier(arena, inner)
        || existential != cert.existential
        || universals.contains(&existential)
    {
        return false;
    }

    let TermNode::App {
        op: Op::BoolAnd,
        args,
    } = arena.node(inner)
    else {
        return false;
    };
    let [first, second] = &**args else {
        return false;
    };
    let Some((lower, upper)) =
        match_gap_bounds(arena, *first, *second, existential, existential_sort)
            .or_else(|| match_gap_bounds(arena, *second, *first, existential, existential_sort))
    else {
        return false;
    };

    let Some((guard_upper, successor)) = match_gap_guard(arena, guard, existential_sort) else {
        return false;
    };
    let allowed: BTreeSet<_> = universals.iter().copied().collect();
    if [lower, upper, guard_upper, successor]
        .into_iter()
        .any(|term| {
            symbols_in(arena, term)
                .iter()
                .any(|symbol| !allowed.contains(symbol))
        })
    {
        return false;
    }

    if !affine_equal(arena, guard_upper, upper)
        || !affine_offset(arena, successor, lower, Rational::integer(1))
    {
        return false;
    }
    let mut cloned = arena.clone();
    let Some(witness) =
        materialize_checked_witness(&mut cloned, universals, existential, &cert.witness)
    else {
        return false;
    };
    affine_equal(&cloned, witness, successor)
}

fn guarded_exists_side(
    arena: &TermArena,
    guard: TermId,
    exists_side: TermId,
) -> Option<(TermId, SymbolId, TermId)> {
    let TermNode::App {
        op: Op::Exists(existential),
        args,
    } = arena.node(exists_side)
    else {
        return None;
    };
    let [inner] = &**args else {
        return None;
    };
    Some((guard, *existential, *inner))
}

fn match_gap_bounds(
    arena: &TermArena,
    lower_atom: TermId,
    upper_atom: TermId,
    existential: SymbolId,
    sort: axeyum_ir::Sort,
) -> Option<(TermId, TermId)> {
    let TermNode::App {
        op: lower_op,
        args: lower_args,
    } = arena.node(lower_atom)
    else {
        return None;
    };
    let [lower_left, lower] = &**lower_args else {
        return None;
    };
    let TermNode::App {
        op: upper_op,
        args: upper_args,
    } = arena.node(upper_atom)
    else {
        return None;
    };
    let operators_match = matches!(
        (sort, lower_op, upper_op),
        (axeyum_ir::Sort::Int, Op::IntGt, Op::IntLt)
            | (axeyum_ir::Sort::Real, Op::RealGt, Op::RealLt)
    );
    if !operators_match {
        return None;
    }
    let [upper_left, upper] = &**upper_args else {
        return None;
    };
    if !matches!(arena.node(*lower_left), TermNode::Symbol(found) if *found == existential)
        || !matches!(arena.node(*upper_left), TermNode::Symbol(found) if *found == existential)
    {
        return None;
    }
    Some((*lower, *upper))
}

fn match_gap_guard(
    arena: &TermArena,
    guard: TermId,
    sort: axeyum_ir::Sort,
) -> Option<(TermId, TermId)> {
    let TermNode::App { op, args } = arena.node(guard) else {
        return None;
    };
    if !matches!(
        (sort, op),
        (axeyum_ir::Sort::Int, Op::IntLe) | (axeyum_ir::Sort::Real, Op::RealLe)
    ) {
        return None;
    }
    let [upper, successor] = &**args else {
        return None;
    };
    Some((*upper, *successor))
}

fn affine_equal(arena: &TermArena, left: TermId, right: TermId) -> bool {
    affine_offset(arena, left, right, Rational::zero())
}

fn affine_offset(arena: &TermArena, left: TermId, right: TermId, expected: Rational) -> bool {
    let Some(difference) = Affine::from_term(arena, left)
        .and_then(|left| Affine::from_term(arena, right).and_then(|right| left.sub(&right)))
    else {
        return false;
    };
    difference.coefficients.is_empty() && difference.constant == expected
}

/// Converts a synthesized term into an arena-stable certificate recipe.
///
/// Every opaque atom must predate witness search. This prevents clone-local term
/// IDs from escaping in a model returned to the caller.
pub(crate) fn affine_skolem_witness(
    arena: &TermArena,
    term: TermId,
    original_term_count: usize,
) -> Option<AffineSkolemWitness> {
    let affine = Affine::from_term(arena, term)?;
    if affine
        .coefficients
        .keys()
        .any(|atom| atom.index() >= original_term_count)
    {
        return None;
    }
    Some(AffineSkolemWitness {
        terms: affine.coefficients.into_iter().collect(),
        constant: affine.constant,
    })
}

fn affine_witness_to_term(
    arena: &mut TermArena,
    witness: &AffineSkolemWitness,
    sort: axeyum_ir::Sort,
) -> Option<TermId> {
    match sort {
        axeyum_ir::Sort::Int => {
            if !witness.constant.is_integer()
                || witness
                    .terms
                    .iter()
                    .any(|(_, coefficient)| !coefficient.is_integer())
            {
                return None;
            }
            let mut acc = None;
            for &(atom, coefficient) in &witness.terms {
                let term = if coefficient == Rational::integer(1) {
                    atom
                } else {
                    let coefficient = arena.int_const(coefficient.numerator());
                    arena.int_mul(coefficient, atom).ok()?
                };
                acc = Some(match acc {
                    Some(previous) => arena.int_add(previous, term).ok()?,
                    None => term,
                });
            }
            if !witness.constant.is_zero() || acc.is_none() {
                let constant = arena.int_const(witness.constant.numerator());
                acc = Some(match acc {
                    Some(previous) => arena.int_add(previous, constant).ok()?,
                    None => constant,
                });
            }
            acc
        }
        axeyum_ir::Sort::Real => {
            let mut acc = None;
            for &(atom, coefficient) in &witness.terms {
                let term = if coefficient == Rational::integer(1) {
                    atom
                } else {
                    let coefficient = arena.real_const(coefficient);
                    arena.real_mul(coefficient, atom).ok()?
                };
                acc = Some(match acc {
                    Some(previous) => arena.real_add(previous, term).ok()?,
                    None => term,
                });
            }
            if !witness.constant.is_zero() || acc.is_none() {
                let constant = arena.real_const(witness.constant);
                acc = Some(match acc {
                    Some(previous) => arena.real_add(previous, constant).ok()?,
                    None => constant,
                });
            }
            acc
        }
        axeyum_ir::Sort::BitVec(_) => {
            let [(term, coefficient)] = witness.terms.as_slice() else {
                return None;
            };
            if *coefficient != Rational::integer(1) || !witness.constant.is_zero() {
                return None;
            }
            match arena.node(*term) {
                TermNode::Symbol(symbol) if arena.symbol(*symbol).1 == sort => Some(*term),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Canonically checks a returned model against the original assertions.
///
/// An attached quantified certificate is independently checked before finite
/// enumeration; assertions without certificates use ordinary evaluator replay.
/// An unsupported domain therefore requires exactly one matching certificate
/// carried by `model`.
///
/// # Errors
///
/// Returns [`SolverError::Backend`] for evaluator failures other than the
/// expected unsupported infinite quantifier domain, or for non-Boolean replay.
pub fn check_model(
    arena: &TermArena,
    assertions: &[TermId],
    model: &Model,
) -> Result<bool, SolverError> {
    check_model_with_assignment(arena, assertions, model, &model.to_assignment())
}

/// [`check_model`] with a caller-provided reconstructed assignment.
///
/// This is used by query-planning consumers that must restore eliminated ground
/// symbols before replay while retaining quantified certificates from `model`.
///
/// # Errors
///
/// See [`check_model`].
pub fn check_model_with_assignment(
    arena: &TermArena,
    assertions: &[TermId],
    model: &Model,
    assignment: &Assignment,
) -> Result<bool, SolverError> {
    let assertion_set: BTreeSet<_> = assertions.iter().copied().collect();
    let certificate_count = model.quantified_sat_certificates().count()
        + model.quantified_bool_model_sat_certificates().count()
        + model.quantified_guard_sat_certificates().count();
    if model
        .quantified_sat_certificates()
        .any(|cert| !assertion_set.contains(&cert.assertion))
    {
        return Ok(false);
    }
    if model
        .quantified_bool_model_sat_certificates()
        .any(|cert| !assertion_set.contains(&cert.assertion))
    {
        return Ok(false);
    }
    if model
        .quantified_guard_sat_certificates()
        .any(|cert| !assertion_set.contains(&cert.assertion))
    {
        return Ok(false);
    }

    let mut checked_certificates = BTreeSet::new();
    for &assertion in assertions {
        if let Some(cert) = model.quantified_sat_certificate(assertion) {
            if !check_quantified_skolem_sat(arena, assertion, cert) {
                return Ok(false);
            }
            checked_certificates.insert(assertion);
            continue;
        }
        if let Some(cert) = model.quantified_bool_model_sat_certificate(assertion) {
            if cert
                .values
                .iter()
                .any(|&(symbol, value)| assignment.get(symbol) != Some(Value::Bool(value)))
                || !crate::check_quantified_bool_model_sat(arena, assertion, cert)
            {
                return Ok(false);
            }
            checked_certificates.insert(assertion);
            continue;
        }
        if let Some(cert) = model.quantified_guard_sat_certificate(assertion) {
            if !crate::check_quantified_guard_sat(arena, assertion, cert) {
                return Ok(false);
            }
            checked_certificates.insert(assertion);
            continue;
        }
        match eval(arena, assertion, assignment) {
            Ok(Value::Bool(true)) => {}
            Ok(Value::Bool(false)) => return Ok(false),
            Ok(value) => {
                return Err(SolverError::Backend(format!(
                    "sat model replay: assertion #{} is non-Boolean {value}",
                    assertion.index()
                )));
            }
            Err(IrError::UnsupportedQuantifierDomain(_)) => {
                return Ok(false);
            }
            Err(error) => {
                return Err(SolverError::Backend(format!(
                    "sat model replay: assertion #{} failed to evaluate: {error}",
                    assertion.index()
                )));
            }
        }
    }
    Ok(checked_certificates.len() == certificate_count)
}

fn substitute_term(
    arena: &mut TermArena,
    term: TermId,
    needle: TermId,
    replacement: TermId,
    memo: &mut HashMap<TermId, TermId>,
) -> TermId {
    if term == needle {
        return replacement;
    }
    if let Some(&cached) = memo.get(&term) {
        return cached;
    }
    let rebuilt = match arena.node(term).clone() {
        TermNode::App { args, .. } => {
            let new_args: Vec<_> = args
                .iter()
                .map(|&arg| substitute_term(arena, arg, needle, replacement, memo))
                .collect();
            arena.rebuild_with_args(term, &new_args)
        }
        _ => term,
    };
    memo.insert(term, rebuilt);
    rebuilt
}

fn contains_quantifier(arena: &TermArena, root: TermId) -> bool {
    let mut seen = BTreeSet::new();
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(term) {
            if matches!(op, Op::Forall(_) | Op::Exists(_)) {
                return true;
            }
            stack.extend(args.iter().copied());
        }
    }
    false
}

fn symbols_in(arena: &TermArena, root: TermId) -> BTreeSet<SymbolId> {
    let mut symbols = BTreeSet::new();
    let mut seen = BTreeSet::new();
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        match arena.node(term) {
            TermNode::Symbol(symbol) => {
                symbols.insert(*symbol);
            }
            TermNode::App { args, .. } => stack.extend(args.iter().copied()),
            _ => {}
        }
    }
    symbols
}

fn definitely_bool(arena: &TermArena, term: TermId) -> Option<bool> {
    match arena.node(term) {
        TermNode::BoolConst(value) => Some(*value),
        TermNode::App { op, args } => match op {
            Op::BoolNot => definitely_bool(arena, args[0]).map(|value| !value),
            Op::BoolAnd => fold_bool(arena, args, true),
            Op::BoolOr => fold_bool(arena, args, false),
            Op::BoolImplies => match (
                definitely_bool(arena, args[0]),
                definitely_bool(arena, args[1]),
            ) {
                (Some(false), _) | (_, Some(true)) => Some(true),
                (Some(true), Some(false)) => Some(false),
                _ => None,
            },
            Op::BoolXor => match (
                definitely_bool(arena, args[0]),
                definitely_bool(arena, args[1]),
            ) {
                (Some(left), Some(right)) => Some(left ^ right),
                _ if args[0] == args[1] => Some(false),
                _ => None,
            },
            Op::Eq | Op::BvSle | Op::BvUle if args[0] == args[1] => Some(true),
            Op::Eq => affine_relation(arena, args[0], args[1], Relation::Eq),
            Op::IntLt | Op::RealLt => affine_relation(arena, args[0], args[1], Relation::Lt),
            Op::IntLe | Op::RealLe => affine_relation(arena, args[0], args[1], Relation::Le),
            Op::IntGt | Op::RealGt => affine_relation(arena, args[0], args[1], Relation::Gt),
            Op::IntGe | Op::RealGe => affine_relation(arena, args[0], args[1], Relation::Ge),
            _ => None,
        },
        _ => None,
    }
}

fn fold_bool(arena: &TermArena, args: &[TermId], identity: bool) -> Option<bool> {
    let decisive = !identity;
    let mut all_known = true;
    for &arg in args {
        match definitely_bool(arena, arg) {
            Some(value) if value == decisive => return Some(decisive),
            Some(_) => {}
            None => all_known = false,
        }
    }
    all_known.then_some(identity)
}

#[derive(Clone, Copy)]
enum Relation {
    Eq,
    Lt,
    Le,
    Gt,
    Ge,
}

fn affine_relation(
    arena: &TermArena,
    left: TermId,
    right: TermId,
    relation: Relation,
) -> Option<bool> {
    let difference = Affine::from_term(arena, left)?.sub(&Affine::from_term(arena, right)?)?;
    if !difference.coefficients.is_empty() {
        return None;
    }
    let ordering = difference.constant.checked_cmp(&Rational::zero())?;
    Some(match relation {
        Relation::Eq => ordering.is_eq(),
        Relation::Lt => ordering.is_lt(),
        Relation::Le => !ordering.is_gt(),
        Relation::Gt => ordering.is_gt(),
        Relation::Ge => !ordering.is_lt(),
    })
}

#[derive(Clone)]
struct Affine {
    coefficients: BTreeMap<TermId, Rational>,
    constant: Rational,
}

impl Affine {
    fn constant(value: Rational) -> Self {
        Self {
            coefficients: BTreeMap::new(),
            constant: value,
        }
    }

    fn atom(term: TermId) -> Self {
        Self {
            coefficients: BTreeMap::from([(term, Rational::integer(1))]),
            constant: Rational::zero(),
        }
    }

    fn from_term(arena: &TermArena, term: TermId) -> Option<Self> {
        match arena.node(term) {
            TermNode::IntConst(value) => Some(Self::constant(Rational::integer(*value))),
            TermNode::RealConst(value) => Some(Self::constant(*value)),
            TermNode::App { op, args } => match op {
                Op::IntAdd | Op::RealAdd => {
                    Self::from_term(arena, args[0])?.add(&Self::from_term(arena, args[1])?)
                }
                Op::IntSub | Op::RealSub => {
                    Self::from_term(arena, args[0])?.sub(&Self::from_term(arena, args[1])?)
                }
                Op::IntNeg | Op::RealNeg => {
                    Self::from_term(arena, args[0])?.scale(Rational::integer(-1))
                }
                Op::IntMul | Op::RealMul => {
                    let left = Self::from_term(arena, args[0])?;
                    let right = Self::from_term(arena, args[1])?;
                    if left.coefficients.is_empty() {
                        right.scale(left.constant)
                    } else if right.coefficients.is_empty() {
                        left.scale(right.constant)
                    } else {
                        None
                    }
                }
                Op::IntToReal => Self::from_term(arena, args[0]),
                _ => Some(Self::atom(term)),
            },
            _ => Some(Self::atom(term)),
        }
    }

    fn add(&self, other: &Self) -> Option<Self> {
        let mut coefficients = self.coefficients.clone();
        for (&term, &coefficient) in &other.coefficients {
            let next = coefficients
                .get(&term)
                .copied()
                .unwrap_or_else(Rational::zero)
                .checked_add(coefficient)?;
            if next.is_zero() {
                coefficients.remove(&term);
            } else {
                coefficients.insert(term, next);
            }
        }
        Some(Self {
            coefficients,
            constant: self.constant.checked_add(other.constant)?,
        })
    }

    fn sub(&self, other: &Self) -> Option<Self> {
        self.add(&other.scale(Rational::integer(-1))?)
    }

    fn scale(&self, factor: Rational) -> Option<Self> {
        if factor.is_zero() {
            return Some(Self::constant(Rational::zero()));
        }
        let mut coefficients = BTreeMap::new();
        for (&term, &coefficient) in &self.coefficients {
            coefficients.insert(term, coefficient.checked_mul(factor)?);
        }
        Some(Self {
            coefficients,
            constant: self.constant.checked_mul(factor)?,
        })
    }
}
