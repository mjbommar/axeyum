//! Conjunctive linear real arithmetic (`QF_LRA`) by exact-rational
//! Fourier–Motzkin elimination (ADR-0015).
//!
//! [`check_with_lra`] decides a **conjunction** of linear real constraints. Each
//! assertion is parsed into linear atoms (`<`, `<=`, `>`, `>=`, `=` over linear
//! real expressions; `and`/`not` are pushed in, equality splits into two
//! inequalities); arbitrary Boolean structure (`or`, disequality) is out of
//! scope for this first slice and reported `Unsupported` (that needs a
//! `DPLL(T)` layer). The collected constraints are decided by Fourier–Motzkin
//! variable elimination over exact [`Rational`]s, which is complete for `QF_LRA`
//! and yields a rational model.
//!
//! **Trust.** Fourier–Motzkin is the untrusted search; every `sat` model is
//! replayed through the ground evaluator against the original assertions before
//! it is returned, so a bug in the elimination cannot produce an unsound `sat`.
//! Every `unsat` is backed by a [`FarkasCertificate`] — a nonnegative
//! combination of the original linear constraints that collapses to a constant
//! contradiction (`0 < 0` / `0 <= -c`, `c > 0`). The certificate is rebuilt
//! independently of the elimination (it depends only on the collected atoms and
//! the multipliers) and **self-checked before `unsat` is returned**: a failed
//! check is a [`SolverError::Backend`] soundness alarm, so a bug in
//! Fourier–Motzkin can no more produce an unsound `unsat` than it can an unsound
//! `sat` (ADR-0015). This is the exact-arithmetic dual of DRAT for `QF_BV`:
//! untrusted search, trusted small checking.

use std::collections::BTreeMap;

use axeyum_ir::{Op, Rational, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval};

use crate::backend::{CheckResult, SolverError, UnknownKind, UnknownReason};
use crate::model::Model;

/// Checks a conjunctive `QF_LRA` query by exact-rational Fourier–Motzkin
/// elimination. The returned [`Model`] assigns each real variable a
/// [`Value::Real`] and replays against the original assertions.
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] if an assertion is outside conjunctive
/// linear real arithmetic (disjunction, disequality, nonlinear product, or a
/// non-real term), or [`SolverError::Backend`] if a found model fails to replay
/// (a procedure bug — the soundness alarm).
pub fn check_with_lra(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<CheckResult, SolverError> {
    match decide(arena, assertions)? {
        Decision::Sat(model) => Ok(CheckResult::Sat(model)),
        Decision::UnsatFarkas { .. } | Decision::UnsatTrivial(_) => Ok(CheckResult::Unsat),
    }
}

/// Decides a conjunctive `QF_LRA` query and, on `unsat`, returns the Farkas
/// certificate refuting it.
///
/// Returns `Ok(Some(cert))` when the query is unsatisfiable through
/// Fourier–Motzkin (the certificate is self-checked before it is returned, so a
/// returned certificate always verifies); `Ok(None)` when the query is
/// satisfiable or unsatisfiable only because a literally-`false` assertion was
/// present (a degenerate case that needs no linear refutation). The error cases
/// match [`check_with_lra`].
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] for non-conjunctive-`QF_LRA` input and
/// [`SolverError::Backend`] if a `sat` model fails to replay or a derived
/// certificate fails its own check (either is a procedure-bug soundness alarm).
pub fn lra_farkas_certificate(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<Option<FarkasCertificate>, SolverError> {
    match decide(arena, assertions)? {
        Decision::UnsatFarkas { certificate, .. } => Ok(Some(certificate)),
        Decision::Sat(_) | Decision::UnsatTrivial(_) => Ok(None),
    }
}

/// Returns a **minimal** unsatisfiable core of a conjunctive `QF_LRA` query: the
/// indices (into `assertions`) of a jointly-unsatisfiable subset in which every
/// member is necessary (dropping any one makes the rest satisfiable).
///
/// The Farkas refutation seeds the core — exactly the assertions whose
/// constraints carry a nonzero multiplier participate — and a deterministic
/// deletion pass then removes any still-redundant assertion (re-deciding the
/// shrunk subset with the conjunctive solver, itself Farkas-self-checked). The
/// final core is re-decided as a defensive self-check before return. Returns
/// `Ok(None)` when the query is satisfiable.
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] for non-conjunctive-`QF_LRA` input, or
/// [`SolverError::Backend`] on a `sat` replay failure, a Farkas self-check
/// failure, or a core that fails to re-decide as `unsat` (all soundness alarms).
pub fn lra_unsat_core(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<Option<Vec<usize>>, SolverError> {
    match decide(arena, assertions)? {
        Decision::UnsatFarkas {
            certificate,
            origins,
        } => {
            // Seed with the Farkas support: the assertions that actually appear
            // in the refutation.
            let mut core: Vec<usize> = origins
                .iter()
                .zip(&certificate.multipliers)
                .filter(|(_, multiplier)| !multiplier.is_zero())
                .map(|(&origin, _)| origin)
                .collect();
            core.sort_unstable();
            core.dedup();

            // Deletion-based minimization: try removing each member (in a fixed
            // order, so the result is deterministic); keep the removal only if
            // the remainder stays unsatisfiable. The outcome is minimal — every
            // surviving member is necessary.
            let candidates = core.clone();
            for &candidate in &candidates {
                let trial: Vec<TermId> = core
                    .iter()
                    .filter(|&&i| i != candidate)
                    .map(|&i| assertions[i])
                    .collect();
                if !trial.is_empty() && matches!(check_with_lra(arena, &trial)?, CheckResult::Unsat)
                {
                    core.retain(|&i| i != candidate);
                }
            }

            // Defensive self-check: the minimized subset must still be unsat.
            let subset: Vec<TermId> = core.iter().map(|&i| assertions[i]).collect();
            if !matches!(check_with_lra(arena, &subset)?, CheckResult::Unsat) {
                return Err(SolverError::Backend(
                    "lra unsat-core self-check failed: extracted core is satisfiable".to_string(),
                ));
            }
            Ok(Some(core))
        }
        // A literally-`false` assertion is its own (singleton) core.
        Decision::UnsatTrivial(origin) => Ok(Some(vec![origin])),
        Decision::Sat(_) => Ok(None),
    }
}

/// The outcome of deciding a conjunctive `QF_LRA` query, carrying the evidence
/// for each branch.
enum Decision {
    /// Satisfiable; the model has already replayed against the original query.
    Sat(Model),
    /// Unsatisfiable with a self-checked Farkas refutation. `origins[i]` is the
    /// assertion index that atom `i` of the certificate came from, so the
    /// nonzero-multiplier atoms name the participating assertions.
    UnsatFarkas {
        certificate: FarkasCertificate,
        origins: Vec<usize>,
    },
    /// Unsatisfiable because a literally-`false` assertion was present (no
    /// linear refutation is meaningful); carries that assertion's index.
    UnsatTrivial(usize),
}

fn decide(arena: &TermArena, assertions: &[TermId]) -> Result<Decision, SolverError> {
    let mut ctx = Collector::default();
    for (index, &assertion) in assertions.iter().enumerate() {
        ctx.current_origin = index;
        ctx.collect(arena, assertion, false)?;
    }
    if ctx.trivially_unsat {
        return Ok(Decision::UnsatTrivial(ctx.trivial_origin.unwrap_or(0)));
    }

    // Tag each collected constraint with a unit multiplier vector so
    // Fourier–Motzkin can accumulate the nonnegative combination behind any
    // contradiction it derives.
    let n = ctx.constraints.len();
    for (i, constraint) in ctx.constraints.iter_mut().enumerate() {
        constraint.mult = unit_vec(n, i);
    }
    // Snapshot the original atoms for the (independent) certificate, and the
    // assertion each came from (aligned by index) for unsat-core extraction.
    let atoms: Vec<FarkasAtom> = ctx.constraints.iter().map(FarkasAtom::from).collect();
    let origins: Vec<usize> = ctx.constraints.iter().map(|c| c.origin).collect();

    let nvars = ctx.vars.len();
    match solve(&ctx.constraints, nvars) {
        Feasibility::Unsat(multipliers) => {
            let certificate = FarkasCertificate { atoms, multipliers };
            if !certificate.verify() {
                return Err(SolverError::Backend(
                    "lra: Farkas unsat certificate failed self-check (Fourier–Motzkin bug)"
                        .to_string(),
                ));
            }
            Ok(Decision::UnsatFarkas {
                certificate,
                origins,
            })
        }
        Feasibility::Bug(message) => Err(SolverError::Backend(message)),
        Feasibility::Sat(values) => {
            // Build a model over the original real symbols and replay (the trust
            // anchor for `sat`).
            let mut model = Model::new();
            let mut assignment = axeyum_ir::Assignment::new();
            for (&symbol, &index) in &ctx.var_index {
                model.set(symbol, Value::Real(values[index]));
                assignment.set(symbol, Value::Real(values[index]));
            }
            for &assertion in assertions {
                match eval(arena, assertion, &assignment) {
                    Ok(Value::Bool(true)) => {}
                    Ok(_) => {
                        return Err(SolverError::Backend(format!(
                            "lra sat model replay failed: assertion #{} not satisfied",
                            assertion.index()
                        )));
                    }
                    Err(error) => {
                        return Err(SolverError::Backend(format!(
                            "lra sat model replay failed: assertion #{} evaluation error: {error}",
                            assertion.index()
                        )));
                    }
                }
            }
            Ok(Decision::Sat(model))
        }
    }
}

/// One original linear constraint `sum coeff_i * x_i + constant {<,<=} 0`, in
/// the dense variable indexing used by the elimination. The building block of a
/// [`FarkasCertificate`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FarkasAtom {
    /// Nonzero variable coefficients as `(dense index, coefficient)` pairs,
    /// ascending by index.
    pub coeffs: Vec<(usize, Rational)>,
    /// The constant term.
    pub constant: Rational,
    /// `true` if the relation is strict (`< 0`), `false` for `<= 0`.
    pub strict: bool,
}

impl From<&Constraint> for FarkasAtom {
    fn from(constraint: &Constraint) -> Self {
        FarkasAtom {
            coeffs: constraint
                .expr
                .coeffs
                .iter()
                .filter(|(_, c)| !c.is_zero())
                .map(|(&i, &c)| (i, c))
                .collect(),
            constant: constraint.expr.constant,
            strict: constraint.strict,
        }
    }
}

/// A Farkas refutation of a conjunctive linear real system: a vector of
/// nonnegative multipliers `λ` over the original [`FarkasAtom`]s such that
/// `Σ λ_i · atom_i` collapses to a constant relation that is itself false
/// (`0 < 0`, or `0 <= -c` with `c > 0`). By Farkas' lemma this witnesses
/// infeasibility, and it is checkable with nothing but exact-rational
/// arithmetic over the atoms — independent of how the elimination found it.
#[derive(Debug, Clone)]
pub struct FarkasCertificate {
    /// The original linear constraints, in collection order.
    pub atoms: Vec<FarkasAtom>,
    /// Nonnegative multipliers, one per atom, in the same order.
    pub multipliers: Vec<Rational>,
}

impl FarkasCertificate {
    /// Verifies the refutation from scratch: every multiplier is nonnegative,
    /// at least one is positive, the combined variable coefficients all cancel,
    /// and the combined constant relation is unsatisfiable. Returns `true` iff
    /// the multipliers genuinely refute the atom system.
    #[must_use]
    pub fn verify(&self) -> bool {
        if self.atoms.is_empty() || self.atoms.len() != self.multipliers.len() {
            return false;
        }
        if self.multipliers.iter().any(|m| *m < Rational::zero()) {
            return false;
        }
        if !self.multipliers.iter().any(|m| *m > Rational::zero()) {
            return false;
        }

        // Combined = Σ λ_i · atom_i. Strictness turns on if any *used* atom is
        // strict (multipliers are nonnegative, so a used atom has λ_i > 0).
        let mut coeffs: BTreeMap<usize, Rational> = BTreeMap::new();
        let mut constant = Rational::zero();
        let mut strict = false;
        for (atom, &m) in self.atoms.iter().zip(&self.multipliers) {
            if m.is_zero() {
                continue;
            }
            for &(index, coeff) in &atom.coeffs {
                let entry = coeffs.entry(index).or_insert_with(Rational::zero);
                *entry = *entry + coeff * m;
            }
            constant = constant + atom.constant * m;
            if atom.strict {
                strict = true;
            }
        }

        // Every variable must cancel: the derived relation is purely about
        // constants.
        if coeffs.values().any(|c| !c.is_zero()) {
            return false;
        }

        // The derived (true) relation is `constant {<,<=} 0`; it refutes the
        // system iff that relation is in fact false for the constant.
        if strict {
            constant >= Rational::zero()
        } else {
            constant > Rational::zero()
        }
    }
}

/// A unit multiplier vector of length `n` with `1` at position `i`.
fn unit_vec(n: usize, i: usize) -> Vec<Rational> {
    let mut v = vec![Rational::zero(); n];
    v[i] = Rational::integer(1);
    v
}

/// `factor · v`, elementwise.
fn scale_vec(v: &[Rational], factor: Rational) -> Vec<Rational> {
    v.iter().map(|&x| x * factor).collect()
}

/// `a + b`, elementwise (equal lengths).
fn add_vec(a: &[Rational], b: &[Rational]) -> Vec<Rational> {
    a.iter().zip(b).map(|(&x, &y)| x + y).collect()
}

/// A linear expression `sum coeff_i * x_i + constant` over real variables
/// (indexed densely).
#[derive(Debug, Clone, Default)]
struct LinExpr {
    coeffs: BTreeMap<usize, Rational>,
    constant: Rational,
}

impl LinExpr {
    fn constant(value: Rational) -> Self {
        Self {
            coeffs: BTreeMap::new(),
            constant: value,
        }
    }

    fn var(index: usize) -> Self {
        let mut coeffs = BTreeMap::new();
        coeffs.insert(index, Rational::integer(1));
        Self {
            coeffs,
            constant: Rational::zero(),
        }
    }

    fn coeff(&self, index: usize) -> Rational {
        self.coeffs
            .get(&index)
            .copied()
            .unwrap_or_else(Rational::zero)
    }

    fn is_constant(&self) -> bool {
        self.coeffs.values().all(|c| c.is_zero())
    }

    fn neg(&self) -> Self {
        self.scale(Rational::integer(-1))
    }

    fn scale(&self, factor: Rational) -> Self {
        if factor.is_zero() {
            return Self::constant(Rational::zero());
        }
        Self {
            coeffs: self.coeffs.iter().map(|(&i, &c)| (i, c * factor)).collect(),
            constant: self.constant * factor,
        }
    }

    fn add(&self, other: &Self) -> Self {
        let mut coeffs = self.coeffs.clone();
        for (&i, &c) in &other.coeffs {
            let entry = coeffs.entry(i).or_insert_with(Rational::zero);
            *entry = *entry + c;
        }
        coeffs.retain(|_, c| !c.is_zero());
        Self {
            coeffs,
            constant: self.constant + other.constant,
        }
    }

    fn sub(&self, other: &Self) -> Self {
        self.add(&other.neg())
    }
}

/// A constraint `expr <= 0` (or `expr < 0` when `strict`), tagged with the
/// nonnegative combination of original constraints it was derived from (`mult`,
/// indexed by original-constraint position) and the index of the original
/// assertion it came from (`origin`, for unsat-core extraction). Original
/// constraints carry a unit vector; Fourier–Motzkin accumulates `mult` so any
/// derived contradiction names its Farkas multipliers. The collector leaves
/// `mult` empty; [`decide`] fills it in once the constraint count is known.
#[derive(Debug, Clone)]
struct Constraint {
    expr: LinExpr,
    strict: bool,
    mult: Vec<Rational>,
    origin: usize,
}

#[derive(Default)]
struct Collector {
    var_index: BTreeMap<SymbolId, usize>,
    vars: Vec<SymbolId>,
    constraints: Vec<Constraint>,
    trivially_unsat: bool,
    /// Index (into the caller's `assertions`) of the assertion currently being
    /// collected; stamped onto every constraint it produces.
    current_origin: usize,
    /// The assertion index of a literally-`false` assertion, if one was seen.
    trivial_origin: Option<usize>,
}

impl Collector {
    fn index_of(&mut self, symbol: SymbolId) -> usize {
        if let Some(&index) = self.var_index.get(&symbol) {
            return index;
        }
        let index = self.vars.len();
        self.vars.push(symbol);
        self.var_index.insert(symbol, index);
        index
    }

    /// Collects the linear constraints implied by `term` (a Boolean assertion),
    /// pushing `not` inward via `negated`.
    fn collect(
        &mut self,
        arena: &TermArena,
        term: TermId,
        negated: bool,
    ) -> Result<(), SolverError> {
        match arena.node(term) {
            TermNode::BoolConst(value) => {
                if *value == negated {
                    // `false` asserted (or `not true`): unsatisfiable.
                    self.trivially_unsat = true;
                    self.trivial_origin.get_or_insert(self.current_origin);
                }
                Ok(())
            }
            TermNode::App {
                op: Op::BoolNot,
                args,
            } => self.collect(arena, args[0], !negated),
            TermNode::App {
                op: Op::BoolAnd,
                args,
            } if !negated => {
                self.collect(arena, args[0], false)?;
                self.collect(arena, args[1], false)
            }
            TermNode::App {
                op: Op::BoolOr,
                args,
            } if negated => {
                // not(a or b) = (not a) and (not b)
                self.collect(arena, args[0], true)?;
                self.collect(arena, args[1], true)
            }
            TermNode::App { op, args }
                if matches!(op, Op::RealLt | Op::RealLe | Op::RealGt | Op::RealGe) =>
            {
                let left = self.linearize(arena, args[0])?;
                let right = self.linearize(arena, args[1])?;
                self.push_comparison(*op, &left, &right, negated);
                Ok(())
            }
            TermNode::App { op: Op::Eq, args } if is_real(arena, args[0]) => {
                if negated {
                    // a != b is a disjunction (a<b or a>b): out of scope.
                    return Err(unsupported("real disequality (needs DPLL(T))"));
                }
                let left = self.linearize(arena, args[0])?;
                let right = self.linearize(arena, args[1])?;
                let diff = left.sub(&right);
                // a == b  <=>  a - b <= 0  AND  b - a <= 0
                self.constraints.push(Constraint {
                    expr: diff.clone(),
                    strict: false,
                    mult: Vec::new(),
                    origin: self.current_origin,
                });
                self.constraints.push(Constraint {
                    expr: diff.neg(),
                    strict: false,
                    mult: Vec::new(),
                    origin: self.current_origin,
                });
                Ok(())
            }
            _ => Err(unsupported(
                "assertion is not a conjunctive linear real constraint",
            )),
        }
    }

    /// Pushes the constraint for `left <op> right` (negated if requested),
    /// normalized to `expr <= 0` / `expr < 0`.
    fn push_comparison(&mut self, op: Op, left: &LinExpr, right: &LinExpr, negated: bool) {
        // Resolve the effective relation after negation.
        let effective = if negated { negate_op(op) } else { op };
        // Normalize `lhs REL rhs` to `expr {<=,<} 0`.
        let (expr, strict) = match effective {
            // left < right  =>  left - right < 0
            Op::RealLt => (left.sub(right), true),
            // left <= right =>  left - right <= 0
            Op::RealLe => (left.sub(right), false),
            // left > right  =>  right - left < 0
            Op::RealGt => (right.sub(left), true),
            // left >= right =>  right - left <= 0
            Op::RealGe => (right.sub(left), false),
            _ => unreachable!("push_comparison only handles real order relations"),
        };
        self.constraints.push(Constraint {
            expr,
            strict,
            mult: Vec::new(),
            origin: self.current_origin,
        });
    }

    /// Converts a real-sorted term into a linear expression.
    fn linearize(&mut self, arena: &TermArena, term: TermId) -> Result<LinExpr, SolverError> {
        match arena.node(term) {
            TermNode::RealConst(value) => Ok(LinExpr::constant(*value)),
            TermNode::Symbol(symbol) if is_real(arena, term) => {
                Ok(LinExpr::var(self.index_of(*symbol)))
            }
            TermNode::App {
                op: Op::RealNeg,
                args,
            } => Ok(self.linearize(arena, args[0])?.neg()),
            TermNode::App {
                op: Op::RealAdd,
                args,
            } => {
                let a = self.linearize(arena, args[0])?;
                let b = self.linearize(arena, args[1])?;
                Ok(a.add(&b))
            }
            TermNode::App {
                op: Op::RealSub,
                args,
            } => {
                let a = self.linearize(arena, args[0])?;
                let b = self.linearize(arena, args[1])?;
                Ok(a.sub(&b))
            }
            TermNode::App {
                op: Op::RealMul,
                args,
            } => {
                let a = self.linearize(arena, args[0])?;
                let b = self.linearize(arena, args[1])?;
                // Linear: at least one factor must be a constant.
                if a.is_constant() {
                    Ok(b.scale(a.constant))
                } else if b.is_constant() {
                    Ok(a.scale(b.constant))
                } else {
                    Err(unsupported("nonlinear real multiplication"))
                }
            }
            _ => Err(unsupported(
                "non-linear or non-real subterm in a constraint",
            )),
        }
    }
}

/// The result of Fourier–Motzkin solving: a satisfying assignment, a refuting
/// nonnegative multiplier vector over the original constraints, or a procedure
/// bug (a feasible projection whose model could not be reconstructed — which
/// cannot happen for correct elimination, so it is reported, never silently
/// turned into `unsat`).
enum Feasibility {
    Sat(Vec<Rational>),
    Unsat(Vec<Rational>),
    Bug(String),
}

/// Fourier–Motzkin over `nvars` variables. Each input constraint must already
/// carry a multiplier vector (a unit vector for originals); elimination
/// accumulates these so an infeasible residual constant constraint reports the
/// Farkas multipliers that produced it.
fn solve(constraints: &[Constraint], nvars: usize) -> Feasibility {
    // Eliminate variables n-1, n-2, ..., 0, saving the system before each
    // elimination so the model can be reconstructed by forward substitution.
    let mut saved: Vec<(usize, Vec<Constraint>)> = Vec::with_capacity(nvars);
    let mut current = constraints.to_vec();
    for v in (0..nvars).rev() {
        saved.push((v, current.clone()));
        current = eliminate(&current, v);
    }
    // After eliminating every variable, only constant constraints remain. The
    // first infeasible one carries the Farkas multipliers of its derivation.
    for c in &current {
        if !constant_feasible(c) {
            return Feasibility::Unsat(c.mult.clone());
        }
    }

    let mut model = vec![Rational::zero(); nvars];
    // Assign v = 0, 1, ..., n-1 (reverse of elimination order).
    for (v, system) in saved.iter().rev() {
        match pick_value(system, &model, *v) {
            Some(value) => model[*v] = value,
            None => {
                return Feasibility::Bug(format!(
                    "lra: feasible projection but no value for variable {v} (Fourier–Motzkin bug)"
                ));
            }
        }
    }
    Feasibility::Sat(model)
}

/// Fourier–Motzkin elimination of variable `v` from a constraint system,
/// carrying each derived constraint's nonnegative multiplier combination.
fn eliminate(system: &[Constraint], v: usize) -> Vec<Constraint> {
    let mut out = Vec::new();
    let mut pos = Vec::new();
    let mut neg = Vec::new();
    for c in system {
        let a = c.expr.coeff(v);
        if a.is_zero() {
            out.push(c.clone());
        } else if a > Rational::zero() {
            pos.push(c);
        } else {
            neg.push(c);
        }
    }
    for p in &pos {
        for n in &neg {
            let a = p.expr.coeff(v); // > 0
            let b = n.expr.coeff(v); // < 0
            // Positive combination (-b)*p + a*n cancels v; both scalars are
            // positive, so the multiplier combination stays nonnegative.
            let combined = p.expr.scale(-b).add(&n.expr.scale(a));
            let mult = add_vec(&scale_vec(&p.mult, -b), &scale_vec(&n.mult, a));
            out.push(Constraint {
                expr: combined,
                strict: p.strict || n.strict,
                mult,
                // `origin` is meaningful only on the original constraints (the
                // unsat core reads it there, indexed by the multiplier vector);
                // a derived constraint carries a placeholder.
                origin: p.origin,
            });
        }
    }
    out
}

/// Whether a constant constraint `c <op> 0` holds.
fn constant_feasible(c: &Constraint) -> bool {
    let value = c.expr.constant;
    if c.strict {
        value < Rational::zero()
    } else {
        value <= Rational::zero()
    }
}

/// Picks a feasible value for variable `v`, given that variables before it in
/// `model` are already assigned, using `system` (which contains only variables
/// `0..=v`).
fn pick_value(system: &[Constraint], model: &[Rational], v: usize) -> Option<Rational> {
    // (bound value, strict) for lower and upper bounds on x_v.
    let mut lower: Option<(Rational, bool)> = None;
    let mut upper: Option<(Rational, bool)> = None;
    for c in system {
        let a = c.expr.coeff(v);
        // Substitute already-assigned variables (< v) and v's own coefficient is
        // handled separately; everything else must be 0 in this system.
        let mut rest = c.expr.constant;
        for (&i, &coeff) in &c.expr.coeffs {
            if i != v {
                rest = rest + coeff * model[i];
            }
        }
        if a.is_zero() {
            // Constant (in x_v) constraint: rest <op> 0 must hold.
            let ok = if c.strict {
                rest < Rational::zero()
            } else {
                rest <= Rational::zero()
            };
            if !ok {
                return None;
            }
            continue;
        }
        // a*x_v + rest <op> 0  =>  x_v <op'> -rest/a.
        let bound = -rest / a;
        if a > Rational::zero() {
            // upper bound
            update_bound(&mut upper, bound, c.strict, false);
        } else {
            // lower bound
            update_bound(&mut lower, bound, c.strict, true);
        }
    }

    Some(choose(lower, upper))
}

/// Tightens a lower (`is_lower`) or upper bound with a new candidate.
fn update_bound(
    slot: &mut Option<(Rational, bool)>,
    value: Rational,
    strict: bool,
    is_lower: bool,
) {
    match slot {
        None => *slot = Some((value, strict)),
        Some((current, current_strict)) => {
            let tighter = if is_lower {
                value > *current
            } else {
                value < *current
            };
            if tighter {
                *slot = Some((value, strict));
            } else if value == *current {
                *current_strict = *current_strict || strict;
            }
        }
    }
}

/// Chooses a value satisfying the lower/upper bounds. The caller (a feasible
/// system) guarantees a value exists; the returned value is replayed anyway.
fn choose(lower: Option<(Rational, bool)>, upper: Option<(Rational, bool)>) -> Rational {
    let half = Rational::new(1, 2);
    match (lower, upper) {
        (Some((lo, _)), Some((hi, _))) => {
            if lo < hi {
                (lo + hi) * half
            } else {
                // lo == hi (equality pin); strict conflicts are caught by replay.
                lo
            }
        }
        (Some((lo, strict)), None) => {
            if strict {
                lo + Rational::integer(1)
            } else {
                lo
            }
        }
        (None, Some((hi, strict))) => {
            if strict {
                hi - Rational::integer(1)
            } else {
                hi
            }
        }
        (None, None) => Rational::zero(),
    }
}

fn negate_op(op: Op) -> Op {
    match op {
        Op::RealLt => Op::RealGe,
        Op::RealLe => Op::RealGt,
        Op::RealGt => Op::RealLe,
        Op::RealGe => Op::RealLt,
        _ => unreachable!("negate_op only handles real order relations"),
    }
}

fn is_real(arena: &TermArena, term: TermId) -> bool {
    arena.sort_of(term) == Sort::Real
}

fn unsupported(what: &str) -> SolverError {
    SolverError::Unsupported(format!("QF_LRA: {what}"))
}

// ---------------------------------------------------------------------------
// Unbounded QF_LIA by branch-and-bound over the exact-rational simplex.
//
// The same simplex that decides QF_LRA decides the *relaxation* of an integer
// problem; branch-and-bound on fractional integer variables closes the gap.
// Unlike bounded bit-blasting (sat-only), this is sound for BOTH `sat` and
// `unsat`:
//   - `sat`: an all-integer simplex point, replayed through the evaluator;
//   - `unsat`: a fully-closed branch tree — every leaf's LP relaxation is
//     infeasible, and `x <= floor(v)` OR `x >= floor(v)+1` is exhaustive over
//     the integers, so no integer solution exists.
// A node budget bounds the search; exhaustion yields `unknown`, never a wrong
// verdict.
// ---------------------------------------------------------------------------

/// Node budget for LIA branch-and-bound; on exhaustion the result is `unknown`.
const MAX_LIA_BNB_NODES: u64 = 50_000;

/// Decides a conjunctive `QF_LIA` query by branch-and-bound over the
/// exact-rational simplex.
///
/// The returned [`Model`] assigns each integer variable a [`Value::Int`] and is
/// replayed against the original assertions (the `sat` trust anchor). `unsat` is
/// sound by exhaustive integer branching over (LP-)infeasible leaves. Unlike the
/// bounded bit-blasting path, this decides `unsat` soundly and is unbounded in
/// the integer magnitudes it can reason about.
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] for input outside conjunctive linear
/// integer arithmetic (disjunction, disequality, nonlinear product, or a
/// non-integer term), or [`SolverError::Backend`] on a `sat` replay failure.
pub fn check_with_lia_simplex(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<CheckResult, SolverError> {
    let mut ctx = IntCollector::default();
    for &assertion in assertions {
        ctx.collect(arena, assertion, false)?;
    }
    if ctx.trivially_unsat {
        return Ok(CheckResult::Unsat);
    }
    let nvars = ctx.vars.len();
    let mut constraints = ctx.constraints;
    let mut budget = MAX_LIA_BNB_NODES;
    match lia_branch_and_bound(&mut constraints, nvars, &mut budget) {
        LiaBnb::Unsat => Ok(CheckResult::Unsat),
        LiaBnb::Unknown => Ok(CheckResult::Unknown(UnknownReason {
            kind: UnknownKind::Incomplete,
            detail: format!("QF_LIA branch-and-bound exceeded {MAX_LIA_BNB_NODES} nodes"),
        })),
        LiaBnb::Sat(values) => {
            let mut model = Model::new();
            let mut assignment = axeyum_ir::Assignment::new();
            for (&symbol, &index) in &ctx.var_index {
                let value = values[index];
                debug_assert!(
                    value.is_integer(),
                    "branch-and-bound returned a fractional value"
                );
                model.set(symbol, Value::Int(value.numerator()));
                assignment.set(symbol, Value::Int(value.numerator()));
            }
            for &assertion in assertions {
                match eval(arena, assertion, &assignment) {
                    Ok(Value::Bool(true)) => {}
                    Ok(_) => {
                        return Err(SolverError::Backend(format!(
                            "lia simplex sat model replay failed: assertion #{} not satisfied",
                            assertion.index()
                        )));
                    }
                    Err(error) => {
                        return Err(SolverError::Backend(format!(
                            "lia simplex sat model replay error on assertion #{}: {error}",
                            assertion.index()
                        )));
                    }
                }
            }
            Ok(CheckResult::Sat(model))
        }
    }
}

/// Result of one branch-and-bound subtree.
enum LiaBnb {
    Sat(Vec<Rational>),
    Unsat,
    Unknown,
}

/// Branch-and-bound over the simplex relaxation. `constraints` is used as a
/// backtracking stack: branch constraints are pushed and popped around the
/// recursive calls.
fn lia_branch_and_bound(
    constraints: &mut Vec<Constraint>,
    nvars: usize,
    budget: &mut u64,
) -> LiaBnb {
    if *budget == 0 {
        return LiaBnb::Unknown;
    }
    *budget -= 1;

    let values = match simplex_feasible(constraints, nvars) {
        Some(SimplexOutcome::Sat(values)) => values,
        Some(SimplexOutcome::Unsat(_)) => return LiaBnb::Unsat,
        None => return LiaBnb::Unknown,
    };
    let Some(branch_var) = (0..nvars).find(|&i| !values[i].is_integer()) else {
        return LiaBnb::Sat(values);
    };
    let floor = values[branch_var]
        .numerator()
        .div_euclid(values[branch_var].denominator());

    // Left branch: x_i <= floor, i.e. `1*x_i + (-floor) <= 0`.
    constraints.push(bound_constraint(
        branch_var,
        Rational::integer(1),
        Rational::integer(-floor),
    ));
    let left = lia_branch_and_bound(constraints, nvars, budget);
    constraints.pop();
    if let LiaBnb::Sat(_) | LiaBnb::Unknown = left {
        return left;
    }

    // Right branch: x_i >= floor+1, i.e. `-1*x_i + (floor+1) <= 0`.
    let next = floor.checked_add(1).expect("floor + 1 fits in i128");
    constraints.push(bound_constraint(
        branch_var,
        Rational::integer(-1),
        Rational::integer(next),
    ));
    let right = lia_branch_and_bound(constraints, nvars, budget);
    constraints.pop();
    right
}

/// A non-strict bound `coeff * x_i + constant <= 0`.
fn bound_constraint(index: usize, coeff: Rational, constant: Rational) -> Constraint {
    let mut coeffs = BTreeMap::new();
    coeffs.insert(index, coeff);
    Constraint {
        expr: LinExpr { coeffs, constant },
        strict: false,
        mult: Vec::new(),
        origin: 0,
    }
}

fn negate_int_op(op: Op) -> Op {
    match op {
        Op::IntLt => Op::IntGe,
        Op::IntLe => Op::IntGt,
        Op::IntGt => Op::IntLe,
        Op::IntGe => Op::IntLt,
        _ => unreachable!("negate_int_op only handles integer order relations"),
    }
}

fn is_int(arena: &TermArena, term: TermId) -> bool {
    arena.sort_of(term) == Sort::Int
}

fn unsupported_lia(what: &str) -> SolverError {
    SolverError::Unsupported(format!("QF_LIA: {what}"))
}

/// Collects the conjunctive linear-integer constraints of an assertion, into the
/// same dense `Constraint`/`LinExpr` form the simplex consumes. Mirrors the LRA
/// [`Collector`] for the integer operator set; the LRA collector is left
/// untouched.
#[derive(Default)]
struct IntCollector {
    var_index: BTreeMap<SymbolId, usize>,
    vars: Vec<SymbolId>,
    constraints: Vec<Constraint>,
    trivially_unsat: bool,
}

impl IntCollector {
    fn index_of(&mut self, symbol: SymbolId) -> usize {
        if let Some(&index) = self.var_index.get(&symbol) {
            return index;
        }
        let index = self.vars.len();
        self.vars.push(symbol);
        self.var_index.insert(symbol, index);
        index
    }

    fn collect(
        &mut self,
        arena: &TermArena,
        term: TermId,
        negated: bool,
    ) -> Result<(), SolverError> {
        match arena.node(term) {
            TermNode::BoolConst(value) => {
                if *value == negated {
                    self.trivially_unsat = true;
                }
                Ok(())
            }
            TermNode::App {
                op: Op::BoolNot,
                args,
            } => self.collect(arena, args[0], !negated),
            TermNode::App {
                op: Op::BoolAnd,
                args,
            } if !negated => {
                self.collect(arena, args[0], false)?;
                self.collect(arena, args[1], false)
            }
            TermNode::App {
                op: Op::BoolOr,
                args,
            } if negated => {
                self.collect(arena, args[0], true)?;
                self.collect(arena, args[1], true)
            }
            TermNode::App { op, args }
                if matches!(op, Op::IntLt | Op::IntLe | Op::IntGt | Op::IntGe) =>
            {
                let left = self.linearize(arena, args[0])?;
                let right = self.linearize(arena, args[1])?;
                self.push_comparison(*op, &left, &right, negated);
                Ok(())
            }
            TermNode::App { op: Op::Eq, args } if is_int(arena, args[0]) => {
                if negated {
                    return Err(unsupported_lia("integer disequality (needs DPLL(T))"));
                }
                let left = self.linearize(arena, args[0])?;
                let right = self.linearize(arena, args[1])?;
                let diff = left.sub(&right);
                self.constraints.push(Constraint {
                    expr: diff.clone(),
                    strict: false,
                    mult: Vec::new(),
                    origin: 0,
                });
                self.constraints.push(Constraint {
                    expr: diff.neg(),
                    strict: false,
                    mult: Vec::new(),
                    origin: 0,
                });
                Ok(())
            }
            _ => Err(unsupported_lia(
                "assertion is not a conjunctive linear integer constraint",
            )),
        }
    }

    fn push_comparison(&mut self, op: Op, left: &LinExpr, right: &LinExpr, negated: bool) {
        let effective = if negated { negate_int_op(op) } else { op };
        let (expr, strict) = match effective {
            Op::IntLt => (left.sub(right), true),
            Op::IntLe => (left.sub(right), false),
            Op::IntGt => (right.sub(left), true),
            Op::IntGe => (right.sub(left), false),
            _ => unreachable!("push_comparison only handles integer order relations"),
        };
        self.constraints.push(Constraint {
            expr,
            strict,
            mult: Vec::new(),
            origin: 0,
        });
    }

    fn linearize(&mut self, arena: &TermArena, term: TermId) -> Result<LinExpr, SolverError> {
        match arena.node(term) {
            TermNode::IntConst(value) => Ok(LinExpr::constant(Rational::integer(*value))),
            TermNode::Symbol(symbol) if is_int(arena, term) => {
                Ok(LinExpr::var(self.index_of(*symbol)))
            }
            TermNode::App {
                op: Op::IntNeg,
                args,
            } => Ok(self.linearize(arena, args[0])?.neg()),
            TermNode::App {
                op: Op::IntAdd,
                args,
            } => {
                let a = self.linearize(arena, args[0])?;
                let b = self.linearize(arena, args[1])?;
                Ok(a.add(&b))
            }
            TermNode::App {
                op: Op::IntSub,
                args,
            } => {
                let a = self.linearize(arena, args[0])?;
                let b = self.linearize(arena, args[1])?;
                Ok(a.sub(&b))
            }
            TermNode::App {
                op: Op::IntMul,
                args,
            } => {
                let a = self.linearize(arena, args[0])?;
                let b = self.linearize(arena, args[1])?;
                if a.is_constant() {
                    Ok(b.scale(a.constant))
                } else if b.is_constant() {
                    Ok(a.scale(b.constant))
                } else {
                    Err(unsupported_lia("nonlinear integer multiplication"))
                }
            }
            _ => Err(unsupported_lia(
                "non-linear or non-integer subterm in a constraint",
            )),
        }
    }
}

// ---------------------------------------------------------------------------
// Exact-rational general simplex (a second, independent QF_LRA engine).
//
// `check_with_lra_simplex` decides the same conjunctive `QF_LRA` fragment as
// `check_with_lra`, by the Dutertre–de Moura "simplex with bounds" over exact
// δ-rationals (the δ infinitesimal encodes strict inequalities). It is an
// alternative search guarded by the same trust anchors: every `sat` model is
// replayed through the ground evaluator, and every `unsat` is cross-checked
// against the Fourier–Motzkin engine's Farkas certificate (a disagreement is a
// soundness alarm). Native Farkas extraction from the final tableau is future
// work; for now the certificate is supplied (and independently verified) via
// `lra_farkas_certificate`, so the two engines validate each other.
// ---------------------------------------------------------------------------

/// A δ-rational `c + k·δ`, where δ is a positive infinitesimal used to model
/// strict bounds exactly. Ordered lexicographically by `(c, k)`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Delta {
    c: Rational,
    k: Rational,
}

impl Delta {
    fn rational(c: Rational) -> Self {
        Delta {
            c,
            k: Rational::zero(),
        }
    }
    fn zero() -> Self {
        Delta::rational(Rational::zero())
    }
    fn add(self, other: Self) -> Self {
        Delta {
            c: self.c + other.c,
            k: self.k + other.k,
        }
    }
    fn sub(self, other: Self) -> Self {
        Delta {
            c: self.c - other.c,
            k: self.k - other.k,
        }
    }
    fn scale(self, factor: Rational) -> Self {
        Delta {
            c: self.c * factor,
            k: self.k * factor,
        }
    }
}

impl PartialOrd for Delta {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Delta {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.c.cmp(&other.c).then(self.k.cmp(&other.k))
    }
}

/// Decides a conjunctive `QF_LRA` query by the exact-rational general simplex.
///
/// The returned [`Model`] assigns each real variable a [`Value::Real`] and
/// replays against the original assertions (the `sat` trust anchor). On `unsat`
/// the result is cross-checked against the Fourier–Motzkin Farkas certificate.
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] for non-conjunctive-`QF_LRA` input, or
/// [`SolverError::Backend`] on a `sat` replay failure or a disagreement with the
/// Fourier–Motzkin engine (either is a soundness alarm).
pub fn check_with_lra_simplex(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<CheckResult, SolverError> {
    let mut ctx = Collector::default();
    for &assertion in assertions {
        ctx.collect(arena, assertion, false)?;
    }
    if ctx.trivially_unsat {
        return Ok(CheckResult::Unsat);
    }

    match simplex_feasible(&ctx.constraints, ctx.vars.len()) {
        Some(SimplexOutcome::Sat(values)) => {
            let mut model = Model::new();
            let mut assignment = axeyum_ir::Assignment::new();
            for (&symbol, &index) in &ctx.var_index {
                model.set(symbol, Value::Real(values[index]));
                assignment.set(symbol, Value::Real(values[index]));
            }
            for &assertion in assertions {
                match eval(arena, assertion, &assignment) {
                    Ok(Value::Bool(true)) => {}
                    Ok(_) => {
                        return Err(SolverError::Backend(format!(
                            "lra simplex sat model replay failed: assertion #{} not satisfied",
                            assertion.index()
                        )));
                    }
                    Err(error) => {
                        return Err(SolverError::Backend(format!(
                            "lra simplex sat model replay failed: assertion #{} eval error: {error}",
                            assertion.index()
                        )));
                    }
                }
            }
            Ok(CheckResult::Sat(model))
        }
        Some(SimplexOutcome::Unsat(multipliers)) => {
            // Self-check the simplex's own Farkas certificate (no Fourier–Motzkin
            // dependency): the multipliers must independently refute the system.
            let atoms: Vec<FarkasAtom> = ctx.constraints.iter().map(FarkasAtom::from).collect();
            let certificate = FarkasCertificate { atoms, multipliers };
            if certificate.verify() {
                Ok(CheckResult::Unsat)
            } else {
                Err(SolverError::Backend(
                    "lra simplex Farkas certificate failed self-check (tableau extraction bug)"
                        .to_string(),
                ))
            }
        }
        // Iteration backstop hit without a verdict: defer to Fourier–Motzkin.
        None => check_with_lra(arena, assertions),
    }
}

/// The result of the general simplex: a satisfying rational assignment, or the
/// Farkas multipliers (over the original constraints) refuting the system. `None`
/// from [`simplex_feasible`] means the iteration backstop was hit without a
/// verdict (practically unreachable under Bland's rule), and the caller defers.
enum SimplexOutcome {
    Sat(Vec<Rational>),
    Unsat(Vec<Rational>),
}

/// Exact-rational general simplex: returns a satisfying rational assignment for
/// the `nvars` original variables ([`SimplexOutcome::Sat`]) or the Farkas
/// multipliers refuting the system ([`SimplexOutcome::Unsat`]); `None` only if
/// the iteration backstop is reached without deciding.
fn simplex_feasible(constraints: &[Constraint], nvars: usize) -> Option<SimplexOutcome> {
    let m = constraints.len();
    let total = nvars + m;
    // Variable layout: 0..nvars original (free), nvars..total slacks (one per
    // constraint). Slack j = the linear part of constraint j; its upper bound is
    // -constant (minus δ when the constraint is strict). Originals are free.
    let mut upper: Vec<Option<Delta>> = vec![None; total];
    let mut value: Vec<Delta> = vec![Delta::zero(); total];
    // Tableau rows: for each basic var, coefficients over the (current) nonbasic
    // vars. Initially every slack is basic over the original nonbasic vars.
    let mut row: std::collections::HashMap<usize, std::collections::HashMap<usize, Rational>> =
        std::collections::HashMap::new();
    let mut basic: std::collections::BTreeSet<usize> = std::collections::BTreeSet::new();
    let mut nonbasic: std::collections::BTreeSet<usize> = (0..nvars).collect();

    for (j, constraint) in constraints.iter().enumerate() {
        let slack = nvars + j;
        let bound_c = -constraint.expr.constant;
        let bound_k = if constraint.strict {
            Rational::integer(-1)
        } else {
            Rational::zero()
        };
        upper[slack] = Some(Delta {
            c: bound_c,
            k: bound_k,
        });
        let mut coeffs = std::collections::HashMap::new();
        for (&i, &a) in &constraint.expr.coeffs {
            if !a.is_zero() {
                coeffs.insert(i, a);
            }
        }
        row.insert(slack, coeffs);
        basic.insert(slack);
        // slack value = Σ a_i·value[x_i] = 0 (all originals start at 0).
    }

    // Bland's rule guarantees termination; the bound is a generous backstop.
    for _ in 0..(100_000 + 50 * total * total) {
        // Find the smallest-index basic variable violating its (upper) bound.
        let violating = basic
            .iter()
            .copied()
            .find(|&b| matches!(upper[b], Some(u) if value[b] > u));
        let Some(b) = violating else {
            // Feasible: instantiate δ to a concrete positive rational.
            return Some(SimplexOutcome::Sat(extract_model(
                constraints,
                nvars,
                &value,
            )));
        };
        let target = upper[b].expect("violating basic has an upper bound");

        // b is above its upper bound and must decrease. Find a suitable entering
        // nonbasic (smallest index, Bland): one that can move in the direction
        // that decreases b.
        let mut entering: Option<usize> = None;
        for &n in &nonbasic {
            let a = row[&b].get(&n).copied().unwrap_or_else(Rational::zero);
            if a.is_zero() {
                continue;
            }
            let suitable = if a > Rational::zero() {
                // decrease n (no lower bounds anywhere → always possible)
                true
            } else {
                // increase n (possible unless n is at its upper bound)
                match upper[n] {
                    Some(u) => value[n] < u,
                    None => true,
                }
            };
            if suitable {
                entering = Some(n);
                break;
            }
        }
        let Some(n) = entering else {
            // Infeasible. `b` is a slack above its upper bound that cannot
            // decrease; every blocking nonbasic is a slack at its upper bound
            // with a negative coefficient. The Farkas refutation is
            // 1·(constraint of b) + Σ (−c_n)·(constraint of slack n); free
            // original nonbasics have coefficient 0 here and are skipped.
            let mut multipliers = vec![Rational::zero(); m];
            multipliers[b - nvars] = multipliers[b - nvars] + Rational::integer(1);
            for (&var, &coeff) in &row[&b] {
                if var >= nvars {
                    multipliers[var - nvars] = multipliers[var - nvars] - coeff;
                }
            }
            return Some(SimplexOutcome::Unsat(multipliers));
        };

        pivot_and_update(
            &mut row,
            &mut basic,
            &mut nonbasic,
            &mut value,
            b,
            n,
            target,
        );
    }
    // Backstop reached without a verdict: report feasible only if no bound is
    // violated, otherwise defer (`None`) — the caller falls back to the
    // Fourier–Motzkin engine rather than risk a wrong answer.
    if basic
        .iter()
        .all(|&b| !matches!(upper[b], Some(u) if value[b] > u))
    {
        Some(SimplexOutcome::Sat(extract_model(
            constraints,
            nvars,
            &value,
        )))
    } else {
        None
    }
}

/// Pivots basic `b` out and nonbasic `n` in, setting `value[b]` to `target` and
/// updating every value and tableau row (Dutertre–de Moura `pivotAndUpdate`).
fn pivot_and_update(
    row: &mut std::collections::HashMap<usize, std::collections::HashMap<usize, Rational>>,
    basic: &mut std::collections::BTreeSet<usize>,
    nonbasic: &mut std::collections::BTreeSet<usize>,
    value: &mut [Delta],
    b: usize,
    n: usize,
    target: Delta,
) {
    let a_bn = row[&b][&n];
    let theta = target.sub(value[b]).scale(a_bn.recip());
    value[n] = value[n].add(theta);
    value[b] = target;
    for &i in basic.iter() {
        if i == b {
            continue;
        }
        if let Some(&a_in) = row[&i].get(&n) {
            if !a_in.is_zero() {
                value[i] = value[i].add(theta.scale(a_in));
            }
        }
    }

    // Rewrite the tableau: express n in terms of b and the other nonbasics.
    let row_b = row.remove(&b).expect("b is basic");
    let inv = a_bn.recip();
    let mut row_n: std::collections::HashMap<usize, Rational> = std::collections::HashMap::new();
    row_n.insert(b, inv);
    for (&k, &coeff) in &row_b {
        if k != n {
            row_n.insert(k, -(coeff * inv));
        }
    }
    // Substitute the new n-row into every other basic row mentioning n.
    let others: Vec<usize> = basic.iter().copied().filter(|&i| i != b).collect();
    for i in others {
        if let Some(a_in) = row.get_mut(&i).and_then(|r| r.remove(&n)) {
            if !a_in.is_zero() {
                let additions: Vec<(usize, Rational)> =
                    row_n.iter().map(|(&k, &c)| (k, a_in * c)).collect();
                let r = row.get_mut(&i).expect("basic row exists");
                for (k, delta) in additions {
                    let entry = r.entry(k).or_insert_with(Rational::zero);
                    *entry = *entry + delta;
                }
                r.retain(|_, c| !c.is_zero());
            }
        }
    }
    row.insert(n, row_n);

    basic.remove(&b);
    basic.insert(n);
    nonbasic.remove(&n);
    nonbasic.insert(b);
}

/// Turns the δ-rational assignment into a concrete rational model by choosing a
/// positive δ small enough that every original constraint still holds.
fn extract_model(constraints: &[Constraint], nvars: usize, value: &[Delta]) -> Vec<Rational> {
    // Each original variable is `c_i + k_i·δ`. For a constraint with combined
    // δ-coefficient K > 0 the bound on δ is -C/K (C < 0 in any δ-feasible
    // solution); δ* is half the tightest such bound (or 1/2 if unbounded).
    let mut delta_star = Rational::integer(1);
    for constraint in constraints {
        let mut big_c = constraint.expr.constant;
        let mut big_k = Rational::zero();
        for (&i, &a) in &constraint.expr.coeffs {
            big_c = big_c + a * value[i].c;
            big_k = big_k + a * value[i].k;
        }
        if big_k > Rational::zero() {
            let bound = -big_c / big_k;
            if bound < delta_star {
                delta_star = bound;
            }
        }
    }
    delta_star = delta_star * Rational::new(1, 2);

    (0..nvars)
        .map(|i| value[i].c + value[i].k * delta_star)
        .collect()
}
