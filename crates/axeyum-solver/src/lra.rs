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

use crate::backend::{CheckResult, SolverError};
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
