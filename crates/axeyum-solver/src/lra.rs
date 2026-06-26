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

// Native uses the std clock; wasm uses the `web_time` drop-in (ADR-0017).
#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;
#[cfg(target_arch = "wasm32")]
use web_time::Instant;

use axeyum_ir::{Op, Rational, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval};

use crate::backend::{CheckResult, SolverError, UnknownKind, UnknownReason};
use crate::model::Model;

/// Whether `deadline` (if set) has passed.
fn past_deadline(deadline: Option<Instant>) -> bool {
    deadline.is_some_and(|d| Instant::now() >= d)
}

/// Non-negative gcd of two `i128`s (`gcd(0, x) = |x|`), for integer-tightening.
/// Callers guard `|a|, |b| < TIGHTEN_COEFF_LIMIT`, so `abs()` cannot overflow.
fn gcd_i128(a: i128, b: i128) -> i128 {
    let (mut a, mut b) = (a.abs(), b.abs());
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

/// Coefficient/constant magnitude bound for applying integer tightening. Real LIA
/// coefficients are tiny; above this the constraint is left strict (sound, no
/// tightening) so the gcd/`⌊⌋` arithmetic below cannot overflow `i128`.
const TIGHTEN_COEFF_LIMIT: i128 = 1 << 62;

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
    check_with_lra_within(arena, assertions, None)
}

/// Like [`check_with_lra`], but bailing to a timely `unknown` once `deadline`
/// (an absolute [`Instant`]) has passed during the Fourier–Motzkin elimination.
///
/// Fourier–Motzkin can blow up combinatorially — each variable elimination
/// replaces `m` lower + `n` upper bounds with `m·n` derived constraints, which
/// compounds across eliminations — so a single `decide` call can run for many
/// seconds with no interruption point, overrunning the caller's deterministic
/// budget. This variant threads the deadline into the elimination loop (checked
/// before each variable is eliminated) and a deterministic constraint-count
/// admission guard, so the call degrades to `unknown` rather than overrunning.
///
/// Bailing to `unknown` is sound — the deadline never converts a `sat`/`unsat`
/// into a wrong verdict — and `deadline == None` is exactly [`check_with_lra`].
///
/// # Errors
///
/// Same as [`check_with_lra`].
pub fn check_with_lra_within(
    arena: &TermArena,
    assertions: &[TermId],
    deadline: Option<Instant>,
) -> Result<CheckResult, SolverError> {
    match decide_within(arena, assertions, deadline)? {
        Decision::Sat(model) => Ok(CheckResult::Sat(model)),
        Decision::UnsatFarkas { .. } | Decision::UnsatTrivial(_) => Ok(CheckResult::Unsat),
        Decision::TimedOut => Ok(CheckResult::Unknown(UnknownReason {
            kind: UnknownKind::ResourceLimit,
            detail: "lra: Fourier–Motzkin elimination exceeded the wall-clock / size budget"
                .to_owned(),
        })),
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
        Decision::Sat(_) | Decision::UnsatTrivial(_) | Decision::TimedOut => Ok(None),
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
        Decision::Sat(_) | Decision::TimedOut => Ok(None),
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
    /// The Fourier–Motzkin elimination did not finish within the wall-clock /
    /// size budget; the query is left undecided (a timely, sound `unknown`).
    TimedOut,
}

fn decide(arena: &TermArena, assertions: &[TermId]) -> Result<Decision, SolverError> {
    decide_within(arena, assertions, None)
}

fn decide_within(
    arena: &TermArena,
    assertions: &[TermId],
    deadline: Option<Instant>,
) -> Result<Decision, SolverError> {
    let mut ctx = Collector::default();
    for (index, &assertion) in assertions.iter().enumerate() {
        ctx.current_origin = index;
        ctx.collect(arena, assertion, false)?;
    }
    // An `i128` overflow while linearizing poisons the collection: the
    // placeholder constraints are garbage and must not be interpreted. Degrade to
    // a graceful `unknown` BEFORE any constraint is solved (overflow never becomes
    // a wrong sat/unsat).
    if ctx.overflow {
        return Ok(Decision::TimedOut);
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
    match solve(&ctx.constraints, nvars, deadline) {
        Feasibility::TimedOut => Ok(Decision::TimedOut),
        Feasibility::Unsat(multipliers) => {
            let certificate = FarkasCertificate {
                atoms,
                multipliers,
                origins: origins.clone(),
                vars: ctx.vars.clone(),
            };
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
    /// `origins[i]` is the index, into the original `assertions` slice, of the
    /// atom `atoms[i]`. An inequality assertion contributes exactly one atom; an
    /// equality `a = b` contributes two (the `a − b ≤ 0` and `b − a ≤ 0` bounds),
    /// so several atoms can share one origin. Indices are in atom order (the
    /// deterministic collection order), so this stays a public determinism
    /// promise.
    pub origins: Vec<usize>,
    /// Maps the dense variable index used in [`FarkasAtom::coeffs`] back to its
    /// [`SymbolId`]: a coefficient pair `(idx, c)` refers to symbol `vars[idx]`.
    /// In dense-index (first-seen) order; lets a consumer (e.g. the Craig
    /// interpolant extractor) turn a Farkas combination back into a typed term.
    pub vars: Vec<SymbolId>,
}

impl FarkasCertificate {
    /// Verifies the refutation from scratch: every multiplier is nonnegative,
    /// at least one is positive, the combined variable coefficients all cancel,
    /// and the combined constant relation is unsatisfiable. Returns `true` iff
    /// the multipliers genuinely refute the atom system.
    #[must_use]
    pub fn verify(&self) -> bool {
        use core::cmp::Ordering;
        if self.atoms.is_empty() || self.atoms.len() != self.multipliers.len() {
            return false;
        }
        let zero = Rational::zero();
        // Overflow-safe sign checks: a multiplier that is not provably `>= 0`
        // (negative, or uncomparable because of an `i128` overflow) refutes the
        // certificate — a failed self-check never licenses a wrong `unsat`.
        if self
            .multipliers
            .iter()
            .any(|m| matches!(m.checked_cmp(&zero), Some(Ordering::Less) | None))
        {
            return false;
        }
        // At least one multiplier must be strictly positive.
        if !self
            .multipliers
            .iter()
            .any(|m| m.checked_cmp(&zero) == Some(Ordering::Greater))
        {
            return false;
        }

        // Combined = Σ λ_i · atom_i. Strictness turns on if any *used* atom is
        // strict (multipliers are nonnegative, so a used atom has λ_i > 0).
        // Any overflow here means the refutation cannot be reconstructed exactly,
        // so we conservatively report it does not verify (overflow never proves an
        // `unsat`).
        let mut coeffs: BTreeMap<usize, Rational> = BTreeMap::new();
        let mut constant = Rational::zero();
        let mut strict = false;
        for (atom, &m) in self.atoms.iter().zip(&self.multipliers) {
            if m.is_zero() {
                continue;
            }
            for &(index, coeff) in &atom.coeffs {
                let entry = coeffs.entry(index).or_insert_with(Rational::zero);
                let Some(term) = coeff.checked_mul(m) else {
                    return false;
                };
                let Some(sum) = (*entry).checked_add(term) else {
                    return false;
                };
                *entry = sum;
            }
            let Some(term) = atom.constant.checked_mul(m) else {
                return false;
            };
            let Some(sum) = constant.checked_add(term) else {
                return false;
            };
            constant = sum;
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
        match constant.checked_cmp(&zero) {
            Some(Ordering::Greater) => true,
            // `0` refutes only a strict `< 0` relation (`0 < 0` is false).
            Some(Ordering::Equal) => strict,
            Some(Ordering::Less) | None => false,
        }
    }
}

/// A unit multiplier vector of length `n` with `1` at position `i`.
fn unit_vec(n: usize, i: usize) -> Vec<Rational> {
    let mut v = vec![Rational::zero(); n];
    v[i] = Rational::integer(1);
    v
}

/// `factor · v`, elementwise; `None` on `i128` overflow (→ `unknown` upstream).
fn scale_vec(v: &[Rational], factor: Rational) -> Option<Vec<Rational>> {
    v.iter().map(|&x| x.checked_mul(factor)).collect()
}

/// `a + b`, elementwise (equal lengths); `None` on overflow (→ `unknown`).
fn add_vec(a: &[Rational], b: &[Rational]) -> Option<Vec<Rational>> {
    a.iter().zip(b).map(|(&x, &y)| x.checked_add(y)).collect()
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

    /// Exact negation, `None` on `i128` overflow (degrades to `unknown` upstream).
    fn neg(&self) -> Option<Self> {
        self.scale(Rational::integer(-1))
    }

    /// Exact scaling, `None` on `i128` overflow (degrades to `unknown` upstream).
    fn scale(&self, factor: Rational) -> Option<Self> {
        if factor.is_zero() {
            return Some(Self::constant(Rational::zero()));
        }
        let mut coeffs = BTreeMap::new();
        for (&i, &c) in &self.coeffs {
            coeffs.insert(i, c.checked_mul(factor)?);
        }
        Some(Self {
            coeffs,
            constant: self.constant.checked_mul(factor)?,
        })
    }

    /// Exact addition, `None` on `i128` overflow (degrades to `unknown` upstream).
    fn add(&self, other: &Self) -> Option<Self> {
        let mut coeffs = self.coeffs.clone();
        for (&i, &c) in &other.coeffs {
            let entry = coeffs.entry(i).or_insert_with(Rational::zero);
            *entry = (*entry).checked_add(c)?;
        }
        coeffs.retain(|_, c| !c.is_zero());
        Some(Self {
            coeffs,
            constant: self.constant.checked_add(other.constant)?,
        })
    }

    /// Exact subtraction, `None` on `i128` overflow (degrades to `unknown`).
    fn sub(&self, other: &Self) -> Option<Self> {
        self.add(&other.neg()?)
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
    /// Set when an `i128` overflow was hit while building a linear expression.
    /// Mirrors `trivially_unsat`: a poisoned collection must NOT be interpreted —
    /// `decide_within` bails to a graceful `unknown` before any constraint is
    /// solved, so the harmless placeholder we substitute for an overflowed
    /// expression can never change a verdict (overflow → `unknown`, full stop).
    overflow: bool,
    /// Index (into the caller's `assertions`) of the assertion currently being
    /// collected; stamped onto every constraint it produces.
    current_origin: usize,
    /// The assertion index of a literally-`false` assertion, if one was seen.
    trivial_origin: Option<usize>,
}

impl Collector {
    /// Unwraps an overflow-checked `LinExpr`; on overflow (`None`) sets the
    /// `overflow` poison flag and returns a harmless zero placeholder so the
    /// collector stays total. The placeholder is never acted on: `decide_within`
    /// checks `overflow` after collection and bails to `unknown` first.
    fn guard(&mut self, expr: Option<LinExpr>) -> LinExpr {
        if let Some(e) = expr {
            e
        } else {
            self.overflow = true;
            LinExpr::constant(Rational::zero())
        }
    }

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
                let diff = self.guard(left.sub(&right));
                let diff_neg = self.guard(diff.neg());
                // a == b  <=>  a - b <= 0  AND  b - a <= 0
                self.constraints.push(Constraint {
                    expr: diff,
                    strict: false,
                    mult: Vec::new(),
                    origin: self.current_origin,
                });
                self.constraints.push(Constraint {
                    expr: diff_neg,
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
        let expr = self.guard(expr);
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
            } => {
                let a = self.linearize(arena, args[0])?;
                Ok(self.guard(a.neg()))
            }
            TermNode::App {
                op: Op::RealAdd,
                args,
            } => {
                let a = self.linearize(arena, args[0])?;
                let b = self.linearize(arena, args[1])?;
                Ok(self.guard(a.add(&b)))
            }
            TermNode::App {
                op: Op::RealSub,
                args,
            } => {
                let a = self.linearize(arena, args[0])?;
                let b = self.linearize(arena, args[1])?;
                Ok(self.guard(a.sub(&b)))
            }
            TermNode::App {
                op: Op::RealMul,
                args,
            } => {
                let a = self.linearize(arena, args[0])?;
                let b = self.linearize(arena, args[1])?;
                // Linear: at least one factor must be a constant.
                if a.is_constant() {
                    Ok(self.guard(b.scale(a.constant)))
                } else if b.is_constant() {
                    Ok(self.guard(a.scale(b.constant)))
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
    /// Elimination ran past the wall-clock deadline or the size guard before a
    /// verdict; left undecided (a sound `unknown` upstream).
    TimedOut,
}

/// Hard ceiling on the number of constraints any single Fourier–Motzkin
/// elimination step may produce. Each step replaces the `pos`/`neg` bound sets
/// with their `|pos|·|neg|` cross product, so a deeply coupled system can blow
/// up double-exponentially in *one* `decide` call — uninterruptibly, since the
/// elimination is a tight loop with no theory callbacks. Above this bound the
/// step declines to `unknown` deterministically (independent of the clock), so
/// the result is reproducible regardless of machine speed.
const MAX_FM_CONSTRAINTS: usize = 20_000;

/// Fourier–Motzkin over `nvars` variables. Each input constraint must already
/// carry a multiplier vector (a unit vector for originals); elimination
/// accumulates these so an infeasible residual constant constraint reports the
/// Farkas multipliers that produced it.
fn solve(constraints: &[Constraint], nvars: usize, deadline: Option<Instant>) -> Feasibility {
    // Eliminate variables n-1, n-2, ..., 0, saving the system before each
    // elimination so the model can be reconstructed by forward substitution.
    let mut saved: Vec<(usize, Vec<Constraint>)> = Vec::with_capacity(nvars);
    let mut current = constraints.to_vec();
    for v in (0..nvars).rev() {
        // Wall-clock bound: this loop is uninterruptible (a tight exact-rational
        // cross product per step), so a long elimination would overrun the
        // caller's deterministic budget. Bail to a timely `unknown` instead.
        if past_deadline(deadline) {
            return Feasibility::TimedOut;
        }
        saved.push((v, current.clone()));
        match eliminate(&current, v, deadline) {
            Some(next) => current = next,
            None => return Feasibility::TimedOut,
        }
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
            PickValue::Value(value) => model[*v] = value,
            // Overflow during back-substitution: degrade to a graceful `unknown`
            // (never a wrong verdict, never a spurious `Bug` soundness alarm).
            PickValue::Overflow => return Feasibility::TimedOut,
            PickValue::NoValue => {
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
///
/// Returns `None` to bail (a sound `unknown` upstream) when the wall-clock
/// `deadline` passes mid-elimination, or when the derived system would exceed
/// [`MAX_FM_CONSTRAINTS`] (a deterministic, clock-independent size guard against
/// the `|pos|·|neg|` cross-product blowup).
fn eliminate(
    system: &[Constraint],
    v: usize,
    deadline: Option<Instant>,
) -> Option<Vec<Constraint>> {
    let mut out = Vec::new();
    let mut pos = Vec::new();
    let mut neg = Vec::new();
    let zero = Rational::zero();
    for c in system {
        let a = c.expr.coeff(v);
        if a.is_zero() {
            out.push(c.clone());
        } else {
            // Overflow here (uncomparable sign) degrades to `unknown`, never a
            // wrong verdict.
            match a.checked_cmp(&zero)? {
                core::cmp::Ordering::Greater => pos.push(c),
                core::cmp::Ordering::Less => neg.push(c),
                core::cmp::Ordering::Equal => out.push(c.clone()),
            }
        }
    }
    // Deterministic size guard: refuse a cross product that would blow past the
    // admission bound before doing the (potentially huge, uninterruptible) work.
    if out
        .len()
        .saturating_add(pos.len().saturating_mul(neg.len()))
        > MAX_FM_CONSTRAINTS
    {
        return None;
    }
    for (i, p) in pos.iter().enumerate() {
        // Re-check the wall clock periodically inside the cross product (rows can
        // still be many thousands even under the size guard).
        if i % 64 == 0 && past_deadline(deadline) {
            return None;
        }
        for n in &neg {
            let a = p.expr.coeff(v); // > 0
            let b = n.expr.coeff(v); // < 0
            // Positive combination (-b)*p + a*n cancels v; both scalars are
            // positive, so the multiplier combination stays nonnegative.
            // Coefficient blowup mid-elimination overflows `i128`; degrade to a
            // graceful `unknown` (`None`) rather than panic or wrong-answer.
            let neg_b = b.checked_neg()?;
            let combined = p.expr.scale(neg_b)?.add(&n.expr.scale(a)?)?;
            let mult = add_vec(&scale_vec(&p.mult, neg_b)?, &scale_vec(&n.mult, a)?)?;
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
    Some(out)
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

/// Outcome of [`pick_value`]: a feasible value, a genuine no-value (a
/// Fourier–Motzkin bug — reported, never silently turned into `unsat`), or an
/// `i128` overflow during back-substitution (degrades to a graceful `unknown`).
enum PickValue {
    Value(Rational),
    NoValue,
    Overflow,
}

/// Picks a feasible value for variable `v`, given that variables before it in
/// `model` are already assigned, using `system` (which contains only variables
/// `0..=v`). Any `i128` overflow yields [`PickValue::Overflow`] (→ `unknown`).
fn pick_value(system: &[Constraint], model: &[Rational], v: usize) -> PickValue {
    use core::cmp::Ordering;
    let zero = Rational::zero();
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
                let Some(term) = coeff.checked_mul(model[i]) else {
                    return PickValue::Overflow;
                };
                let Some(sum) = rest.checked_add(term) else {
                    return PickValue::Overflow;
                };
                rest = sum;
            }
        }
        if a.is_zero() {
            // Constant (in x_v) constraint: rest <op> 0 must hold (compared to
            // zero, so the cross-multiplication never overflows).
            let ok = if c.strict { rest < zero } else { rest <= zero };
            if !ok {
                return PickValue::NoValue;
            }
            continue;
        }
        // a*x_v + rest <op> 0  =>  x_v <op'> -rest/a.
        let Some(bound) = rest.checked_neg().and_then(|nr| nr.checked_div(a)) else {
            return PickValue::Overflow;
        };
        // Sign of `a` decides upper vs lower; compared to zero, never overflows.
        match a.cmp(&zero) {
            Ordering::Greater => {
                if update_bound(&mut upper, bound, c.strict, false).is_none() {
                    return PickValue::Overflow;
                }
            }
            Ordering::Less => {
                if update_bound(&mut lower, bound, c.strict, true).is_none() {
                    return PickValue::Overflow;
                }
            }
            Ordering::Equal => unreachable!("a is non-zero here"),
        }
    }

    match choose(lower, upper) {
        Some(value) => PickValue::Value(value),
        None => PickValue::Overflow,
    }
}

/// Tightens a lower (`is_lower`) or upper bound with a new candidate. Returns
/// `None` on an `i128` overflow during the bound comparison (→ `unknown`).
fn update_bound(
    slot: &mut Option<(Rational, bool)>,
    value: Rational,
    strict: bool,
    is_lower: bool,
) -> Option<()> {
    use core::cmp::Ordering;
    match slot {
        None => *slot = Some((value, strict)),
        Some((current, current_strict)) => {
            let order = value.checked_cmp(current)?;
            let tighter = if is_lower {
                order == Ordering::Greater
            } else {
                order == Ordering::Less
            };
            if tighter {
                *slot = Some((value, strict));
            } else if order == Ordering::Equal {
                *current_strict = *current_strict || strict;
            }
        }
    }
    Some(())
}

/// Chooses a value satisfying the lower/upper bounds. The caller (a feasible
/// system) guarantees a value exists; the returned value is replayed anyway.
/// `None` on an `i128` overflow building the midpoint (→ `unknown`).
fn choose(lower: Option<(Rational, bool)>, upper: Option<(Rational, bool)>) -> Option<Rational> {
    use core::cmp::Ordering;
    let half = Rational::new(1, 2);
    let value = match (lower, upper) {
        (Some((lo, _)), Some((hi, _))) => {
            match lo.checked_cmp(&hi)? {
                Ordering::Less => lo.checked_add(hi)?.checked_mul(half)?,
                // lo >= hi (equality pin); strict conflicts are caught by replay.
                _ => lo,
            }
        }
        (Some((lo, strict)), None) => {
            if strict {
                lo.checked_add(Rational::integer(1))?
            } else {
                lo
            }
        }
        (None, Some((hi, strict))) => {
            if strict {
                hi.checked_sub(Rational::integer(1))?
            } else {
                hi
            }
        }
        (None, None) => Rational::zero(),
    };
    Some(value)
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
    lia_simplex_within(arena, assertions, None)
}

/// Like [`check_with_lia_simplex`], but bailing to `unknown` once `deadline` (a
/// wall-clock budget, typically derived from `SolverConfig::timeout`) passes — so a
/// branch-and-bound grinding on an unbounded integer difference constraint
/// (`c > y ∧ c < y+1`) honors the caller's timeout instead of running to the node
/// budget. `deadline == None` is exactly [`check_with_lia_simplex`].
pub fn check_with_lia_simplex_within(
    arena: &TermArena,
    assertions: &[TermId],
    deadline: Option<Instant>,
) -> Result<CheckResult, SolverError> {
    lia_simplex_with_options(arena, assertions, deadline, false)
}

/// Conjunctive LIA oracle that treats integer-valued uninterpreted-function
/// applications as opaque integer variables. This is sound for UNSAT transfer:
/// the abstraction is a relaxation of the original UFLIA constraints. A
/// satisfiable abstraction is not a full UFLIA model, so it deliberately returns
/// `Unknown` instead of `Sat`.
pub(crate) fn check_with_lia_opaque_apps(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<CheckResult, SolverError> {
    lia_simplex_with_options(arena, assertions, None, true)
}

fn lia_simplex_within(
    arena: &TermArena,
    assertions: &[TermId],
    deadline: Option<Instant>,
) -> Result<CheckResult, SolverError> {
    lia_simplex_with_options(arena, assertions, deadline, false)
}

fn lia_simplex_with_options(
    arena: &TermArena,
    assertions: &[TermId],
    deadline: Option<Instant>,
    allow_opaque_apps: bool,
) -> Result<CheckResult, SolverError> {
    let mut ctx = IntCollector::new(allow_opaque_apps);
    for (index, &assertion) in assertions.iter().enumerate() {
        ctx.current_origin = index;
        ctx.collect(arena, assertion, false)?;
    }
    // An `i128` overflow while linearizing poisons the collection; degrade to a
    // graceful `unknown` before any constraint is interpreted (never a wrong
    // verdict).
    if ctx.overflow {
        return Ok(CheckResult::Unknown(UnknownReason {
            kind: UnknownKind::ResourceLimit,
            detail: "lia simplex: i128 overflow while linearizing the integer constraints"
                .to_owned(),
        }));
    }
    if ctx.trivially_unsat {
        return Ok(CheckResult::Unsat);
    }
    let nvars = ctx.variable_count();
    let has_opaque_vars = ctx.has_opaque_vars();
    let mut constraints = ctx.constraints;
    // Integer tightening (gcd-aware): a *strict* constraint `L + c0 < 0` whose variable
    // part `L = Σ aᵢ·xᵢ` has integral coefficients and integral constant is, over the
    // integers, equivalent to a NON-strict bound — and tightening it makes the LP
    // relaxation EXACT, so the integer-infeasible cases decide immediately instead of
    // branch-and-bound grinding. `L` is a multiple of `g = gcd(aᵢ)`, so `L + c0 < 0`
    // ⟺ `L ≤ -c0-1` ⟺ `L ≤ g·⌊(-c0-1)/g⌋`. The new constant is `-g·⌊(-c0-1)/g⌋`
    // (which reduces to `c0+1` when `g = 1`). E.g. `2x < 2y` (g=2) ⟹ `2x-2y ≤ -2` (not
    // the loose `≤ -1`), so `2x<2y ∧ 2y<2x+2` is LP-infeasible (`unsat`). Only applied
    // when `L`/`c0` are provably integral (else left strict — sound; simplex handles it).
    for constraint in &mut constraints {
        if !constraint.strict
            || !constraint.expr.constant.is_integer()
            || !constraint.expr.coeffs.values().all(|r| r.is_integer())
        {
            continue;
        }
        let c0 = constraint.expr.constant.numerator();
        // Guard magnitudes so the arithmetic below cannot overflow; an out-of-range
        // coefficient just leaves this constraint strict (sound — simplex handles it).
        if c0.abs() >= TIGHTEN_COEFF_LIMIT
            || constraint
                .expr
                .coeffs
                .values()
                .any(|r| r.numerator().abs() >= TIGHTEN_COEFF_LIMIT)
        {
            continue;
        }
        let g = constraint
            .expr
            .coeffs
            .values()
            .fold(0i128, |g, r| gcd_i128(g, r.numerator()));
        // `L + c0 < 0` (L a multiple of g) ⟺ `L ≤ g·⌊(-c0-1)/g⌋`; new constant is its
        // negation. `g = 0` (no variables) ⟹ `c0 + 1`, the same as the `g = 1` formula.
        let new_const = if g == 0 {
            c0 + 1
        } else {
            -g * (-c0 - 1).div_euclid(g)
        };
        constraint.expr.constant = Rational::integer(new_const);
        constraint.strict = false;
    }
    // ADDITIVE coverage (P2.4). Branch-and-bound below decides bounded systems
    // but STALLS (`Unknown`, grinding to the node budget) on LP-feasible-but-
    // integer-infeasible systems over UNBOUNDED variables (e.g. `3x = 3y + 1`-
    // shaped polytopes). A bounded round of sound Gomory fractional cuts closes
    // many such cases to `unsat` (or finds an integer point), and is fast and
    // deterministic (bounded rounds/rows/cols/magnitude). It is run FIRST as a
    // cheap, fully-sound oracle: every verdict it returns is checked the same way
    // B&B's is (`unsat` by a standard-form infeasibility certificate built only
    // from integer-valid cuts; `sat` by replay against the original assertions).
    // When it DECLINES (`None`) we fall through to the unchanged B&B, so no case
    // B&B already decides loses coverage and — both engines being sound — no
    // verdict can change to a wrong one.
    // A Gomory `Sat` is still replayed below (the shared trust anchor): a
    // reconstruction slip can only ever cause a (rejected, alarmed) replay
    // failure, never an unsound `sat`.
    let outcome = if let Some(decided) = lia_gomory_cuts(&constraints, nvars, deadline) {
        decided
    } else {
        let mut budget = MAX_LIA_BNB_NODES;
        lia_branch_and_bound(&mut constraints, nvars, &mut budget, deadline)
    };
    match outcome {
        LiaBnb::Unsat => Ok(CheckResult::Unsat),
        LiaBnb::Unknown => Ok(CheckResult::Unknown(UnknownReason {
            kind: UnknownKind::Incomplete,
            detail: format!("QF_LIA branch-and-bound exceeded {MAX_LIA_BNB_NODES} nodes"),
        })),
        LiaBnb::Sat(values) => {
            if has_opaque_vars {
                return Ok(CheckResult::Unknown(UnknownReason {
                    kind: UnknownKind::Incomplete,
                    detail: "opaque integer UF abstraction is satisfiable; SAT model lifting is \
                             owned by the UFLIA backend"
                        .to_owned(),
                }));
            }
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

/// Three-valued outcome of the **LP relaxation** of an integer constraint set —
/// the cheap entailment probe the online [`crate::lia_online`] theory propagation
/// uses. Soundness anchor: the LP relaxation drops the integrality requirement, so
/// `Infeasible` over the reals implies the integer system is infeasible too (the
/// integer points are a subset of the real points). `Feasible` is therefore
/// *inconclusive* about integer feasibility — the probe declines to propagate on it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LpRelaxation {
    /// The real relaxation has a satisfying point. Inconclusive about ℤ (may still
    /// be integer-infeasible) — the caller must NOT treat this as entailment.
    Feasible,
    /// The real relaxation is infeasible ⇒ the integer system is infeasible too.
    Infeasible,
    /// Overflow / outside the conjunctive-linear-integer fragment / iteration
    /// backstop: inconclusive (never asserted as `Infeasible`).
    Unknown,
}

/// Tests the **LP relaxation** of the conjunctive integer atom set `assertions`
/// (each a linear integer order atom or its `BoolNot`, or a true integer equality)
/// by a single exact-rational simplex feasibility solve — **no** integer
/// tightening, Gomory cuts, or branch-and-bound (those are what make a full
/// integer decision heavy). The cheap, sound entailment probe driving online `LIA`
/// theory propagation in [`crate::lia_online`].
///
/// Returns [`LpRelaxation::Infeasible`] only when the real relaxation has no
/// satisfying point — which soundly implies the integer system is infeasible
/// (integer solutions are a subset of real ones). [`LpRelaxation::Feasible`] is
/// inconclusive about ℤ. Any overflow, an unsupported (e.g. disjunctive /
/// disequality) atom, or the simplex backstop yields [`LpRelaxation::Unknown`] —
/// never a wrong `Infeasible`.
pub(crate) fn lp_relaxation_feasibility(arena: &TermArena, assertions: &[TermId]) -> LpRelaxation {
    lp_relaxation_feasibility_with_options(arena, assertions, false)
}

fn lp_relaxation_feasibility_with_options(
    arena: &TermArena,
    assertions: &[TermId],
    allow_opaque_apps: bool,
) -> LpRelaxation {
    let mut ctx = IntCollector::new(allow_opaque_apps);
    for (index, &assertion) in assertions.iter().enumerate() {
        ctx.current_origin = index;
        if ctx.collect(arena, assertion, false).is_err() {
            return LpRelaxation::Unknown;
        }
    }
    if ctx.overflow {
        return LpRelaxation::Unknown;
    }
    if ctx.trivially_unsat {
        return LpRelaxation::Infeasible;
    }
    match simplex_feasible(&ctx.constraints, ctx.variable_count()) {
        Some(SimplexOutcome::Sat(_)) => LpRelaxation::Feasible,
        Some(SimplexOutcome::Unsat(_)) => LpRelaxation::Infeasible,
        // Iteration backstop without a verdict: stay conservative.
        None => LpRelaxation::Unknown,
    }
}

/// Returns a sound core of a conjunctive integer system whose LP relaxation is
/// already infeasible. The core indices refer to `assertions`.
///
/// This is deliberately only the relaxation core: if the real relaxation is
/// feasible but the integer system is infeasible, this returns `Ok(None)` and the
/// caller must use a full integer procedure. When a core is returned, it is
/// self-checked by re-running the LP relaxation on the subset, so it can be used
/// directly as a theory lemma for integer arithmetic.
pub(crate) fn lia_lp_relaxation_unsat_core(
    arena: &TermArena,
    assertions: &[TermId],
    allow_opaque_apps: bool,
) -> Result<Option<Vec<usize>>, SolverError> {
    let mut ctx = IntCollector::new(allow_opaque_apps);
    for (index, &assertion) in assertions.iter().enumerate() {
        ctx.current_origin = index;
        ctx.collect(arena, assertion, false)?;
    }
    if ctx.overflow || ctx.trivially_unsat || ctx.constraints.is_empty() {
        return Ok(None);
    }
    let Some(SimplexOutcome::Unsat(multipliers)) =
        simplex_feasible(&ctx.constraints, ctx.variable_count())
    else {
        return Ok(None);
    };

    let mut core: Vec<usize> = ctx
        .constraints
        .iter()
        .zip(&multipliers)
        .filter(|(_, multiplier)| !multiplier.is_zero())
        .map(|(constraint, _)| constraint.origin)
        .collect();
    core.sort_unstable();
    core.dedup();
    if core.is_empty() {
        return Ok(None);
    }

    let subset: Vec<TermId> = core.iter().map(|&i| assertions[i]).collect();
    if !matches!(
        lp_relaxation_feasibility_with_options(arena, &subset, allow_opaque_apps),
        LpRelaxation::Infeasible
    ) {
        return Err(SolverError::Backend(
            "lia LP unsat-core self-check failed: extracted core is feasible".to_owned(),
        ));
    }
    Ok(Some(core))
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
    deadline: Option<Instant>,
) -> LiaBnb {
    // A 2-variable unbounded difference constraint (e.g. `c > y ∧ c < y+1`) is
    // integer-infeasible but real-feasible, and branch-and-bound keeps finding
    // shifted fractional points — grinding toward the node budget with each node's
    // simplex over an ever-deeper constraint stack. The wall-clock deadline keeps it
    // honoring `config.timeout` (the node budget alone is the deterministic backstop).
    if *budget == 0 || past_deadline(deadline) {
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

    // `-floor` and `floor + 1` are the branch constants; an out-of-range floor
    // (a colossal fractional coordinate) makes them overflow `i128`. Degrade to a
    // graceful `unknown` rather than panic (never a wrong verdict).
    let (Some(neg_floor), Some(next)) = (floor.checked_neg(), floor.checked_add(1)) else {
        return LiaBnb::Unknown;
    };

    // Left branch: x_i <= floor, i.e. `1*x_i + (-floor) <= 0`.
    constraints.push(bound_constraint(
        branch_var,
        Rational::integer(1),
        Rational::integer(neg_floor),
    ));
    let left = lia_branch_and_bound(constraints, nvars, budget, deadline);
    constraints.pop();
    if let LiaBnb::Sat(_) | LiaBnb::Unknown = left {
        return left;
    }

    // Right branch: x_i >= floor+1, i.e. `-1*x_i + (floor+1) <= 0`.
    constraints.push(bound_constraint(
        branch_var,
        Rational::integer(-1),
        Rational::integer(next),
    ));
    let right = lia_branch_and_bound(constraints, nvars, budget, deadline);
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

// ---------------------------------------------------------------------------
// Gomory fractional cuts over a self-contained integer standard-form tableau
// (P2.4). Used only as an ADDITIVE fallback when branch-and-bound stalls on an
// LP-feasible-but-integer-infeasible system over UNBOUNDED variables.
//
// SOUNDNESS DESIGN — why a self-contained standard form, not the LRA simplex's
// own tableau. The `QF_LRA` general simplex above (`simplex_feasible`) is a
// Dutertre–de Moura "simplex with bounds": its original variables are FREE (no
// `x >= 0`) and its slacks sit at upper bounds. The textbook Gomory fractional
// cut `Σ_j frac(a_j)·x_Nj >= frac(β)` is valid ONLY under the standard
// assumption that every nonbasic variable is integer and `>= 0`. That
// assumption does NOT hold in the bounds form, so extracting a cut from that
// tableau would be unsound without a transformation we would then have to
// re-prove. Instead this engine builds its OWN classical integer standard form
// in which EVERY structural variable is integer-constrained and `>= 0`, so the
// derivation is verbatim valid and self-evidently sound:
//
//   * each (free, possibly-negative) integer variable `x_i` is split into
//     `x_i = p_i - n_i` with `p_i, n_i >= 0` integers;
//   * each constraint `Σ a_i·x_i + c (<= | =) 0` becomes an EQUALITY
//     `Σ a_i·(p_i - n_i) + c + s = 0` with a slack `s >= 0`.
//
// We REQUIRE all `a_i` and `c` to be integers and the constraint to be
// non-strict; then every slack `s = -c - Σ a_i·x_i` is an integer at any
// integer point, so all of `p_i, n_i, s` are nonneg INTEGER variables. Any
// constraint that is strict or has a non-integer coefficient/constant ⇒ we
// DECLINE (`unknown`): we never emit a cut whose integer-validity we cannot
// guarantee. The Gomory cut on a fractional basic variable of THIS tableau is
// therefore valid for every integer-feasible point and cuts off the current
// fractional vertex.
//
// Everything is exact `Rational`/`i128` with `checked_*`; any overflow, the
// round bound, the row/column-count guard, or the deadline ⇒ graceful
// `unknown` (`None`), never OOM, never a loop, never a wrong verdict.
// ---------------------------------------------------------------------------

/// Maximum number of cut-and-re-solve rounds before declining to `unknown`.
const MAX_GOMORY_ROUNDS: usize = 16;

/// Maximum number of rows (constraints) the Gomory tableau will admit; above
/// this we decline (`unknown`) rather than risk a large dense pivot blow-up.
const MAX_GOMORY_ROWS: usize = 256;

/// Maximum number of structural columns (`2*nvars + nrows` plus accumulated
/// cuts) the Gomory tableau will admit; above this we decline (`unknown`).
const MAX_GOMORY_COLS: usize = 1024;

/// Maximum absolute integer magnitude allowed in any tableau coefficient's
/// numerator/denominator; beyond it we decline, keeping all arithmetic well
/// inside `i128` even after repeated pivots/cuts.
const GOMORY_MAGNITUDE_LIMIT: i128 = 1 << 40;

/// A dense exact-rational standard-form simplex tableau in which EVERY column is
/// a nonneg integer-constrained variable. Row `i` reads
/// `x_{basis[i]} = rhs[i] + Σ_j body[i][j]·x_{nonbasic[j]}` (nonbasic vars at 0).
struct GomoryTableau {
    /// `body[i][j]` is the coefficient of the `j`-th nonbasic in row `i`.
    body: Vec<Vec<Rational>>,
    /// `rhs[i]` is the value of basic variable `basis[i]` at the current vertex.
    rhs: Vec<Rational>,
    /// Global index of the basic variable owning row `i`.
    basis: Vec<usize>,
    /// Global indices of the nonbasic (column) variables, in column order.
    nonbasic: Vec<usize>,
    /// Number of leading global indices (`0..integral_upto`) that are
    /// integer-constrained. In our build EVERY structural variable is integer,
    /// so this equals the total variable count; kept explicit for clarity.
    integral_upto: usize,
}

/// Builds the integer standard-form tableau from the collected constraints, or
/// `None` if any constraint is unfit for a sound Gomory cut (strict, or a
/// non-integer coefficient/constant) or any guard (size/magnitude/overflow)
/// trips. `nvars` is the original-variable count.
///
/// Layout of global variable indices:
///   `0 .. nvars`            → `p_i` (positive part of original `x_i`)
///   `nvars .. 2*nvars`      → `n_i` (negative part of original `x_i`)
///   `2*nvars .. 2*nvars+m`  → `s_j` (slack of constraint `j`)
/// All are nonneg integers. `x_i = p_i - n_i`.
fn build_gomory_tableau(constraints: &[Constraint], nvars: usize) -> Option<GomoryTableau> {
    let m = constraints.len();
    if m == 0 || m > MAX_GOMORY_ROWS {
        return None;
    }
    let total = 2usize.checked_mul(nvars)?.checked_add(m)?;
    if total > MAX_GOMORY_COLS {
        return None;
    }
    // Nonbasic columns: the `2*nvars` split variables (p_i, n_i). Basic: the m
    // slacks (one per constraint), initially equal to `-constant`.
    let nonbasic: Vec<usize> = (0..2 * nvars).collect();
    let col_of: BTreeMap<usize, usize> =
        nonbasic.iter().enumerate().map(|(j, &g)| (g, j)).collect();

    let mut body: Vec<Vec<Rational>> = Vec::with_capacity(m);
    let mut rhs: Vec<Rational> = Vec::with_capacity(m);
    let mut basis: Vec<usize> = Vec::with_capacity(m);

    for (j, c) in constraints.iter().enumerate() {
        // A sound Gomory cut in this form needs an INTEGER, NON-STRICT row.
        if c.strict || !c.expr.constant.is_integer() {
            return None;
        }
        // Slack form: s_j = -c - Σ a_i·(p_i - n_i).
        // As a tableau row over the nonbasic (p,n) columns:
        //   s_j = (-c) + Σ_i (-a_i)·p_i + Σ_i (a_i)·n_i.
        let mut row = vec![Rational::zero(); nonbasic.len()];
        for (&i, &a) in &c.expr.coeffs {
            if !a.is_integer() {
                return None;
            }
            if a.numerator().abs() >= GOMORY_MAGNITUDE_LIMIT {
                return None;
            }
            // p_i column gets -a; n_i column gets +a.
            let neg_a = a.checked_neg()?;
            let pj = *col_of.get(&i)?;
            let nj = *col_of.get(&(nvars + i))?;
            row[pj] = row[pj].checked_add(neg_a)?;
            row[nj] = row[nj].checked_add(a)?;
        }
        if c.expr.constant.numerator().abs() >= GOMORY_MAGNITUDE_LIMIT {
            return None;
        }
        let r = c.expr.constant.checked_neg()?;
        body.push(row);
        rhs.push(r);
        basis.push(2 * nvars + j); // slack s_j
    }

    Some(GomoryTableau {
        body,
        rhs,
        basis,
        nonbasic,
        integral_upto: total,
    })
}

/// Result of [`gomory_solve_lp`]: the LP relaxation of the current tableau is
/// feasible (and the tableau is left at an optimal/feasible vertex), infeasible,
/// or the search declined (overflow / iteration backstop → `unknown`).
enum GomoryLp {
    Feasible,
    Infeasible,
    Decline,
}

/// Drives the dense standard-form tableau to a feasible vertex (all `rhs >= 0`)
/// by a dual-simplex-style / Bland primal repair: while some basic variable is
/// negative, pivot to restore feasibility. Returns `Infeasible` when a negative
/// basic row has no entering column (a Farkas-style certificate of infeasibility
/// in standard form), `Decline` on overflow or the iteration backstop.
///
/// All structural variables are `>= 0`; a feasible vertex has every `rhs[i] >= 0`.
fn gomory_solve_lp(t: &mut GomoryTableau) -> GomoryLp {
    let nrows = t.body.len();
    let ncols = t.nonbasic.len();
    // Generous deterministic backstop; Bland's rule (smallest-index choice)
    // guarantees termination, this only bounds pathological inputs.
    let max_iters = 2000usize.saturating_add(40usize.saturating_mul(nrows.saturating_mul(ncols)));
    for _ in 0..max_iters {
        // Find the smallest-index basic variable whose value is negative.
        let mut leave: Option<usize> = None;
        let mut leave_basic = usize::MAX;
        for i in 0..nrows {
            if t.rhs[i].numerator() < 0 && t.basis[i] < leave_basic {
                leave_basic = t.basis[i];
                leave = Some(i);
            }
        }
        let Some(li) = leave else {
            return GomoryLp::Feasible;
        };
        // Row `li`: x_basic = rhs(<0) + Σ_j body·x_nonbasic. To raise it, we need
        // a nonbasic column whose increase raises x_basic, i.e. a POSITIVE body
        // coefficient (all nonbasics are currently 0 and bounded below by 0, so
        // they can only increase). Bland: smallest global index.
        let mut enter: Option<usize> = None;
        let mut enter_global = usize::MAX;
        for j in 0..ncols {
            if t.body[li][j].numerator() > 0 && t.nonbasic[j] < enter_global {
                enter_global = t.nonbasic[j];
                enter = Some(j);
            }
        }
        let Some(ej) = enter else {
            // Row `li`: x_basic = rhs(<0) + Σ body_j·x_nonbasic, every body_j <= 0
            // and every x_nonbasic >= 0, so x_basic <= rhs < 0, contradicting
            // x_basic >= 0. The standard-form system is infeasible.
            return GomoryLp::Infeasible;
        };
        if gomory_pivot(t, li, ej).is_none() {
            return GomoryLp::Decline;
        }
        // Magnitude guard after each pivot: bail before coefficients can blow up.
        if !gomory_within_magnitude(t) {
            return GomoryLp::Decline;
        }
    }
    GomoryLp::Decline
}

/// Whether every coefficient in the tableau is within [`GOMORY_MAGNITUDE_LIMIT`]
/// (numerator and denominator), so subsequent exact arithmetic stays in `i128`.
fn gomory_within_magnitude(t: &GomoryTableau) -> bool {
    let ok = |r: &Rational| {
        r.numerator().abs() < GOMORY_MAGNITUDE_LIMIT
            && r.denominator().abs() < GOMORY_MAGNITUDE_LIMIT
    };
    t.rhs.iter().all(ok) && t.body.iter().all(|row| row.iter().all(ok))
}

/// Pivots nonbasic column `ej` into the basis in place of the basic owning row
/// `li`. Standard dense Gauss–Jordan pivot over exact rationals; `None` on any
/// `i128` overflow (caller declines to `unknown`).
fn gomory_pivot(t: &mut GomoryTableau, li: usize, ej: usize) -> Option<()> {
    let nrows = t.body.len();
    let ncols = t.nonbasic.len();
    // Row `li`: x_basic = rhs + Σ_j body[li][j]·x_nonbasic. Solve for x_{enter}:
    //   x_enter = (-rhs/p) - (1/p)·x_basic + Σ_{j≠ej} (-body[li][j]/p)·x_nonbasic
    // where p = body[li][ej] (the pivot, nonzero). After the pivot, row `li` is
    // owned by `enter` and column `ej` is owned by the leaving basic.
    let p = t.body[li][ej];
    if p.is_zero() {
        return None;
    }
    let leaving = t.basis[li];
    // New row for the entering variable.
    // Solve row `li` (`l = rhs + Σ_k body·N_k`, `N_ej = e`, `p = body[ej]`) for
    // the entering var `e`:
    //   e = (1/p)·l − (rhs/p) − Σ_{k≠ej} (body[k]/p)·N_k.
    // So in the new row owned by `e`, the column `ej` (now hosting the leaving
    // var `l`) has coefficient `+1/p`, and every other column `k` has
    // `−body[k]/p`.
    let mut new_row = vec![Rational::zero(); ncols];
    for (j, slot) in new_row.iter_mut().enumerate() {
        if j == ej {
            // This column position now hosts the (former) leaving basic, coeff +1/p.
            *slot = Rational::integer(1).checked_div(p)?;
        } else {
            *slot = t.body[li][j].checked_neg()?.checked_div(p)?;
        }
    }
    let new_rhs = t.rhs[li].checked_neg()?.checked_div(p)?;
    // Substitute into every OTHER row that mentions column `ej`.
    for i in 0..nrows {
        if i == li {
            continue;
        }
        let a = t.body[i][ej];
        if a.is_zero() {
            continue;
        }
        // Row i has a term `a·x_enter`. We substitute
        //   x_enter = new_rhs + Σ_k new_row[k]·x_k,
        // where column `ej` now hosts the LEAVING variable. The old value at
        // column `ej` (`= a`, the entering-var coefficient) is the term being
        // substituted away, so it MUST be cleared before folding in
        // `a·new_row[ej]` — otherwise the stale `a` is double-counted (an unsound
        // tableau, caught here as a `sat` replay failure rather than escaping).
        t.body[i][ej] = Rational::zero();
        let row_i = &mut t.body[i];
        for (slot, &nr) in row_i.iter_mut().zip(new_row.iter()) {
            *slot = slot.checked_add(a.checked_mul(nr)?)?;
        }
        t.rhs[i] = t.rhs[i].checked_add(a.checked_mul(new_rhs)?)?;
    }
    // The entering variable's global index (`t.nonbasic[ej]`) now owns row `li`;
    // column `ej` now hosts the leaving variable.
    let entering_global = t.nonbasic[ej];
    t.body[li] = new_row;
    t.rhs[li] = new_rhs;
    t.basis[li] = entering_global;
    t.nonbasic[ej] = leaving;
    Some(())
}

/// `frac(t) = t - floor(t)` ∈ [0,1), exact; `None` on `i128` overflow.
fn rational_frac(r: Rational) -> Option<Rational> {
    let num = r.numerator();
    let den = r.denominator();
    // `den > 0` always; floor = div_euclid gives the largest integer <= r.
    let floor = num.div_euclid(den);
    r.checked_sub(Rational::integer(floor))
}

/// Adds a Gomory fractional cut derived from row `li` (whose basic variable is
/// integer-constrained and currently fractional) as a NEW row with a fresh
/// slack column `g`. Our row convention is `x_B = β + Σ_j a_j·x_Nj`; in it the
/// valid cut is `Σ_j frac(-a_j)·x_Nj >= frac(β)` (see the SIGN CONVENTION note in
/// the body for why `frac(-a_j)`, NOT `frac(a_j)`), encoded as the equality
///   `g = -frac(β) + Σ_j frac(-a_j)·x_Nj`   (so `g >= 0` ⇔ the cut holds).
///
/// Returns `None` on overflow / a size or magnitude guard (caller declines).
///
/// SOUNDNESS (short form; full re-derivation in the body): every nonbasic `x_Nj`
/// is a nonneg INTEGER variable and the basic variable of row `li` is
/// integer-constrained, so at any integer-feasible point
/// `S := Σ frac(-a_j)·x_Nj` is `>= 0` and `≡ frac(β) ∈ (0,1) (mod 1)`, hence
/// `S >= frac(β)`: the cut NEVER removes an integer point. It is violated at the
/// current vertex (`x_Nj = 0` ⇒ `0 >= frac(β) > 0`, false), so re-solving makes
/// progress. We never *assert* `g`'s integrality — we only rely on the cut's
/// validity, the soundness direction.
fn add_gomory_cut(t: &mut GomoryTableau, li: usize) -> Option<()> {
    let ncols = t.nonbasic.len();
    if t.body.len() >= MAX_GOMORY_ROWS || ncols >= MAX_GOMORY_COLS {
        return None;
    }
    let frac_beta = rational_frac(t.rhs[li])?;
    if frac_beta.is_zero() {
        return None; // not actually fractional; nothing to cut.
    }
    // SIGN CONVENTION. Our tableau row is `x_B = β + Σ_j a_j·x_Nj`, i.e.
    // `x_B + Σ_j (-a_j)·x_Nj = β`. Matching the textbook standard form
    // `x_B + Σ_j ā_j·x_Nj = β̄` gives `ā_j = -a_j` and `β̄ = β`. The textbook
    // Gomory fractional cut `Σ_j frac(ā_j)·x_Nj >= frac(β̄)` is therefore
    // `Σ_j frac(-a_j)·x_Nj >= frac(β)` IN OUR CONVENTION — the cut coefficient is
    // `frac(-a_j)`, NOT `frac(a_j)`.
    //
    // Validity (re-derived in this convention): at any integer-feasible point,
    // x_B and every x_Nj are integers, so from `x_B = β + Σ a_j x_Nj`,
    // `S := Σ frac(-a_j) x_Nj ≡ Σ(-a_j)x_Nj ≡ β - x_B ≡ β (mod 1)`; since `S >= 0`
    // and `S ≡ frac(β) ∈ (0,1) (mod 1)`, `S >= frac(β)`. So the cut never removes
    // an integer point (the soundness direction). It cuts off the current vertex
    // (all x_Nj = 0 ⇒ `0 >= frac(β) > 0`, false).
    //
    // The cut introduces exactly ONE new basic variable `g` (its slack) and NO
    // new nonbasic column — its body is `Σ_j frac(-a_j)·x_Nj` over the EXISTING
    // nonbasic columns, with `g = -frac(β) + Σ_j frac(-a_j)·x_Nj` (so `g >= 0`
    // ⇔ the cut holds).
    let mut new_row = Vec::with_capacity(ncols);
    for coeff in &t.body[li] {
        new_row.push(rational_frac(coeff.checked_neg()?)?);
    }
    let basic_global = next_fresh_global(t);
    t.body.push(new_row);
    t.rhs.push(frac_beta.checked_neg()?);
    t.basis.push(basic_global);
    if !gomory_within_magnitude(t) {
        return None;
    }
    Some(())
}

/// The smallest global index not currently used by any basic or nonbasic var.
fn next_fresh_global(t: &GomoryTableau) -> usize {
    let mut max = t.integral_upto;
    for &b in &t.basis {
        max = max.max(b + 1);
    }
    for &n in &t.nonbasic {
        max = max.max(n + 1);
    }
    max
}

/// Runs a bounded round of Gomory fractional cuts on the integer standard form.
/// Returns `Some(LiaBnb::Unsat)` if the system is integer-infeasible,
/// `Some(LiaBnb::Sat(values))` if an integer point is found (values over the
/// `nvars` ORIGINAL variables, for the caller's replay), or `None` to DECLINE
/// (`unknown`) — round bound, size/magnitude guard, overflow, or deadline.
///
/// `None` is always sound: declining never converts a decided case to a wrong
/// verdict, and the only definite verdicts we return are integer-valid.
fn lia_gomory_cuts(
    constraints: &[Constraint],
    nvars: usize,
    deadline: Option<Instant>,
) -> Option<LiaBnb> {
    if past_deadline(deadline) {
        return None;
    }
    let mut t = build_gomory_tableau(constraints, nvars)?;

    for _round in 0..MAX_GOMORY_ROUNDS {
        if past_deadline(deadline) {
            return None;
        }
        match gomory_solve_lp(&mut t) {
            GomoryLp::Infeasible => return Some(LiaBnb::Unsat),
            GomoryLp::Decline => return None,
            GomoryLp::Feasible => {}
        }
        // Find a basic, integer-constrained variable whose value is fractional.
        let mut cut_row: Option<usize> = None;
        for i in 0..t.body.len() {
            // Only original-form integer variables (p_i, n_i, s_j) are
            // integer-constrained; the fresh cut slacks (global >= integral_upto)
            // we do NOT require to be integral, so we never cut on them.
            if t.basis[i] < t.integral_upto && !t.rhs[i].is_integer() {
                cut_row = Some(i);
                break;
            }
        }
        let Some(li) = cut_row else {
            // No fractional integer-constrained basic ⇒ the structural variables
            // are all integers; reconstruct the original `x_i = p_i - n_i` and
            // return it for replay. (Cut slacks may be fractional; irrelevant.)
            return gomory_reconstruct(&t, nvars).map(LiaBnb::Sat);
        };
        add_gomory_cut(&mut t, li)?;
    }
    None // round bound hit ⇒ decline (never loop, never a wrong verdict).
}

/// Reads the integer values of the original variables `x_i = p_i - n_i` out of a
/// feasible all-integer tableau. `None` on overflow. The caller replays this
/// against the original assertions, so a reconstruction slip can only ever cause
/// a (rejected, alarmed) replay failure, never an unsound `sat`.
fn gomory_reconstruct(t: &GomoryTableau, nvars: usize) -> Option<Vec<Rational>> {
    // Value of every global variable: basics from `rhs`, nonbasics are 0.
    let mut val: BTreeMap<usize, Rational> = BTreeMap::new();
    for (i, &b) in t.basis.iter().enumerate() {
        val.insert(b, t.rhs[i]);
    }
    let get = |g: usize| val.get(&g).copied().unwrap_or_else(Rational::zero);
    let mut out = Vec::with_capacity(nvars);
    for i in 0..nvars {
        let p = get(i);
        let n = get(nvars + i);
        let x = p.checked_sub(n)?;
        out.push(x);
    }
    Some(out)
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
    opaque_var_index: BTreeMap<TermId, usize>,
    vars: Vec<SymbolId>,
    next_var: usize,
    allow_opaque_apps: bool,
    constraints: Vec<Constraint>,
    trivially_unsat: bool,
    current_origin: usize,
    /// Set on an `i128` overflow while linearizing; poisons the collection so the
    /// caller degrades to `unknown` (mirrors the LRA [`Collector`]).
    overflow: bool,
}

impl IntCollector {
    fn new(allow_opaque_apps: bool) -> Self {
        Self {
            allow_opaque_apps,
            ..Self::default()
        }
    }

    /// Unwraps an overflow-checked `LinExpr`; on overflow sets the poison flag and
    /// returns a harmless placeholder (never acted on — the caller bails first).
    fn guard(&mut self, expr: Option<LinExpr>) -> LinExpr {
        if let Some(e) = expr {
            e
        } else {
            self.overflow = true;
            LinExpr::constant(Rational::zero())
        }
    }

    fn index_of(&mut self, symbol: SymbolId) -> usize {
        if let Some(&index) = self.var_index.get(&symbol) {
            return index;
        }
        let index = self.next_var;
        self.next_var += 1;
        self.vars.push(symbol);
        self.var_index.insert(symbol, index);
        index
    }

    fn index_of_opaque(&mut self, term: TermId) -> usize {
        if let Some(&index) = self.opaque_var_index.get(&term) {
            return index;
        }
        let index = self.next_var;
        self.next_var += 1;
        self.opaque_var_index.insert(term, index);
        index
    }

    fn variable_count(&self) -> usize {
        self.next_var
    }

    fn has_opaque_vars(&self) -> bool {
        !self.opaque_var_index.is_empty()
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
                let diff = self.guard(left.sub(&right));
                let diff_neg = self.guard(diff.neg());
                self.constraints.push(Constraint {
                    expr: diff,
                    strict: false,
                    mult: Vec::new(),
                    origin: self.current_origin,
                });
                self.constraints.push(Constraint {
                    expr: diff_neg,
                    strict: false,
                    mult: Vec::new(),
                    origin: self.current_origin,
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
        let expr = self.guard(expr);
        self.constraints.push(Constraint {
            expr,
            strict,
            mult: Vec::new(),
            origin: self.current_origin,
        });
    }

    fn linearize(&mut self, arena: &TermArena, term: TermId) -> Result<LinExpr, SolverError> {
        match arena.node(term) {
            TermNode::IntConst(value) => Ok(LinExpr::constant(Rational::integer(*value))),
            TermNode::Symbol(symbol) if is_int(arena, term) => {
                Ok(LinExpr::var(self.index_of(*symbol)))
            }
            TermNode::App {
                op: Op::Apply(_), ..
            } if self.allow_opaque_apps && is_int(arena, term) => {
                Ok(LinExpr::var(self.index_of_opaque(term)))
            }
            TermNode::App {
                op: Op::IntNeg,
                args,
            } => {
                let a = self.linearize(arena, args[0])?;
                Ok(self.guard(a.neg()))
            }
            TermNode::App {
                op: Op::IntAdd,
                args,
            } => {
                let a = self.linearize(arena, args[0])?;
                let b = self.linearize(arena, args[1])?;
                Ok(self.guard(a.add(&b)))
            }
            TermNode::App {
                op: Op::IntSub,
                args,
            } => {
                let a = self.linearize(arena, args[0])?;
                let b = self.linearize(arena, args[1])?;
                Ok(self.guard(a.sub(&b)))
            }
            TermNode::App {
                op: Op::IntMul,
                args,
            } => {
                let a = self.linearize(arena, args[0])?;
                let b = self.linearize(arena, args[1])?;
                if a.is_constant() {
                    Ok(self.guard(b.scale(a.constant)))
                } else if b.is_constant() {
                    Ok(self.guard(a.scale(b.constant)))
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
    /// Exact addition; `None` on `i128` overflow (degrades to `unknown`).
    fn add(self, other: Self) -> Option<Self> {
        Some(Delta {
            c: self.c.checked_add(other.c)?,
            k: self.k.checked_add(other.k)?,
        })
    }
    /// Exact subtraction; `None` on `i128` overflow (degrades to `unknown`).
    fn sub(self, other: Self) -> Option<Self> {
        Some(Delta {
            c: self.c.checked_sub(other.c)?,
            k: self.k.checked_sub(other.k)?,
        })
    }
    /// Exact scaling; `None` on `i128` overflow (degrades to `unknown`).
    fn scale(self, factor: Rational) -> Option<Self> {
        Some(Delta {
            c: self.c.checked_mul(factor)?,
            k: self.k.checked_mul(factor)?,
        })
    }
    /// Lexicographic `(c, k)` comparison; `None` on `i128` overflow during the
    /// cross-multiplication (the caller defers to `unknown`, never a wrong answer).
    fn checked_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(
            self.c
                .checked_cmp(&other.c)?
                .then(self.k.checked_cmp(&other.k)?),
        )
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
            let origins: Vec<usize> = ctx.constraints.iter().map(|c| c.origin).collect();
            let certificate = FarkasCertificate {
                atoms,
                multipliers,
                origins,
                vars: ctx.vars.clone(),
            };
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
    use core::cmp::Ordering;
    let zero = Rational::zero();
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
        // `-constant` can overflow (`i128::MIN`); on overflow defer to `unknown`.
        let bound_c = constraint.expr.constant.checked_neg()?;
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
        // Smallest-index basic variable violating its (upper) bound (`Overflow`
        // = an `i128` overflow during a comparison, deferred to `unknown`).
        let b = match first_violating(&basic, &value, &upper) {
            Violating::Some(b) => b,
            Violating::Overflow => return None,
            // Feasible: instantiate δ to a concrete positive rational.
            Violating::None => {
                return Some(SimplexOutcome::Sat(extract_model(
                    constraints,
                    nvars,
                    &value,
                )?));
            }
        };
        let target = upper[b].expect("violating basic has an upper bound");

        // b is above its upper bound and must decrease. Find a suitable entering
        // nonbasic (smallest index, Bland): one that can move in the direction
        // that decreases b.
        let mut entering: Option<usize> = None;
        for &n in &nonbasic {
            let a = row[&b].get(&n).copied().unwrap_or(zero);
            if a.is_zero() {
                continue;
            }
            // Sign of `a` (compared to zero) never overflows.
            let suitable = if a.cmp(&zero) == Ordering::Greater {
                // decrease n (no lower bounds anywhere → always possible)
                true
            } else {
                // increase n (possible unless n is at its upper bound)
                match upper[n] {
                    Some(u) => value[n].checked_cmp(&u)? == Ordering::Less,
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
            // Coefficient overflow here defers to `unknown` (never a wrong unsat;
            // the certificate is independently re-verified upstream anyway).
            let mut multipliers = vec![Rational::zero(); m];
            multipliers[b - nvars] = multipliers[b - nvars].checked_add(Rational::integer(1))?;
            for (&var, &coeff) in &row[&b] {
                if var >= nvars {
                    multipliers[var - nvars] = multipliers[var - nvars].checked_sub(coeff)?;
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
        )?;
    }
    // Backstop reached without a verdict: report feasible only if no bound is
    // violated, otherwise defer (`None`) — the caller falls back to the
    // Fourier–Motzkin engine rather than risk a wrong answer.
    match first_violating(&basic, &value, &upper) {
        Violating::Some(_) | Violating::Overflow => None,
        Violating::None => Some(SimplexOutcome::Sat(extract_model(
            constraints,
            nvars,
            &value,
        )?)),
    }
}

/// Outcome of [`first_violating`]: a violating basic variable, none violating, or
/// an `i128` overflow during a bound comparison (deferred to a graceful
/// `unknown` upstream — never a wrong verdict).
enum Violating {
    Some(usize),
    None,
    Overflow,
}

/// The smallest-index basic variable above its upper bound.
fn first_violating(
    basic: &std::collections::BTreeSet<usize>,
    value: &[Delta],
    upper: &[Option<Delta>],
) -> Violating {
    use core::cmp::Ordering;
    for &b in basic {
        if let Some(u) = upper[b] {
            match value[b].checked_cmp(&u) {
                Some(Ordering::Greater) => return Violating::Some(b),
                Some(_) => {}
                None => return Violating::Overflow,
            }
        }
    }
    Violating::None
}

/// Pivots basic `b` out and nonbasic `n` in, setting `value[b]` to `target` and
/// updating every value and tableau row (Dutertre–de Moura `pivotAndUpdate`).
///
/// Returns `None` on any `i128` overflow (the caller defers to a graceful
/// `unknown`, never a wrong verdict). On `None` the tableau may be left partially
/// updated, but the caller discards it.
fn pivot_and_update(
    row: &mut std::collections::HashMap<usize, std::collections::HashMap<usize, Rational>>,
    basic: &mut std::collections::BTreeSet<usize>,
    nonbasic: &mut std::collections::BTreeSet<usize>,
    value: &mut [Delta],
    b: usize,
    n: usize,
    target: Delta,
) -> Option<()> {
    let a_bn = row[&b][&n];
    // `1 / a_bn` is `a_bn.recip()`, made overflow-safe via `checked_div`.
    let inv = Rational::integer(1).checked_div(a_bn)?;
    let theta = target.sub(value[b])?.scale(inv)?;
    value[n] = value[n].add(theta)?;
    value[b] = target;
    for &i in basic.iter() {
        if i == b {
            continue;
        }
        if let Some(&a_in) = row[&i].get(&n) {
            if !a_in.is_zero() {
                value[i] = value[i].add(theta.scale(a_in)?)?;
            }
        }
    }

    // Rewrite the tableau: express n in terms of b and the other nonbasics.
    let row_b = row.remove(&b).expect("b is basic");
    let mut row_n: std::collections::HashMap<usize, Rational> = std::collections::HashMap::new();
    row_n.insert(b, inv);
    for (&k, &coeff) in &row_b {
        if k != n {
            row_n.insert(k, coeff.checked_mul(inv)?.checked_neg()?);
        }
    }
    // Substitute the new n-row into every other basic row mentioning n.
    let others: Vec<usize> = basic.iter().copied().filter(|&i| i != b).collect();
    for i in others {
        if let Some(a_in) = row.get_mut(&i).and_then(|r| r.remove(&n)) {
            if !a_in.is_zero() {
                let additions: Vec<(usize, Rational)> = row_n
                    .iter()
                    .map(|(&k, &c)| a_in.checked_mul(c).map(|p| (k, p)))
                    .collect::<Option<_>>()?;
                let r = row.get_mut(&i).expect("basic row exists");
                for (k, delta) in additions {
                    let entry = r.entry(k).or_insert_with(Rational::zero);
                    *entry = (*entry).checked_add(delta)?;
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
    Some(())
}

/// Turns the δ-rational assignment into a concrete rational model by choosing a
/// positive δ small enough that every original constraint still holds. `None` on
/// any `i128` overflow (the caller defers to a graceful `unknown`).
fn extract_model(
    constraints: &[Constraint],
    nvars: usize,
    value: &[Delta],
) -> Option<Vec<Rational>> {
    use core::cmp::Ordering;
    let zero = Rational::zero();
    // Each original variable is `c_i + k_i·δ`. For a constraint with combined
    // δ-coefficient K > 0 the bound on δ is -C/K (C < 0 in any δ-feasible
    // solution); δ* is half the tightest such bound (or 1/2 if unbounded).
    let mut delta_star = Rational::integer(1);
    for constraint in constraints {
        let mut big_c = constraint.expr.constant;
        let mut big_k = Rational::zero();
        for (&i, &a) in &constraint.expr.coeffs {
            big_c = big_c.checked_add(a.checked_mul(value[i].c)?)?;
            big_k = big_k.checked_add(a.checked_mul(value[i].k)?)?;
        }
        if big_k.checked_cmp(&zero)? == Ordering::Greater {
            let bound = big_c.checked_neg()?.checked_div(big_k)?;
            if bound.checked_cmp(&delta_star)? == Ordering::Less {
                delta_star = bound;
            }
        }
    }
    delta_star = delta_star.checked_mul(Rational::new(1, 2))?;

    (0..nvars)
        .map(|i| value[i].c.checked_add(value[i].k.checked_mul(delta_star)?))
        .collect()
}

#[cfg(test)]
mod gomory_internal_tests {
    use super::*;

    /// Builds the constraint set for `2x + 2y <= 1 ∧ 2x + 2y >= 1`
    /// (i.e. `x + y = 1/2`), which is LP-feasible but has NO integer point.
    /// Variables: index 0 = x, index 1 = y.
    fn x_plus_y_half() -> Vec<Constraint> {
        // 2x + 2y <= 1  →  2x + 2y - 1 <= 0
        let mut c0 = BTreeMap::new();
        c0.insert(0, Rational::integer(2));
        c0.insert(1, Rational::integer(2));
        // 2x + 2y >= 1  →  1 - 2x - 2y <= 0
        let mut c1 = BTreeMap::new();
        c1.insert(0, Rational::integer(-2));
        c1.insert(1, Rational::integer(-2));
        vec![
            Constraint {
                expr: LinExpr {
                    coeffs: c0,
                    constant: Rational::integer(-1),
                },
                strict: false,
                mult: Vec::new(),
                origin: 0,
            },
            Constraint {
                expr: LinExpr {
                    coeffs: c1,
                    constant: Rational::integer(1),
                },
                strict: false,
                mult: Vec::new(),
                origin: 1,
            },
        ]
    }

    #[test]
    fn bnb_alone_leaves_x_plus_y_half_unknown() {
        // Branch-and-bound with a generous-but-finite budget keeps finding shifted
        // fractional vertices and exhausts the budget → `Unknown`. This documents
        // that the Gomory round adds STRICTLY NEW coverage.
        let mut constraints = x_plus_y_half();
        // A small finite node budget; B&B keeps finding shifted fractional
        // vertices and never closes the tree, so it exhausts the budget →
        // `Unknown`. (The production path uses MAX_LIA_BNB_NODES = 50_000 and is
        // likewise inconclusive here; a small budget keeps this test fast while
        // making the same point.)
        let mut budget = 300u64;
        let outcome = lia_branch_and_bound(&mut constraints, 2, &mut budget, None);
        assert!(
            matches!(outcome, LiaBnb::Unknown),
            "B&B alone must stall to Unknown on x+y=1/2, got a decision"
        );
        assert_eq!(budget, 0, "B&B should have consumed its whole node budget");
    }

    #[test]
    fn gomory_decides_x_plus_y_half_unsat() {
        // The same system is decided `unsat` by the bounded Gomory cut round.
        let constraints = x_plus_y_half();
        let outcome = lia_gomory_cuts(&constraints, 2, None);
        assert!(
            matches!(outcome, Some(LiaBnb::Unsat)),
            "Gomory cuts must decide x+y=1/2 unsat, got {:?}",
            outcome.map(|o| match o {
                LiaBnb::Sat(_) => "Sat",
                LiaBnb::Unsat => "Unsat",
                LiaBnb::Unknown => "Unknown",
            })
        );
    }

    #[test]
    fn lp_relaxation_unsat_core_names_integer_assertions() {
        let mut arena = TermArena::new();
        let x = arena.int_var("x").expect("x");
        let zero = arena.int_const(0);
        let one = arena.int_const(1);
        let ge = arena.int_ge(x, one).expect("x>=1");
        let le = arena.int_le(x, zero).expect("x<=0");

        let core = lia_lp_relaxation_unsat_core(&arena, &[ge, le], false)
            .expect("core extraction")
            .expect("LP-infeasible core");
        assert_eq!(core, vec![0, 1]);
    }

    #[test]
    fn lp_relaxation_unsat_core_allows_opaque_int_apps() {
        let mut arena = TermArena::new();
        let f = arena
            .declare_fun("f", &[Sort::Int], Sort::Int)
            .expect("declare f");
        let zero = arena.int_const(0);
        let app = arena.apply(f, &[zero]).expect("f(0)");
        let one = arena.int_const(1);
        let ge = arena.int_ge(app, one).expect("f(0)>=1");
        let le = arena.int_le(app, zero).expect("f(0)<=0");

        let core = lia_lp_relaxation_unsat_core(&arena, &[ge, le], true)
            .expect("core extraction")
            .expect("LP-infeasible opaque core");
        assert_eq!(core, vec![0, 1]);
    }
}
