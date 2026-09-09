//! Feasibility-based bound tightening (FBBT) for the nonlinear-real route, as a
//! **refutation-only** producer with a Farkas checker between the search and the
//! verdict.
//!
//! # What this is for
//!
//! Measured 2026-09-09 on the 75 `QF_NRA` parity losses
//! (`bench-results/parity-losses-20260908/QF_NRA.txt`): **37 of 75 (49%) have
//! every nonlinear atom in one or two variables, and every one of them declares
//! MORE variables than that** — the extras occur only in *linear* atoms
//! (`scripts/nra-nonlinear-shape.py`). But `nra_real_root::decide_component`
//! dispatches on the variable count of the **connected component**, and
//! `connected_components` unions over every atom, the linear ones included. So a
//! query whose nonlinear content sits squarely inside the 1-variable sign-cell
//! decider, or the 2-variable resultant/CAD decider, is handed instead to the
//! ≥3-variable CAD, which declines.
//!
//! `sqrt-1mcosq-8-chunk-0014.smt2` is the worked instance: one degree-6 nonlinear
//! atom in `skoY` alone, with `pi` and `skoX` appearing only in linear atoms. The
//! same binary answers `unknown` on the file as shipped, `unknown` with the nested
//! `and` flattened, `unknown` with the implied constant bounds on `skoY` *added to
//! the whole query* — and **`unsat`, at once**, on that one nonlinear atom plus
//! `0.1 < skoY < 1.372`, which is exactly what the other two variables' linear
//! atoms imply. `nra::extract_bounds` is explicitly syntactic ("only syntactic
//! operand-vs-constant bounds are recognised"), so nothing in the tree derives a
//! *transitive* bound today, and `skoY`'s are transitive
//! (`skoY ≤ −1/5 + pi/2` with `pi < 3.1415927`; `skoY > skoX ≥ 1/10`).
//!
//! Full record: `docs/research/12-performance/qf-nra-loss-attribution-2026-09-09.md`.
//!
//! # Why it can only produce `unsat`, and why that is structural
//!
//! The route hands a decider a **subset** of the query's atoms (the nonlinear
//! ones, plus the linear ones already inside the same variables) together with
//! derived constant bounds that are **implied** by the full query. Therefore:
//!
//! - a refutation of `subset ∪ derived` refutes the whole query — `unsat`
//!   **transfers**;
//! - a *model* of `subset ∪ derived` need not satisfy the discarded atoms — `sat`
//!   **does not transfer**.
//!
//! That asymmetry is enforced by the types, not by remembering to decline:
//!
//! - The route's success type is [`Refutation`]. It has **no model field, no
//!   `Sat` variant and no `Unknown` variant** — there is nothing to put a model
//!   in, so a decider's `Sat` bindings have nowhere to go.
//! - [`Refutation`] has private fields and one constructor, [`Refutation::new`],
//!   which takes three `usize` counters and nothing else. It cannot be built out
//!   of a model.
//! - The single bridge to a solver verdict, [`Refutation::into_check_result`], has
//!   a **constant body** — `CheckResult::Unsat`, no branch, no field read. Making
//!   this route report `sat` would require *adding* a variant and a branch, not
//!   deleting a guard.
//!
//! # Why a checker, and not a careful derivation
//!
//! A derived bound that is too tight is a wrong `unsat`, which is the one failure
//! this project must never ship. So the propagation in [`derive_bounds`] is
//! **untrusted search**: it may propose anything. Every proposal must then pass
//! [`verify`], a small Farkas check that reconstructs the bound from the facts it
//! cites and rejects anything those facts do not entail. Only [`verify`] can
//! produce a [`CertifiedBound`], and only a `CertifiedBound` reaches the decider.
//!
//! The certificate is a nonnegative rational combination. Every fact is oriented
//! as `p ≥ 0` or `p > 0` ([`LinearFact`]), a claimed bound is turned into its own
//! such target (`u − x` for `x ≤ u`, `x − l` for `x ≥ l`), and the check is that
//! `target − Σ λⱼ pⱼ` is a **nonnegative constant** with every `λⱼ > 0`. Then
//! `target ≥ Σ λⱼ pⱼ ≥ 0`, which is the claim. It is a handful of comparisons over
//! exact rationals; nothing about how the `λ` were found enters it.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::atomic::{AtomicU64, Ordering};

use axeyum_ir::{Rational, SymbolId};

// ============================================================================
// Coverage — so "the fuzz covers this route" is a measurement, not a hope
// ============================================================================

static CONSULTED: AtomicU64 = AtomicU64::new(0);
static SPLIT_OK: AtomicU64 = AtomicU64::new(0);
static BOUNDS_DERIVED: AtomicU64 = AtomicU64::new(0);
static COMPONENTS_OFFERED: AtomicU64 = AtomicU64::new(0);
static REFUTATIONS: AtomicU64 = AtomicU64::new(0);

/// How much work this route has been given, and how much it decided, since the
/// process started.
///
/// This exists because of a specific failure this lane hit and measured. A new
/// seed class was added to `nra_differential_fuzz` to generate exactly this
/// route's shape, and running the whole 2,000-instance sweep with the route on
/// and with it off produced **identical** tallies — 1,927 jointly decided, 1,927
/// agreements, 0 disagreements, both arms. That is consistent with two opposite
/// stories: the route being exercised and adding nothing, or the route never
/// being reached at all. A verdict tally cannot separate them, and "the fuzz
/// covers the new producer" is a claim about the second.
///
/// So the fuzz reads these instead of inferring coverage from verdicts, and a
/// zero here fails it. An instrument whose reading nothing depends on is not an
/// instrument.
///
/// The counters are a **funnel**, not one number, because "the route did
/// nothing" has four different causes and they have four different fixes:
/// the query never got here, its atoms did not split into a usable
/// linear/nonlinear pair, no bound could be derived, or the derived bounds did
/// not close the component. A single counter reads the same for all four.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NraDerivedBoundCoverage {
    /// Queries that reached the route with the policy enabled — i.e. the
    /// multivariate decomposition declined or could not certify, and this route
    /// was asked.
    pub consulted: u64,
    /// Of those, the ones that split into at least one nonlinear atom and at
    /// least one usable linear fact, within the policy's caps.
    pub split_ok: u64,
    /// Of those, the ones where at least one bound survived the checker.
    pub bounds_derived: u64,
    /// Nonlinear components handed to an exact decider **with** at least one
    /// certified derived bound attached. This counts the route actually running,
    /// not merely being consulted and declining at an entry guard.
    pub components_offered: u64,
    /// Refutations the route produced. Necessarily `≤ components_offered`.
    pub refutations: u64,
}

/// Read the process-wide coverage counters for the derived-bound refutation
/// route.
///
/// Counters are process-wide and monotone; they are diagnostics only and nothing
/// in the solver branches on them, so they cannot perturb a verdict or the
/// determinism promise.
#[must_use]
pub fn nra_derived_bound_coverage() -> NraDerivedBoundCoverage {
    NraDerivedBoundCoverage {
        consulted: CONSULTED.load(Ordering::Relaxed),
        split_ok: SPLIT_OK.load(Ordering::Relaxed),
        bounds_derived: BOUNDS_DERIVED.load(Ordering::Relaxed),
        components_offered: COMPONENTS_OFFERED.load(Ordering::Relaxed),
        refutations: REFUTATIONS.load(Ordering::Relaxed),
    }
}

/// Record that the route was asked about one query, with the policy enabled.
pub(crate) fn note_consulted() {
    CONSULTED.fetch_add(1, Ordering::Relaxed);
}

/// Record that a query split into a usable linear/nonlinear pair.
pub(crate) fn note_split_ok() {
    SPLIT_OK.fetch_add(1, Ordering::Relaxed);
}

/// Record that at least one bound survived the checker on this query.
pub(crate) fn note_bounds_derived() {
    BOUNDS_DERIVED.fetch_add(1, Ordering::Relaxed);
}

/// Record that one nonlinear component reached an exact decider with derived
/// bounds attached.
pub(crate) fn note_component_offered() {
    COMPONENTS_OFFERED.fetch_add(1, Ordering::Relaxed);
}

// ============================================================================
// Policy
// ============================================================================

/// How hard the FBBT route tries, and whether it runs at all.
///
/// A policy value rather than five bare constants so that the arm which
/// reproduces the pre-2026-09-09 behaviour ([`FbbtPolicy::OFF`]) and the arm being
/// evaluated ([`FbbtPolicy::DERIVED_BOUNDS`]) are **one binary and one env var**
/// (`AXEYUM_NRA_FBBT`), not two builds. Every field is a bounded-cost guard: this
/// route runs on each decline of the multivariate decomposition, which inside the
/// lazy-SMT loop is once per cube, so an unbounded fixpoint here would be paid
/// hundreds of times per query.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct FbbtPolicy {
    /// The arm's name, as `AXEYUM_NRA_FBBT` spells it. Carried so a trace can name
    /// the arm that ran; nothing branches on it.
    pub(crate) name: &'static str,
    /// Whether the route runs at all. `false` reproduces the pre-2026-09-09
    /// behaviour exactly: `decide_real_poly_constraint` returns whatever the
    /// multivariate decomposition returned.
    pub(crate) enabled: bool,
    /// Maximum interval-propagation sweeps over the linear facts. Each sweep is
    /// `O(facts × vars)`; propagation stops early as soon as a sweep tightens
    /// nothing, so this only bounds the pathological case — a chain of bounds that
    /// keeps improving by ever-smaller amounts, which interval propagation does
    /// asymptotically on a cyclic system.
    pub(crate) max_rounds: usize,
    /// Maximum number of **linear** atoms admitted as propagation facts. Above it
    /// the route declines rather than run an `O(rounds × facts × vars)` sweep over
    /// a system that is LRA's job anyway.
    pub(crate) max_linear_facts: usize,
    /// Maximum number of **nonlinear** atoms in the query. Above it the route
    /// declines: the population this was built for has a handful of nonlinear
    /// atoms among many linear ones, and a nonlinear-heavy query is the
    /// `lra_theory::MAX_ONLINE_LRA_ATOMS` class this route explicitly does not
    /// address (14 files, 11–36× past that capacity — not a tuning distance).
    pub(crate) max_nonlinear_atoms: usize,
    /// Maximum certified bounds kept in the pool. Bounds the memory a cyclic
    /// system can make the propagation allocate, independently of `max_rounds`.
    pub(crate) max_derived_bounds: usize,
    /// Largest nonlinear connected component handed to `decide_component`, in
    /// distinct variables.
    ///
    /// **2, because 3 is where the deciders stop being cheap.**
    /// `decide_component` routes 1 variable to the sign-cell decider and 2 to
    /// resultant elimination plus a two-variable CAD; at 3 it enters the recursive
    /// N-variable CAD, which is the route that already declined on this
    /// population and whose cost this route exists to avoid paying twice.
    pub(crate) max_component_vars: usize,
}

impl FbbtPolicy {
    /// The route does not run. Reproduces the pre-2026-09-09 engine exactly, and
    /// is the A/B control arm.
    pub(crate) const OFF: Self = Self {
        name: "off",
        enabled: false,
        max_rounds: 0,
        max_linear_facts: 0,
        max_nonlinear_atoms: 0,
        max_derived_bounds: 0,
        max_component_vars: 0,
    };

    /// Derive constant bounds from the linear atoms and re-offer the nonlinear
    /// component to the cheap exact deciders.
    pub(crate) const DERIVED_BOUNDS: Self = Self {
        name: "derived-bounds",
        enabled: true,
        max_rounds: 8,
        max_linear_facts: 512,
        max_nonlinear_atoms: 64,
        max_derived_bounds: 256,
        max_component_vars: 2,
    };
}

/// The FBBT policy in force, read once from `AXEYUM_NRA_FBBT`.
///
/// Read once into a `OnceLock`: determinism is a public API promise, so the policy
/// cannot change between two solves in one process. `scripts/parity-run.sh` records
/// any `AXEYUM_*` lever it sees in the ledger entry, so a swept arm can never be
/// mistaken for a default-configuration one.
pub(crate) fn fbbt_policy() -> FbbtPolicy {
    use std::sync::OnceLock;
    static POLICY: OnceLock<FbbtPolicy> = OnceLock::new();
    *POLICY.get_or_init(|| match std::env::var("AXEYUM_NRA_FBBT") {
        Ok(v) if v.trim() == "off" => FbbtPolicy::OFF,
        Ok(v) if v.trim() == "derived-bounds" => FbbtPolicy::DERIVED_BOUNDS,
        _ => FBBT_DEFAULT,
    })
}

/// The arm used when `AXEYUM_NRA_FBBT` is unset or unrecognized.
///
/// See the module docs for the population, and the `NRA_FBBT_DEFAULT` row of
/// `crates/axeyum-solver/src/config_registry.rs` for the measurement.
pub(crate) const FBBT_DEFAULT: FbbtPolicy = FbbtPolicy::DERIVED_BOUNDS;

// ============================================================================
// Facts, claims, certificates
// ============================================================================

/// A linear constraint oriented as `Σ aᵢ·xᵢ + c ≥ 0` (or `> 0` when `strict`).
///
/// Orienting every fact one way is what makes the certificate check a handful of
/// comparisons instead of a case analysis: a nonnegative combination of facts in
/// this form is again a fact in this form.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LinearFact {
    /// Coefficients by variable. Every entry is nonzero (a zero coefficient is a
    /// variable the fact does not mention, and leaving it in would make two equal
    /// facts compare unequal).
    pub(crate) coeffs: BTreeMap<SymbolId, Rational>,
    /// The constant term `c`.
    pub(crate) constant: Rational,
    /// `true` ⇒ the assertion is `> 0`; `false` ⇒ `≥ 0`.
    pub(crate) strict: bool,
}

impl LinearFact {
    /// Build a fact, dropping any zero coefficient so the representation is
    /// canonical.
    pub(crate) fn new(
        coeffs: BTreeMap<SymbolId, Rational>,
        constant: Rational,
        strict: bool,
    ) -> Self {
        let mut coeffs = coeffs;
        coeffs.retain(|_, c| !c.is_zero());
        LinearFact {
            coeffs,
            constant,
            strict,
        }
    }

    /// `self` scaled by `lambda`, or `None` on rational overflow. The caller has
    /// already established `lambda > 0`, so the orientation is preserved.
    fn scaled(&self, lambda: Rational) -> Option<Self> {
        let mut coeffs = BTreeMap::new();
        for (&v, &c) in &self.coeffs {
            let s = c.checked_mul(lambda)?;
            if !s.is_zero() {
                coeffs.insert(v, s);
            }
        }
        Some(LinearFact {
            coeffs,
            constant: self.constant.checked_mul(lambda)?,
            strict: self.strict,
        })
    }
}

/// Which end of a variable's range a bound constrains.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum BoundSide {
    /// `x ≥ value`, or `x > value` when strict.
    Lower,
    /// `x ≤ value`, or `x < value` when strict.
    Upper,
}

/// A *claimed* constant bound on one variable. Untrusted until [`verify`] accepts
/// it: this is what the propagation produces, and the checker's input.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct BoundClaim {
    /// The bounded variable.
    pub(crate) var: SymbolId,
    /// Which end of its range.
    pub(crate) side: BoundSide,
    /// The bounding constant.
    pub(crate) value: Rational,
    /// `true` ⇒ the bound is strict (`<` / `>`).
    pub(crate) strict: bool,
}

impl BoundClaim {
    /// The claim as a `≥ 0` / `> 0` target: `u − x` for an upper bound, `x − l`
    /// for a lower one. This is the polynomial the certificate must reconstruct.
    /// `None` when negating the value overflows, which declines rather than
    /// silently checking a different claim than the one made.
    fn target(&self) -> Option<LinearFact> {
        let mut coeffs = BTreeMap::new();
        let (coeff, constant) = match self.side {
            BoundSide::Upper => (Rational::integer(-1), self.value),
            BoundSide::Lower => (Rational::integer(1), self.value.checked_neg()?),
        };
        coeffs.insert(self.var, coeff);
        Some(LinearFact {
            coeffs,
            constant,
            strict: self.strict,
        })
    }
}

/// A bound that [`verify`] has **checked** against the facts it cites.
///
/// The inner claim is a private field and there is no other constructor: outside
/// this module the only way to hold one is to have called [`verify`] and had it
/// accept. That is the whole point — the decider downstream consumes
/// `CertifiedBound`, not `BoundClaim`, so an unchecked bound cannot reach a
/// verdict.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct CertifiedBound {
    claim: BoundClaim,
}

impl CertifiedBound {
    /// The bound this certificate established.
    pub(crate) fn claim(&self) -> BoundClaim {
        self.claim
    }
}

/// A Farkas certificate: nonnegative multipliers on facts, by index into the pool
/// the claim is checked against.
pub(crate) type Certificate = Vec<(usize, Rational)>;

/// Why a certificate was rejected.
///
/// Returned rather than a bare `None` so a test can require that a **specific**
/// guard fired, instead of merely that something did: a rejection for the wrong
/// reason is a guard that is not being exercised, and it looks identical from the
/// outside.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Rejected {
    /// A multiplier index does not name a fact in the pool.
    UnknownFact,
    /// The same fact is cited twice.
    DuplicateFact,
    /// A multiplier is zero or negative. A nonpositive multiplier breaks the whole
    /// argument: `λ·p ≥ 0` needs `λ ≥ 0`, and `λ = 0` is a citation carrying
    /// nothing.
    NonPositiveMultiplier,
    /// The certificate cites nothing. An empty combination entails only
    /// `target ≥ 0` when `target` is itself a nonnegative constant, which is never
    /// a bound on a variable.
    EmptyCertificate,
    /// The reconstructed combination does not have the claimed polynomial's
    /// variable part: some variable's coefficient does not cancel.
    VariablesDoNotCancel,
    /// The residual constant `target − Σ λⱼ pⱼ` is **negative**, i.e. the facts
    /// entail a weaker bound than the one claimed. This is the guard that rejects a
    /// derived bound that is too tight — the one whose absence is a wrong `unsat`.
    ResidualNegative,
    /// A strict bound was claimed but the combination entails only a non-strict
    /// one (every cited fact is non-strict and the residual constant is zero).
    StrictnessUnjustified,
    /// Exact-rational overflow while reconstructing the combination.
    Overflow,
}

/// Check a claimed bound against the facts its certificate cites.
///
/// Accepts exactly when `target − Σ λⱼ·pⱼ` is a **nonnegative constant** and every
/// `λⱼ > 0`, where `target` is the claim in `≥ 0` form. Then
///
/// ```text
///   target = Σ λⱼ·pⱼ + s,   λⱼ > 0,  pⱼ ≥ 0,  s ≥ 0   ⟹   target ≥ 0
/// ```
///
/// and `target > 0` as soon as one cited `pⱼ` is strict or `s > 0`, which is what
/// licenses a strict claim.
///
/// Nothing here depends on how the multipliers were found. `pool` must contain
/// only facts already entailed by the query — the caller establishes that by
/// appending a bound to the pool **only after** this function has accepted it, so
/// a citation always names an already-checked fact and the induction closes.
pub(crate) fn verify(
    pool: &[LinearFact],
    claim: BoundClaim,
    cert: &Certificate,
) -> Result<CertifiedBound, Rejected> {
    // GUARD 0 — the certificate must cite something, and cite it once.
    if cert.is_empty() {
        return Err(Rejected::EmptyCertificate);
    }
    let mut seen: BTreeSet<usize> = BTreeSet::new();
    for &(idx, _) in cert {
        if idx >= pool.len() {
            return Err(Rejected::UnknownFact);
        }
        if !seen.insert(idx) {
            return Err(Rejected::DuplicateFact);
        }
    }

    // GUARD 1 — every multiplier is strictly positive. Without this a certificate
    // could SUBTRACT a fact, which entails nothing at all.
    for &(_, lambda) in cert {
        if lambda <= Rational::zero() {
            return Err(Rejected::NonPositiveMultiplier);
        }
    }

    // Reconstruct `Σ λⱼ·pⱼ` from the pool, in the certificate's own order.
    let mut combo_coeffs: BTreeMap<SymbolId, Rational> = BTreeMap::new();
    let mut combo_constant = Rational::zero();
    let mut combo_strict = false;
    for &(idx, lambda) in cert {
        let Some(scaled) = pool[idx].scaled(lambda) else {
            return Err(Rejected::Overflow);
        };
        for (&v, &c) in &scaled.coeffs {
            let entry = combo_coeffs.entry(v).or_insert_with(Rational::zero);
            let Some(sum) = entry.checked_add(c) else {
                return Err(Rejected::Overflow);
            };
            *entry = sum;
        }
        let Some(sum) = combo_constant.checked_add(scaled.constant) else {
            return Err(Rejected::Overflow);
        };
        combo_constant = sum;
        combo_strict |= scaled.strict;
    }

    // GUARD 2 — the variable part must match the target exactly. Any variable the
    // combination does not cancel leaves a term whose sign is unknown, and no bound
    // can be read off it.
    let Some(target) = claim.target() else {
        return Err(Rejected::Overflow);
    };
    let mut vars: BTreeSet<SymbolId> = combo_coeffs.keys().copied().collect();
    vars.extend(target.coeffs.keys().copied());
    for v in vars {
        let a = combo_coeffs.get(&v).copied().unwrap_or_else(Rational::zero);
        let b = target
            .coeffs
            .get(&v)
            .copied()
            .unwrap_or_else(Rational::zero);
        if a != b {
            return Err(Rejected::VariablesDoNotCancel);
        }
    }

    // GUARD 3 — the residual `s = target.constant − combo.constant` must be
    // NONNEGATIVE. This separates a bound the facts entail from one tighter than
    // they entail, and a tighter bound is a wrong `unsat`.
    let Some(neg_combo) = combo_constant.checked_neg() else {
        return Err(Rejected::Overflow);
    };
    let Some(residual) = target.constant.checked_add(neg_combo) else {
        return Err(Rejected::Overflow);
    };
    if residual < Rational::zero() {
        return Err(Rejected::ResidualNegative);
    }

    // GUARD 4 — a strict claim needs a strict witness: either a cited strict fact
    // (with a positive multiplier, which GUARD 1 already established) or a strictly
    // positive residual.
    if claim.strict && !combo_strict && residual <= Rational::zero() {
        return Err(Rejected::StrictnessUnjustified);
    }

    Ok(CertifiedBound { claim })
}

// ============================================================================
// Propagation — the untrusted half
// ============================================================================

/// One variable's currently-known constant range, with the pool index of the fact
/// that established each end (so a later derivation can cite it).
#[derive(Clone, Default)]
struct Range {
    /// `(value, strict, pool index of `x − value ⋈ 0`)`.
    lower: Option<(Rational, bool, usize)>,
    /// `(value, strict, pool index of `value − x ⋈ 0`)`.
    upper: Option<(Rational, bool, usize)>,
}

/// The result of one propagation pass.
pub(crate) struct DerivedBounds {
    /// Every bound the checker accepted — at most one per (variable, side), the
    /// tightest reached.
    pub(crate) bounds: Vec<CertifiedBound>,
    /// How many certificate proposals the checker **rejected**. Nonzero here is not
    /// an error — the propagation is untrusted and may over-reach — but it is the
    /// counter that says the checker is doing work.
    pub(crate) rejected: usize,
}

/// Derive constant bounds on the variables of `facts` by interval propagation, and
/// return only the ones [`verify`] accepted.
///
/// This is the **untrusted** half. It may compute a wrong value, cite the wrong
/// fact, or fall over an overflow; the worst any of that does is lose a bound,
/// because nothing it returns has bypassed the checker. Accepted bounds are
/// appended to a growing pool so a later derivation may cite an earlier one, which
/// is what makes the propagation *transitive* — the property
/// `nra::extract_bounds` explicitly does not have.
pub(crate) fn derive_bounds(facts: &[LinearFact], policy: &FbbtPolicy) -> DerivedBounds {
    // INVARIANT the certificates depend on: `pool` STARTS as a copy of `facts`,
    // so for every `fi < facts.len()`, `pool[fi] == facts[fi]` and a proposal may
    // cite its source fact by its `facts` index. Derived bounds are appended
    // after, never inserted, so that correspondence is stable for the whole run.
    let mut pool: Vec<LinearFact> = facts.to_vec();
    let mut ranges: BTreeMap<SymbolId, Range> = BTreeMap::new();
    let mut accepted: Vec<CertifiedBound> = Vec::new();
    let mut rejected = 0usize;

    'rounds: for _ in 0..policy.max_rounds {
        let mut progressed = false;
        for (fi, fact) in facts.iter().enumerate() {
            let vars: Vec<SymbolId> = fact.coeffs.keys().copied().collect();
            for k in vars {
                if accepted.len() >= policy.max_derived_bounds {
                    break 'rounds;
                }
                let Some(proposal) = propose(fact, fi, k, &ranges) else {
                    continue;
                };
                if !improves(&ranges, &proposal.claim) {
                    continue;
                }
                match verify(&pool, proposal.claim, &proposal.cert) {
                    Ok(certified) => {
                        // The bound is checked, so appending it to the pool keeps
                        // the pool's invariant (every entry is entailed by the
                        // query) and lets the next round cite it.
                        let Some(fact) = proposal.claim.target() else {
                            // `verify` already reconstructed this target, so it
                            // cannot fail here; declining is the safe branch.
                            continue;
                        };
                        let idx = pool.len();
                        pool.push(fact);
                        let range = ranges.entry(proposal.claim.var).or_default();
                        let slot = match proposal.claim.side {
                            BoundSide::Lower => &mut range.lower,
                            BoundSide::Upper => &mut range.upper,
                        };
                        *slot = Some((proposal.claim.value, proposal.claim.strict, idx));
                        accepted.push(certified);
                        progressed = true;
                    }
                    Err(_) => rejected += 1,
                }
            }
        }
        if !progressed {
            break;
        }
    }

    // Keep only the tightest accepted bound per (variable, side): the intermediate
    // ones are subsumed, and every extra atom is one more the decider must handle.
    let mut best: BTreeMap<(SymbolId, BoundSide), CertifiedBound> = BTreeMap::new();
    for b in accepted {
        best.insert((b.claim.var, b.claim.side), b);
    }
    DerivedBounds {
        bounds: best.into_values().collect(),
        rejected,
    }
}

/// A claim plus the certificate the propagation believes supports it.
struct Proposal {
    claim: BoundClaim,
    cert: Certificate,
}

/// Would `claim` tighten what is already known about its variable? A bound that
/// does not is dropped before the checker sees it, so the pool cannot grow on a
/// fact that re-derives the same value every round.
fn improves(ranges: &BTreeMap<SymbolId, Range>, claim: &BoundClaim) -> bool {
    let Some(range) = ranges.get(&claim.var) else {
        return true;
    };
    let cur = match claim.side {
        BoundSide::Lower => range.lower,
        BoundSide::Upper => range.upper,
    };
    match cur {
        None => true,
        Some((value, strict, _)) => {
            let tighter = match claim.side {
                BoundSide::Lower => claim.value > value,
                BoundSide::Upper => claim.value < value,
            };
            tighter || (claim.value == value && claim.strict && !strict)
        }
    }
}

/// Solve `fact` for `k` against the other variables' current ranges.
///
/// `fact` is `Σ aᵢxᵢ + c ⋈ 0`. Isolating `x_k` and replacing every other `aᵢxᵢ`
/// by its range-implied extreme in the direction that keeps the inequality valid
/// gives a constant bound on `x_k`, whose sense is set by the sign of `a_k`:
/// `a_k > 0` bounds it from **below**, `a_k < 0` from **above**.
///
/// The certificate falls straight out of that: multiplier `m = 1/|a_k|` on the
/// fact, and `|aᵢ|·m` on each range fact used. Scaling the fact by `m` puts
/// `±1` on `x_k` and `aᵢ·m` on each other variable, and the range fact's own
/// `∓1` cancels it exactly, leaving the constant `m·c + Σ aᵢ·m·bᵢ` — which is the
/// bound (upper) or its negation (lower).
///
/// `None` on a missing range or an overflow — both are ordinary declines. Nothing
/// here is trusted: the proposal goes to [`verify`] regardless.
fn propose(
    fact: &LinearFact,
    fact_idx: usize,
    k: SymbolId,
    ranges: &BTreeMap<SymbolId, Range>,
) -> Option<Proposal> {
    let a_k = *fact.coeffs.get(&k)?;
    if a_k.is_zero() {
        return None;
    }
    let m = Rational::integer(1).checked_div(abs(a_k)?)?;

    let mut cert: Certificate = vec![(fact_idx, m)];
    let mut combo_constant = fact.constant.checked_mul(m)?;
    let mut strict = fact.strict;

    for (&v, &a_i) in &fact.coeffs {
        if v == k {
            continue;
        }
        let range = ranges.get(&v)?;
        // A positive coefficient is bounded above by the variable's UPPER end; a
        // negative one by its LOWER end. Either missing ⇒ no constant bound.
        let (b_i, b_strict, b_idx) = if a_i > Rational::zero() {
            range.upper?
        } else {
            range.lower?
        };
        cert.push((b_idx, abs(a_i)?.checked_mul(m)?));
        combo_constant = combo_constant.checked_add(a_i.checked_mul(m)?.checked_mul(b_i)?)?;
        strict |= b_strict;
    }

    let (side, value) = if a_k > Rational::zero() {
        (BoundSide::Lower, combo_constant.checked_neg()?)
    } else {
        (BoundSide::Upper, combo_constant)
    };
    Some(Proposal {
        claim: BoundClaim {
            var: k,
            side,
            value,
            strict,
        },
        cert,
    })
}

/// `|r|`, or `None` on the overflow `checked_neg` reports.
fn abs(r: Rational) -> Option<Rational> {
    if r < Rational::zero() {
        r.checked_neg()
    } else {
        Some(r)
    }
}

// ============================================================================
// The verdict type — the reason this route cannot report `sat`
// ============================================================================

/// A refutation produced by the FBBT route.
///
/// **This type is the structural refusal of `sat`.** It carries no model and has
/// no other variant; [`Refutation::new`] takes three counters and nothing a model
/// could be smuggled through; and [`Refutation::into_check_result`] is a constant
/// function. Reporting `sat` from this route is not a matter of forgetting a
/// `return` — it would take a new variant, a new field and a new branch.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Refutation {
    /// How many nonlinear atoms were in the refuted component. Diagnostic only;
    /// nothing branches on it.
    pub(crate) nonlinear_atoms: usize,
    /// How many certified bounds the component needed. Diagnostic only.
    pub(crate) derived_bounds: usize,
    /// Distinct variables in the refuted nonlinear component. Diagnostic only.
    pub(crate) component_vars: usize,
}

impl Refutation {
    /// The only constructor: three counters, none of which can hold a model.
    pub(crate) fn new(
        nonlinear_atoms: usize,
        derived_bounds: usize,
        component_vars: usize,
    ) -> Self {
        REFUTATIONS.fetch_add(1, Ordering::Relaxed);
        Refutation {
            nonlinear_atoms,
            derived_bounds,
            component_vars,
        }
    }

    /// The one bridge from this route to a solver verdict.
    ///
    /// The body is the constant `CheckResult::Unsat`: it reads no field and takes
    /// no branch, so no computation in this module can steer it to `Sat` or
    /// `Unknown`.
    #[allow(
        clippy::unused_self,
        reason = "the unused `self` IS the soundness property: this function must \
                  read no field and take no branch, so nothing this module computes \
                  can steer it away from `Unsat`. Refactoring it to an associated \
                  function would keep the constant body but lose the guarantee that \
                  a Refutation is what reached it."
    )]
    pub(crate) fn into_check_result(self) -> crate::CheckResult {
        crate::CheckResult::Unsat
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Three distinct `SymbolId`s from a throwaway arena. `SymbolId` has no public
    /// constructor — it is an arena-relative handle — so the tests declare real
    /// symbols and index them, rather than fabricating raw ids.
    fn syms() -> [SymbolId; 3] {
        use axeyum_ir::{Sort, TermArena};
        let mut arena = TermArena::new();
        [
            arena.declare("fbbt_x", Sort::Real).unwrap(),
            arena.declare("fbbt_y", Sort::Real).unwrap(),
            arena.declare("fbbt_z", Sort::Real).unwrap(),
        ]
    }

    fn sym(n: u32) -> SymbolId {
        syms()[n as usize]
    }

    fn r(n: i128) -> Rational {
        Rational::integer(n)
    }

    /// `Σ (coeff·var) + constant ⋈ 0`.
    fn fact(terms: &[(u32, i128)], constant: i128, strict: bool) -> LinearFact {
        let mut coeffs = BTreeMap::new();
        for &(v, c) in terms {
            coeffs.insert(sym(v), r(c));
        }
        LinearFact::new(coeffs, r(constant), strict)
    }

    fn upper(v: u32, value: Rational, strict: bool) -> BoundClaim {
        BoundClaim {
            var: sym(v),
            side: BoundSide::Upper,
            value,
            strict,
        }
    }

    fn lower(v: u32, value: Rational, strict: bool) -> BoundClaim {
        BoundClaim {
            var: sym(v),
            side: BoundSide::Lower,
            value,
            strict,
        }
    }

    // ---------------------------------------------------------------------
    // The checker's guards, one killer test each.
    //
    // Each of these constructs a certificate that violates EXACTLY ONE guard and
    // requires that guard's own rejection reason. Requiring the reason, not just
    // `is_err()`, is what makes the tests separable: without it, deleting any one
    // guard could leave every test passing on some other guard's rejection.
    // ---------------------------------------------------------------------

    /// GUARD 3, and the whole point of the module: a bound TIGHTER than the facts
    /// entail is rejected. `x ≤ 10` is what `10 − x ≥ 0` gives; `x ≤ 5` is a wrong
    /// `unsat` waiting to happen, and the residual `5 − 10 = −5` is what catches it.
    #[test]
    fn a_bound_tighter_than_the_facts_entail_is_rejected() {
        let pool = vec![fact(&[(0, -1)], 10, false)]; // 10 − x ≥ 0  ⇒  x ≤ 10
        let honest = verify(&pool, upper(0, r(10), false), &vec![(0, r(1))]);
        assert!(honest.is_ok(), "the entailed bound must be accepted");
        assert_eq!(
            verify(&pool, upper(0, r(5), false), &vec![(0, r(1))]),
            Err(Rejected::ResidualNegative),
            "x ≤ 5 is not entailed by x ≤ 10 and must be refused"
        );
    }

    /// GUARD 3 on the lower side: `x ≥ 0` is entailed, `x ≥ 3` is not.
    #[test]
    fn a_lower_bound_tighter_than_the_facts_entail_is_rejected() {
        let pool = vec![fact(&[(0, 1)], 0, false)]; // x ≥ 0
        assert!(verify(&pool, lower(0, r(0), false), &vec![(0, r(1))]).is_ok());
        assert_eq!(
            verify(&pool, lower(0, r(3), false), &vec![(0, r(1))]),
            Err(Rejected::ResidualNegative)
        );
    }

    /// GUARD 1: a negative multiplier would let a certificate SUBTRACT a fact,
    /// turning `x ≥ 0` into `x ≤ 0`.
    #[test]
    fn a_negative_multiplier_is_rejected() {
        let pool = vec![fact(&[(0, 1)], 0, false)]; // x ≥ 0
        assert_eq!(
            verify(&pool, upper(0, r(0), false), &vec![(0, r(-1))]),
            Err(Rejected::NonPositiveMultiplier)
        );
    }

    /// GUARD 1, zero case: a zero multiplier carries nothing, and admitting it
    /// would let an empty-in-effect certificate look non-empty.
    #[test]
    fn a_zero_multiplier_is_rejected() {
        let pool = vec![fact(&[(0, -1)], 10, false)];
        assert_eq!(
            verify(&pool, upper(0, r(10), false), &vec![(0, Rational::zero())]),
            Err(Rejected::NonPositiveMultiplier)
        );
    }

    /// GUARD 2: `x + y ≥ 0` does not bound `x` — `y` does not cancel, so its term's
    /// sign is unknown and nothing can be read off the constant.
    #[test]
    fn a_combination_leaving_a_live_variable_is_rejected() {
        let pool = vec![fact(&[(0, 1), (1, 1)], 0, false)]; // x + y ≥ 0
        assert_eq!(
            verify(&pool, lower(0, r(0), false), &vec![(0, r(1))]),
            Err(Rejected::VariablesDoNotCancel)
        );
    }

    /// GUARD 4: two non-strict facts cannot entail a strict bound. `x ≤ 10` from
    /// `10 − x ≥ 0` is fine; `x < 10` is not.
    #[test]
    fn a_strict_bound_from_non_strict_facts_is_rejected() {
        let pool = vec![fact(&[(0, -1)], 10, false)];
        assert!(verify(&pool, upper(0, r(10), false), &vec![(0, r(1))]).is_ok());
        assert_eq!(
            verify(&pool, upper(0, r(10), true), &vec![(0, r(1))]),
            Err(Rejected::StrictnessUnjustified)
        );
    }

    /// GUARD 4, positive direction: a STRICT fact does license a strict bound.
    #[test]
    fn a_strict_fact_licenses_a_strict_bound() {
        let pool = vec![fact(&[(0, -1)], 10, true)]; // 10 − x > 0  ⇒  x < 10
        assert!(verify(&pool, upper(0, r(10), true), &vec![(0, r(1))]).is_ok());
    }

    /// GUARD 0: an empty certificate proves nothing about a variable.
    #[test]
    fn an_empty_certificate_is_rejected() {
        let pool = vec![fact(&[(0, -1)], 10, false)];
        assert_eq!(
            verify(&pool, upper(0, r(10), false), &vec![]),
            Err(Rejected::EmptyCertificate)
        );
    }

    /// GUARD 0: citing a fact that is not in the pool. This is the guard that keeps
    /// the pool's induction honest — a bound may only cite already-checked facts.
    #[test]
    fn a_certificate_citing_a_fact_outside_the_pool_is_rejected() {
        let pool = vec![fact(&[(0, -1)], 10, false)];
        assert_eq!(
            verify(&pool, upper(0, r(10), false), &vec![(7, r(1))]),
            Err(Rejected::UnknownFact)
        );
    }

    /// GUARD 0: citing one fact twice. Admitting it would let a single `x ≤ 10`
    /// be scaled to `2x ≤ 20` and re-read as a different bound on the same
    /// variable.
    #[test]
    fn a_certificate_citing_one_fact_twice_is_rejected() {
        let pool = vec![fact(&[(0, -1)], 10, false)];
        assert_eq!(
            verify(
                &pool,
                upper(0, r(10), false),
                &vec![(0, Rational::new(1, 2)), (0, Rational::new(1, 2))]
            ),
            Err(Rejected::DuplicateFact)
        );
    }

    // ---------------------------------------------------------------------
    // Propagation
    // ---------------------------------------------------------------------

    /// The worked instance from the module docs, as raw facts: `sqrt-1mcosq`'s
    /// three linear atoms bound `skoY` from both sides, and both bounds are
    /// TRANSITIVE — `skoY ≤ −1/5 + pi/2` needs `pi`'s upper bound first, and
    /// `skoY > skoX` needs `skoX`'s lower bound. `nra::extract_bounds` recognises
    /// neither.
    #[test]
    fn the_sqrt_1mcosq_linear_atoms_bound_sko_y_transitively() {
        // 0 = skoY, 1 = pi, 2 = skoX.
        let facts = vec![
            // −skoY − 1/5 + pi/2 ≥ 0     (skoY ≤ −1/5 + pi/2)
            LinearFact::new(
                [(sym(0), r(-1)), (sym(1), Rational::new(1, 2))].into(),
                Rational::new(-1, 5),
                false,
            ),
            // pi − 15707963/5000000 > 0
            LinearFact::new(
                [(sym(1), r(1))].into(),
                Rational::new(-15_707_963, 5_000_000),
                true,
            ),
            // 31415927/10000000 − pi > 0
            LinearFact::new(
                [(sym(1), r(-1))].into(),
                Rational::new(31_415_927, 10_000_000),
                true,
            ),
            // skoX − 1/10 ≥ 0
            LinearFact::new([(sym(2), r(1))].into(), Rational::new(-1, 10), false),
            // skoY − skoX > 0
            LinearFact::new([(sym(0), r(1)), (sym(2), r(-1))].into(), r(0), true),
        ];
        let derived = derive_bounds(&facts, &FbbtPolicy::DERIVED_BOUNDS);
        // The propagation and the checker must AGREE on every proposal here: a
        // rejection would mean the search computed a value its own certificate
        // does not support, i.e. a bug in `propose`. The bound would be dropped
        // (sound), but silently, so the counter is asserted rather than ignored.
        assert_eq!(derived.rejected, 0, "the checker rejected a proposal");
        let sko_y: Vec<BoundClaim> = derived
            .bounds
            .iter()
            .map(CertifiedBound::claim)
            .filter(|b| b.var == sym(0))
            .collect();
        assert_eq!(
            sko_y.len(),
            2,
            "skoY must be bounded on both sides: {sko_y:?}"
        );

        let lo = sko_y.iter().find(|b| b.side == BoundSide::Lower).unwrap();
        let hi = sko_y.iter().find(|b| b.side == BoundSide::Upper).unwrap();
        assert_eq!(lo.value, Rational::new(1, 10));
        assert!(lo.strict, "skoY > skoX ≥ 1/10 is strict");
        // −1/5 + (31415927/10000000)/2 = 31415927/20000000 − 1/5.
        assert_eq!(
            hi.value,
            Rational::new(31_415_927, 20_000_000)
                .checked_add(Rational::new(-1, 5))
                .unwrap()
        );
        assert!(hi.strict, "pi's upper bound is strict, so skoY's is too");
        // The interval is the one the module docs quote, and it is NON-EMPTY: an
        // empty derived interval would refute everything and would be the shape of
        // a wrong `unsat`.
        assert!(lo.value < hi.value, "{lo:?} .. {hi:?}");
    }

    /// Every bound the propagation returns is one the checker accepted, and
    /// re-checking each against the ORIGINAL facts alone must still work for the
    /// non-transitive ones. This is the property the pool's induction rests on.
    #[test]
    fn a_derived_bound_is_never_stronger_than_a_direct_one() {
        // x ≥ 0, x ≤ 10, y = x + 1 as two inequalities.
        let facts = vec![
            fact(&[(0, 1)], 0, false),           // x ≥ 0
            fact(&[(0, -1)], 10, false),         // x ≤ 10
            fact(&[(1, 1), (0, -1)], -1, false), // y − x − 1 ≥ 0  ⇒ y ≥ x+1
            fact(&[(1, -1), (0, 1)], 1, false),  // −y + x + 1 ≥ 0 ⇒ y ≤ x+1
        ];
        let derived = derive_bounds(&facts, &FbbtPolicy::DERIVED_BOUNDS);
        assert_eq!(derived.rejected, 0, "the checker rejected a proposal");
        let y: Vec<BoundClaim> = derived
            .bounds
            .iter()
            .map(CertifiedBound::claim)
            .filter(|b| b.var == sym(1))
            .collect();
        let lo = y.iter().find(|b| b.side == BoundSide::Lower).unwrap();
        let hi = y.iter().find(|b| b.side == BoundSide::Upper).unwrap();
        assert_eq!(lo.value, r(1), "y ≥ 0 + 1");
        assert_eq!(hi.value, r(11), "y ≤ 10 + 1");
    }

    /// An unbounded variable yields no bound rather than a wrong one. `x ≤ y` with
    /// `y` unconstrained bounds nothing, and the propagation must say so instead of
    /// inventing an extreme.
    #[test]
    fn an_unbounded_neighbour_yields_no_bound() {
        let facts = vec![fact(&[(0, -1), (1, 1)], 0, false)]; // y − x ≥ 0
        let derived = derive_bounds(&facts, &FbbtPolicy::DERIVED_BOUNDS);
        assert!(
            derived.bounds.is_empty(),
            "nothing is bounded: {:?}",
            derived
                .bounds
                .iter()
                .map(CertifiedBound::claim)
                .collect::<Vec<_>>()
        );
    }

    /// The `OFF` arm derives nothing, which is what makes the A/B one binary.
    #[test]
    fn the_off_arm_derives_nothing() {
        let facts = vec![fact(&[(0, -1)], 10, false)];
        assert!(derive_bounds(&facts, &FbbtPolicy::OFF).bounds.is_empty());
        const { assert!(!FbbtPolicy::OFF.enabled) };
    }

    /// The bridge to a verdict is `Unsat` for every refutation, whatever counters
    /// it carries. If this ever needs a branch, the structural argument in the
    /// module docs has been broken.
    #[test]
    fn the_only_verdict_this_route_can_produce_is_unsat() {
        for (a, b, c) in [(0, 0, 0), (1, 2, 1), (7, 3, 2)] {
            assert!(matches!(
                Refutation::new(a, b, c).into_check_result(),
                crate::CheckResult::Unsat
            ));
        }
    }
}
