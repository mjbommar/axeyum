//! Bounded, source-bound polynomial rewrite traces (ADR-2500).
//!
//! Replay shares exact polynomial arithmetic with the producer, but never
//! invokes the trace producer or heuristic equality search. A checked trace
//! certifies rational equality; kernel admission is a separate operation.
use axeyum_ir::Rational;
use serde::{Deserialize, Serialize};

use crate::{CasExpr, normalize};

/// Stable polynomial expression encoding over rational assignments.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(
    tag = "kind",
    content = "args",
    rename_all = "snake_case",
    deny_unknown_fields
)]
pub enum PolynomialExpr {
    /// Canonical numerator and positive denominator, as decimal strings.
    Const {
        /// Signed normalized numerator.
        numerator: String,
        /// Positive normalized denominator.
        denominator: String,
    },
    /// A parameter, distinct from a distinguished mathematical constant.
    Var(String),
    /// Sum; the empty sum is zero.
    Add(Vec<Self>),
    /// Product; the empty product is one.
    Mul(Vec<Self>),
    /// Additive inverse.
    Neg(Box<Self>),
    /// Nonnegative integer power; exponent zero denotes one.
    Pow {
        /// Base expression.
        base: Box<Self>,
        /// Exact nonnegative exponent.
        exponent: u32,
    },
}

/// Limits are enforced both on construction and by the replay caller.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TraceLimits {
    /// Maximum ordered steps.
    pub steps: usize,
    /// Maximum nodes in each expression.
    pub nodes: usize,
    /// Maximum expression/path depth.
    pub depth: usize,
    /// Conservative maximum expanded monomials.
    pub terms: u64,
    /// Maximum total polynomial degree.
    pub degree: u32,
    /// Aggregate syntax/arithmetic work across the operation.
    pub work: u64,
    /// Maximum serialized input/output bytes.
    pub bytes: usize,
}
impl Default for TraceLimits {
    fn default() -> Self {
        Self {
            steps: 128,
            nodes: 256,
            depth: 32,
            terms: 512,
            degree: 32,
            work: 1_000_000,
            bytes: 1_048_576,
        }
    }
}
impl TraceLimits {
    fn bounded_by(self, other: Self) -> bool {
        self.steps <= other.steps
            && self.nodes <= other.nodes
            && self.depth <= other.depth
            && self.terms <= other.terms
            && self.degree <= other.degree
            && self.work <= other.work
            && self.bytes <= other.bytes
    }
    pub(crate) fn policy(self) -> Result<Self, TraceError> {
        if !self.bounded_by(Self::default()) {
            return Err(resource("limits exceed the version-1 hard caps"));
        }
        Ok(self)
    }
}

/// A specific rejection, unsupported fragment, or exhausted resource.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TraceError {
    /// Evidence does not establish the requested claim.
    Rejected {
        /// Failing step, or None for an envelope/endpoint failure.
        step: Option<usize>,
        /// Concrete failed obligation.
        reason: String,
    },
    /// The requested fragment/format is outside this rule set.
    Unsupported(String),
    /// Checking or production exhausted its explicit policy.
    ResourceLimit(String),
}
fn reject(step: Option<usize>, reason: &str) -> TraceError {
    TraceError::Rejected {
        step,
        reason: reason.to_owned(),
    }
}
fn resource(reason: &str) -> TraceError {
    TraceError::ResourceLimit(reason.to_owned())
}

fn decode_coefficient(numerator: &str, denominator: &str) -> Result<Rational, TraceError> {
    if numerator.len() > 40 || denominator.len() > 40 {
        return Err(resource("coefficient exceeds version-1 width"));
    }
    let digits = |text: &str| !text.is_empty() && text.bytes().all(|b| b.is_ascii_digit());
    if !digits(numerator.strip_prefix('-').unwrap_or(numerator)) || !digits(denominator) {
        return Err(reject(None, "malformed coefficient text"));
    }
    let num = numerator
        .parse::<i128>()
        .map_err(|_| resource("coefficient exceeds version-1 width"))?;
    let den = denominator
        .parse::<i128>()
        .map_err(|_| resource("coefficient exceeds version-1 width"))?;
    if den <= 0 {
        return Err(reject(None, "constant denominator must be positive"));
    }
    let r = Rational::checked_new(num, den)
        .ok_or_else(|| resource("coefficient cannot be normalized"))?;
    if r.numerator().to_string() != numerator || r.denominator().to_string() != denominator {
        return Err(reject(None, "constant encoding is not canonical"));
    }
    Ok(r)
}

fn decode_wide_coefficient(numerator: &str, denominator: &str) -> Result<Rational, TraceError> {
    use num_bigint::BigInt;
    use num_rational::BigRational;
    if numerator.len() > 5000 || denominator.len() > 5000 {
        return Err(resource("wide coefficient text cap"));
    }
    let digits = |text: &str| !text.is_empty() && text.bytes().all(|b| b.is_ascii_digit());
    if !digits(numerator.strip_prefix('-').unwrap_or(numerator)) || !digits(denominator) {
        return Err(reject(None, "malformed wide coefficient"));
    }
    let n: BigInt = numerator
        .parse()
        .map_err(|_| reject(None, "wide numerator"))?;
    let d: BigInt = denominator
        .parse()
        .map_err(|_| reject(None, "wide denominator"))?;
    if d <= BigInt::from(0) {
        return Err(reject(None, "wide denominator must be positive"));
    }
    if n.bits().max(d.bits()) > crate::wide_polynomial::COEFFICIENT_BITS {
        return Err(resource("wide coefficient bit cap"));
    }
    let rational = BigRational::new(n, d);
    if rational.numer().to_string() != numerator || rational.denom().to_string() != denominator {
        return Err(reject(None, "wide coefficient is not canonical"));
    }
    Rational::from_big_rational(&rational).ok_or_else(|| resource("wide rational carrier"))
}

/// One local equality, with complete surrounding-expression binding.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RewriteStep {
    /// Consecutive zero-based ID.
    pub id: usize,
    /// Full expression entering this step.
    pub before: PolynomialExpr,
    /// Full expression leaving this step.
    pub after: PolynomialExpr,
    /// Child indices from the root to the rewritten subexpression.
    pub location: Vec<usize>,
    /// Versioned operation-specific polynomial rule.
    pub rule: String,
    /// Exact exponent for a power rule; absent for other rules.
    pub exponent: Option<u32>,
    /// Previous step ID, or empty for the first step.
    pub premises: Vec<usize>,
    /// Version 1 permits only the explicit empty assumption context.
    pub context: String,
    /// Version 1 admits unconditional polynomial equalities only.
    pub side_conditions: Vec<PolynomialExpr>,
    /// Canonical normal form of the local before/after expression.
    pub witness: PolynomialExpr,
}

/// Ordered equality evidence, never a kernel-admission receipt.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RewriteTrace {
    /// Expression/rule contract version.
    pub version: String,
    /// Scalar semantics; version 1 is rational arithmetic.
    pub sort: String,
    /// Original expression, carried in full.
    pub input: PolynomialExpr,
    /// Claimed final expression, carried in full.
    pub result: PolynomialExpr,
    /// Explicit assumptions; version 1 requires the empty context.
    pub assumptions: Vec<PolynomialExpr>,
    /// Producer's resource contract, checked against local policy.
    pub limits: TraceLimits,
    /// Ordered local certificates.
    pub steps: Vec<RewriteStep>,
}

struct Work {
    wide: bool,
    remaining: u64,
    limits: TraceLimits,
}
impl Work {
    fn charge(&mut self, amount: u64) -> Result<(), TraceError> {
        self.remaining = self
            .remaining
            .checked_sub(amount)
            .ok_or_else(|| resource("trace work exhausted"))?;
        Ok(())
    }
    fn normal_form(&mut self, value: &CasExpr) -> Result<CasExpr, TraceError> {
        if self.wide {
            crate::wide_polynomial::normalize_with_budget(value, self.limits, &mut self.remaining)
        } else {
            normalize(value)
                .map(|p| p.to_expr())
                .ok_or_else(|| resource("exact coefficient arithmetic exhausted"))
        }
    }
    fn expression_at(
        &mut self,
        expr: &PolynomialExpr,
        index: usize,
    ) -> Result<CasExpr, TraceError> {
        self.expression(expr).map_err(|error| match error {
            TraceError::Rejected { reason, .. } => TraceError::Rejected {
                step: Some(index),
                reason,
            },
            other => other,
        })
    }

    fn expression(&mut self, expr: &PolynomialExpr) -> Result<CasExpr, TraceError> {
        self.convert(expr, 0, &mut 0).map(|(expr, _, _)| expr)
    }
    fn convert(
        &mut self,
        expr: &PolynomialExpr,
        depth: usize,
        nodes: &mut usize,
    ) -> Result<(CasExpr, u64, u32), TraceError> {
        if depth > self.limits.depth {
            return Err(resource("expression depth exhausted"));
        }
        *nodes += 1;
        if *nodes > self.limits.nodes {
            return Err(resource("expression node limit exhausted"));
        }
        self.charge(1)?;
        let (result, terms, degree) = match expr {
            PolynomialExpr::Const {
                numerator,
                denominator,
            } => (
                CasExpr::Const(if self.wide {
                    decode_wide_coefficient(numerator, denominator)?
                } else {
                    decode_coefficient(numerator, denominator)?
                }),
                1,
                0,
            ),
            PolynomialExpr::Var(name) => {
                if name.is_empty() || name.len() > 128 {
                    return Err(reject(None, "invalid parameter name"));
                }
                (CasExpr::Var(name.clone()), 1, 1)
            }
            PolynomialExpr::Add(children) | PolynomialExpr::Mul(children) => {
                let product = matches!(expr, PolynomialExpr::Mul(_));
                let mut terms: u64 = u64::from(product);
                let mut degree: u32 = 0;
                let mut converted = Vec::new();
                for child in children {
                    let (value, count, child_degree) = self.convert(child, depth + 1, nodes)?;
                    terms = if product {
                        terms.checked_mul(count)
                    } else {
                        terms.checked_add(count)
                    }
                    .ok_or_else(|| resource("expansion size overflow"))?;
                    degree = if product {
                        degree
                            .checked_add(child_degree)
                            .ok_or_else(|| resource("degree overflow"))?
                    } else {
                        degree.max(child_degree)
                    };
                    if terms > self.limits.terms || degree > self.limits.degree {
                        return Err(resource("polynomial expansion limit exhausted"));
                    }
                    self.charge(terms)?;
                    converted.push(value);
                }
                (
                    if product {
                        CasExpr::Mul(converted)
                    } else {
                        CasExpr::Add(converted)
                    },
                    if self.wide && degree == 0 {
                        1
                    } else {
                        terms.max(1)
                    },
                    degree,
                )
            }
            PolynomialExpr::Neg(child) => {
                let (value, terms, degree) = self.convert(child, depth + 1, nodes)?;
                (CasExpr::Neg(Box::new(value)), terms, degree)
            }
            PolynomialExpr::Pow { base, exponent } => {
                // Charge even powers of constants; a huge exponent cannot bypass
                // the work/degree contract just because its formal degree is zero.
                if *exponent > if self.wide { 512 } else { self.limits.degree } {
                    return Err(resource("power limit exhausted"));
                }
                let (value, terms, degree) = self.convert(base, depth + 1, nodes)?;
                let terms = terms
                    .checked_pow(*exponent)
                    .ok_or_else(|| resource("power expansion overflow"))?;
                let degree = degree
                    .checked_mul(*exponent)
                    .ok_or_else(|| resource("degree overflow"))?;
                self.charge(terms.saturating_mul(u64::from(*exponent).max(1)))?;
                (CasExpr::Pow(Box::new(value), *exponent), terms, degree)
            }
        };
        if terms > self.limits.terms || degree > self.limits.degree {
            return Err(resource("polynomial expansion limit exhausted"));
        }
        Ok((result, terms, degree))
    }
}

impl PolynomialExpr {
    /// Converts an existing CAS expression without losing its admitted syntax.
    ///
    /// # Errors
    /// Declines nonpolynomials, wide coefficients, or policy exhaustion.
    pub fn from_cas(expr: &CasExpr, limits: TraceLimits) -> Result<Self, TraceError> {
        Self::from_cas_mode(expr, limits, false)
    }
    /// Encode version-2 wide rational polynomial syntax with the same local caps.
    ///
    /// # Errors
    /// Nonpolynomial syntax, oversized coefficients or exhausted shape/work policy.
    pub fn from_cas_wide(expr: &CasExpr, limits: TraceLimits) -> Result<Self, TraceError> {
        Self::from_cas_mode(expr, limits, true)
    }
    fn from_cas_mode(expr: &CasExpr, limits: TraceLimits, wide: bool) -> Result<Self, TraceError> {
        fn encode(
            expr: &CasExpr,
            depth: usize,
            limits: TraceLimits,
            nodes: &mut usize,
            wide: bool,
        ) -> Result<PolynomialExpr, TraceError> {
            if depth > limits.depth {
                return Err(resource("expression depth exhausted"));
            }
            *nodes += 1;
            if *nodes > limits.nodes {
                return Err(resource("expression node limit exhausted"));
            }
            match expr {
                CasExpr::Add(xs) | CasExpr::Mul(xs) if xs.len() > limits.nodes => {
                    return Err(resource("expression node limit exhausted"));
                }
                CasExpr::Var(name) if name.is_empty() || name.len() > 128 => {
                    return Err(reject(None, "invalid parameter name"));
                }
                _ => {}
            }
            let mut child = |value: &CasExpr| encode(value, depth + 1, limits, nodes, wide);
            Ok(match expr {
                CasExpr::Const(r) if wide => {
                    let numerator = r.numerator_big();
                    let denominator = r.denominator_big();
                    if numerator.bits().max(denominator.bits())
                        > crate::wide_polynomial::COEFFICIENT_BITS
                    {
                        return Err(resource("wide coefficient bit cap"));
                    }
                    PolynomialExpr::Const {
                        numerator: numerator.to_string(),
                        denominator: denominator.to_string(),
                    }
                }
                CasExpr::Const(r) => PolynomialExpr::Const {
                    numerator: r
                        .checked_numerator()
                        .ok_or_else(|| resource("promoted coefficient outside version 1"))?
                        .to_string(),
                    denominator: r
                        .checked_denominator()
                        .ok_or_else(|| resource("promoted coefficient outside version 1"))?
                        .to_string(),
                },
                CasExpr::Var(name) => PolynomialExpr::Var(name.clone()),
                CasExpr::Add(xs) => {
                    PolynomialExpr::Add(xs.iter().map(child).collect::<Result<_, _>>()?)
                }
                CasExpr::Mul(xs) => {
                    PolynomialExpr::Mul(xs.iter().map(child).collect::<Result<_, _>>()?)
                }
                CasExpr::Neg(x) => PolynomialExpr::Neg(Box::new(child(x)?)),
                CasExpr::Pow(x, exponent) => PolynomialExpr::Pow {
                    base: Box::new(child(x)?),
                    exponent: *exponent,
                },
                CasExpr::Div(..) | CasExpr::Unary(..) => {
                    return Err(TraceError::Unsupported(
                        "domain-dependent/nonpolynomial rewrite".to_owned(),
                    ));
                }
            })
        }
        let limits = limits.policy()?;
        let encoded = encode(expr, 0, limits, &mut 0, wide)?;
        Work {
            wide,
            remaining: limits.work,
            limits,
        }
        .expression(&encoded)?;
        Ok(encoded)
    }
    /// Rebuilds a bounded typed CAS expression from this wire tree.
    ///
    /// # Errors
    /// Invalid coefficients, syntax limits, or polynomial-expansion exhaustion.
    pub fn to_cas(&self, limits: TraceLimits) -> Result<CasExpr, TraceError> {
        self.to_cas_mode(limits, false)
    }
    /// Decode version-2 wide rational polynomial syntax.
    ///
    /// # Errors
    /// Noncanonical coefficients or exceeded local syntax/work/bit bounds.
    pub fn to_cas_wide(&self, limits: TraceLimits) -> Result<CasExpr, TraceError> {
        self.to_cas_mode(limits, true)
    }
    fn to_cas_mode(&self, limits: TraceLimits, wide: bool) -> Result<CasExpr, TraceError> {
        let limits = limits.policy()?;
        Work {
            wide,
            remaining: limits.work,
            limits,
        }
        .expression(self)
    }

    fn children(&self) -> Vec<&Self> {
        match self {
            Self::Add(xs) | Self::Mul(xs) => xs.iter().collect(),
            Self::Neg(x) | Self::Pow { base: x, .. } => vec![x],
            Self::Const { .. } | Self::Var(_) => Vec::new(),
        }
    }
    fn local(&self, path: &[usize]) -> Option<&Self> {
        if let Some((index, rest)) = path.split_first() {
            self.children().get(*index).copied()?.local(rest)
        } else {
            Some(self)
        }
    }
    fn replace(&self, path: &[usize], value: &Self) -> Option<Self> {
        let Some((index, rest)) = path.split_first() else {
            return Some(value.clone());
        };
        let mut copy = self.clone();
        let child = match &mut copy {
            Self::Add(xs) | Self::Mul(xs) => xs.get_mut(*index)?,
            Self::Neg(x) | Self::Pow { base: x, .. } if *index == 0 => x,
            _ => return None,
        };
        *child = child.replace(rest, value)?;
        Some(copy)
    }
    fn rule(&self) -> Option<(&'static str, Option<u32>)> {
        match self {
            Self::Add(_) => Some(("polynomial.add.v1", None)),
            Self::Mul(_) => Some(("polynomial.mul.v1", None)),
            Self::Neg(_) => Some(("polynomial.neg.v1", None)),
            Self::Pow { exponent, .. } => Some(("polynomial.pow.v1", Some(*exponent))),
            Self::Const { .. } | Self::Var(_) => None,
        }
    }
}

/// Produces deterministic postorder local polynomial certificates.
///
/// # Errors
/// Returns no completed certificate for unsupported syntax or exhausted limits.
pub fn normalize_with_trace(
    input: &CasExpr,
    limits: TraceLimits,
) -> Result<RewriteTrace, TraceError> {
    normalize_trace_mode(input, limits, false)
}
/// Produce version-2 local certificates using bounded promoted rational arithmetic.
///
/// # Errors
/// Unsupported syntax or exhausted coefficient, syntax, expansion or work policy.
pub fn normalize_with_trace_wide(
    input: &CasExpr,
    limits: TraceLimits,
) -> Result<RewriteTrace, TraceError> {
    normalize_trace_mode(input, limits, true)
}
fn normalize_trace_mode(
    input: &CasExpr,
    limits: TraceLimits,
    wide: bool,
) -> Result<RewriteTrace, TraceError> {
    fn locations(expr: &PolynomialExpr, path: &mut Vec<usize>, out: &mut Vec<Vec<usize>>) {
        for (index, child) in expr.children().into_iter().enumerate() {
            path.push(index);
            locations(child, path, out);
            path.pop();
        }
        if expr.rule().is_some() {
            out.push(path.clone());
        }
    }
    let limits = limits.policy()?;
    let source = PolynomialExpr::from_cas_mode(input, limits, wide)?;
    let mut paths = Vec::new();
    locations(&source, &mut Vec::new(), &mut paths);
    let mut trace = RewriteTrace {
        version: if wide {
            "cas-polynomial-trace-v2"
        } else {
            "cas-polynomial-trace-v1"
        }
        .to_owned(),
        sort: "rational".to_owned(),
        input: source.clone(),
        result: source.clone(),
        assumptions: Vec::new(),
        limits,
        steps: Vec::new(),
    };
    let mut work = Work {
        wide,
        remaining: limits.work,
        limits,
    };
    for path in paths {
        let local = trace
            .result
            .local(&path)
            .ok_or_else(|| reject(None, "producer location disappeared"))?;
        let (rule, exponent) = local
            .rule()
            .ok_or_else(|| reject(None, "producer operation disappeared"))?;
        let value = work.expression(local)?;
        let normal = work.normal_form(&value)?;
        let witness = PolynomialExpr::from_cas_mode(&normal, limits, wide)?;
        work.expression(&witness)?;
        if *local == witness {
            continue;
        }
        if trace.steps.len() >= limits.steps {
            return Err(resource("step limit exhausted"));
        }
        let after = trace
            .result
            .replace(&path, &witness)
            .ok_or_else(|| reject(None, "producer replacement failed"))?;
        work.expression(&after)?;
        let id = trace.steps.len();
        trace.steps.push(RewriteStep {
            id,
            before: trace.result.clone(),
            after: after.clone(),
            location: path,
            rule: rule.to_owned(),
            exponent,
            premises: id.checked_sub(1).into_iter().collect(),
            context: if wide { "empty-v2" } else { "empty-v1" }.to_owned(),
            side_conditions: Vec::new(),
            witness,
        });
        trace.result = after;
    }
    // A producer cannot return a completed trace that its declared replay or
    // serialized-byte contract cannot support.
    trace.to_json(limits)?;
    Ok(trace)
}

/// Replays the evidence against an independently supplied statement.
///
/// # Errors
/// Distinguishes invalid evidence, unsupported contracts, and exhausted policy.
pub fn check_trace(
    trace: &RewriteTrace,
    input: &PolynomialExpr,
    result: &PolynomialExpr,
    policy: TraceLimits,
) -> Result<(), TraceError> {
    let policy = policy.policy()?;
    let wide = match trace.version.as_str() {
        "cas-polynomial-trace-v1" => false,
        "cas-polynomial-trace-v2" => true,
        _ => return Err(TraceError::Unsupported("trace version".into())),
    };
    if trace.sort != "rational" {
        return Err(TraceError::Unsupported(
            "trace version or scalar sort".to_owned(),
        ));
    }
    if !trace.limits.bounded_by(policy) {
        return Err(resource("untrusted trace exceeds caller policy"));
    }
    if !trace.assumptions.is_empty() {
        return Err(TraceError::Unsupported(
            "nonempty assumption context".to_owned(),
        ));
    }
    let mut work = Work {
        wide,
        remaining: trace.limits.work,
        limits: trace.limits,
    };
    work.expression(input)?;
    work.expression(result)?;
    if trace.input != *input || trace.result != *result {
        return Err(reject(None, "trace does not bind the requested statement"));
    }
    if trace.steps.len() > trace.limits.steps {
        return Err(resource("step limit exhausted"));
    }
    let mut current = input;
    for (index, step) in trace.steps.iter().enumerate() {
        let fail = |reason| reject(Some(index), reason);
        if step.id != index || step.before != *current {
            return Err(fail("step ID or continuity mismatch"));
        }
        if step.premises != index.checked_sub(1).into_iter().collect::<Vec<_>>() {
            return Err(fail("premise binding mismatch"));
        }
        if step.context != if wide { "empty-v2" } else { "empty-v1" }
            || !step.side_conditions.is_empty()
        {
            return Err(fail("step context mismatch"));
        }
        if step.location.len() > trace.limits.depth {
            return Err(resource("location depth exhausted"));
        }
        work.expression_at(&step.before, index)?;
        work.expression_at(&step.after, index)?;
        let local = step
            .before
            .local(&step.location)
            .ok_or_else(|| fail("invalid rewrite location"))?;
        if local.rule() != Some((step.rule.as_str(), step.exponent)) {
            return Err(fail("rule or arguments mismatch"));
        }
        let before = work.expression_at(local, index)?;
        let witness = work.expression_at(&step.witness, index)?;
        let normal = work.normal_form(&before)?;
        let claimed = work.normal_form(&witness)?;
        if normal != claimed
            || PolynomialExpr::from_cas_mode(&normal, trace.limits, wide)? != step.witness
        {
            return Err(fail("local arithmetic witness mismatch"));
        }
        if step.before.replace(&step.location, &step.witness).as_ref() != Some(&step.after) {
            return Err(fail("rewrite changed the surrounding expression"));
        }
        current = &step.after;
    }
    if *current != *result {
        return Err(reject(None, "final endpoint mismatch"));
    }
    Ok(())
}

impl RewriteTrace {
    /// Exports deterministic JSON after checking its complete equality claim.
    ///
    /// # Errors
    /// Invalid evidence, arithmetic/serialization limits, or unsupported scope.
    pub fn to_json(&self, policy: TraceLimits) -> Result<String, TraceError> {
        check_trace(self, &self.input, &self.result, policy)?;
        let text =
            serde_json::to_string(self).map_err(|_| reject(None, "JSON serialization failed"))?;
        if text.len() > policy.bytes.min(self.limits.bytes) {
            return Err(resource("serialized byte limit exhausted"));
        }
        Ok(text)
    }
}

/// Reads bounded JSON and replays it against an external statement.
///
/// # Errors
/// Parsing, binding, arithmetic, scope and local-policy failures are explicit.
pub fn replay_json(
    bytes: &[u8],
    input: &PolynomialExpr,
    result: &PolynomialExpr,
    limits: TraceLimits,
) -> Result<RewriteTrace, TraceError> {
    limits.policy()?;
    if bytes.len() > limits.bytes {
        return Err(resource("serialized byte limit exhausted"));
    }
    let trace: RewriteTrace =
        serde_json::from_slice(bytes).map_err(|_| reject(None, "invalid trace JSON"))?;
    if bytes.len() > trace.limits.bytes {
        return Err(resource("serialized byte limit exhausted"));
    }
    check_trace(&trace, input, result, limits)?;
    Ok(trace)
}
