//! Denotation-preserving canonicalization.
//!
//! The first canonicalizer is deliberately small and exact: every enabled
//! rule preserves term denotation under every assignment, so no model
//! projection is needed.

use std::collections::{BTreeSet, HashMap};

use axeyum_ir::{Assignment, IrError, Op, Sort, TermArena, TermId, TermNode, Value, eval};

use crate::{
    ModelProjection, Preservation, RewriteManifest, RewriteRule, RewriteRuleId, RewriteTestRoute,
};

const BOOL_CONST_FOLD: &str = "bool.const_fold.v1";
const BOOL_DOUBLE_NOT: &str = "bool.double_not.v1";
const BOOL_AND_IDENTITY: &str = "bool.and_identity.v1";
const BOOL_AND_ANNIHILATOR: &str = "bool.and_annihilator.v1";
const BOOL_AND_IDEMPOTENT: &str = "bool.and_idempotent.v1";
const BOOL_OR_IDENTITY: &str = "bool.or_identity.v1";
const BOOL_OR_ANNIHILATOR: &str = "bool.or_annihilator.v1";
const BOOL_OR_IDEMPOTENT: &str = "bool.or_idempotent.v1";
const BOOL_XOR_IDENTITY: &str = "bool.xor_identity.v1";
const BOOL_XOR_SELF: &str = "bool.xor_self.v1";
const BOOL_IMPLIES_CONST: &str = "bool.implies_const.v1";
const BOOL_IMPLIES_REFLEXIVE: &str = "bool.implies_reflexive.v1";
const EQ_REFLEXIVE: &str = "eq.reflexive.v1";
const ITE_CONST_CONDITION: &str = "ite.const_condition.v1";
const ITE_SAME_BRANCHES: &str = "ite.same_branches.v1";
const BV_CONST_FOLD: &str = "bv.const_fold.v1";
const BV_ADD_ZERO: &str = "bv.add_zero.v1";
const BV_SUB_ZERO: &str = "bv.sub_zero.v1";
const BV_SUB_SELF: &str = "bv.sub_self.v1";
const BV_MUL_ONE: &str = "bv.mul_one.v1";
const BV_MUL_ZERO: &str = "bv.mul_zero.v1";
const BV_AND_IDENTITY: &str = "bv.and_identity.v1";
const BV_AND_ZERO: &str = "bv.and_zero.v1";
const BV_AND_IDEMPOTENT: &str = "bv.and_idempotent.v1";
const BV_OR_IDENTITY: &str = "bv.or_identity.v1";
const BV_OR_ONES: &str = "bv.or_ones.v1";
const BV_OR_IDEMPOTENT: &str = "bv.or_idempotent.v1";
const BV_XOR_IDENTITY: &str = "bv.xor_identity.v1";
const BV_XOR_SELF: &str = "bv.xor_self.v1";
const BV_SHIFT_ZERO: &str = "bv.shift_zero.v1";
const BV_EXTRACT_WHOLE: &str = "bv.extract_whole.v1";
const BV_EXTEND_ZERO: &str = "bv.extend_zero.v1";
const BV_ROTATE_ZERO: &str = "bv.rotate_zero.v1";

/// A canonicalizer configured by a validated rewrite manifest.
#[derive(Debug, Clone)]
pub struct Canonicalizer {
    manifest: RewriteManifest,
}

impl Canonicalizer {
    /// Creates a canonicalizer from a checked manifest.
    pub fn new(manifest: RewriteManifest) -> Self {
        Self { manifest }
    }

    /// Returns the manifest governing this canonicalizer.
    pub fn manifest(&self) -> &RewriteManifest {
        &self.manifest
    }

    /// Canonicalizes one root term in place, appending any rewritten terms to
    /// the same arena.
    ///
    /// # Errors
    ///
    /// Returns [`RewriteError::Ir`] if rebuilding a term violates an IR
    /// invariant. For terms built by [`TermArena`], that indicates arena
    /// corruption or cross-arena `TermId` misuse.
    pub fn canonicalize(
        &self,
        arena: &mut TermArena,
        root: TermId,
    ) -> Result<CanonicalizeOutcome, RewriteError> {
        let outcome = self.canonicalize_terms(arena, &[root])?;
        Ok(CanonicalizeOutcome {
            term: outcome.terms[0],
            report: outcome.report,
        })
    }

    /// Canonicalizes multiple roots with one memo table so shared subterms are
    /// rewritten once.
    ///
    /// # Errors
    ///
    /// Returns [`RewriteError::Ir`] on the same conditions as
    /// [`Canonicalizer::canonicalize`].
    pub fn canonicalize_terms(
        &self,
        arena: &mut TermArena,
        roots: &[TermId],
    ) -> Result<CanonicalizeTermsOutcome, RewriteError> {
        let enabled = self.enabled_rule_set();
        let mut memo = HashMap::new();
        let mut report = RewriteReport::default();
        let mut terms = Vec::with_capacity(roots.len());

        for &root in roots {
            let term = canonicalize_root(arena, root, &enabled, &mut memo, &mut report)?;
            terms.push(term);
        }

        Ok(CanonicalizeTermsOutcome { terms, report })
    }

    fn enabled_rule_set(&self) -> BTreeSet<&str> {
        self.manifest
            .enabled_rules()
            .map(|rule| rule.id.as_str())
            .collect()
    }
}

impl Default for Canonicalizer {
    fn default() -> Self {
        Self::new(default_manifest())
    }
}

/// Result of canonicalizing one root term.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CanonicalizeOutcome {
    /// Canonical root term.
    pub term: TermId,
    /// Rule applications performed while producing `term`.
    pub report: RewriteReport,
}

impl CanonicalizeOutcome {
    /// Returns `true` if at least one rewrite rule fired.
    pub fn changed(&self) -> bool {
        self.report.changed()
    }
}

/// Result of canonicalizing multiple roots.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CanonicalizeTermsOutcome {
    /// Canonical root terms, in input order.
    pub terms: Vec<TermId>,
    /// Rule applications performed while producing `terms`.
    pub report: RewriteReport,
}

impl CanonicalizeTermsOutcome {
    /// Returns `true` if at least one rewrite rule fired.
    pub fn changed(&self) -> bool {
        self.report.changed()
    }
}

/// Rule-application trace for a canonicalization pass.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct RewriteReport {
    applications: Vec<RuleApplication>,
}

impl RewriteReport {
    /// Returns all rule applications in deterministic traversal order.
    pub fn applications(&self) -> &[RuleApplication] {
        &self.applications
    }

    /// Returns `true` if at least one rewrite rule fired.
    pub fn changed(&self) -> bool {
        !self.applications.is_empty()
    }

    fn record(&mut self, rule_id: &'static str, before: TermId, after: TermId) {
        self.applications.push(RuleApplication {
            rule_id: rewrite_id(rule_id),
            before,
            after,
        });
    }
}

/// One local rule application.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuleApplication {
    /// Stable rewrite rule ID.
    pub rule_id: RewriteRuleId,
    /// Term being rewritten.
    pub before: TermId,
    /// Replacement term.
    pub after: TermId,
}

/// Errors from canonicalization.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RewriteError {
    /// Term construction or evaluation failed while rebuilding a well-typed
    /// term.
    Ir(IrError),
}

impl From<IrError> for RewriteError {
    fn from(error: IrError) -> Self {
        Self::Ir(error)
    }
}

impl core::fmt::Display for RewriteError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            RewriteError::Ir(error) => write!(f, "IR error during rewrite: {error}"),
        }
    }
}

impl core::error::Error for RewriteError {}

/// Canonicalizes one term using the default denotation-preserving rule set.
///
/// # Errors
///
/// Returns [`RewriteError::Ir`] if rebuilding a term fails.
pub fn canonicalize(
    arena: &mut TermArena,
    root: TermId,
) -> Result<CanonicalizeOutcome, RewriteError> {
    Canonicalizer::default().canonicalize(arena, root)
}

/// Canonicalizes multiple terms using the default denotation-preserving rule
/// set.
///
/// # Errors
///
/// Returns [`RewriteError::Ir`] if rebuilding a term fails.
pub fn canonicalize_terms(
    arena: &mut TermArena,
    roots: &[TermId],
) -> Result<CanonicalizeTermsOutcome, RewriteError> {
    Canonicalizer::default().canonicalize_terms(arena, roots)
}

/// Returns the default Phase 3 rewrite manifest.
///
/// All rules in this manifest are exact-denotation rules with identity model
/// projection.
///
/// # Panics
///
/// Panics only if the statically declared default rule table violates the
/// manifest contract.
pub fn default_manifest() -> RewriteManifest {
    RewriteManifest::new(default_rules()).expect("default rewrite manifest is valid")
}

#[allow(clippy::too_many_lines)]
fn default_rules() -> Vec<RewriteRule> {
    vec![
        rule(
            BOOL_CONST_FOLD,
            "Boolean constant fold",
            "all operands are Boolean constants and the result sort is Bool",
        ),
        rule(
            BOOL_DOUBLE_NOT,
            "Double Boolean negation",
            "`not` applied to a `not` term",
        ),
        rule(
            BOOL_AND_IDENTITY,
            "Boolean and identity",
            "`and` with one operand equal to true",
        ),
        rule(
            BOOL_AND_ANNIHILATOR,
            "Boolean and annihilator",
            "`and` with one operand equal to false",
        ),
        rule(
            BOOL_AND_IDEMPOTENT,
            "Boolean and idempotence",
            "`and` with structurally identical operands",
        ),
        rule(
            BOOL_OR_IDENTITY,
            "Boolean or identity",
            "`or` with one operand equal to false",
        ),
        rule(
            BOOL_OR_ANNIHILATOR,
            "Boolean or annihilator",
            "`or` with one operand equal to true",
        ),
        rule(
            BOOL_OR_IDEMPOTENT,
            "Boolean or idempotence",
            "`or` with structurally identical operands",
        ),
        rule(
            BOOL_XOR_IDENTITY,
            "Boolean xor identity",
            "`xor` with one operand equal to false",
        ),
        rule(
            BOOL_XOR_SELF,
            "Boolean xor self-cancellation",
            "`xor` with structurally identical operands",
        ),
        rule(
            BOOL_IMPLIES_CONST,
            "Boolean implication constant identities",
            "`=>` with a constant antecedent or consequent",
        ),
        rule(
            BOOL_IMPLIES_REFLEXIVE,
            "Boolean implication reflexivity",
            "`=>` with structurally identical operands",
        ),
        rule(
            EQ_REFLEXIVE,
            "Equality reflexivity",
            "`=` with structurally identical operands",
        ),
        rule(
            ITE_CONST_CONDITION,
            "If-then-else constant condition",
            "`ite` with a constant Boolean condition",
        ),
        rule(
            ITE_SAME_BRANCHES,
            "If-then-else same branches",
            "`ite` with structurally identical branches",
        ),
        rule(
            BV_CONST_FOLD,
            "Bit-vector constant fold",
            "all operands are constants and the result sort is a bit-vector",
        ),
        rule(
            BV_ADD_ZERO,
            "Bit-vector addition identity",
            "`bvadd` with one operand equal to zero",
        ),
        rule(
            BV_SUB_ZERO,
            "Bit-vector subtraction identity",
            "`bvsub` with the right operand equal to zero",
        ),
        rule(
            BV_SUB_SELF,
            "Bit-vector subtraction self-cancellation",
            "`bvsub` with structurally identical operands",
        ),
        rule(
            BV_MUL_ONE,
            "Bit-vector multiplication identity",
            "`bvmul` with one operand equal to one",
        ),
        rule(
            BV_MUL_ZERO,
            "Bit-vector multiplication zero",
            "`bvmul` with one operand equal to zero",
        ),
        rule(
            BV_AND_IDENTITY,
            "Bit-vector and all-ones identity",
            "`bvand` with one operand equal to all ones",
        ),
        rule(
            BV_AND_ZERO,
            "Bit-vector and zero",
            "`bvand` with one operand equal to zero",
        ),
        rule(
            BV_AND_IDEMPOTENT,
            "Bit-vector and idempotence",
            "`bvand` with structurally identical operands",
        ),
        rule(
            BV_OR_IDENTITY,
            "Bit-vector or zero identity",
            "`bvor` with one operand equal to zero",
        ),
        rule(
            BV_OR_ONES,
            "Bit-vector or all-ones",
            "`bvor` with one operand equal to all ones",
        ),
        rule(
            BV_OR_IDEMPOTENT,
            "Bit-vector or idempotence",
            "`bvor` with structurally identical operands",
        ),
        rule(
            BV_XOR_IDENTITY,
            "Bit-vector xor zero identity",
            "`bvxor` with one operand equal to zero",
        ),
        rule(
            BV_XOR_SELF,
            "Bit-vector xor self-cancellation",
            "`bvxor` with structurally identical operands",
        ),
        rule(
            BV_SHIFT_ZERO,
            "Bit-vector shift-by-zero identity",
            "`bvshl`, `bvlshr`, or `bvashr` with a zero shift amount",
        ),
        rule(
            BV_EXTRACT_WHOLE,
            "Bit-vector whole extract identity",
            "`extract` over the full input width",
        ),
        rule(
            BV_EXTEND_ZERO,
            "Bit-vector zero-width extension identity",
            "`zero_extend` or `sign_extend` by zero bits",
        ),
        rule(
            BV_ROTATE_ZERO,
            "Bit-vector rotate-by-zero identity",
            "`rotate_left` or `rotate_right` by zero bits",
        ),
    ]
}

fn rule(id: &str, name: &str, precondition: &str) -> RewriteRule {
    RewriteRule {
        id: RewriteRuleId::new(id).expect("static rewrite rule ID is valid"),
        name: name.to_owned(),
        precondition: precondition.to_owned(),
        preservation: Preservation::Denotation,
        projection: ModelProjection::Identity,
        tests: vec![
            RewriteTestRoute::ExhaustiveSmallWidth,
            RewriteTestRoute::OracleDifferential,
        ],
        enabled_by_default: true,
    }
}

fn rewrite_id(id: &str) -> RewriteRuleId {
    RewriteRuleId::new(id).expect("static rewrite rule ID is valid")
}

fn canonicalize_root(
    arena: &mut TermArena,
    root: TermId,
    enabled: &BTreeSet<&str>,
    memo: &mut HashMap<TermId, TermId>,
    report: &mut RewriteReport,
) -> Result<TermId, RewriteError> {
    let mut stack = vec![(root, false)];

    while let Some((term, children_ready)) = stack.pop() {
        if memo.contains_key(&term) {
            continue;
        }

        let node = arena.node(term).clone();
        match node {
            TermNode::BoolConst(_)
            | TermNode::BvConst { .. }
            | TermNode::IntConst(_)
            | TermNode::RealConst(_)
            | TermNode::Symbol(_) => {
                memo.insert(term, term);
            }
            TermNode::App { op, args } if children_ready => {
                let rewritten_args = args.iter().map(|arg| memo[arg]).collect::<Vec<_>>();
                let application = rewrite_app(arena, op, &rewritten_args, enabled)?;
                let rewritten = application.term;
                if let Some(rule_id) = application.rule_id {
                    report.record(rule_id, term, rewritten);
                }
                memo.insert(term, rewritten);
            }
            TermNode::App { args, .. } => {
                stack.push((term, true));
                for &arg in args.iter().rev() {
                    stack.push((arg, false));
                }
            }
        }
    }

    Ok(memo[&root])
}

struct LocalRewrite {
    term: TermId,
    rule_id: Option<&'static str>,
}

#[allow(clippy::too_many_lines)]
fn rewrite_app(
    arena: &mut TermArena,
    op: Op,
    args: &[TermId],
    enabled: &BTreeSet<&str>,
) -> Result<LocalRewrite, IrError> {
    if all_constant(arena, args) {
        let rebuilt = build_app(arena, op, args)?;
        let folded = value_to_term(arena, eval(arena, rebuilt, &Assignment::new())?)?;
        let rule_id = match arena.sort_of(folded) {
            Sort::Bool => BOOL_CONST_FOLD,
            // `all_constant` matches only Bool/BV constants, so a folded term is
            // only ever Bool/BV here; the array and integer arms are unreachable.
            Sort::BitVec(_) | Sort::Array { .. } | Sort::Int | Sort::Real | Sort::Datatype(_) => {
                BV_CONST_FOLD
            }
        };
        if enabled.contains(rule_id) {
            return Ok(applied(folded, rule_id));
        }
    }

    let local = match op {
        Op::BoolNot => rewrite_bool_not(arena, args, enabled),
        Op::BoolAnd => rewrite_bool_and(arena, args, enabled),
        Op::BoolOr => rewrite_bool_or(arena, args, enabled),
        Op::BoolXor => rewrite_bool_xor(arena, args, enabled),
        Op::BoolImplies => rewrite_bool_implies(arena, args, enabled)?,
        Op::BvAdd => rewrite_bv_add(arena, args, enabled),
        Op::BvSub => rewrite_bv_sub(arena, args, enabled)?,
        Op::BvMul => rewrite_bv_mul(arena, args, enabled)?,
        Op::BvAnd => rewrite_bv_and(arena, args, enabled),
        Op::BvOr => rewrite_bv_or(arena, args, enabled),
        Op::BvXor => rewrite_bv_xor(arena, args, enabled)?,
        Op::BvShl | Op::BvLshr | Op::BvAshr => rewrite_bv_shift(arena, args, enabled),
        Op::Eq => rewrite_eq(arena, args, enabled),
        Op::Ite => rewrite_ite(arena, args, enabled),
        Op::Extract { hi, lo } => rewrite_extract(arena, hi, lo, args, enabled),
        Op::ZeroExt { by } | Op::SignExt { by } => rewrite_extend(by, args, enabled),
        Op::RotateLeft { by } | Op::RotateRight { by } => rewrite_rotate(by, args, enabled),
        Op::BvNot
        | Op::BvNand
        | Op::BvNor
        | Op::BvXnor
        | Op::BvNeg
        | Op::BvUdiv
        | Op::BvUrem
        | Op::BvSdiv
        | Op::BvSrem
        | Op::BvSmod
        | Op::BvUlt
        | Op::BvUle
        | Op::BvUgt
        | Op::BvUge
        | Op::BvSlt
        | Op::BvSle
        | Op::BvSgt
        | Op::BvSge
        | Op::BvComp
        | Op::Concat
        | Op::Select
        | Op::Store
        | Op::ConstArray { .. }
        | Op::Bv2Nat
        | Op::Int2Bv { .. }
        | Op::Apply(_)
        | Op::IntNeg
        | Op::IntAdd
        | Op::IntSub
        | Op::IntMul
        | Op::IntDiv
        | Op::IntMod
        | Op::IntAbs
        | Op::IntLt
        | Op::IntLe
        | Op::IntGt
        | Op::IntGe
        | Op::RealNeg
        | Op::RealAdd
        | Op::RealSub
        | Op::RealMul
        | Op::RealDiv
        | Op::RealLt
        | Op::RealLe
        | Op::RealGt
        | Op::RealGe
        | Op::Forall(_)
        | Op::Exists(_)
        | Op::DtConstruct { .. }
        | Op::DtSelect { .. }
        | Op::DtTest(_) => None,
    };

    if let Some(local) = local {
        return Ok(local);
    }

    Ok(LocalRewrite {
        term: build_app(arena, op, args)?,
        rule_id: None,
    })
}

fn rewrite_bool_not(
    arena: &mut TermArena,
    args: &[TermId],
    enabled: &BTreeSet<&str>,
) -> Option<LocalRewrite> {
    if enabled.contains(BOOL_DOUBLE_NOT)
        && let TermNode::App {
            op: Op::BoolNot,
            args: inner,
        } = arena.node(args[0])
    {
        return Some(applied(inner[0], BOOL_DOUBLE_NOT));
    }
    None
}

fn rewrite_bool_and(
    arena: &mut TermArena,
    args: &[TermId],
    enabled: &BTreeSet<&str>,
) -> Option<LocalRewrite> {
    let [a, b] = [args[0], args[1]];
    if enabled.contains(BOOL_AND_ANNIHILATOR) {
        if is_bool(arena, a, false) {
            return Some(applied(a, BOOL_AND_ANNIHILATOR));
        }
        if is_bool(arena, b, false) {
            return Some(applied(b, BOOL_AND_ANNIHILATOR));
        }
    }
    if enabled.contains(BOOL_AND_IDENTITY) {
        if is_bool(arena, a, true) {
            return Some(applied(b, BOOL_AND_IDENTITY));
        }
        if is_bool(arena, b, true) {
            return Some(applied(a, BOOL_AND_IDENTITY));
        }
    }
    if enabled.contains(BOOL_AND_IDEMPOTENT) && a == b {
        return Some(applied(a, BOOL_AND_IDEMPOTENT));
    }
    None
}

fn rewrite_bool_or(
    arena: &mut TermArena,
    args: &[TermId],
    enabled: &BTreeSet<&str>,
) -> Option<LocalRewrite> {
    let [a, b] = [args[0], args[1]];
    if enabled.contains(BOOL_OR_ANNIHILATOR) {
        if is_bool(arena, a, true) {
            return Some(applied(a, BOOL_OR_ANNIHILATOR));
        }
        if is_bool(arena, b, true) {
            return Some(applied(b, BOOL_OR_ANNIHILATOR));
        }
    }
    if enabled.contains(BOOL_OR_IDENTITY) {
        if is_bool(arena, a, false) {
            return Some(applied(b, BOOL_OR_IDENTITY));
        }
        if is_bool(arena, b, false) {
            return Some(applied(a, BOOL_OR_IDENTITY));
        }
    }
    if enabled.contains(BOOL_OR_IDEMPOTENT) && a == b {
        return Some(applied(a, BOOL_OR_IDEMPOTENT));
    }
    None
}

fn rewrite_bool_xor(
    arena: &mut TermArena,
    args: &[TermId],
    enabled: &BTreeSet<&str>,
) -> Option<LocalRewrite> {
    let [a, b] = [args[0], args[1]];
    if enabled.contains(BOOL_XOR_IDENTITY) {
        if is_bool(arena, a, false) {
            return Some(applied(b, BOOL_XOR_IDENTITY));
        }
        if is_bool(arena, b, false) {
            return Some(applied(a, BOOL_XOR_IDENTITY));
        }
    }
    if enabled.contains(BOOL_XOR_SELF) && a == b {
        return Some(applied(arena.bool_const(false), BOOL_XOR_SELF));
    }
    None
}

fn rewrite_bool_implies(
    arena: &mut TermArena,
    args: &[TermId],
    enabled: &BTreeSet<&str>,
) -> Result<Option<LocalRewrite>, IrError> {
    let [a, b] = [args[0], args[1]];
    if enabled.contains(BOOL_IMPLIES_CONST) {
        if is_bool(arena, a, false) || is_bool(arena, b, true) {
            return Ok(Some(applied(arena.bool_const(true), BOOL_IMPLIES_CONST)));
        }
        if is_bool(arena, a, true) {
            return Ok(Some(applied(b, BOOL_IMPLIES_CONST)));
        }
        if is_bool(arena, b, false) {
            return Ok(Some(applied(arena.not(a)?, BOOL_IMPLIES_CONST)));
        }
    }
    if enabled.contains(BOOL_IMPLIES_REFLEXIVE) && a == b {
        return Ok(Some(applied(
            arena.bool_const(true),
            BOOL_IMPLIES_REFLEXIVE,
        )));
    }
    Ok(None)
}

fn rewrite_bv_add(
    arena: &TermArena,
    args: &[TermId],
    enabled: &BTreeSet<&str>,
) -> Option<LocalRewrite> {
    let [a, b] = [args[0], args[1]];
    if enabled.contains(BV_ADD_ZERO) {
        if is_bv_zero(arena, a) {
            return Some(applied(b, BV_ADD_ZERO));
        }
        if is_bv_zero(arena, b) {
            return Some(applied(a, BV_ADD_ZERO));
        }
    }
    None
}

fn rewrite_bv_sub(
    arena: &mut TermArena,
    args: &[TermId],
    enabled: &BTreeSet<&str>,
) -> Result<Option<LocalRewrite>, IrError> {
    let [a, b] = [args[0], args[1]];
    if enabled.contains(BV_SUB_ZERO) && is_bv_zero(arena, b) {
        return Ok(Some(applied(a, BV_SUB_ZERO)));
    }
    if enabled.contains(BV_SUB_SELF) && a == b {
        let width = arena
            .sort_of(a)
            .bv_width()
            .expect("bvsub operands have BV sort");
        return Ok(Some(applied(arena.bv_const(width, 0)?, BV_SUB_SELF)));
    }
    Ok(None)
}

fn rewrite_bv_mul(
    arena: &mut TermArena,
    args: &[TermId],
    enabled: &BTreeSet<&str>,
) -> Result<Option<LocalRewrite>, IrError> {
    let [a, b] = [args[0], args[1]];
    if enabled.contains(BV_MUL_ZERO) {
        if let Some((width, 0)) = bv_const(arena, a) {
            return Ok(Some(applied(arena.bv_const(width, 0)?, BV_MUL_ZERO)));
        }
        if let Some((width, 0)) = bv_const(arena, b) {
            return Ok(Some(applied(arena.bv_const(width, 0)?, BV_MUL_ZERO)));
        }
    }
    if enabled.contains(BV_MUL_ONE) {
        if is_bv_one(arena, a) {
            return Ok(Some(applied(b, BV_MUL_ONE)));
        }
        if is_bv_one(arena, b) {
            return Ok(Some(applied(a, BV_MUL_ONE)));
        }
    }
    Ok(None)
}

fn rewrite_bv_and(
    arena: &TermArena,
    args: &[TermId],
    enabled: &BTreeSet<&str>,
) -> Option<LocalRewrite> {
    let [a, b] = [args[0], args[1]];
    if enabled.contains(BV_AND_ZERO) {
        if is_bv_zero(arena, a) {
            return Some(applied(a, BV_AND_ZERO));
        }
        if is_bv_zero(arena, b) {
            return Some(applied(b, BV_AND_ZERO));
        }
    }
    if enabled.contains(BV_AND_IDENTITY) {
        if is_bv_ones(arena, a) {
            return Some(applied(b, BV_AND_IDENTITY));
        }
        if is_bv_ones(arena, b) {
            return Some(applied(a, BV_AND_IDENTITY));
        }
    }
    if enabled.contains(BV_AND_IDEMPOTENT) && a == b {
        return Some(applied(a, BV_AND_IDEMPOTENT));
    }
    None
}

fn rewrite_bv_or(
    arena: &TermArena,
    args: &[TermId],
    enabled: &BTreeSet<&str>,
) -> Option<LocalRewrite> {
    let [a, b] = [args[0], args[1]];
    if enabled.contains(BV_OR_ONES) {
        if is_bv_ones(arena, a) {
            return Some(applied(a, BV_OR_ONES));
        }
        if is_bv_ones(arena, b) {
            return Some(applied(b, BV_OR_ONES));
        }
    }
    if enabled.contains(BV_OR_IDENTITY) {
        if is_bv_zero(arena, a) {
            return Some(applied(b, BV_OR_IDENTITY));
        }
        if is_bv_zero(arena, b) {
            return Some(applied(a, BV_OR_IDENTITY));
        }
    }
    if enabled.contains(BV_OR_IDEMPOTENT) && a == b {
        return Some(applied(a, BV_OR_IDEMPOTENT));
    }
    None
}

fn rewrite_bv_xor(
    arena: &mut TermArena,
    args: &[TermId],
    enabled: &BTreeSet<&str>,
) -> Result<Option<LocalRewrite>, IrError> {
    let [a, b] = [args[0], args[1]];
    if enabled.contains(BV_XOR_IDENTITY) {
        if is_bv_zero(arena, a) {
            return Ok(Some(applied(b, BV_XOR_IDENTITY)));
        }
        if is_bv_zero(arena, b) {
            return Ok(Some(applied(a, BV_XOR_IDENTITY)));
        }
    }
    if enabled.contains(BV_XOR_SELF) && a == b {
        let width = arena
            .sort_of(a)
            .bv_width()
            .expect("bvxor operands have BV sort");
        return Ok(Some(applied(arena.bv_const(width, 0)?, BV_XOR_SELF)));
    }
    Ok(None)
}

fn rewrite_bv_shift(
    arena: &TermArena,
    args: &[TermId],
    enabled: &BTreeSet<&str>,
) -> Option<LocalRewrite> {
    if enabled.contains(BV_SHIFT_ZERO) && is_bv_zero(arena, args[1]) {
        return Some(applied(args[0], BV_SHIFT_ZERO));
    }
    None
}

fn rewrite_eq(
    arena: &mut TermArena,
    args: &[TermId],
    enabled: &BTreeSet<&str>,
) -> Option<LocalRewrite> {
    if enabled.contains(EQ_REFLEXIVE) && args[0] == args[1] {
        return Some(applied(arena.bool_const(true), EQ_REFLEXIVE));
    }
    None
}

fn rewrite_ite(
    arena: &TermArena,
    args: &[TermId],
    enabled: &BTreeSet<&str>,
) -> Option<LocalRewrite> {
    if enabled.contains(ITE_CONST_CONDITION)
        && let Some(condition) = bool_const(arena, args[0])
    {
        return Some(applied(
            if condition { args[1] } else { args[2] },
            ITE_CONST_CONDITION,
        ));
    }
    if enabled.contains(ITE_SAME_BRANCHES) && args[1] == args[2] {
        return Some(applied(args[1], ITE_SAME_BRANCHES));
    }
    None
}

fn rewrite_extract(
    arena: &TermArena,
    hi: u32,
    lo: u32,
    args: &[TermId],
    enabled: &BTreeSet<&str>,
) -> Option<LocalRewrite> {
    if enabled.contains(BV_EXTRACT_WHOLE)
        && lo == 0
        && arena.sort_of(args[0]).bv_width() == Some(hi + 1)
    {
        return Some(applied(args[0], BV_EXTRACT_WHOLE));
    }
    None
}

fn rewrite_extend(by: u32, args: &[TermId], enabled: &BTreeSet<&str>) -> Option<LocalRewrite> {
    if enabled.contains(BV_EXTEND_ZERO) && by == 0 {
        return Some(applied(args[0], BV_EXTEND_ZERO));
    }
    None
}

fn rewrite_rotate(by: u32, args: &[TermId], enabled: &BTreeSet<&str>) -> Option<LocalRewrite> {
    if enabled.contains(BV_ROTATE_ZERO) && by == 0 {
        return Some(applied(args[0], BV_ROTATE_ZERO));
    }
    None
}

pub(crate) fn build_app(arena: &mut TermArena, op: Op, args: &[TermId]) -> Result<TermId, IrError> {
    match op {
        Op::BoolNot => arena.not(args[0]),
        Op::BoolAnd => arena.and(args[0], args[1]),
        Op::BoolOr => arena.or(args[0], args[1]),
        Op::BoolXor => arena.xor(args[0], args[1]),
        Op::BoolImplies => arena.implies(args[0], args[1]),
        Op::BvNot => arena.bv_not(args[0]),
        Op::BvAnd => arena.bv_and(args[0], args[1]),
        Op::BvOr => arena.bv_or(args[0], args[1]),
        Op::BvXor => arena.bv_xor(args[0], args[1]),
        Op::BvNand => arena.bv_nand(args[0], args[1]),
        Op::BvNor => arena.bv_nor(args[0], args[1]),
        Op::BvXnor => arena.bv_xnor(args[0], args[1]),
        Op::BvNeg => arena.bv_neg(args[0]),
        Op::BvAdd => arena.bv_add(args[0], args[1]),
        Op::BvSub => arena.bv_sub(args[0], args[1]),
        Op::BvMul => arena.bv_mul(args[0], args[1]),
        Op::BvUdiv => arena.bv_udiv(args[0], args[1]),
        Op::BvUrem => arena.bv_urem(args[0], args[1]),
        Op::BvSdiv => arena.bv_sdiv(args[0], args[1]),
        Op::BvSrem => arena.bv_srem(args[0], args[1]),
        Op::BvSmod => arena.bv_smod(args[0], args[1]),
        Op::BvShl => arena.bv_shl(args[0], args[1]),
        Op::BvLshr => arena.bv_lshr(args[0], args[1]),
        Op::BvAshr => arena.bv_ashr(args[0], args[1]),
        Op::BvUlt => arena.bv_ult(args[0], args[1]),
        Op::BvUle => arena.bv_ule(args[0], args[1]),
        Op::BvUgt => arena.bv_ugt(args[0], args[1]),
        Op::BvUge => arena.bv_uge(args[0], args[1]),
        Op::BvSlt => arena.bv_slt(args[0], args[1]),
        Op::BvSle => arena.bv_sle(args[0], args[1]),
        Op::BvSgt => arena.bv_sgt(args[0], args[1]),
        Op::BvSge => arena.bv_sge(args[0], args[1]),
        Op::Eq => arena.eq(args[0], args[1]),
        Op::Ite => arena.ite(args[0], args[1], args[2]),
        Op::BvComp => arena.bv_comp(args[0], args[1]),
        Op::Extract { hi, lo } => arena.extract(hi, lo, args[0]),
        Op::Concat => arena.concat(args[0], args[1]),
        Op::ZeroExt { by } => arena.zero_ext(by, args[0]),
        Op::SignExt { by } => arena.sign_ext(by, args[0]),
        Op::RotateLeft { by } => arena.rotate_left(by, args[0]),
        Op::RotateRight { by } => arena.rotate_right(by, args[0]),
        Op::Select => arena.select(args[0], args[1]),
        Op::Store => arena.store(args[0], args[1], args[2]),
        Op::ConstArray { index } => arena.const_array(index, args[0]),
        Op::Bv2Nat => arena.bv2nat(args[0]),
        Op::Int2Bv { width } => arena.int2bv(width, args[0]),
        Op::Apply(func) => arena.apply(func, args),
        Op::IntNeg => arena.int_neg(args[0]),
        Op::IntAdd => arena.int_add(args[0], args[1]),
        Op::IntSub => arena.int_sub(args[0], args[1]),
        Op::IntMul => arena.int_mul(args[0], args[1]),
        Op::IntDiv => arena.int_div(args[0], args[1]),
        Op::IntMod => arena.int_mod(args[0], args[1]),
        Op::IntAbs => arena.int_abs(args[0]),
        Op::IntLt => arena.int_lt(args[0], args[1]),
        Op::IntLe => arena.int_le(args[0], args[1]),
        Op::IntGt => arena.int_gt(args[0], args[1]),
        Op::IntGe => arena.int_ge(args[0], args[1]),
        Op::RealNeg => arena.real_neg(args[0]),
        Op::RealAdd => arena.real_add(args[0], args[1]),
        Op::RealSub => arena.real_sub(args[0], args[1]),
        Op::RealMul => arena.real_mul(args[0], args[1]),
        Op::RealDiv => arena.real_div(args[0], args[1]),
        Op::RealLt => arena.real_lt(args[0], args[1]),
        Op::RealLe => arena.real_le(args[0], args[1]),
        Op::RealGt => arena.real_gt(args[0], args[1]),
        Op::RealGe => arena.real_ge(args[0], args[1]),
        Op::Forall(var) => arena.forall(var, args[0]),
        Op::Exists(var) => arena.exists(var, args[0]),
        Op::DtConstruct { constructor, .. } => arena.construct(constructor, args),
        Op::DtSelect { constructor, index } => arena.dt_select(constructor, index, args[0]),
        Op::DtTest(constructor) => arena.dt_test(constructor, args[0]),
    }
}

/// Rebuilds `term`, replacing any subterm that is a key in `replacements` with
/// its mapped value.
///
/// A match is replaced **non-recursively** (the replacement value is returned
/// as-is, not itself rewritten), so a caller can map subterms to fresh variables
/// — e.g. abstracting expensive operators for a low-memory solving strategy —
/// and rebuild any constraints over those variables separately. `memo` shares
/// work across the DAG and across calls under the *same* `replacements` map;
/// pass a fresh `memo` when `replacements` changes.
///
/// # Errors
///
/// Returns [`IrError`] from the IR builders; for a faithful rebuild of
/// well-sorted input this cannot occur.
// The maps are keyed by `TermId` (a small `Copy` id); the default hasher is the
// intended use, so the standard `HashMap` types are part of the signature.
#[allow(clippy::implicit_hasher)]
pub fn replace_subterms(
    arena: &mut TermArena,
    term: TermId,
    replacements: &HashMap<TermId, TermId>,
    memo: &mut HashMap<TermId, TermId>,
) -> Result<TermId, IrError> {
    if let Some(&mapped) = replacements.get(&term) {
        return Ok(mapped);
    }
    if let Some(&cached) = memo.get(&term) {
        return Ok(cached);
    }
    let node = arena.node(term).clone();
    let result = match node {
        TermNode::BoolConst(_)
        | TermNode::BvConst { .. }
        | TermNode::IntConst(_)
        | TermNode::RealConst(_)
        | TermNode::Symbol(_) => term,
        TermNode::App { op, args } => {
            let mut new_args = Vec::with_capacity(args.len());
            for &arg in &args {
                new_args.push(replace_subterms(arena, arg, replacements, memo)?);
            }
            build_app(arena, op, &new_args)?
        }
    };
    memo.insert(term, result);
    Ok(result)
}

fn applied(term: TermId, rule_id: &'static str) -> LocalRewrite {
    LocalRewrite {
        term,
        rule_id: Some(rule_id),
    }
}

fn all_constant(arena: &TermArena, args: &[TermId]) -> bool {
    args.iter().all(|&arg| {
        matches!(
            arena.node(arg),
            TermNode::BoolConst(_) | TermNode::BvConst { .. }
        )
    })
}

fn value_to_term(arena: &mut TermArena, value: Value) -> Result<TermId, IrError> {
    match value {
        Value::Bool(value) => Ok(arena.bool_const(value)),
        Value::Bv { width, value } => arena.bv_const(width, value),
        Value::Datatype { datatype, .. } => Err(IrError::SortMismatch {
            expected: "Bool or BitVec",
            found: Sort::Datatype(datatype),
        }),
        Value::Array(array) => Err(IrError::SortMismatch {
            expected: "Bool or BitVec",
            found: Sort::Array {
                index: array.index_width(),
                element: array.element_width(),
            },
        }),
        Value::Int(value) => Ok(arena.int_const(value)),
        Value::Real(value) => Ok(arena.real_const(value)),
    }
}

fn bool_const(arena: &TermArena, term: TermId) -> Option<bool> {
    match arena.node(term) {
        TermNode::BoolConst(value) => Some(*value),
        TermNode::BvConst { .. }
        | TermNode::IntConst(_)
        | TermNode::RealConst(_)
        | TermNode::Symbol(_)
        | TermNode::App { .. } => None,
    }
}

fn is_bool(arena: &TermArena, term: TermId, expected: bool) -> bool {
    bool_const(arena, term) == Some(expected)
}

fn bv_const(arena: &TermArena, term: TermId) -> Option<(u32, u128)> {
    match arena.node(term) {
        TermNode::BvConst { width, value } => Some((*width, *value)),
        TermNode::BoolConst(_)
        | TermNode::IntConst(_)
        | TermNode::RealConst(_)
        | TermNode::Symbol(_)
        | TermNode::App { .. } => None,
    }
}

fn is_bv_zero(arena: &TermArena, term: TermId) -> bool {
    bv_const(arena, term).is_some_and(|(_, value)| value == 0)
}

fn is_bv_one(arena: &TermArena, term: TermId) -> bool {
    bv_const(arena, term).is_some_and(|(_, value)| value == 1)
}

fn is_bv_ones(arena: &TermArena, term: TermId) -> bool {
    bv_const(arena, term).is_some_and(|(width, value)| value == mask(width))
}

fn mask(width: u32) -> u128 {
    if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    }
}
