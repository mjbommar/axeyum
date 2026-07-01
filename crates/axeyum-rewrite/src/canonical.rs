//! Denotation-preserving canonicalization.
//!
//! The first canonicalizer is deliberately small and exact: every enabled
//! rule preserves term denotation under every assignment, so no model
//! projection is needed.

use std::collections::{BTreeSet, HashMap};

use axeyum_ir::{
    ArraySortKey, Assignment, IrError, Op, Sort, TermArena, TermId, TermNode, Value, eval,
};

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
const EQ_BOOL_CONST: &str = "eq.bool_const.v1";
const SELECT_STORE_SAME: &str = "array.select_store_same.v1";
const SELECT_CONST_ARRAY: &str = "array.select_const.v1";
const BV_COMPARE_REFLEXIVE: &str = "bv.compare_reflexive.v1";
const BV_COMPARE_SATURATE: &str = "bv.compare_saturate.v1";
const ITE_CONST_CONDITION: &str = "ite.const_condition.v1";
const ITE_SAME_BRANCHES: &str = "ite.same_branches.v1";
const ITE_BOOL_IDENTITY: &str = "ite.bool_identity.v1";
const BV_CONST_FOLD: &str = "bv.const_fold.v1";
const BV_DOUBLE_NOT: &str = "bv.double_not.v1";
const BV_DOUBLE_NEG: &str = "bv.double_neg.v1";
const BV_ADD_ZERO: &str = "bv.add_zero.v1";
const BV_SUB_ZERO: &str = "bv.sub_zero.v1";
const BV_SUB_SELF: &str = "bv.sub_self.v1";
const BV_MUL_ONE: &str = "bv.mul_one.v1";
const BV_MUL_ZERO: &str = "bv.mul_zero.v1";
const BV_MUL_POW2: &str = "bv.mul_pow2.v1";
const BV_UDIV_POW2: &str = "bv.udiv_pow2.v1";
const BV_UREM_POW2: &str = "bv.urem_pow2.v1";
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
const BV_EXTRACT_CONCAT: &str = "bv.extract_concat.v1";
const BV_EXTRACT_EXTEND: &str = "bv.extract_extend.v1";
const BV_CONCAT_EXTRACT: &str = "bv.concat_extract.v1";
const BV_EXTEND_ZERO: &str = "bv.extend_zero.v1";
const BV_ROTATE_ZERO: &str = "bv.rotate_zero.v1";
const COMMUTATIVE_ORDER: &str = "commutative.operand_order.v1";

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
            EQ_BOOL_CONST,
            "Boolean equality with a constant",
            "`=` of a Boolean term with a Boolean constant (`true`/`false`)",
        ),
        rule(
            SELECT_STORE_SAME,
            "Array read-over-write same index",
            "`(select (store a i v) i)` — selecting at the just-written index",
        ),
        rule(
            SELECT_CONST_ARRAY,
            "Array select of a constant array",
            "`(select (const-array v) i)` — every index of a constant array is `v`",
        ),
        rule(
            BV_COMPARE_REFLEXIVE,
            "Bit-vector comparison reflexivity",
            "a `bvult`/`bvule`/`bvugt`/`bvuge`/`bvslt`/`bvsle`/`bvsgt`/`bvsge` with structurally identical operands",
        ),
        rule(
            BV_COMPARE_SATURATE,
            "Bit-vector unsigned comparison saturation",
            "an unsigned `bvult`/`bvule`/`bvugt`/`bvuge` against 0 or all-ones that is a tautology/contradiction",
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
            ITE_BOOL_IDENTITY,
            "If-then-else Boolean identity",
            "`ite` of a Boolean condition with branches `true`/`false` is the condition",
        ),
        rule(
            BV_CONST_FOLD,
            "Bit-vector constant fold",
            "all operands are constants and the result sort is a bit-vector",
        ),
        rule(
            BV_DOUBLE_NOT,
            "Double bit-vector complement",
            "`bvnot` applied to a `bvnot` term",
        ),
        rule(
            BV_DOUBLE_NEG,
            "Double bit-vector negation",
            "`bvneg` applied to a `bvneg` term",
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
            BV_MUL_POW2,
            "Bit-vector multiply by power of two",
            "`bvmul` with a power-of-two constant operand",
        ),
        rule(
            BV_UDIV_POW2,
            "Unsigned divide by power of two",
            "`bvudiv` whose divisor (second operand) is a power-of-two constant",
        ),
        rule(
            BV_UREM_POW2,
            "Unsigned remainder by power of two",
            "`bvurem` whose divisor (second operand) is a power-of-two constant",
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
            BV_EXTRACT_CONCAT,
            "Extract of concat slice selection",
            "`extract` whose range lies entirely within one side of a `concat`",
        ),
        rule(
            BV_EXTRACT_EXTEND,
            "Extract within the original bits of an extend",
            "`extract` over a `zero_extend`/`sign_extend` whose high index lies below the original width",
        ),
        rule(
            BV_CONCAT_EXTRACT,
            "Concat of adjacent extracts of the same term",
            "`concat` of two `extract`s over the same term with adjacent (gap-free, overlap-free) ranges",
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
        rule(
            COMMUTATIVE_ORDER,
            "Commutative operand order",
            "a commutative operator with operands out of canonical order: AC operators (`and`/`or`/`xor`/`bvadd`/`bvmul`/`bvand`/`bvor`/`bvxor`/`bvxnor`) are flattened across their nested same-op tree and the operands sorted by ascending `TermId`; commutative-only operators (`=`/`bvnand`/`bvnor`) have just their two operands sorted",
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
            | TermNode::WideBvConst(_)
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
            Sort::BitVec(_)
            | Sort::Array { .. }
            | Sort::Int
            | Sort::Real
            | Sort::Datatype(_)
            | Sort::Uninterpreted(_)
            | Sort::Float { .. }
            | Sort::Seq(_) => BV_CONST_FOLD,
        };
        if enabled.contains(rule_id) {
            return Ok(applied(folded, rule_id));
        }
    }

    // Commutative-operand canonicalization. Two flavours, both governed by the
    // `commutative.operand_order.v1` rule:
    //
    //   * AC operators (associative *and* commutative — `and`/`or`/`xor`,
    //     `bvadd`/`bvmul`/`bvand`/`bvor`/`bvxor`/`bvxnor`): flatten the whole
    //     nested same-op tree into one operand multiset, sort by ascending
    //     `TermId`, and rebuild a left-associated tree over the sorted operands.
    //     So `a*(b*c)`, `(a*b)*c`, and `c*(a*b)` all canonicalize to the SAME
    //     term. This is denotation-preserving because the operator is both
    //     associative (regroup freely) and commutative (reorder freely).
    //   * Commutative-but-not-associative binary operators (`=`, `bvnand`,
    //     `bvnor`): only the two operands are sorted, never flattened — their
    //     grouping is meaningful, so `(= (= a b) c)` must keep its structure.
    //
    // The shared payoff: structurally-identical-operand rules (e.g. `=`
    // reflexivity) then fold goals such as `(= (a*(b*c)) (c*(a*b)))` to `true`
    // with no bit-blasting. The reorder is recorded only if no later rule fires
    // and the rebuilt term actually differs from the input application.
    let mut reordered = false;
    let normalized_args;
    let args = if is_ac(op) && enabled.contains(COMMUTATIVE_ORDER) {
        let flat = flatten_ac(arena, op, args);
        // A single operand or already-sorted flat list of the same length is a
        // no-op; only treat as a rewrite when the flattened/sorted operands
        // differ from the raw `args`.
        if flat.as_slice() == args {
            args
        } else {
            normalized_args = flat;
            reordered = true;
            normalized_args.as_slice()
        }
    } else if is_commutative(op) && args.len() == 2 && args[0] > args[1] {
        normalized_args = vec![args[1], args[0]];
        reordered = enabled.contains(COMMUTATIVE_ORDER);
        if reordered {
            normalized_args.as_slice()
        } else {
            args
        }
    } else {
        args
    };

    // AC flattening can yield more than two operands; the op-specific binary
    // rules below all assume exactly two. When the flattened operand list is
    // wider than binary, skip them and rebuild the canonical left-associated AC
    // tree directly. (The binary const-fold/identity/idempotent rules would not
    // fire on the multiset form anyway: constants are folded bottom-up at each
    // binary node when the AC tree is rebuilt, and duplicates remain explicit.)
    if reordered && args.len() != 2 {
        return Ok(applied(
            rebuild_left_assoc(arena, op, args)?,
            COMMUTATIVE_ORDER,
        ));
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
        Op::BvUdiv => rewrite_bv_udiv(arena, args, enabled)?,
        Op::BvUrem => rewrite_bv_urem(arena, args, enabled)?,
        Op::BvNot => rewrite_bv_not(arena, args, enabled),
        Op::BvNeg => rewrite_bv_neg(arena, args, enabled),
        Op::Eq => rewrite_eq(arena, args, enabled),
        Op::BvUlt
        | Op::BvUgt
        | Op::BvSlt
        | Op::BvSgt
        | Op::BvUle
        | Op::BvUge
        | Op::BvSle
        | Op::BvSge => rewrite_bv_compare(arena, op, args, enabled),
        Op::Ite => rewrite_ite(arena, args, enabled),
        Op::Extract { hi, lo } => rewrite_extract(arena, hi, lo, args, enabled)?,
        Op::ZeroExt { by } | Op::SignExt { by } => rewrite_extend(by, args, enabled),
        Op::RotateLeft { by } | Op::RotateRight { by } => rewrite_rotate(by, args, enabled),
        Op::Concat => rewrite_concat(arena, args, enabled)?,
        Op::Select => rewrite_select(arena, args, enabled),
        Op::BvNand
        | Op::BvNor
        | Op::BvXnor
        | Op::BvSdiv
        | Op::BvSrem
        | Op::BvSmod
        | Op::BvComp
        | Op::Store
        | Op::ConstArray { .. }
        | Op::IntToReal
        | Op::RealToInt
        | Op::RealIsInt
        | Op::Bv2Nat
        | Op::Int2Bv { .. }
        | Op::FpFromBits { .. }
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
        | Op::DtTest(_)
        // Sequences (ADR-0051, P2.7): no canonicalization rule yet — decline.
        | Op::SeqLen
        | Op::SeqEmpty(_)
        | Op::SeqUnit
        | Op::SeqConcat => None,
    };

    if let Some(local) = local {
        return Ok(local);
    }

    if reordered {
        return Ok(applied(build_app(arena, op, args)?, COMMUTATIVE_ORDER));
    }

    Ok(LocalRewrite {
        term: build_app(arena, op, args)?,
        rule_id: None,
    })
}

/// Returns `true` if `op` is commutative, so its binary operands may be reordered
/// without changing the term's denotation.
///
/// Only genuinely commutative operators are listed. Non-commutative operators
/// (`bvsub`, the div/rem family, shifts, comparisons, `concat`, `=>`, `ite`,
/// uninterpreted `apply`, and the array ops) are deliberately excluded: their
/// operand order is meaningful.
fn is_commutative(op: Op) -> bool {
    matches!(
        op,
        Op::BoolAnd
            | Op::BoolOr
            | Op::BoolXor
            | Op::Eq
            | Op::BvAdd
            | Op::BvMul
            | Op::BvAnd
            | Op::BvOr
            | Op::BvXor
            | Op::BvNand
            | Op::BvNor
            | Op::BvXnor
    )
}

/// Returns `true` if `op` is both associative **and** commutative, so a nested
/// tree of the same operator may be flattened into one operand multiset, sorted,
/// and rebuilt without changing the term's denotation.
///
/// The included set is exactly the AC operators: `and`/`or`/`xor`,
/// `bvadd`/`bvmul`/`bvand`/`bvor`/`bvxor`, and `bvxnor` (bitwise xnor is
/// associative — `NOT(a XOR b)` reduces to bitwise equivalence, which is
/// associative; confirmed by exhaustive small-width evaluation). Commutative but
/// **not** associative operators are deliberately excluded so they are never
/// flattened: `=` (a binary predicate; `(= (= a b) c)` is a distinct term),
/// `bvnand`, and `bvnor`. All non-commutative operators are excluded as well.
fn is_ac(op: Op) -> bool {
    matches!(
        op,
        Op::BoolAnd
            | Op::BoolOr
            | Op::BoolXor
            | Op::BvAdd
            | Op::BvMul
            | Op::BvAnd
            | Op::BvOr
            | Op::BvXor
            | Op::BvXnor
    )
}

/// Flattens the nested same-`op` tree rooted at `op(args…)` into a single operand
/// list (children whose op equals `op` are recursively inlined), then sorts the
/// operands by ascending `TermId`. The result is the canonical operand multiset
/// for an AC operator: `a*(b*c)`, `(a*b)*c`, and `c*(a*b)` all flatten to the
/// same sorted list. Duplicate operands are kept (the multiset is preserved), so
/// the transform is exact for every AC operator including the non-idempotent ones
/// (`bvadd`, `bvmul`, `bvxor`, `bvxnor`).
///
/// `op` must be an [`is_ac`] operator (so every same-op node is binary).
fn flatten_ac(arena: &TermArena, op: Op, args: &[TermId]) -> Vec<TermId> {
    let mut operands = Vec::new();
    for &arg in args {
        collect_ac_operands(arena, op, arg, &mut operands);
    }
    operands.sort_unstable();
    operands
}

/// Appends the flattened operands of `term` for AC operator `op` into `out`: if
/// `term` is itself an application of `op`, recurse into its children; otherwise
/// `term` is a leaf operand.
fn collect_ac_operands(arena: &TermArena, op: Op, term: TermId, out: &mut Vec<TermId>) {
    if let TermNode::App { op: inner, args } = arena.node(term)
        && *inner == op
    {
        let args = args.clone();
        for &arg in &args {
            collect_ac_operands(arena, op, arg, out);
        }
    } else {
        out.push(term);
    }
}

/// Rebuilds a left-associated tree `op(…op(op(args[0], args[1]), args[2])…)` over
/// `args` (length `>= 2`) using the typed arena builders. Used to reassemble the
/// canonical form of an AC operator from its sorted operand list.
///
/// # Errors
///
/// Returns [`IrError`] if a rebuilt node violates the operator's sort contract,
/// which cannot happen when reassembling operands of a well-formed AC term.
fn rebuild_left_assoc(arena: &mut TermArena, op: Op, args: &[TermId]) -> Result<TermId, IrError> {
    let mut acc = args[0];
    for &arg in &args[1..] {
        acc = build_app(arena, op, &[acc, arg])?;
    }
    Ok(acc)
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

/// `bvnot(bvnot x) -> x`. Bitwise complement is an involution, so two
/// complements cancel exactly under every assignment.
fn rewrite_bv_not(
    arena: &TermArena,
    args: &[TermId],
    enabled: &BTreeSet<&str>,
) -> Option<LocalRewrite> {
    if enabled.contains(BV_DOUBLE_NOT)
        && let TermNode::App {
            op: Op::BvNot,
            args: inner,
        } = arena.node(args[0])
    {
        return Some(applied(inner[0], BV_DOUBLE_NOT));
    }
    None
}

/// `bvneg(bvneg x) -> x`. Two's-complement negation is an involution
/// (`-(-x) = x mod 2^w` for every bit-vector, including the sign-bit-only
/// `INT_MIN` value), so two negations cancel exactly under every assignment.
fn rewrite_bv_neg(
    arena: &TermArena,
    args: &[TermId],
    enabled: &BTreeSet<&str>,
) -> Option<LocalRewrite> {
    if enabled.contains(BV_DOUBLE_NEG)
        && let TermNode::App {
            op: Op::BvNeg,
            args: inner,
        } = arena.node(args[0])
    {
        return Some(applied(inner[0], BV_DOUBLE_NEG));
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
    // Strength reduction: `x * 2^k ≡ (x << k) (mod 2^w)` for `0 < k < w`. Both
    // operand orders are handled (AC-normalization may have already moved the
    // constant). `value == 1` (i.e. `k == 0`) is left to `bv.mul_one.v1`.
    if enabled.contains(BV_MUL_POW2) {
        if let Some(rewritten) = bv_mul_pow2(arena, a, b)? {
            return Ok(Some(rewritten));
        }
        if let Some(rewritten) = bv_mul_pow2(arena, b, a)? {
            return Ok(Some(rewritten));
        }
    }
    Ok(None)
}

/// If `constant` is a power-of-two bit-vector constant greater than one,
/// rewrites `constant * other` to `other << k` where `constant == 2^k`.
///
/// `value.is_power_of_two() && value > 1` selects exactly the powers of two
/// `2^k` with `1 <= k < width` (`value = 2^k < 2^width`), so `k =
/// value.trailing_zeros()` is always `< width` and the shift amount fits the
/// operand width. Multiplying a width-`w` bit-vector by `2^k` is exactly a left
/// shift by `k` with the same modular wraparound, so this is denotation-
/// preserving with identity model projection.
fn bv_mul_pow2(
    arena: &mut TermArena,
    constant: TermId,
    other: TermId,
) -> Result<Option<LocalRewrite>, IrError> {
    if let Some((width, value)) = bv_const(arena, constant)
        && value > 1
        && value.is_power_of_two()
    {
        let k = value.trailing_zeros();
        let shift = arena.bv_const(width, u128::from(k))?;
        return Ok(Some(applied(arena.bv_shl(other, shift)?, BV_MUL_POW2)));
    }
    Ok(None)
}

/// Strength reduction: `bvudiv x 2^k -> bvlshr x k`.
///
/// Unsigned floor division by a power of two `2^k` (`1 <= 2^k < 2^width`) equals
/// a logical (zero-filling) right shift by `k` for **every** value of `x`,
/// including `x = all-ones`. The rule fires only when the *divisor* — the second
/// operand `args[1]` — is the power-of-two constant; division is not commutative,
/// so a power-of-two *dividend* must never trigger it. `value == 1` (`k == 0`)
/// reduces to `bvlshr x 0`, which `bv.shift_zero.v1` then folds to `x`. The
/// divisor `0` is not a power of two, so the SMT-LIB totality case `bvudiv x 0 =
/// all-ones` is correctly skipped.
fn rewrite_bv_udiv(
    arena: &mut TermArena,
    args: &[TermId],
    enabled: &BTreeSet<&str>,
) -> Result<Option<LocalRewrite>, IrError> {
    if enabled.contains(BV_UDIV_POW2)
        && let Some((width, value)) = bv_const(arena, args[1])
        && value.is_power_of_two()
    {
        let k = value.trailing_zeros();
        let shift = arena.bv_const(width, u128::from(k))?;
        return Ok(Some(applied(arena.bv_lshr(args[0], shift)?, BV_UDIV_POW2)));
    }
    Ok(None)
}

/// Strength reduction: `bvurem x 2^k -> bvand x (2^k - 1)`.
///
/// The unsigned remainder of `x` modulo a power of two `2^k` (`1 <= 2^k <
/// 2^width`) is exactly the low `k` bits of `x`, i.e. masking with `2^k - 1`, for
/// **every** value of `x`. The rule fires only when the *divisor* (second operand
/// `args[1]`) is the power-of-two constant; remainder is not commutative, so a
/// power-of-two *first* operand must never trigger it. `value == 1` (`k == 0`)
/// reduces to `bvand x 0`, i.e. `0`. The divisor `0` is not a power of two, so the
/// SMT-LIB totality case `bvurem x 0 = x` is correctly skipped.
fn rewrite_bv_urem(
    arena: &mut TermArena,
    args: &[TermId],
    enabled: &BTreeSet<&str>,
) -> Result<Option<LocalRewrite>, IrError> {
    if enabled.contains(BV_UREM_POW2)
        && let Some((width, value)) = bv_const(arena, args[1])
        && value.is_power_of_two()
    {
        let mask = arena.bv_const(width, value - 1)?;
        return Ok(Some(applied(arena.bv_and(args[0], mask)?, BV_UREM_POW2)));
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
    // Boolean equality with a Boolean constant: `(= p true)` ≡ `p`, `(= p false)` ≡
    // `(not p)` (and symmetric). A Boolean constant operand forces the other to be
    // Boolean-sorted, so this never matches a bit-vector equality. (An equality of
    // two constants is folded earlier by the constant-fold rule.)
    if enabled.contains(EQ_BOOL_CONST) {
        for (const_arg, other) in [(args[0], args[1]), (args[1], args[0])] {
            if let Some(value) = bool_const(arena, const_arg) {
                return if value {
                    Some(applied(other, EQ_BOOL_CONST))
                } else {
                    Some(applied(arena.not(other).ok()?, EQ_BOOL_CONST))
                };
            }
        }
    }
    None
}

/// Bit-vector comparison reflexivity: `op x x` folds to a Boolean constant.
///
/// For structurally identical operands (the same `TermId`, since the arena
/// hash-conses), `x ⋈ x` has the same Boolean value under every assignment,
/// signed or unsigned:
///
///   * strict ordering (`bvult`/`bvugt`/`bvslt`/`bvsgt`) is always `false`;
///   * non-strict ordering (`bvule`/`bvuge`/`bvsle`/`bvsge`) is always `true`.
///
/// The folded result is a `Bool` constant, so later constant-fold rules can
/// take it from there. Exact-denotation, identity model projection.
fn rewrite_bv_compare(
    arena: &mut TermArena,
    op: Op,
    args: &[TermId],
    enabled: &BTreeSet<&str>,
) -> Option<LocalRewrite> {
    if enabled.contains(BV_COMPARE_REFLEXIVE) && args[0] == args[1] {
        let value = match op {
            Op::BvUlt | Op::BvUgt | Op::BvSlt | Op::BvSgt => false,
            Op::BvUle | Op::BvUge | Op::BvSle | Op::BvSge => true,
            _ => return None,
        };
        return Some(applied(arena.bool_const(value), BV_COMPARE_REFLEXIVE));
    }
    // Unsigned comparison saturation against 0 (the unsigned min) and all-ones (the
    // unsigned max). Only the extreme-end direction is a tautology/contradiction
    // (e.g. `x ≤ MAX` is always true, but `x < MAX` is NOT); see each arm.
    if enabled.contains(BV_COMPARE_SATURATE) {
        let (za, zb) = (is_bv_zero(arena, args[0]), is_bv_zero(arena, args[1]));
        let (oa, ob) = (
            is_bv_all_ones(arena, args[0]),
            is_bv_all_ones(arena, args[1]),
        );
        let saturated = match op {
            // a < b: false if b == 0 (nothing < 0) or a == MAX (MAX < nothing).
            Op::BvUlt if zb || oa => Some(false),
            // a ≤ b: true if a == 0 (0 ≤ all) or b == MAX (all ≤ MAX).
            Op::BvUle if za || ob => Some(true),
            // a > b: false if a == 0 (0 > nothing) or b == MAX (nothing > MAX).
            Op::BvUgt if za || ob => Some(false),
            // a ≥ b: true if b == 0 (all ≥ 0) or a == MAX (MAX ≥ all).
            Op::BvUge if zb || oa => Some(true),
            _ => None,
        };
        if let Some(value) = saturated {
            return Some(applied(arena.bool_const(value), BV_COMPARE_SATURATE));
        }
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
    // `(ite c true false)` ≡ `c` for a Boolean condition `c` — the ite is just the
    // condition. (The dual `(ite c false true)` ≡ `(not c)` needs a fresh `not`
    // term, so it is left to the general structure rather than this immutable pass.)
    if enabled.contains(ITE_BOOL_IDENTITY)
        && bool_const(arena, args[1]) == Some(true)
        && bool_const(arena, args[2]) == Some(false)
    {
        return Some(applied(args[0], ITE_BOOL_IDENTITY));
    }
    None
}

/// `extract` simplifications.
///
/// `BV_EXTRACT_WHOLE`: `((_ extract (w-1) 0) x)` over the full input width `w`
/// is `x` itself.
///
/// `BV_EXTRACT_CONCAT`: when the inner term is a binary `(concat a b)` (with `a`
/// the high bits, `b` the low bits) and the `[hi:lo]` range lies entirely within
/// one side, drop the concat and extract directly from that side. SMT-LIB places
/// `b` in bits `0..wb` and `a` in bits `wb..`, so with `wb = width(b)`:
///
/// * `hi < wb` — range entirely in the low part `b`: `((_ extract hi lo) b)`;
/// * `lo >= wb` — range entirely in the high part `a`: subtract `wb` from both
///   indices, `((_ extract (hi - wb) (lo - wb)) a)`;
/// * otherwise the range straddles the boundary and is left unchanged.
///
/// This selects exactly the same bits, so it is exact-denotation with identity
/// model projection.
fn rewrite_extract(
    arena: &mut TermArena,
    hi: u32,
    lo: u32,
    args: &[TermId],
    enabled: &BTreeSet<&str>,
) -> Result<Option<LocalRewrite>, IrError> {
    if enabled.contains(BV_EXTRACT_WHOLE)
        && lo == 0
        && arena.sort_of(args[0]).bv_width() == Some(hi + 1)
    {
        return Ok(Some(applied(args[0], BV_EXTRACT_WHOLE)));
    }
    if enabled.contains(BV_EXTRACT_CONCAT)
        && let TermNode::App {
            op: Op::Concat,
            args: concat_args,
        } = arena.node(args[0])
    {
        let a = concat_args[0];
        let b = concat_args[1];
        let wb = arena
            .sort_of(b)
            .bv_width()
            .expect("concat low operand has BV sort");
        if hi < wb {
            return Ok(Some(applied(arena.extract(hi, lo, b)?, BV_EXTRACT_CONCAT)));
        } else if lo >= wb {
            return Ok(Some(applied(
                arena.extract(hi - wb, lo - wb, a)?,
                BV_EXTRACT_CONCAT,
            )));
        }
    }
    // `extract within the original bits of an extend`: both `zero_extend` and
    // `sign_extend` keep the low `width(x)` bits exactly equal to `x`'s bits and
    // only differ in the appended high bits. When the whole extract range lies
    // strictly below the original width (`hi < width(x)`), it touches only those
    // unchanged low bits, so `((_ extract hi lo) (extend x)) ≡ ((_ extract hi lo)
    // x)` regardless of which extend — exact-denotation, identity projection. When
    // `hi >= width(x)` the range reaches the appended bits (which differ between
    // zero/sign extend and may straddle the boundary), so the rule is skipped.
    if enabled.contains(BV_EXTRACT_EXTEND)
        && let TermNode::App {
            op: Op::ZeroExt { .. } | Op::SignExt { .. },
            args: inner,
        } = arena.node(args[0])
    {
        let x = inner[0];
        let xw = arena
            .sort_of(x)
            .bv_width()
            .expect("extend operand has BV sort");
        if hi < xw {
            return Ok(Some(applied(arena.extract(hi, lo, x)?, BV_EXTRACT_EXTEND)));
        }
    }
    Ok(None)
}

/// `(select (store a i v) i)` → `v` (read-over-write, same index) and
/// `(select (const-array v) i)` → `v` (constant array). Both are exact-denotation
/// and return the stored/constant value directly.
fn rewrite_select(
    arena: &TermArena,
    args: &[TermId],
    enabled: &BTreeSet<&str>,
) -> Option<LocalRewrite> {
    let [array, idx] = [args[0], args[1]];
    match arena.node(array) {
        TermNode::App {
            op: Op::Store,
            args: store_args,
        } if enabled.contains(SELECT_STORE_SAME) && store_args[1] == idx => {
            // store_args = [a, i, v]; reading at the just-written index `i` gives `v`.
            Some(applied(store_args[2], SELECT_STORE_SAME))
        }
        TermNode::App {
            op: Op::ConstArray { .. },
            args: const_args,
        } if enabled.contains(SELECT_CONST_ARRAY) => {
            // A constant array maps every index to its single value.
            Some(applied(const_args[0], SELECT_CONST_ARRAY))
        }
        _ => None,
    }
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

/// `concat of adjacent extracts of the same term`: reassemble two contiguous
/// slices of one term into a single slice.
///
/// `Op::Concat` is binary: `args[0]` is the HIGH operand and `args[1]` is the
/// LOW operand. When both are extracts over the **same** inner term `x` —
/// `args[0] = ((_ extract hi1 lo1) x)` and `args[1] = ((_ extract hi2 lo2) x)` —
/// and the slices are **adjacent** (`lo1 == hi2 + 1`: the high slice begins
/// exactly one bit above the low slice, with no gap and no overlap), the
/// concatenation reproduces the contiguous range `lo2..=hi1`, so it rewrites to
/// `((_ extract hi1 lo2) x)`. Exact-denotation with identity model projection.
/// A gap/overlap, or extracts over different terms, leaves the term unchanged.
fn rewrite_concat(
    arena: &mut TermArena,
    args: &[TermId],
    enabled: &BTreeSet<&str>,
) -> Result<Option<LocalRewrite>, IrError> {
    if enabled.contains(BV_CONCAT_EXTRACT)
        && let TermNode::App {
            op: Op::Extract { hi: hi1, lo: lo1 },
            args: high_args,
        } = arena.node(args[0])
        && let (hi1, lo1, x_high) = (*hi1, *lo1, high_args[0])
        && let TermNode::App {
            op: Op::Extract { hi: hi2, lo: lo2 },
            args: low_args,
        } = arena.node(args[1])
        && let (hi2, lo2, x_low) = (*hi2, *lo2, low_args[0])
        && x_high == x_low
        && lo1 == hi2 + 1
    {
        return Ok(Some(applied(
            arena.extract(hi1, lo2, x_high)?,
            BV_CONCAT_EXTRACT,
        )));
    }
    Ok(None)
}

/// Rebuilds the application `op(args…)` via the typed arena builders, re-running
/// their sort checks. The inverse of destructuring a [`TermNode::App`]; useful
/// for bottom-up rewrites that reconstruct a node from transformed children.
///
/// # Errors
///
/// Returns [`IrError`] if the operands do not satisfy the operator's sort
/// contract (which cannot happen when reassembling a well-formed term).
pub fn build_app(arena: &mut TermArena, op: Op, args: &[TermId]) -> Result<TermId, IrError> {
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
        Op::ConstArray { index } => arena.const_array_with_index_sort(index.to_sort(), args[0]),
        Op::IntToReal => arena.int_to_real(args[0]),
        Op::RealToInt => arena.real_to_int(args[0]),
        Op::RealIsInt => arena.real_is_int(args[0]),
        Op::Bv2Nat => arena.bv2nat(args[0]),
        Op::Int2Bv { width } => arena.int2bv(width, args[0]),
        Op::FpFromBits { exp, sig } => arena.fp_from_bits(args[0], exp, sig),
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
        // Sequences (ADR-0051, P2.7): reassemble via the sequence builders.
        Op::SeqLen => arena.seq_len(args[0]),
        Op::SeqEmpty(element) => Ok(arena.seq_empty(element)),
        Op::SeqUnit => arena.seq_unit(args[0]),
        Op::SeqConcat => arena.seq_concat(args[0], args[1]),
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
        | TermNode::WideBvConst(_)
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
        Value::WideBv(w) => Ok(arena.wide_bv_const(w)),
        Value::Datatype { datatype, .. } => Err(IrError::SortMismatch {
            expected: "Bool or BitVec",
            found: Sort::Datatype(datatype),
        }),
        Value::Array(array) => Err(IrError::SortMismatch {
            expected: "Bool or BitVec",
            found: Sort::Array {
                index: ArraySortKey::BitVec(array.index_width()),
                element: ArraySortKey::BitVec(array.element_width()),
            },
        }),
        Value::GenericArray(array) => Err(IrError::SortMismatch {
            expected: "Bool or BitVec",
            found: Sort::Array {
                index: array.index_sort(),
                element: array.element_sort(),
            },
        }),
        Value::Int(value) => Ok(arena.int_const(value)),
        Value::Real(value) => Ok(arena.real_const(value)),
        // A real-algebraic value has no constant-term encoding (ADR-0038): it is
        // produced by the NRA decider's witness model and is never folded back
        // into a term here.
        Value::RealAlgebraic(_) => Err(IrError::Unsupported(
            "real-algebraic value has no constant term (ADR-0038)",
        )),
        Value::Uninterpreted { sort, .. } => Err(IrError::SortMismatch {
            expected: "Bool or BitVec",
            found: Sort::Uninterpreted(sort),
        }),
        // A sequence value has no constant-term encoding yet (ADR-0051, P2.7):
        // sequences are not const-folded back into terms here — decline exactly.
        Value::Seq(_) => Err(IrError::Unsupported(
            "sequence value has no constant term (ADR-0051)",
        )),
    }
}

fn bool_const(arena: &TermArena, term: TermId) -> Option<bool> {
    match arena.node(term) {
        TermNode::BoolConst(value) => Some(*value),
        TermNode::BvConst { .. }
        | TermNode::WideBvConst(_)
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
        | TermNode::WideBvConst(_)
        | TermNode::IntConst(_)
        | TermNode::RealConst(_)
        | TermNode::Symbol(_)
        | TermNode::App { .. } => None,
    }
}

fn is_bv_zero(arena: &TermArena, term: TermId) -> bool {
    bv_const(arena, term).is_some_and(|(_, value)| value == 0)
}

/// Whether `term` is the all-ones bit-vector constant (the unsigned maximum) of its
/// width. Wide (>128-bit) constants return `None` from [`bv_const`] and so are not
/// detected here — the rule simply does not fire on them.
fn is_bv_all_ones(arena: &TermArena, term: TermId) -> bool {
    bv_const(arena, term).is_some_and(|(width, value)| {
        let all_ones = if width >= 128 {
            u128::MAX
        } else {
            (1u128 << width) - 1
        };
        value == all_ones
    })
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

#[cfg(test)]
mod commutative_tests {
    use axeyum_ir::{Assignment, Op, Sort, TermArena, TermId, TermNode, Value, eval};

    use super::canonicalize;

    /// Each pair of binary commutative builders must canonicalize to the same
    /// term regardless of operand order.
    #[test]
    #[allow(clippy::many_single_char_names)]
    fn commutative_ops_canonicalize_order_independently() {
        let mut a = TermArena::new();
        let x = a.bv_var("x", 4).unwrap();
        let y = a.bv_var("y", 4).unwrap();
        let p = a.bool_var("p").unwrap();
        let q = a.bool_var("q").unwrap();

        // (builder applied as (lhs, rhs), then (rhs, lhs)) must agree.
        let bv_cases: [fn(&mut TermArena, TermId, TermId) -> TermId; 8] = [
            |a, l, r| a.bv_add(l, r).unwrap(),
            |a, l, r| a.bv_mul(l, r).unwrap(),
            |a, l, r| a.bv_and(l, r).unwrap(),
            |a, l, r| a.bv_or(l, r).unwrap(),
            |a, l, r| a.bv_xor(l, r).unwrap(),
            |a, l, r| a.bv_nand(l, r).unwrap(),
            |a, l, r| a.bv_nor(l, r).unwrap(),
            |a, l, r| a.bv_xnor(l, r).unwrap(),
        ];
        for case in bv_cases {
            let forward = case(&mut a, x, y);
            let reverse = case(&mut a, y, x);
            let cf = canonicalize(&mut a, forward).unwrap().term;
            let cr = canonicalize(&mut a, reverse).unwrap().term;
            assert_eq!(cf, cr, "bv commutative op did not canonicalize uniquely");
        }

        let bool_cases: [fn(&mut TermArena, TermId, TermId) -> TermId; 3] = [
            |a, l, r| a.and(l, r).unwrap(),
            |a, l, r| a.or(l, r).unwrap(),
            |a, l, r| a.xor(l, r).unwrap(),
        ];
        for case in bool_cases {
            let forward = case(&mut a, p, q);
            let reverse = case(&mut a, q, p);
            let cf = canonicalize(&mut a, forward).unwrap().term;
            let cr = canonicalize(&mut a, reverse).unwrap().term;
            assert_eq!(cf, cr, "bool commutative op did not canonicalize uniquely");
        }

        // `=` is commutative on both BV and Bool operands.
        let eq_bv_fwd = a.eq(x, y).unwrap();
        let eq_bv_rev = a.eq(y, x).unwrap();
        assert_eq!(
            canonicalize(&mut a, eq_bv_fwd).unwrap().term,
            canonicalize(&mut a, eq_bv_rev).unwrap().term,
        );
        let eq_bool_fwd = a.eq(p, q).unwrap();
        let eq_bool_rev = a.eq(q, p).unwrap();
        assert_eq!(
            canonicalize(&mut a, eq_bool_fwd).unwrap().term,
            canonicalize(&mut a, eq_bool_rev).unwrap().term,
        );
    }

    /// The headline win: `(= (bvmul a b) (bvmul b a))` folds to `true` because
    /// both multipliers canonicalize to the same term and the `=` reflexivity
    /// rule then fires — no multiplier bit-blasting.
    #[test]
    fn multiplier_commutativity_goal_folds_to_true() {
        let mut a = TermArena::new();
        let x = a.bv_var("x", 8).unwrap();
        let y = a.bv_var("y", 8).unwrap();
        let xy = a.bv_mul(x, y).unwrap();
        let yx = a.bv_mul(y, x).unwrap();
        let goal = a.eq(xy, yx).unwrap();

        let outcome = canonicalize(&mut a, goal).unwrap();
        assert_eq!(outcome.term, a.bool_const(true));
    }

    /// Non-commutative operators must never have their operands reordered.
    #[test]
    fn non_commutative_ops_are_not_reordered() {
        let mut a = TermArena::new();
        // Declare so that x has the larger TermId; (op x y) with x > y would be
        // "out of ascending order" — but for non-commutative ops it must stay.
        let y = a.bv_var("y", 8).unwrap();
        let x = a.bv_var("x", 8).unwrap();
        assert!(x > y, "test relies on x having the larger TermId");

        let sub = a.bv_sub(x, y).unwrap();
        assert_eq!(canonicalize(&mut a, sub).unwrap().term, sub);

        let udiv = a.bv_udiv(x, y).unwrap();
        assert_eq!(canonicalize(&mut a, udiv).unwrap().term, udiv);

        let ult = a.bv_ult(x, y).unwrap();
        assert_eq!(canonicalize(&mut a, ult).unwrap().term, ult);

        let concat = a.concat(x, y).unwrap();
        assert_eq!(canonicalize(&mut a, concat).unwrap().term, concat);

        // Uninterpreted-function argument order is meaningful.
        let f = a
            .declare_fun("f", &[Sort::BitVec(8), Sort::BitVec(8)], Sort::BitVec(8))
            .unwrap();
        let fxy = a.apply(f, &[x, y]).unwrap();
        assert_eq!(canonicalize(&mut a, fxy).unwrap().term, fxy);
    }

    /// Denotation must be preserved: original and canonicalized terms agree under
    /// every assignment, including nested mixed terms.
    #[test]
    #[allow(clippy::many_single_char_names)]
    fn commutative_canonicalization_preserves_denotation() {
        let mut a = TermArena::new();
        let x_sym = a.declare("x", Sort::BitVec(3)).unwrap();
        let y_sym = a.declare("y", Sort::BitVec(3)).unwrap();
        let z_sym = a.declare("z", Sort::BitVec(3)).unwrap();
        let p_sym = a.declare("p", Sort::Bool).unwrap();
        let x = a.var(x_sym);
        let y = a.var(y_sym);
        let z = a.var(z_sym);
        let p = a.var(p_sym);

        // Nested mixed commutative/non-commutative terms.
        let mul = a.bv_mul(z, x).unwrap();
        let add = a.bv_add(mul, y).unwrap();
        let sub = a.bv_sub(add, x).unwrap();
        let and = a.bv_and(sub, z).unwrap();
        let eq = a.eq(and, y).unwrap();
        let xor = a.bv_xor(y, mul).unwrap();
        let eq2 = a.eq(xor, z).unwrap();
        let body = a.and(eq, eq2).unwrap();
        let goal = a.or(p, body).unwrap();
        let terms = [mul, add, and, goal];

        let rewritten = terms
            .iter()
            .map(|&t| canonicalize(&mut a, t).unwrap().term)
            .collect::<Vec<_>>();

        for xv in 0..8u128 {
            for yv in 0..8u128 {
                for zv in 0..8u128 {
                    for pv in [false, true] {
                        let mut asg = Assignment::new();
                        asg.set(
                            x_sym,
                            Value::Bv {
                                width: 3,
                                value: xv,
                            },
                        );
                        asg.set(
                            y_sym,
                            Value::Bv {
                                width: 3,
                                value: yv,
                            },
                        );
                        asg.set(
                            z_sym,
                            Value::Bv {
                                width: 3,
                                value: zv,
                            },
                        );
                        asg.set(p_sym, Value::Bool(pv));
                        for (&orig, &canon) in terms.iter().zip(&rewritten) {
                            assert_eq!(
                                eval(&a, orig, &asg).unwrap(),
                                eval(&a, canon, &asg).unwrap(),
                            );
                        }
                    }
                }
            }
        }
    }

    /// Every association of an AC operator over the same three operands must
    /// canonicalize to one and the same term: `a*(b*c)`, `(a*b)*c`, and
    /// `c*(a*b)` (and the reversed grouping) all coincide after AC-flattening.
    #[test]
    #[allow(clippy::many_single_char_names)]
    fn ac_ops_canonicalize_associatively() {
        let mut a = TermArena::new();
        let x = a.bv_var("x", 4).unwrap();
        let y = a.bv_var("y", 4).unwrap();
        let z = a.bv_var("z", 4).unwrap();
        let p = a.bool_var("p").unwrap();
        let q = a.bool_var("q").unwrap();
        let r = a.bool_var("r").unwrap();

        // Each bv builder, applied as a*(b*c), (a*b)*c, c*(a*b), must agree.
        let bv_cases: [fn(&mut TermArena, TermId, TermId) -> TermId; 6] = [
            |a, l, r| a.bv_add(l, r).unwrap(),
            |a, l, r| a.bv_mul(l, r).unwrap(),
            |a, l, r| a.bv_and(l, r).unwrap(),
            |a, l, r| a.bv_or(l, r).unwrap(),
            |a, l, r| a.bv_xor(l, r).unwrap(),
            |a, l, r| a.bv_xnor(l, r).unwrap(),
        ];
        for case in bv_cases {
            let bc = case(&mut a, y, z);
            let right = case(&mut a, x, bc); // a*(b*c)
            let ab = case(&mut a, x, y);
            let left = case(&mut a, ab, z); // (a*b)*c
            let ab2 = case(&mut a, x, y);
            let rot = case(&mut a, z, ab2); // c*(a*b)
            let cr = canonicalize(&mut a, right).unwrap().term;
            let cl = canonicalize(&mut a, left).unwrap().term;
            let crot = canonicalize(&mut a, rot).unwrap().term;
            assert_eq!(cr, cl, "AC bv op: a*(b*c) != (a*b)*c");
            assert_eq!(cl, crot, "AC bv op: (a*b)*c != c*(a*b)");
        }

        let bool_cases: [fn(&mut TermArena, TermId, TermId) -> TermId; 3] = [
            |a, l, r| a.and(l, r).unwrap(),
            |a, l, r| a.or(l, r).unwrap(),
            |a, l, r| a.xor(l, r).unwrap(),
        ];
        for case in bool_cases {
            let qr = case(&mut a, q, r);
            let right = case(&mut a, p, qr);
            let pq = case(&mut a, p, q);
            let left = case(&mut a, pq, r);
            let pq2 = case(&mut a, p, q);
            let rot = case(&mut a, r, pq2);
            let cr = canonicalize(&mut a, right).unwrap().term;
            let cl = canonicalize(&mut a, left).unwrap().term;
            let crot = canonicalize(&mut a, rot).unwrap().term;
            assert_eq!(cr, cl, "AC bool op: p*(q*r) != (p*q)*r");
            assert_eq!(cl, crot, "AC bool op: (p*q)*r != r*(p*q)");
        }
    }

    /// The AC headline win: `(= (a*(b*c)) (c*(a*b)))` folds to `true` because
    /// both multiplier trees AC-canonicalize to the same term and `=` reflexivity
    /// then fires — no multiplier bit-blasting, even across the multiplier tree.
    #[test]
    #[allow(clippy::many_single_char_names)]
    fn ac_multiplier_tree_equality_folds_to_true() {
        let mut a = TermArena::new();
        let x = a.bv_var("x", 8).unwrap();
        let y = a.bv_var("y", 8).unwrap();
        let z = a.bv_var("z", 8).unwrap();
        let bc = a.bv_mul(y, z).unwrap();
        let lhs = a.bv_mul(x, bc).unwrap(); // a*(b*c)
        let ab = a.bv_mul(x, y).unwrap();
        let rhs = a.bv_mul(z, ab).unwrap(); // c*(a*b)
        let goal = a.eq(lhs, rhs).unwrap();

        let outcome = canonicalize(&mut a, goal).unwrap();
        assert_eq!(outcome.term, a.bool_const(true));
    }

    /// AC-flattening must preserve denotation: original and canonical agree under
    /// every 3-bit assignment, for each AC operator over a nested tree — including
    /// `bvxnor`, whose associativity justifies its AC inclusion.
    #[test]
    #[allow(clippy::many_single_char_names)]
    fn ac_flattening_preserves_denotation() {
        let mut a = TermArena::new();
        let x_sym = a.declare("x", Sort::BitVec(3)).unwrap();
        let y_sym = a.declare("y", Sort::BitVec(3)).unwrap();
        let z_sym = a.declare("z", Sort::BitVec(3)).unwrap();
        let w_sym = a.declare("w", Sort::BitVec(3)).unwrap();
        let x = a.var(x_sym);
        let y = a.var(y_sym);
        let z = a.var(z_sym);
        let w = a.var(w_sym);

        // For each AC bv builder, build a deep mixed-association tree over 4 vars.
        let bv_cases: [fn(&mut TermArena, TermId, TermId) -> TermId; 6] = [
            |a, l, r| a.bv_add(l, r).unwrap(),
            |a, l, r| a.bv_mul(l, r).unwrap(),
            |a, l, r| a.bv_and(l, r).unwrap(),
            |a, l, r| a.bv_or(l, r).unwrap(),
            |a, l, r| a.bv_xor(l, r).unwrap(),
            |a, l, r| a.bv_xnor(l, r).unwrap(),
        ];
        let mut terms = Vec::new();
        for case in bv_cases {
            // (x op (y op z)) op ((z op w) op x) — nested, repeated operands.
            let yz = case(&mut a, y, z);
            let left = case(&mut a, x, yz);
            let zw = case(&mut a, z, w);
            let right = case(&mut a, zw, x);
            terms.push(case(&mut a, left, right));
        }
        let rewritten = terms
            .iter()
            .map(|&t| canonicalize(&mut a, t).unwrap().term)
            .collect::<Vec<_>>();

        for xv in 0..8u128 {
            for yv in 0..8u128 {
                for zv in 0..8u128 {
                    for wv in 0..8u128 {
                        let mut asg = Assignment::new();
                        asg.set(
                            x_sym,
                            Value::Bv {
                                width: 3,
                                value: xv,
                            },
                        );
                        asg.set(
                            y_sym,
                            Value::Bv {
                                width: 3,
                                value: yv,
                            },
                        );
                        asg.set(
                            z_sym,
                            Value::Bv {
                                width: 3,
                                value: zv,
                            },
                        );
                        asg.set(
                            w_sym,
                            Value::Bv {
                                width: 3,
                                value: wv,
                            },
                        );
                        for (&orig, &canon) in terms.iter().zip(&rewritten) {
                            assert_eq!(
                                eval(&a, orig, &asg).unwrap(),
                                eval(&a, canon, &asg).unwrap(),
                                "AC flattening changed denotation",
                            );
                        }
                    }
                }
            }
        }
    }

    /// Operators that are commutative but NOT associative (`=`, `bvnand`,
    /// `bvnor`) and non-commutative operators must NOT be AC-flattened: a nested
    /// tree keeps its grouping. We assert each canonicalizes to a term that still
    /// has the original outer op with the original (or merely binary-sorted)
    /// grouping — never collapsed across the nesting.
    #[test]
    #[allow(clippy::many_single_char_names)]
    fn non_ac_ops_are_not_flattened() {
        let mut a = TermArena::new();
        let x = a.bv_var("x", 4).unwrap();
        let y = a.bv_var("y", 4).unwrap();
        let z = a.bv_var("z", 4).unwrap();
        let p = a.bool_var("p").unwrap();
        let q = a.bool_var("q").unwrap();

        // bvnand: associative-looking grouping must be preserved (its denotation
        // depends on grouping). Canonical of nand(nand(x,y), z) must still have a
        // nand whose operand is itself a nand — i.e. NOT flattened to 3 leaves.
        let inner = a.bv_nand(x, y).unwrap();
        let outer = a.bv_nand(inner, z).unwrap();
        let canon = canonicalize(&mut a, outer).unwrap().term;
        let TermNode::App {
            op: Op::BvNand,
            args,
        } = a.node(canon)
        else {
            panic!("bvnand canonical must remain a bvnand");
        };
        let has_nand_child = args
            .iter()
            .any(|&c| matches!(a.node(c), TermNode::App { op: Op::BvNand, .. }));
        assert!(has_nand_child, "bvnand must not be AC-flattened");

        // bvnor likewise.
        let inner = a.bv_nor(x, y).unwrap();
        let outer = a.bv_nor(inner, z).unwrap();
        let canon = canonicalize(&mut a, outer).unwrap().term;
        let TermNode::App {
            op: Op::BvNor,
            args,
        } = a.node(canon)
        else {
            panic!("bvnor canonical must remain a bvnor");
        };
        assert!(
            args.iter()
                .any(|&c| matches!(a.node(c), TermNode::App { op: Op::BvNor, .. })),
            "bvnor must not be AC-flattened"
        );

        // Eq-nesting: (= (= p q) (= q p)) — Eq is commutative-only. The two inner
        // equalities canonicalize equal, so `=` reflexivity folds to true, but the
        // point is the OUTER `=` is never AC-flattened into a 3-way structure.
        let eq_pq = a.eq(p, q).unwrap();
        let eq_qp = a.eq(q, p).unwrap();
        let bool_eq = a.eq(eq_pq, eq_qp).unwrap();
        let canon = canonicalize(&mut a, bool_eq).unwrap().term;
        assert_eq!(
            canon,
            a.bool_const(true),
            "(= (= p q) (= q p)) folds to true"
        );

        // bvsub: non-commutative, nested grouping must be untouched.
        let sub_inner = a.bv_sub(x, y).unwrap();
        let sub_outer = a.bv_sub(sub_inner, z).unwrap();
        assert_eq!(canonicalize(&mut a, sub_outer).unwrap().term, sub_outer);

        // A comparison is not AC-flattenable (Bool result, non-commutative).
        let ult = a.bv_ult(x, y).unwrap();
        assert_eq!(canonicalize(&mut a, ult).unwrap().term, ult);

        // concat is non-commutative; nesting preserved.
        let cc_inner = a.concat(x, y).unwrap();
        let cc_outer = a.concat(cc_inner, z).unwrap();
        assert_eq!(canonicalize(&mut a, cc_outer).unwrap().term, cc_outer);

        // Uninterpreted apply argument order/grouping is meaningful.
        let f = a
            .declare_fun("f", &[Sort::BitVec(4), Sort::BitVec(4)], Sort::BitVec(4))
            .unwrap();
        let fxy = a.apply(f, &[x, y]).unwrap();
        assert_eq!(canonicalize(&mut a, fxy).unwrap().term, fxy);
    }

    /// `bvnot(bvnot x)` cancels to `x`; a triple `bvnot` collapses to a single
    /// `bvnot`; a lone `bvnot x` is left untouched.
    #[test]
    fn bv_double_not_involution() {
        let mut a = TermArena::new();
        let x = a.bv_var("x", 4).unwrap();

        let not_x = a.bv_not(x).unwrap();
        let not_not_x = a.bv_not(not_x).unwrap();
        assert_eq!(canonicalize(&mut a, not_not_x).unwrap().term, x);

        let not_not_not_x = a.bv_not(not_not_x).unwrap();
        assert_eq!(canonicalize(&mut a, not_not_not_x).unwrap().term, not_x);

        // A single complement is not rewritten.
        assert_eq!(canonicalize(&mut a, not_x).unwrap().term, not_x);
    }

    /// `bvneg(bvneg x)` cancels to `x`; a triple `bvneg` collapses to a single
    /// `bvneg`; a lone `bvneg x` is left untouched.
    #[test]
    fn bv_double_neg_involution() {
        let mut a = TermArena::new();
        let x = a.bv_var("x", 4).unwrap();

        let neg_x = a.bv_neg(x).unwrap();
        let neg_neg_x = a.bv_neg(neg_x).unwrap();
        assert_eq!(canonicalize(&mut a, neg_neg_x).unwrap().term, x);

        let neg_neg_neg_x = a.bv_neg(neg_neg_x).unwrap();
        assert_eq!(canonicalize(&mut a, neg_neg_neg_x).unwrap().term, neg_x);

        // A single negation is not rewritten.
        assert_eq!(canonicalize(&mut a, neg_x).unwrap().term, neg_x);
    }

    /// The double-not/double-neg involutions preserve denotation over every
    /// 4-bit assignment, including the all-zeros, all-ones, and sign-bit-only
    /// `INT_MIN` (`1000`) overflow corner where `bvneg` is its own value.
    #[test]
    fn bv_double_involutions_preserve_denotation() {
        let mut a = TermArena::new();
        let x_sym = a.declare("x", Sort::BitVec(4)).unwrap();
        let x = a.var(x_sym);

        let not_not_x = {
            let n = a.bv_not(x).unwrap();
            a.bv_not(n).unwrap()
        };
        let neg_neg_x = {
            let n = a.bv_neg(x).unwrap();
            a.bv_neg(n).unwrap()
        };
        let terms = [not_not_x, neg_neg_x];
        let rewritten = terms
            .iter()
            .map(|&t| canonicalize(&mut a, t).unwrap().term)
            .collect::<Vec<_>>();
        // Both involutions collapse fully to `x`.
        assert!(rewritten.iter().all(|&t| t == x));

        for xv in 0..16u128 {
            let mut asg = Assignment::new();
            asg.set(
                x_sym,
                Value::Bv {
                    width: 4,
                    value: xv,
                },
            );
            for (&orig, &canon) in terms.iter().zip(&rewritten) {
                assert_eq!(
                    eval(&a, orig, &asg).unwrap(),
                    eval(&a, canon, &asg).unwrap(),
                    "double involution changed denotation at x = {xv}",
                );
            }
        }

        // Explicit INT_MIN corner: bvneg(bvneg 0b1000) == 0b1000.
        let mut asg = Assignment::new();
        asg.set(
            x_sym,
            Value::Bv {
                width: 4,
                value: 0b1000,
            },
        );
        assert_eq!(
            eval(&a, neg_neg_x, &asg).unwrap(),
            Value::Bv {
                width: 4,
                value: 0b1000,
            },
        );
    }

    /// All eight BV comparison ops applied to structurally identical operands
    /// fold to the right Boolean constant: `false` for the strict orderings and
    /// `true` for the non-strict ones.
    #[test]
    fn bv_compare_reflexive_folds_all_eight() {
        let mut a = TermArena::new();
        let x = a.bv_var("x", 4).unwrap();
        let truth = a.bool_const(true);
        let falsity = a.bool_const(false);

        // (builder, expected folded constant).
        let strict: [fn(&mut TermArena, TermId, TermId) -> TermId; 4] = [
            |a, l, r| a.bv_ult(l, r).unwrap(),
            |a, l, r| a.bv_ugt(l, r).unwrap(),
            |a, l, r| a.bv_slt(l, r).unwrap(),
            |a, l, r| a.bv_sgt(l, r).unwrap(),
        ];
        for case in strict {
            let cmp = case(&mut a, x, x);
            assert_eq!(
                canonicalize(&mut a, cmp).unwrap().term,
                falsity,
                "strict `x ⋈ x` must fold to false",
            );
        }

        let non_strict: [fn(&mut TermArena, TermId, TermId) -> TermId; 4] = [
            |a, l, r| a.bv_ule(l, r).unwrap(),
            |a, l, r| a.bv_uge(l, r).unwrap(),
            |a, l, r| a.bv_sle(l, r).unwrap(),
            |a, l, r| a.bv_sge(l, r).unwrap(),
        ];
        for case in non_strict {
            let cmp = case(&mut a, x, x);
            assert_eq!(
                canonicalize(&mut a, cmp).unwrap().term,
                truth,
                "non-strict `x ⋈ x` must fold to true",
            );
        }
    }

    /// `(ite c true false)` collapses to the condition `c`; a non-`true`/`false`
    /// branch pair is left alone.
    #[test]
    #[allow(clippy::many_single_char_names)]
    fn ite_bool_identity_collapses_to_condition() {
        let mut a = TermArena::new();
        let c = a.bool_var("c").unwrap();
        let t = a.bool_const(true);
        let f = a.bool_const(false);
        let ite = a.ite(c, t, f).unwrap();
        assert_eq!(
            canonicalize(&mut a, ite).unwrap().term,
            c,
            "`(ite c true false)` is just `c`",
        );

        // Branches that are not exactly true/false do not fold to the condition.
        let p = a.bool_var("p").unwrap();
        let ite2 = a.ite(c, t, p).unwrap();
        assert_ne!(
            canonicalize(&mut a, ite2).unwrap().term,
            c,
            "`(ite c true p)` must not collapse to `c`",
        );
    }

    /// `(= p true)` and `(= true p)` collapse to `p`; `(= p false)` to `(not p)`; a
    /// bit-vector equality with a constant is NOT affected.
    #[test]
    #[allow(clippy::many_single_char_names, clippy::similar_names)]
    fn eq_with_boolean_constant_simplifies() {
        let mut a = TermArena::new();
        let p = a.bool_var("p").unwrap();
        let t = a.bool_const(true);
        let f = a.bool_const(false);
        let not_p = a.not(p).unwrap();

        let eq_pt = a.eq(p, t).unwrap();
        let eq_tp = a.eq(t, p).unwrap();
        let eq_pf = a.eq(p, f).unwrap();
        assert_eq!(canonicalize(&mut a, eq_pt).unwrap().term, p);
        assert_eq!(canonicalize(&mut a, eq_tp).unwrap().term, p);
        assert_eq!(canonicalize(&mut a, eq_pf).unwrap().term, not_p);

        // A bit-vector `=` with a constant is a predicate, not simplified to the var.
        let x = a.bv_var("x", 4).unwrap();
        let five = a.bv_const(4, 5).unwrap();
        let bv_eq = a.eq(x, five).unwrap();
        assert_eq!(
            canonicalize(&mut a, bv_eq).unwrap().term,
            bv_eq,
            "bit-vector equality with a constant must not be rewritten",
        );

        // Denotation: (= q true) ≡ q and (= q false) ≡ ¬q over both Boolean values.
        let qs = a.declare("q", Sort::Bool).unwrap();
        let q = a.var(qs);
        let q_true = a.eq(q, t).unwrap();
        let q_false = a.eq(q, f).unwrap();
        let q_true_c = canonicalize(&mut a, q_true).unwrap().term;
        let q_false_c = canonicalize(&mut a, q_false).unwrap().term;
        for b in [false, true] {
            let mut asg = Assignment::new();
            asg.set(qs, Value::Bool(b));
            assert_eq!(
                eval(&a, q_true, &asg).unwrap(),
                eval(&a, q_true_c, &asg).unwrap(),
            );
            assert_eq!(
                eval(&a, q_false, &asg).unwrap(),
                eval(&a, q_false_c, &asg).unwrap(),
            );
        }
    }

    /// Array select folds: read-over-write at the same index, and select of a
    /// constant array, both return the stored/constant value; a read at a
    /// *different* (non-identical) index is left alone.
    #[test]
    #[allow(clippy::many_single_char_names)]
    fn array_select_folds() {
        let mut a = TermArena::new();
        let arr = a.array_var("arr", 4, 8).unwrap();
        let i = a.bv_var("i", 4).unwrap();
        let j = a.bv_var("j", 4).unwrap();
        let v = a.bv_var("v", 8).unwrap();

        // (select (store arr i v) i) -> v
        let stored = a.store(arr, i, v).unwrap();
        let sel_same = a.select(stored, i).unwrap();
        assert_eq!(canonicalize(&mut a, sel_same).unwrap().term, v);

        // (select (store arr i v) j) with j != i (different TermId) is NOT folded.
        let sel_other = a.select(stored, j).unwrap();
        assert_eq!(canonicalize(&mut a, sel_other).unwrap().term, sel_other);

        // (select (const-array v) j) -> v for any index.
        let ca = a.const_array(4, v).unwrap();
        let sel_const = a.select(ca, j).unwrap();
        assert_eq!(canonicalize(&mut a, sel_const).unwrap().term, v);
    }

    /// A comparison of two *different* operands is never folded by reflexivity.
    #[test]
    fn bv_compare_reflexive_ignores_distinct_operands() {
        let mut a = TermArena::new();
        let x = a.bv_var("x", 4).unwrap();
        let y = a.bv_var("y", 4).unwrap();
        let ult = a.bv_ult(x, y).unwrap();
        assert_eq!(canonicalize(&mut a, ult).unwrap().term, ult);
    }

    /// Unsigned comparison saturation against 0 / all-ones folds the tautologies and
    /// contradictions, and — crucially — leaves the non-extreme directions alone.
    #[test]
    #[allow(clippy::many_single_char_names)]
    fn bv_compare_saturation_folds_only_the_extremes() {
        let mut a = TermArena::new();
        let x = a.bv_var("x", 4).unwrap();
        let y = a.bv_var("y", 4).unwrap();
        let zero = a.bv_const(4, 0).unwrap();
        let ones = a.bv_const(4, 15).unwrap();
        let f = a.bool_const(false);
        let t = a.bool_const(true);

        // (comparison term, expected folded constant).
        let folds: [(TermId, TermId); 8] = [
            (a.bv_ult(x, zero).unwrap(), f), // x < 0 -> false
            (a.bv_ule(x, ones).unwrap(), t), // x <= MAX -> true
            (a.bv_ugt(x, ones).unwrap(), f), // x > MAX -> false
            (a.bv_uge(x, zero).unwrap(), t), // x >= 0 -> true
            (a.bv_ult(ones, y).unwrap(), f), // MAX < y -> false
            (a.bv_ule(zero, y).unwrap(), t), // 0 <= y -> true
            (a.bv_ugt(zero, y).unwrap(), f), // 0 > y -> false
            (a.bv_uge(ones, y).unwrap(), t), // MAX >= y -> true
        ];
        for (cmp, expected) in folds {
            assert_eq!(canonicalize(&mut a, cmp).unwrap().term, expected);
        }

        // Must NOT fold (genuine non-tautologies + a signed case + no extreme const).
        let not_folded: [TermId; 4] = [
            a.bv_ult(x, ones).unwrap(), // x < MAX: false only when x == MAX
            a.bv_ule(x, zero).unwrap(), // x <= 0: true only when x == 0
            a.bv_slt(x, zero).unwrap(), // signed: not handled (extremes differ)
            a.bv_ult(x, y).unwrap(),    // no extreme constant
        ];
        for cmp in not_folded {
            assert_eq!(
                canonicalize(&mut a, cmp).unwrap().term,
                cmp,
                "non-extreme comparison must not be saturated",
            );
        }
    }

    /// Exhaustive denotation gate: each saturation fold must match the original
    /// comparison at every 4-bit value of `x`.
    #[test]
    fn bv_compare_saturation_preserves_denotation() {
        let mut a = TermArena::new();
        let x_sym = a.declare("x", Sort::BitVec(4)).unwrap();
        let x = a.var(x_sym);
        let zero = a.bv_const(4, 0).unwrap();
        let ones = a.bv_const(4, 15).unwrap();

        let cases: [(TermId, bool); 4] = [
            (a.bv_ult(x, zero).unwrap(), false),
            (a.bv_ule(x, ones).unwrap(), true),
            (a.bv_ugt(x, ones).unwrap(), false),
            (a.bv_uge(x, zero).unwrap(), true),
        ];
        for (cmp, expected) in cases {
            for v in 0..16u128 {
                let mut asg = Assignment::new();
                asg.set(x_sym, Value::Bv { width: 4, value: v });
                assert_eq!(
                    eval(&a, cmp, &asg).unwrap(),
                    Value::Bool(expected),
                    "saturation fold must match the comparison at every value",
                );
            }
        }
    }

    /// Denotation cross-check: for a few comparison ops (including a signed one),
    /// the folded constant equals the original comparison evaluated at every
    /// 4-bit value of `x` — covering signed and unsigned semantics, including the
    /// sign-bit-set range where signed/unsigned ordering diverge.
    #[test]
    fn bv_compare_reflexive_preserves_denotation() {
        let mut a = TermArena::new();
        let x_sym = a.declare("x", Sort::BitVec(4)).unwrap();
        let x = a.var(x_sym);

        // Unsigned strict, unsigned non-strict, signed strict, signed non-strict.
        let ult = a.bv_ult(x, x).unwrap();
        let uge = a.bv_uge(x, x).unwrap();
        let slt = a.bv_slt(x, x).unwrap();
        let sle = a.bv_sle(x, x).unwrap();
        let terms = [ult, uge, slt, sle];
        let rewritten = terms
            .iter()
            .map(|&t| canonicalize(&mut a, t).unwrap().term)
            .collect::<Vec<_>>();

        for xv in 0..16u128 {
            let mut asg = Assignment::new();
            asg.set(
                x_sym,
                Value::Bv {
                    width: 4,
                    value: xv,
                },
            );
            for (&orig, &canon) in terms.iter().zip(&rewritten) {
                assert_eq!(
                    eval(&a, orig, &asg).unwrap(),
                    eval(&a, canon, &asg).unwrap(),
                    "compare reflexivity changed denotation at x = {xv}",
                );
            }
        }
    }

    /// `bvmul x 2^k` strength-reduces to `bvshl x k`, regardless of which side
    /// the power-of-two constant sits on.
    #[test]
    #[allow(clippy::many_single_char_names)]
    fn bv_mul_pow2_strength_reduces_left_shift() {
        let mut a = TermArena::new();
        let x = a.bv_var("x", 8).unwrap();
        let four = a.bv_const(8, 4).unwrap();
        let two = a.bv_const(8, 2).unwrap();
        let expected = a.bv_shl(x, two).unwrap();

        // Constant on the right.
        let mul_right = a.bv_mul(x, four).unwrap();
        assert_eq!(canonicalize(&mut a, mul_right).unwrap().term, expected);

        // Constant on the left.
        let mul_left = a.bv_mul(four, x).unwrap();
        assert_eq!(canonicalize(&mut a, mul_left).unwrap().term, expected);
    }

    /// `bvmul x 4` and its canonical `bvshl x 2` agree under every 4-bit value
    /// of `x`, including the high-bit wraparound cases where the product
    /// overflows the width.
    #[test]
    fn bv_mul_pow2_preserves_denotation() {
        let mut a = TermArena::new();
        let x_sym = a.declare("x", Sort::BitVec(4)).unwrap();
        let x = a.var(x_sym);
        let four = a.bv_const(4, 4).unwrap();
        let mul = a.bv_mul(x, four).unwrap();
        let canon = canonicalize(&mut a, mul).unwrap().term;

        // It actually strength-reduced to a left shift by 2.
        let two = a.bv_const(4, 2).unwrap();
        let expected = a.bv_shl(x, two).unwrap();
        assert_eq!(canon, expected);

        for xv in 0..16u128 {
            let mut asg = Assignment::new();
            asg.set(
                x_sym,
                Value::Bv {
                    width: 4,
                    value: xv,
                },
            );
            assert_eq!(
                eval(&a, mul, &asg).unwrap(),
                eval(&a, canon, &asg).unwrap(),
                "mul-by-power-of-two changed denotation at x = {xv}",
            );
        }
    }

    /// Negatives: non-power-of-two and constant-free multiplies are not
    /// strength-reduced; `*1` and `*0` still go to their existing identities.
    #[test]
    #[allow(clippy::many_single_char_names)]
    fn bv_mul_pow2_negatives() {
        let mut a = TermArena::new();
        let x = a.bv_var("x", 8).unwrap();
        let y = a.bv_var("y", 8).unwrap();
        let three = a.bv_const(8, 3).unwrap();
        let one = a.bv_const(8, 1).unwrap();
        let zero = a.bv_const(8, 0).unwrap();

        // Non-power-of-two: unchanged (still a bvmul).
        let mul_three = a.bv_mul(x, three).unwrap();
        let canon_three = canonicalize(&mut a, mul_three).unwrap().term;
        assert!(matches!(
            a.node(canon_three),
            TermNode::App { op: Op::BvMul, .. }
        ));

        // No constant operand: unchanged (still a bvmul).
        let mul_xy = a.bv_mul(x, y).unwrap();
        let canon_xy = canonicalize(&mut a, mul_xy).unwrap().term;
        assert!(matches!(
            a.node(canon_xy),
            TermNode::App { op: Op::BvMul, .. }
        ));

        // `* 1` still folds to `x` via bv.mul_one.v1, not a shift.
        let mul_one = a.bv_mul(x, one).unwrap();
        assert_eq!(canonicalize(&mut a, mul_one).unwrap().term, x);

        // `* 0` still folds to `0` via bv.mul_zero.v1.
        let mul_zero = a.bv_mul(x, zero).unwrap();
        assert_eq!(canonicalize(&mut a, mul_zero).unwrap().term, zero);
    }

    /// `bvudiv x 8` (width 8) strength-reduces to `bvlshr x 3`, and `bvurem x 8`
    /// to `bvand x 7`.
    #[test]
    #[allow(clippy::many_single_char_names)]
    fn bv_udiv_urem_pow2_strength_reduce() {
        let mut a = TermArena::new();
        let x = a.bv_var("x", 8).unwrap();
        let eight = a.bv_const(8, 8).unwrap();

        let three = a.bv_const(8, 3).unwrap();
        let expected_div = a.bv_lshr(x, three).unwrap();
        let udiv = a.bv_udiv(x, eight).unwrap();
        assert_eq!(canonicalize(&mut a, udiv).unwrap().term, expected_div);

        let seven = a.bv_const(8, 7).unwrap();
        let expected_rem = a.bv_and(x, seven).unwrap();
        let urem = a.bv_urem(x, eight).unwrap();
        assert_eq!(canonicalize(&mut a, urem).unwrap().term, expected_rem);
    }

    /// Exhaustive denotation check over all 4-bit `x` (including high-bit-set
    /// values): `bvudiv x 4 ≡ bvlshr x 2` and `bvurem x 4 ≡ bvand x 3`.
    #[test]
    fn bv_udiv_urem_pow2_preserve_denotation() {
        let mut a = TermArena::new();
        let x_sym = a.declare("x", Sort::BitVec(4)).unwrap();
        let x = a.var(x_sym);
        let four = a.bv_const(4, 4).unwrap();

        let udiv = a.bv_udiv(x, four).unwrap();
        let canon_div = canonicalize(&mut a, udiv).unwrap().term;
        let two = a.bv_const(4, 2).unwrap();
        let expected_div = a.bv_lshr(x, two).unwrap();
        assert_eq!(canon_div, expected_div);

        let urem = a.bv_urem(x, four).unwrap();
        let canon_rem = canonicalize(&mut a, urem).unwrap().term;
        let three = a.bv_const(4, 3).unwrap();
        let expected_rem = a.bv_and(x, three).unwrap();
        assert_eq!(canon_rem, expected_rem);

        for xv in 0..16u128 {
            let mut asg = Assignment::new();
            asg.set(
                x_sym,
                Value::Bv {
                    width: 4,
                    value: xv,
                },
            );
            assert_eq!(
                eval(&a, udiv, &asg).unwrap(),
                eval(&a, canon_div, &asg).unwrap(),
                "bvudiv-by-power-of-two changed denotation at x = {xv}",
            );
            assert_eq!(
                eval(&a, urem, &asg).unwrap(),
                eval(&a, canon_rem, &asg).unwrap(),
                "bvurem-by-power-of-two changed denotation at x = {xv}",
            );
        }
    }

    /// Soundness guards: only the UNSIGNED ops with a power-of-two **divisor**
    /// reduce. A non-power-of-two divisor, a power-of-two **dividend** (variable
    /// divisor), and the signed div/rem family are all left unchanged.
    #[test]
    #[allow(clippy::many_single_char_names)]
    fn bv_udiv_urem_pow2_negatives() {
        let mut a = TermArena::new();
        let x = a.bv_var("x", 8).unwrap();
        let three = a.bv_const(8, 3).unwrap();
        let eight = a.bv_const(8, 8).unwrap();
        let four = a.bv_const(8, 4).unwrap();

        // Non-power-of-two divisor: unchanged.
        let udiv_three = a.bv_udiv(x, three).unwrap();
        let canon = canonicalize(&mut a, udiv_three).unwrap().term;
        assert!(matches!(
            a.node(canon),
            TermNode::App { op: Op::BvUdiv, .. }
        ));

        // Power-of-two DIVIDEND, variable divisor: not reduced (only args[1] fires).
        let udiv_const_dividend = a.bv_udiv(eight, x).unwrap();
        let canon = canonicalize(&mut a, udiv_const_dividend).unwrap().term;
        assert!(matches!(
            a.node(canon),
            TermNode::App { op: Op::BvUdiv, .. }
        ));
        let urem_const_first = a.bv_urem(eight, x).unwrap();
        let canon = canonicalize(&mut a, urem_const_first).unwrap().term;
        assert!(matches!(
            a.node(canon),
            TermNode::App { op: Op::BvUrem, .. }
        ));

        // Signed div/rem by a power of two: NOT reduced (unsound shift), stays signed.
        let sdiv = a.bv_sdiv(x, four).unwrap();
        let canon = canonicalize(&mut a, sdiv).unwrap().term;
        assert!(matches!(
            a.node(canon),
            TermNode::App { op: Op::BvSdiv, .. }
        ));
        let srem = a.bv_srem(x, four).unwrap();
        let canon = canonicalize(&mut a, srem).unwrap().term;
        assert!(matches!(
            a.node(canon),
            TermNode::App { op: Op::BvSrem, .. }
        ));
    }

    /// `extract` whose range lies entirely in the low part `b` of `(concat a b)`
    /// rewrites to `extract` of `b` directly; entirely in the high part `a`
    /// rewrites to `extract` of `a` with both indices shifted down by `width(b)`;
    /// a straddling range is left unchanged.
    #[test]
    #[allow(clippy::many_single_char_names)]
    fn extract_of_concat_slice_selection() {
        let mut a = TermArena::new();
        let hi_term = a.bv_var("a", 4).unwrap();
        let lo_term = a.bv_var("b", 4).unwrap();
        // concat(a, b): a is the high 4 bits (4..8), b is the low 4 bits (0..4).
        let concat = a.concat(hi_term, lo_term).unwrap();

        // Low part: extract(2, 0, concat) -> extract(2, 0, b).
        let low = a.extract(2, 0, concat).unwrap();
        let expected_low = a.extract(2, 0, lo_term).unwrap();
        assert_eq!(canonicalize(&mut a, low).unwrap().term, expected_low);

        // High part: extract(6, 4, concat) -> extract(2, 0, a).
        let high = a.extract(6, 4, concat).unwrap();
        let expected_high = a.extract(2, 0, hi_term).unwrap();
        assert_eq!(canonicalize(&mut a, high).unwrap().term, expected_high);

        // Straddle: extract(5, 2, concat) crosses bit 4 and is NOT rewritten.
        let straddle = a.extract(5, 2, concat).unwrap();
        let canon = canonicalize(&mut a, straddle).unwrap().term;
        assert!(matches!(
            a.node(canon),
            TermNode::App {
                op: Op::Extract { hi: 5, lo: 2 },
                ..
            }
        ));
    }

    /// Exhaustive denotation check: for width-3 `a` and `b` (concat width 6),
    /// `extract(hi, lo, concat(a, b))` equals its rewritten form over ALL 64
    /// assignments of `(a, b)`. Covers a low-part range (in `b`) and a high-part
    /// range (in `a`, where the `- wb` index subtraction matters).
    #[test]
    #[allow(clippy::many_single_char_names)]
    fn extract_of_concat_preserves_denotation() {
        let mut a = TermArena::new();
        let a_sym = a.declare("a", Sort::BitVec(3)).unwrap();
        let b_sym = a.declare("b", Sort::BitVec(3)).unwrap();
        let a_term = a.var(a_sym);
        let b_term = a.var(b_sym);
        let concat = a.concat(a_term, b_term).unwrap();

        // Low-part range entirely in `b` (bits 0..3): extract(2, 1, concat).
        let low = a.extract(2, 1, concat).unwrap();
        let canon_low = canonicalize(&mut a, low).unwrap().term;
        let expected_low = a.extract(2, 1, b_term).unwrap();
        assert_eq!(canon_low, expected_low);

        // High-part range entirely in `a` (bits 3..6): extract(5, 4, concat).
        // The rewrite subtracts wb = 3 from both indices -> extract(2, 1, a).
        let high = a.extract(5, 4, concat).unwrap();
        let canon_high = canonicalize(&mut a, high).unwrap().term;
        let expected_high = a.extract(2, 1, a_term).unwrap();
        assert_eq!(canon_high, expected_high);

        for av in 0..8u128 {
            for bv in 0..8u128 {
                let mut asg = Assignment::new();
                asg.set(
                    a_sym,
                    Value::Bv {
                        width: 3,
                        value: av,
                    },
                );
                asg.set(
                    b_sym,
                    Value::Bv {
                        width: 3,
                        value: bv,
                    },
                );
                assert_eq!(
                    eval(&a, low, &asg).unwrap(),
                    eval(&a, canon_low, &asg).unwrap(),
                    "extract-of-concat (low part) changed denotation at a={av}, b={bv}",
                );
                assert_eq!(
                    eval(&a, high, &asg).unwrap(),
                    eval(&a, canon_high, &asg).unwrap(),
                    "extract-of-concat (high part) changed denotation at a={av}, b={bv}",
                );
            }
        }
    }

    /// `extract` whose high index lies strictly below the original width of a
    /// `zero_extend`/`sign_extend` rewrites to the same `extract` over the
    /// pre-extension term; a range reaching the extended bits is left unchanged.
    #[test]
    #[allow(clippy::many_single_char_names, clippy::similar_names)]
    fn extract_within_extend_original_bits() {
        let mut a = TermArena::new();
        let x = a.bv_var("x", 4).unwrap();
        let zext = a.zero_ext(4, x).unwrap();
        let sext = a.sign_ext(4, x).unwrap();

        // hi = 2 < width(x) = 4: drop the zero_extend.
        let from_zext = a.extract(2, 0, zext).unwrap();
        let expected = a.extract(2, 0, x).unwrap();
        assert_eq!(canonicalize(&mut a, from_zext).unwrap().term, expected);

        // Same for sign_extend (low bits are identical to x's).
        let from_sext = a.extract(2, 0, sext).unwrap();
        assert_eq!(canonicalize(&mut a, from_sext).unwrap().term, expected);

        // hi = 5 >= width(x) = 4: range touches the extended bits, NOT rewritten.
        let touches_ext = a.extract(5, 0, zext).unwrap();
        let canon = canonicalize(&mut a, touches_ext).unwrap().term;
        assert!(matches!(
            a.node(canon),
            TermNode::App {
                op: Op::Extract { hi: 5, lo: 0 },
                ..
            }
        ));
    }

    /// Exhaustive denotation check: over all 16 values of a 4-bit `x`,
    /// `extract(2, 0, zero_extend(4, x))` and `extract(2, 0, sign_extend(4, x))`
    /// both equal `extract(2, 0, x)`.
    #[test]
    #[allow(clippy::many_single_char_names, clippy::similar_names)]
    fn extract_within_extend_preserves_denotation() {
        let mut a = TermArena::new();
        let x_sym = a.declare("x", Sort::BitVec(4)).unwrap();
        let x = a.var(x_sym);
        let zext = a.zero_ext(4, x).unwrap();
        let sext = a.sign_ext(4, x).unwrap();

        let from_zext = a.extract(2, 0, zext).unwrap();
        let from_sext = a.extract(2, 0, sext).unwrap();
        let canon_zext = canonicalize(&mut a, from_zext).unwrap().term;
        let canon_sext = canonicalize(&mut a, from_sext).unwrap().term;
        let expected = a.extract(2, 0, x).unwrap();
        assert_eq!(canon_zext, expected);
        assert_eq!(canon_sext, expected);

        for xv in 0..16u128 {
            let mut asg = Assignment::new();
            asg.set(
                x_sym,
                Value::Bv {
                    width: 4,
                    value: xv,
                },
            );
            assert_eq!(
                eval(&a, from_zext, &asg).unwrap(),
                eval(&a, canon_zext, &asg).unwrap(),
                "extract-within-zero_extend changed denotation at x={xv}",
            );
            assert_eq!(
                eval(&a, from_sext, &asg).unwrap(),
                eval(&a, canon_sext, &asg).unwrap(),
                "extract-within-sign_extend changed denotation at x={xv}",
            );
        }
    }

    /// `concat` of two adjacent extracts (`lo1 == hi2 + 1`) of the same term
    /// reassembles into one `extract`; a gap, or different inner terms, is left
    /// unchanged.
    #[test]
    #[allow(clippy::many_single_char_names)]
    fn concat_of_adjacent_extracts_reassembled() {
        let mut a = TermArena::new();
        let x = a.bv_var("x", 6).unwrap();
        let y = a.bv_var("y", 6).unwrap();

        // Adjacent: extract(5,3,x) over extract(2,0,x), lo1=3 == hi2+1=3.
        let high = a.extract(5, 3, x).unwrap();
        let low = a.extract(2, 0, x).unwrap();
        let concat = a.concat(high, low).unwrap();
        let expected = a.extract(5, 0, x).unwrap();
        assert_eq!(canonicalize(&mut a, concat).unwrap().term, expected);

        // Gap: extract(5,4,x) over extract(2,0,x), lo1=4 != hi2+1=3. NOT rewritten.
        let high_gap = a.extract(5, 4, x).unwrap();
        let concat_gap = a.concat(high_gap, low).unwrap();
        let canon_gap = canonicalize(&mut a, concat_gap).unwrap().term;
        assert!(matches!(
            a.node(canon_gap),
            TermNode::App { op: Op::Concat, .. }
        ));

        // Different inner terms: extract(5,3,x) over extract(2,0,y). NOT rewritten.
        let low_other = a.extract(2, 0, y).unwrap();
        let concat_other = a.concat(high, low_other).unwrap();
        let canon_other = canonicalize(&mut a, concat_other).unwrap().term;
        assert!(matches!(
            a.node(canon_other),
            TermNode::App { op: Op::Concat, .. }
        ));
    }

    /// Exhaustive denotation check: over all 64 values of a 6-bit `x`,
    /// `concat(extract(5,3,x), extract(2,0,x))` equals its reassembled form
    /// `extract(5,0,x)` (which is the whole `x`).
    #[test]
    #[allow(clippy::many_single_char_names)]
    fn concat_of_adjacent_extracts_preserves_denotation() {
        let mut a = TermArena::new();
        let x_sym = a.declare("x", Sort::BitVec(6)).unwrap();
        let x = a.var(x_sym);
        let high = a.extract(5, 3, x).unwrap();
        let low = a.extract(2, 0, x).unwrap();
        let concat = a.concat(high, low).unwrap();
        let canon = canonicalize(&mut a, concat).unwrap().term;
        let expected = a.extract(5, 0, x).unwrap();
        assert_eq!(canon, expected);

        for xv in 0..64u128 {
            let mut asg = Assignment::new();
            asg.set(
                x_sym,
                Value::Bv {
                    width: 6,
                    value: xv,
                },
            );
            assert_eq!(
                eval(&a, concat, &asg).unwrap(),
                eval(&a, canon, &asg).unwrap(),
                "concat-of-adjacent-extracts changed denotation at x={xv}",
            );
        }
    }
}
