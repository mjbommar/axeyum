//! Rewrite contracts and canonicalization for Axeyum.
//!
//! Every rule has an ID, precondition, preservation classification, projection
//! obligation, and test route from the start. The default Phase 3
//! canonicalizer enables only denotation-preserving rules, so model projection
//! remains identity until a later equisatisfiability layer explicitly provides
//! projection and replay.

use std::collections::BTreeSet;

mod arrays;
mod canonical;
mod datatypes;
mod elim_unconstrained;
mod functions;
mod int_blast;
mod int_divmod;
mod lower_bv;
mod propagate_values;
mod quantifiers;
mod reconstruct;
mod solve_eqs;

pub use arrays::{ArrayElimError, ArrayElimination, eliminate_arrays};
pub use canonical::{
    CanonicalizeOutcome, CanonicalizeTermsOutcome, Canonicalizer, RewriteError, RewriteReport,
    RuleApplication, build_app, canonicalize, canonicalize_terms, default_manifest,
    replace_subterms,
};
pub use datatypes::simplify_datatypes;
pub use elim_unconstrained::{UnconstrainedElimination, elim_unconstrained};
pub use functions::{FuncElimError, FunctionElimination, eliminate_functions};
pub use int_blast::{IntBlastError, IntBlasting, MAX_INT_BLAST_WIDTH, blast_integers};
pub use int_divmod::eliminate_int_divmod;
pub use lower_bv::lower_derived_bv;
pub use propagate_values::{ValuePropagation, propagate_values};
pub use quantifiers::{
    Instantiation, QUANT_EXPAND_BIT_LIMIT, QuantExpandError, expand_quantifiers,
    instantiate_universals, instantiate_with_triggers,
};
pub use reconstruct::ModelReconstructionTrail;
pub use solve_eqs::{EqSolution, solve_eqs};

/// Stable rewrite rule identifier used in logs and future certificates.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct RewriteRuleId(String);

impl RewriteRuleId {
    /// Creates a rule ID.
    ///
    /// IDs are restricted to lowercase ASCII letters, digits, `.`, `_`, and
    /// `-`, so they are stable in logs and artifact paths.
    ///
    /// # Errors
    ///
    /// Returns [`ManifestError::InvalidRuleId`] when `id` is empty or contains
    /// a disallowed character.
    pub fn new(id: &str) -> Result<Self, ManifestError> {
        let valid = !id.is_empty()
            && id.bytes().all(|b| {
                b.is_ascii_lowercase() || b.is_ascii_digit() || matches!(b, b'.' | b'_' | b'-')
            });
        if valid {
            Ok(Self(id.to_owned()))
        } else {
            Err(ManifestError::InvalidRuleId(id.to_owned()))
        }
    }

    /// Returns the rule ID as text.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// Semantic strength of a rewrite rule.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Preservation {
    /// Output term has exactly the same value as input term for every model.
    Denotation,
    /// Output query is equisatisfiable but may need model projection.
    Equisatisfiable,
}

/// Model-projection obligation introduced by a rewrite.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModelProjection {
    /// No projection is needed because the original model is preserved.
    Identity,
    /// Projection is required but not yet implemented; rule must remain off by default.
    Required {
        /// Human-readable projection obligation.
        description: String,
    },
    /// Projection is implemented and must be tested before default enablement.
    Implemented {
        /// Human-readable projection route.
        description: String,
    },
}

/// Required validation route for a rewrite rule.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RewriteTestRoute {
    /// Exhaust all inputs for small widths.
    ExhaustiveSmallWidth,
    /// Random evaluator equivalence over generated terms and assignments.
    RandomEvaluator,
    /// Oracle check against an SMT backend.
    OracleDifferential,
    /// Model-projection replay test for non-denotational rewrites.
    ModelProjectionReplay,
    /// Future proof obligation checked outside the rewriter.
    ProofObligation,
}

/// Metadata for one rewrite rule.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RewriteRule {
    /// Stable rule ID.
    pub id: RewriteRuleId,
    /// Human-readable rule name.
    pub name: String,
    /// Sort/width/operator precondition.
    pub precondition: String,
    /// Preservation class.
    pub preservation: Preservation,
    /// Model projection requirement.
    pub projection: ModelProjection,
    /// Validation routes required for this rule.
    pub tests: Vec<RewriteTestRoute>,
    /// Whether the rule is allowed in the default canonicalizer.
    pub enabled_by_default: bool,
}

/// Checked collection of rewrite metadata.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RewriteManifest {
    rules: Vec<RewriteRule>,
}

impl RewriteManifest {
    /// Creates and validates a manifest.
    ///
    /// # Errors
    ///
    /// Returns [`ManifestError`] if rule IDs duplicate, a rule has no
    /// precondition or test route, or a non-denotational default rule lacks
    /// implemented projection and replay tests.
    pub fn new(rules: Vec<RewriteRule>) -> Result<Self, ManifestError> {
        validate_rules(&rules)?;
        Ok(Self { rules })
    }

    /// Returns all rules in stable manifest order.
    pub fn rules(&self) -> &[RewriteRule] {
        &self.rules
    }

    /// Iterates over rules enabled in the default canonicalizer.
    pub fn enabled_rules(&self) -> impl Iterator<Item = &RewriteRule> {
        self.rules.iter().filter(|rule| rule.enabled_by_default)
    }

    /// Returns `true` if no rules are registered.
    pub fn is_empty(&self) -> bool {
        self.rules.is_empty()
    }

    /// Number of rules in the manifest.
    pub fn len(&self) -> usize {
        self.rules.len()
    }
}

fn validate_rules(rules: &[RewriteRule]) -> Result<(), ManifestError> {
    let mut seen = BTreeSet::new();
    for rule in rules {
        if !seen.insert(rule.id.clone()) {
            return Err(ManifestError::DuplicateRuleId(rule.id.as_str().to_owned()));
        }
        if rule.precondition.trim().is_empty() {
            return Err(ManifestError::MissingPrecondition(
                rule.id.as_str().to_owned(),
            ));
        }
        if rule.tests.is_empty() {
            return Err(ManifestError::MissingTestRoute(rule.id.as_str().to_owned()));
        }
        validate_projection(rule)?;
    }
    Ok(())
}

fn validate_projection(rule: &RewriteRule) -> Result<(), ManifestError> {
    if rule.preservation == Preservation::Denotation {
        return if rule.projection == ModelProjection::Identity {
            Ok(())
        } else {
            Err(ManifestError::UnexpectedProjection(
                rule.id.as_str().to_owned(),
            ))
        };
    }

    match &rule.projection {
        ModelProjection::Identity => Err(ManifestError::MissingProjection(
            rule.id.as_str().to_owned(),
        )),
        ModelProjection::Required { .. } if rule.enabled_by_default => Err(
            ManifestError::DefaultEquisatWithoutImplementedProjection(rule.id.as_str().to_owned()),
        ),
        ModelProjection::Required { .. } => Ok(()),
        ModelProjection::Implemented { .. } => validate_default_projection_test(rule),
    }
}

fn validate_default_projection_test(rule: &RewriteRule) -> Result<(), ManifestError> {
    let has_projection_test = rule
        .tests
        .contains(&RewriteTestRoute::ModelProjectionReplay);
    if rule.enabled_by_default && !has_projection_test {
        Err(ManifestError::DefaultEquisatWithoutProjectionTest(
            rule.id.as_str().to_owned(),
        ))
    } else {
        Ok(())
    }
}

/// Manifest validation errors.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ManifestError {
    /// Rule ID is empty or contains non-stable characters.
    InvalidRuleId(String),
    /// A rule ID appears more than once.
    DuplicateRuleId(String),
    /// A rule omitted its sort/width/operator precondition.
    MissingPrecondition(String),
    /// A rule omitted its validation route.
    MissingTestRoute(String),
    /// A denotation-preserving rule declared a non-identity projection.
    UnexpectedProjection(String),
    /// An equisatisfiable rule omitted its projection obligation.
    MissingProjection(String),
    /// A default equisatisfiable rule has no implemented model projection.
    DefaultEquisatWithoutImplementedProjection(String),
    /// A default equisatisfiable rule has no projection replay test.
    DefaultEquisatWithoutProjectionTest(String),
}

impl core::fmt::Display for ManifestError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ManifestError::InvalidRuleId(id) => write!(f, "invalid rewrite rule ID `{id}`"),
            ManifestError::DuplicateRuleId(id) => write!(f, "duplicate rewrite rule ID `{id}`"),
            ManifestError::MissingPrecondition(id) => {
                write!(f, "rewrite rule `{id}` has no precondition")
            }
            ManifestError::MissingTestRoute(id) => {
                write!(f, "rewrite rule `{id}` has no test route")
            }
            ManifestError::UnexpectedProjection(id) => {
                write!(
                    f,
                    "denotation-preserving rewrite rule `{id}` has a projection"
                )
            }
            ManifestError::MissingProjection(id) => {
                write!(f, "equisatisfiable rewrite rule `{id}` has no projection")
            }
            ManifestError::DefaultEquisatWithoutImplementedProjection(id) => write!(
                f,
                "default equisatisfiable rewrite rule `{id}` has no implemented projection"
            ),
            ManifestError::DefaultEquisatWithoutProjectionTest(id) => write!(
                f,
                "default equisatisfiable rewrite rule `{id}` has no projection replay test"
            ),
        }
    }
}

impl core::error::Error for ManifestError {}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use axeyum_ir::{Assignment, Sort, TermArena, TermId, Value, eval};

    use super::{
        ManifestError, ModelProjection, Preservation, RewriteManifest, RewriteRule, RewriteRuleId,
        RewriteTestRoute, canonicalize, default_manifest,
    };

    fn denotation_rule(id: &str) -> RewriteRule {
        RewriteRule {
            id: RewriteRuleId::new(id).unwrap(),
            name: "x + 0 -> x".to_owned(),
            precondition: "operand sort is BV(w)".to_owned(),
            preservation: Preservation::Denotation,
            projection: ModelProjection::Identity,
            tests: vec![RewriteTestRoute::ExhaustiveSmallWidth],
            enabled_by_default: true,
        }
    }

    #[test]
    fn manifest_accepts_default_denotation_rule() {
        let manifest = RewriteManifest::new(vec![denotation_rule("bv.add_zero_rhs.v1")]).unwrap();

        assert_eq!(manifest.len(), 1);
        assert_eq!(manifest.enabled_rules().count(), 1);
    }

    #[test]
    fn manifest_rejects_duplicate_ids() {
        let rule = denotation_rule("bv.add_zero_rhs.v1");

        assert!(matches!(
            RewriteManifest::new(vec![rule.clone(), rule]),
            Err(ManifestError::DuplicateRuleId(_))
        ));
    }

    #[test]
    fn equisat_rules_need_projection_and_stay_off_by_default_until_tested() {
        let mut rule = denotation_rule("query.slice_unused.v1");
        rule.preservation = Preservation::Equisatisfiable;
        rule.projection = ModelProjection::Required {
            description: "lift sliced model to original query".to_owned(),
        };
        rule.enabled_by_default = false;
        assert!(RewriteManifest::new(vec![rule.clone()]).is_ok());

        rule.enabled_by_default = true;
        assert!(matches!(
            RewriteManifest::new(vec![rule]),
            Err(ManifestError::DefaultEquisatWithoutImplementedProjection(_))
        ));
    }

    #[test]
    fn default_equisat_rules_need_projection_replay_tests() {
        let mut rule = denotation_rule("query.slice_unused.v1");
        rule.preservation = Preservation::Equisatisfiable;
        rule.projection = ModelProjection::Implemented {
            description: "identity on remaining symbols plus defaults".to_owned(),
        };
        rule.enabled_by_default = true;
        assert!(matches!(
            RewriteManifest::new(vec![rule.clone()]),
            Err(ManifestError::DefaultEquisatWithoutProjectionTest(_))
        ));

        rule.tests.push(RewriteTestRoute::ModelProjectionReplay);
        assert!(RewriteManifest::new(vec![rule]).is_ok());
    }

    #[test]
    fn default_manifest_enables_only_denotation_identity_projection_rules() {
        let manifest = default_manifest();

        assert!(!manifest.is_empty());
        assert!(manifest.rules().iter().all(|rule| {
            rule.enabled_by_default
                && rule.preservation == Preservation::Denotation
                && rule.projection == ModelProjection::Identity
                && rule.tests.contains(&RewriteTestRoute::ExhaustiveSmallWidth)
                && rule.tests.contains(&RewriteTestRoute::OracleDifferential)
        }));
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn default_rules_fire_on_focused_examples() {
        let mut covered = BTreeSet::new();

        assert_rule_fires(&mut covered, "bool.const_fold.v1", |a| {
            let t = a.bool_const(true);
            let f = a.bool_const(false);
            (a.and(t, f).unwrap(), f)
        });
        assert_rule_fires(&mut covered, "bool.double_not.v1", |a| {
            let p = a.bool_var("p").unwrap();
            let np = a.not(p).unwrap();
            (a.not(np).unwrap(), p)
        });
        assert_rule_fires(&mut covered, "bool.and_identity.v1", |a| {
            let p = a.bool_var("p").unwrap();
            let t = a.bool_const(true);
            (a.and(p, t).unwrap(), p)
        });
        assert_rule_fires(&mut covered, "bool.and_annihilator.v1", |a| {
            let p = a.bool_var("p").unwrap();
            let f = a.bool_const(false);
            (a.and(p, f).unwrap(), f)
        });
        assert_rule_fires(&mut covered, "bool.and_idempotent.v1", |a| {
            let p = a.bool_var("p").unwrap();
            (a.and(p, p).unwrap(), p)
        });
        assert_rule_fires(&mut covered, "bool.or_identity.v1", |a| {
            let p = a.bool_var("p").unwrap();
            let f = a.bool_const(false);
            (a.or(p, f).unwrap(), p)
        });
        assert_rule_fires(&mut covered, "bool.or_annihilator.v1", |a| {
            let p = a.bool_var("p").unwrap();
            let t = a.bool_const(true);
            (a.or(p, t).unwrap(), t)
        });
        assert_rule_fires(&mut covered, "bool.or_idempotent.v1", |a| {
            let p = a.bool_var("p").unwrap();
            (a.or(p, p).unwrap(), p)
        });
        assert_rule_fires(&mut covered, "bool.xor_identity.v1", |a| {
            let p = a.bool_var("p").unwrap();
            let f = a.bool_const(false);
            (a.xor(p, f).unwrap(), p)
        });
        assert_rule_fires(&mut covered, "bool.xor_self.v1", |a| {
            let p = a.bool_var("p").unwrap();
            let f = a.bool_const(false);
            (a.xor(p, p).unwrap(), f)
        });
        assert_rule_fires(&mut covered, "bool.implies_const.v1", |a| {
            let p = a.bool_var("p").unwrap();
            let f = a.bool_const(false);
            let np = a.not(p).unwrap();
            (a.implies(p, f).unwrap(), np)
        });
        assert_rule_fires(&mut covered, "bool.implies_reflexive.v1", |a| {
            let p = a.bool_var("p").unwrap();
            let t = a.bool_const(true);
            (a.implies(p, p).unwrap(), t)
        });
        assert_rule_fires(&mut covered, "eq.reflexive.v1", |a| {
            let x = a.bv_var("x", 4).unwrap();
            let t = a.bool_const(true);
            (a.eq(x, x).unwrap(), t)
        });
        assert_rule_fires(&mut covered, "eq.bool_const.v1", |a| {
            let p = a.bool_var("p").unwrap();
            let t = a.bool_const(true);
            // `(= p true)` ≡ `p`.
            (a.eq(p, t).unwrap(), p)
        });
        assert_rule_fires(&mut covered, "array.select_store_same.v1", |a| {
            let arr = a.array_var("arr", 4, 8).unwrap();
            let i = a.bv_var("i", 4).unwrap();
            let v = a.bv_var("v", 8).unwrap();
            let stored = a.store(arr, i, v).unwrap();
            (a.select(stored, i).unwrap(), v)
        });
        assert_rule_fires(&mut covered, "array.select_const.v1", |a| {
            let v = a.bv_var("v", 8).unwrap();
            let i = a.bv_var("i", 4).unwrap();
            let ca = a.const_array(4, v).unwrap();
            (a.select(ca, i).unwrap(), v)
        });
        assert_rule_fires(&mut covered, "bv.compare_reflexive.v1", |a| {
            let x = a.bv_var("x", 4).unwrap();
            let f = a.bool_const(false);
            (a.bv_ult(x, x).unwrap(), f)
        });
        assert_rule_fires(&mut covered, "bv.compare_saturate.v1", |a| {
            let x = a.bv_var("x", 4).unwrap();
            let zero = a.bv_const(4, 0).unwrap();
            let f = a.bool_const(false);
            // `x < 0` is unsatisfiable for unsigned bit-vectors.
            (a.bv_ult(x, zero).unwrap(), f)
        });
        assert_rule_fires(&mut covered, "ite.const_condition.v1", |a| {
            let p = a.bool_var("p").unwrap();
            let q = a.bool_var("q").unwrap();
            let t = a.bool_const(true);
            (a.ite(t, p, q).unwrap(), p)
        });
        assert_rule_fires(&mut covered, "ite.same_branches.v1", |a| {
            let c = a.bool_var("c").unwrap();
            let p = a.bool_var("p").unwrap();
            (a.ite(c, p, p).unwrap(), p)
        });
        assert_rule_fires(&mut covered, "ite.bool_identity.v1", |a| {
            let c = a.bool_var("c").unwrap();
            let t = a.bool_const(true);
            let f = a.bool_const(false);
            (a.ite(c, t, f).unwrap(), c)
        });
        assert_rule_fires(&mut covered, "bv.const_fold.v1", |a| {
            let one = a.bv_const(4, 1).unwrap();
            let two = a.bv_const(4, 2).unwrap();
            let three = a.bv_const(4, 3).unwrap();
            (a.bv_add(one, two).unwrap(), three)
        });
        assert_rule_fires(&mut covered, "bv.double_not.v1", |a| {
            let x = a.bv_var("x", 4).unwrap();
            let nx = a.bv_not(x).unwrap();
            (a.bv_not(nx).unwrap(), x)
        });
        assert_rule_fires(&mut covered, "bv.double_neg.v1", |a| {
            let x = a.bv_var("x", 4).unwrap();
            let nx = a.bv_neg(x).unwrap();
            (a.bv_neg(nx).unwrap(), x)
        });
        assert_rule_fires(&mut covered, "bv.add_zero.v1", |a| {
            let x = a.bv_var("x", 4).unwrap();
            let zero = a.bv_const(4, 0).unwrap();
            (a.bv_add(x, zero).unwrap(), x)
        });
        assert_rule_fires(&mut covered, "bv.sub_zero.v1", |a| {
            let x = a.bv_var("x", 4).unwrap();
            let zero = a.bv_const(4, 0).unwrap();
            (a.bv_sub(x, zero).unwrap(), x)
        });
        assert_rule_fires(&mut covered, "bv.sub_self.v1", |a| {
            let x = a.bv_var("x", 4).unwrap();
            let zero = a.bv_const(4, 0).unwrap();
            (a.bv_sub(x, x).unwrap(), zero)
        });
        assert_rule_fires(&mut covered, "bv.mul_one.v1", |a| {
            let x = a.bv_var("x", 4).unwrap();
            let one = a.bv_const(4, 1).unwrap();
            (a.bv_mul(x, one).unwrap(), x)
        });
        assert_rule_fires(&mut covered, "bv.mul_zero.v1", |a| {
            let x = a.bv_var("x", 4).unwrap();
            let zero = a.bv_const(4, 0).unwrap();
            (a.bv_mul(x, zero).unwrap(), zero)
        });
        assert_rule_fires(&mut covered, "bv.mul_pow2.v1", |a| {
            // `bvmul x 4` strength-reduces to `bvshl x 2`.
            let x = a.bv_var("x", 4).unwrap();
            let four = a.bv_const(4, 4).unwrap();
            let two = a.bv_const(4, 2).unwrap();
            (a.bv_mul(x, four).unwrap(), a.bv_shl(x, two).unwrap())
        });
        assert_rule_fires(&mut covered, "bv.udiv_pow2.v1", |a| {
            // `bvudiv x 8` strength-reduces to `bvlshr x 3`.
            let x = a.bv_var("x", 8).unwrap();
            let eight = a.bv_const(8, 8).unwrap();
            let three = a.bv_const(8, 3).unwrap();
            (a.bv_udiv(x, eight).unwrap(), a.bv_lshr(x, three).unwrap())
        });
        assert_rule_fires(&mut covered, "bv.urem_pow2.v1", |a| {
            // `bvurem x 8` strength-reduces to `bvand x 7`.
            let x = a.bv_var("x", 8).unwrap();
            let eight = a.bv_const(8, 8).unwrap();
            let seven = a.bv_const(8, 7).unwrap();
            (a.bv_urem(x, eight).unwrap(), a.bv_and(x, seven).unwrap())
        });
        assert_rule_fires(&mut covered, "bv.and_identity.v1", |a| {
            let x = a.bv_var("x", 4).unwrap();
            let ones = a.bv_const(4, 15).unwrap();
            (a.bv_and(x, ones).unwrap(), x)
        });
        assert_rule_fires(&mut covered, "bv.and_zero.v1", |a| {
            let x = a.bv_var("x", 4).unwrap();
            let zero = a.bv_const(4, 0).unwrap();
            (a.bv_and(x, zero).unwrap(), zero)
        });
        assert_rule_fires(&mut covered, "bv.and_idempotent.v1", |a| {
            let x = a.bv_var("x", 4).unwrap();
            (a.bv_and(x, x).unwrap(), x)
        });
        assert_rule_fires(&mut covered, "bv.or_identity.v1", |a| {
            let x = a.bv_var("x", 4).unwrap();
            let zero = a.bv_const(4, 0).unwrap();
            (a.bv_or(x, zero).unwrap(), x)
        });
        assert_rule_fires(&mut covered, "bv.or_ones.v1", |a| {
            let x = a.bv_var("x", 4).unwrap();
            let ones = a.bv_const(4, 15).unwrap();
            (a.bv_or(x, ones).unwrap(), ones)
        });
        assert_rule_fires(&mut covered, "bv.or_idempotent.v1", |a| {
            let x = a.bv_var("x", 4).unwrap();
            (a.bv_or(x, x).unwrap(), x)
        });
        assert_rule_fires(&mut covered, "bv.xor_identity.v1", |a| {
            let x = a.bv_var("x", 4).unwrap();
            let zero = a.bv_const(4, 0).unwrap();
            (a.bv_xor(x, zero).unwrap(), x)
        });
        assert_rule_fires(&mut covered, "bv.xor_self.v1", |a| {
            let x = a.bv_var("x", 4).unwrap();
            let zero = a.bv_const(4, 0).unwrap();
            (a.bv_xor(x, x).unwrap(), zero)
        });
        assert_rule_fires(&mut covered, "bv.shift_zero.v1", |a| {
            let x = a.bv_var("x", 4).unwrap();
            let zero = a.bv_const(4, 0).unwrap();
            (a.bv_shl(x, zero).unwrap(), x)
        });
        assert_rule_fires(&mut covered, "bv.extract_whole.v1", |a| {
            let x = a.bv_var("x", 4).unwrap();
            (a.extract(3, 0, x).unwrap(), x)
        });
        assert_rule_fires(&mut covered, "bv.extract_concat.v1", |a| {
            // extract(2, 0, concat(a4, b4)) selects bits within the low part b4,
            // so it rewrites to extract(2, 0, b4).
            let a4 = a.bv_var("a4", 4).unwrap();
            let b4 = a.bv_var("b4", 4).unwrap();
            let concat = a.concat(a4, b4).unwrap();
            (
                a.extract(2, 0, concat).unwrap(),
                a.extract(2, 0, b4).unwrap(),
            )
        });
        assert_rule_fires(&mut covered, "bv.extract_extend.v1", |a| {
            // extract(2, 0, zero_extend(4, x4)) lies in the original 4 bits
            // (hi=2 < 4), so it rewrites to extract(2, 0, x4).
            let x4 = a.bv_var("x4", 4).unwrap();
            let zext = a.zero_ext(4, x4).unwrap();
            (a.extract(2, 0, zext).unwrap(), a.extract(2, 0, x4).unwrap())
        });
        assert_rule_fires(&mut covered, "bv.concat_extract.v1", |a| {
            // concat(extract(5,3,x6), extract(2,0,x6)) — adjacent slices of the
            // same term (lo1=3 == hi2+1) — reassemble to extract(5, 0, x6).
            let x6 = a.bv_var("x6", 6).unwrap();
            let high = a.extract(5, 3, x6).unwrap();
            let low = a.extract(2, 0, x6).unwrap();
            (a.concat(high, low).unwrap(), a.extract(5, 0, x6).unwrap())
        });
        assert_rule_fires(&mut covered, "bv.extend_zero.v1", |a| {
            let x = a.bv_var("x", 4).unwrap();
            (a.zero_ext(0, x).unwrap(), x)
        });
        assert_rule_fires(&mut covered, "bv.rotate_zero.v1", |a| {
            let x = a.bv_var("x", 4).unwrap();
            (a.rotate_left(0, x).unwrap(), x)
        });
        assert_rule_fires(&mut covered, "commutative.operand_order.v1", |a| {
            // Declare `y` first so `y` has the smaller `TermId`; `(bvmul x y)`
            // then reorders to `(bvmul y x)`.
            let y = a.bv_var("y", 4).unwrap();
            let x = a.bv_var("x", 4).unwrap();
            (a.bv_mul(x, y).unwrap(), a.bv_mul(y, x).unwrap())
        });

        let enabled = default_manifest()
            .enabled_rules()
            .map(|rule| rule.id.as_str().to_owned())
            .collect::<BTreeSet<_>>();
        assert_eq!(covered, enabled);
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn canonicalized_terms_are_evaluator_equivalent_on_small_assignments() {
        let mut a = TermArena::new();
        let x_sym = a.declare("x", Sort::BitVec(3)).unwrap();
        let y_sym = a.declare("y", Sort::BitVec(3)).unwrap();
        let p_sym = a.declare("p", Sort::Bool).unwrap();
        let q_sym = a.declare("q", Sort::Bool).unwrap();
        let x = a.var(x_sym);
        let y = a.var(y_sym);
        let p = a.var(p_sym);
        let q = a.var(q_sym);
        let zero = a.bv_const(3, 0).unwrap();
        let one = a.bv_const(3, 1).unwrap();
        let ones = a.bv_const(3, 7).unwrap();
        let f = a.bool_const(false);
        let t = a.bool_const(true);

        let x_and_ones = a.bv_and(x, ones).unwrap();
        let add_zero = a.bv_add(x_and_ones, zero).unwrap();
        let y_times_one = a.bv_mul(y, one).unwrap();
        let x_xor_x = a.bv_xor(x, x).unwrap();
        let bv_choice = a.ite(p, x_xor_x, y_times_one).unwrap();
        let p_or_false = a.or(p, f).unwrap();
        let q_and_true = a.and(q, t).unwrap();
        let bool_mix = a.xor(p_or_false, q_and_true).unwrap();
        let eq_reflexive = a.eq(add_zero, add_zero).unwrap();
        let terms = [add_zero, bv_choice, bool_mix, eq_reflexive];

        let rewritten = terms
            .iter()
            .map(|&term| canonicalize(&mut a, term).unwrap().term)
            .collect::<Vec<_>>();

        for x_value in 0..8 {
            for y_value in 0..8 {
                for p_value in [false, true] {
                    for q_value in [false, true] {
                        let mut assignment = Assignment::new();
                        assignment.set(
                            x_sym,
                            Value::Bv {
                                width: 3,
                                value: x_value,
                            },
                        );
                        assignment.set(
                            y_sym,
                            Value::Bv {
                                width: 3,
                                value: y_value,
                            },
                        );
                        assignment.set(p_sym, Value::Bool(p_value));
                        assignment.set(q_sym, Value::Bool(q_value));

                        for (&original, &canonical) in terms.iter().zip(&rewritten) {
                            assert_eq!(
                                eval(&a, original, &assignment).unwrap(),
                                eval(&a, canonical, &assignment).unwrap()
                            );
                        }
                    }
                }
            }
        }
    }

    #[test]
    #[allow(clippy::many_single_char_names, clippy::too_many_lines)]
    fn generated_canonicalized_terms_are_evaluator_equivalent() {
        let mut a = TermArena::new();
        let x_sym = a.declare("x", Sort::BitVec(3)).unwrap();
        let y_sym = a.declare("y", Sort::BitVec(3)).unwrap();
        let p_sym = a.declare("p", Sort::Bool).unwrap();
        let q_sym = a.declare("q", Sort::Bool).unwrap();
        let leaves = GeneratedLeaves {
            x: a.var(x_sym),
            y: a.var(y_sym),
            p: a.var(p_sym),
            q: a.var(q_sym),
            zero: a.bv_const(3, 0).unwrap(),
            one: a.bv_const(3, 1).unwrap(),
            ones: a.bv_const(3, 7).unwrap(),
            t: a.bool_const(true),
            f: a.bool_const(false),
        };

        let mut terms = Vec::new();
        for seed in 0..128 {
            let term = if seed % 3 == 0 {
                build_generated_bool(&mut a, seed, 4, leaves)
            } else {
                build_generated_bv(&mut a, seed, 4, leaves)
            };
            terms.push(term);
        }

        let mut changed_terms = 0;
        let mut applications = 0;
        let rewritten = terms
            .iter()
            .map(|&term| {
                let outcome = canonicalize(&mut a, term).unwrap();
                if outcome.changed() {
                    changed_terms += 1;
                }
                applications += outcome.report.applications().len();
                outcome.term
            })
            .collect::<Vec<_>>();

        assert!(
            changed_terms >= 32,
            "generated corpus should exercise many rewrite sites"
        );
        assert!(
            applications >= 96,
            "generated corpus should exercise nested rewrite traversal"
        );

        for x_value in 0..8 {
            for y_value in 0..8 {
                for p_value in [false, true] {
                    for q_value in [false, true] {
                        let mut assignment = Assignment::new();
                        assignment.set(
                            x_sym,
                            Value::Bv {
                                width: 3,
                                value: x_value,
                            },
                        );
                        assignment.set(
                            y_sym,
                            Value::Bv {
                                width: 3,
                                value: y_value,
                            },
                        );
                        assignment.set(p_sym, Value::Bool(p_value));
                        assignment.set(q_sym, Value::Bool(q_value));

                        for (&original, &canonical) in terms.iter().zip(&rewritten) {
                            assert_eq!(
                                eval(&a, original, &assignment).unwrap(),
                                eval(&a, canonical, &assignment).unwrap(),
                                "seeded term #{} changed denotation",
                                original.index()
                            );
                        }
                    }
                }
            }
        }
    }

    fn assert_rule_fires(
        covered: &mut BTreeSet<String>,
        rule_id: &str,
        build: impl FnOnce(&mut TermArena) -> (TermId, TermId),
    ) {
        let mut arena = TermArena::new();
        let (root, expected) = build(&mut arena);
        let outcome = canonicalize(&mut arena, root).unwrap();

        assert_eq!(outcome.term, expected, "wrong output for {rule_id}");
        assert!(
            outcome
                .report
                .applications()
                .iter()
                .any(|application| application.rule_id.as_str() == rule_id),
            "rule {rule_id} did not fire"
        );
        covered.insert(rule_id.to_owned());
    }

    #[derive(Clone, Copy)]
    struct GeneratedLeaves {
        x: TermId,
        y: TermId,
        p: TermId,
        q: TermId,
        zero: TermId,
        one: TermId,
        ones: TermId,
        t: TermId,
        f: TermId,
    }

    fn build_generated_bv(
        arena: &mut TermArena,
        seed: u64,
        depth: u8,
        leaves: GeneratedLeaves,
    ) -> TermId {
        if depth == 0 {
            return match seed % 5 {
                0 => leaves.x,
                1 => leaves.y,
                2 => leaves.zero,
                3 => leaves.one,
                _ => leaves.ones,
            };
        }

        let lhs = build_generated_bv(arena, mix(seed, 1), depth - 1, leaves);
        let rhs = build_generated_bv(arena, mix(seed, 2), depth - 1, leaves);
        let condition = build_generated_bool(arena, mix(seed, 3), depth - 1, leaves);

        match seed % 20 {
            0 => arena.bv_add(lhs, leaves.zero).unwrap(),
            1 => arena.bv_add(lhs, rhs).unwrap(),
            2 => arena.bv_sub(lhs, leaves.zero).unwrap(),
            3 => arena.bv_sub(lhs, lhs).unwrap(),
            4 => arena.bv_mul(lhs, leaves.one).unwrap(),
            5 => arena.bv_mul(lhs, rhs).unwrap(),
            6 => arena.bv_mul(lhs, leaves.zero).unwrap(),
            7 => arena.bv_and(lhs, leaves.ones).unwrap(),
            8 => arena.bv_and(lhs, leaves.zero).unwrap(),
            9 => arena.bv_and(lhs, lhs).unwrap(),
            10 => arena.bv_or(lhs, leaves.zero).unwrap(),
            11 => arena.bv_or(lhs, leaves.ones).unwrap(),
            12 => arena.bv_xor(lhs, leaves.zero).unwrap(),
            13 => arena.bv_xor(lhs, lhs).unwrap(),
            14 => arena.bv_shl(lhs, leaves.zero).unwrap(),
            15 => arena.bv_lshr(lhs, leaves.zero).unwrap(),
            16 => arena.bv_ashr(lhs, leaves.zero).unwrap(),
            17 => arena.extract(2, 0, lhs).unwrap(),
            18 => arena.zero_ext(0, lhs).unwrap(),
            _ => arena.ite(condition, lhs, rhs).unwrap(),
        }
    }

    fn build_generated_bool(
        arena: &mut TermArena,
        seed: u64,
        depth: u8,
        leaves: GeneratedLeaves,
    ) -> TermId {
        if depth == 0 {
            return match seed % 6 {
                0 => leaves.p,
                1 => leaves.q,
                2 => leaves.t,
                3 => leaves.f,
                4 => arena.eq(leaves.x, leaves.x).unwrap(),
                _ => arena.eq(leaves.x, leaves.y).unwrap(),
            };
        }

        let lhs = build_generated_bool(arena, mix(seed, 5), depth - 1, leaves);
        let rhs = build_generated_bool(arena, mix(seed, 6), depth - 1, leaves);
        let lhs_bv = build_generated_bv(arena, mix(seed, 7), depth - 1, leaves);
        let rhs_bv = build_generated_bv(arena, mix(seed, 8), depth - 1, leaves);

        match seed % 16 {
            0 => {
                let inner = arena.not(lhs).unwrap();
                arena.not(inner).unwrap()
            }
            1 => arena.and(lhs, leaves.t).unwrap(),
            2 => arena.and(lhs, leaves.f).unwrap(),
            3 => arena.and(lhs, lhs).unwrap(),
            4 => arena.or(lhs, leaves.f).unwrap(),
            5 => arena.or(lhs, leaves.t).unwrap(),
            6 => arena.or(lhs, lhs).unwrap(),
            7 => arena.xor(lhs, leaves.f).unwrap(),
            8 => arena.xor(lhs, lhs).unwrap(),
            9 => arena.implies(lhs, leaves.f).unwrap(),
            10 => arena.implies(lhs, lhs).unwrap(),
            11 => arena.eq(lhs, lhs).unwrap(),
            12 => arena.eq(lhs_bv, lhs_bv).unwrap(),
            13 => arena.bv_ult(lhs_bv, rhs_bv).unwrap(),
            14 => arena.ite(lhs, rhs, rhs).unwrap(),
            _ => arena.ite(leaves.t, lhs, rhs).unwrap(),
        }
    }

    fn mix(seed: u64, salt: u64) -> u64 {
        let mut x = seed ^ salt.wrapping_mul(0x9e37_79b9_7f4a_7c15);
        x ^= x >> 30;
        x = x.wrapping_mul(0xbf58_476d_1ce4_e5b9);
        x ^= x >> 27;
        x = x.wrapping_mul(0x94d0_49bb_1331_11eb);
        x ^ (x >> 31)
    }
}
