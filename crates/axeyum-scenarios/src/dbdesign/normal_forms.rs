//! Keys, candidate keys, BCNF and 3NF — decided, and then *certified*.
//!
//! # Why a key claim needs more care than it usually gets
//!
//! "`X` is a candidate key" is two claims wearing one name: `X` determines
//! every attribute, and *no proper subset does*. The first has an Armstrong
//! derivation. The second is a claim about things that are **not** derivable,
//! and a system that reports it without evidence is asking to be believed
//! about an absence.
//!
//! [ADR-0455](../../../../docs/research/09-decisions/adr-0455-minimality-is-relative-to-decidedness.md)
//! is the house rule here: a minimality claim is *absolute* only when every
//! removal test was **decided**, and *budget-relative* otherwise. Attribute
//! closure is a total function on a finite lattice — every removal test
//! terminates with a definite verdict, always — so key minimality in this
//! module is always in the absolute regime, and [`KeyAnalysis`] records the
//! count of decided tests rather than leaving the reader to assume it.
//!
//! [ADR-0460](../../../../docs/research/09-decisions/adr-0460-a-decided-subset-test-may-still-be-a-test-of-the-route.md)
//! adds the sharper condition: a decided test still has to be a test *of the
//! claim* and not of some decomposition the producer chose. That failure mode
//! is structurally absent here. Closure is defined by `F` alone; there is no
//! decomposition, no monomial order, no budget and no heuristic anywhere in
//! the test, so "the subset is not a superkey" cannot be an artefact of how
//! the question was set up. The independent evidence makes this concrete:
//! every non-superkey verdict is backed by a two-row relation that satisfies
//! `F`, and *that* object refutes superkey-hood on its own terms without
//! mentioning closure at all.
//!
//! # The completeness claim
//!
//! [`certify_key_completeness`] establishes the stronger statement — *these
//! are **all** the candidate keys* — the only way a finite claim of that shape
//! can be established: by examining every subset of the attributes. Each of
//! the `2^n` subsets is either a superset of a reported key, or it is issued a
//! two-row counterexample relation which is then **checked** by
//! [`super::armstrong::check_two_tuple_witness`]. The search uses closure; the
//! verification does not.

use super::armstrong::{
    Derivation, TwoTupleWitness, check_derivation, check_two_tuple_witness, derive,
    two_tuple_witness,
};
use super::{AttrSet, DbDesignError, Schema};

/// The largest schema arity for which the exhaustive subset sweep is run.
///
/// `2^24` closure evaluations is already a minute of work; beyond that the
/// completeness claim is refused outright rather than reported on a truncated
/// sweep. An "all candidate keys" answer from a partial enumeration would be
/// exactly the kind of empty result that is indistinguishable from a strong
/// negative one.
pub const MAX_EXHAUSTIVE_ARITY: usize = 24;

/// Everything the key analysis established, with the counts that make its
/// minimality claim auditable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KeyAnalysis {
    /// The candidate keys, ascending by bitmask so the list is stable.
    pub candidate_keys: Vec<AttrSet>,
    /// The union of the candidate keys: the *prime* attributes, which 3NF
    /// needs.
    pub prime_attributes: AttrSet,
    /// How many removal tests were run while establishing minimality.
    pub minimality_tests: usize,
    /// How many of those returned a definite verdict. Equal to
    /// `minimality_tests` in every run this module can produce — closure is
    /// total — and recorded anyway, because ADR-0455's distinction is only
    /// useful if the number is present rather than assumed.
    pub minimality_tests_decided: usize,
}

impl KeyAnalysis {
    /// Is the minimality claim absolute in the sense of ADR-0455?
    pub fn minimality_is_absolute(&self) -> bool {
        self.minimality_tests == self.minimality_tests_decided
    }
}

/// Is `x` a superkey — does it determine every attribute?
pub fn is_superkey(schema: &Schema, x: AttrSet) -> bool {
    schema.closure(x) == schema.all()
}

/// A certified answer to "is `x` a superkey?".
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SuperkeyCertificate {
    /// It is: here is the Armstrong derivation of `X → R`.
    Yes(Box<Derivation>),
    /// It is not: here is a two-row relation satisfying `F` whose rows agree
    /// on `X` and differ on an attribute outside `X⁺`.
    No(Box<TwoTupleWitness>),
}

/// Decide superkey-hood **and** verify the certificate before returning it.
///
/// The verification is not decoration. `derive` and `two_tuple_witness` are
/// both driven by closure; running the independent checker here means a caller
/// never receives a certificate that has not already been replayed by code
/// that does not know what closure is.
///
/// # Errors
///
/// If the certificate this module built fails its own checker — which is a bug
/// in this module, reported rather than swallowed.
pub fn certify_superkey(schema: &Schema, x: AttrSet) -> Result<SuperkeyCertificate, DbDesignError> {
    let all = schema.all();
    if is_superkey(schema, x) {
        let derivation = derive(schema, x, all)?;
        check_derivation(schema.fds(), &derivation)?;
        Ok(SuperkeyCertificate::Yes(Box::new(derivation)))
    } else {
        let witness = two_tuple_witness(schema, x, all)?;
        check_two_tuple_witness(schema, &witness)?;
        Ok(SuperkeyCertificate::No(Box::new(witness)))
    }
}

/// Enumerate every candidate key, with each minimality test decided and each
/// negative verdict independently certified.
///
/// # Errors
///
/// If the schema is wider than [`MAX_EXHAUSTIVE_ARITY`], or if any certificate
/// fails its checker.
pub fn analyze_keys(schema: &Schema) -> Result<KeyAnalysis, DbDesignError> {
    let arity = schema.arity();
    if arity > MAX_EXHAUSTIVE_ARITY {
        return Err(DbDesignError::new(format!(
            "arity {arity} exceeds the exhaustive sweep limit of {MAX_EXHAUSTIVE_ARITY}; an \
             `all candidate keys` answer from a truncated sweep would be a claim, not a result"
        )));
    }
    let all = schema.all();
    let mut candidate_keys = Vec::new();
    let mut minimality_tests = 0usize;
    let mut minimality_tests_decided = 0usize;

    // Ascending bitmask order: subsets come out in a stable order, and a set is
    // reached only after every one of its proper subsets, which is not relied
    // on but does make the trace readable.
    for bits in 0u64..(1u64 << arity) {
        let x = AttrSet::from_indices((0..arity).filter(|index| (bits >> index) & 1 == 1));
        if schema.closure(x) != all {
            continue;
        }
        // Superkey. Minimal iff dropping any one attribute loses it.
        let mut minimal = true;
        for index in x.iter() {
            minimality_tests += 1;
            // Closure is total on a finite lattice, so this verdict is always
            // definite; there is no budget that could make it `unknown`.
            minimality_tests_decided += 1;
            if schema.closure(x.without(index)) == all {
                minimal = false;
            }
        }
        if minimal {
            candidate_keys.push(x);
        }
    }

    // Every candidate key gets its derivation and its per-attribute removal
    // witness checked, here, before the analysis is handed to anyone.
    let mut prime_attributes = AttrSet::EMPTY;
    for &key in &candidate_keys {
        prime_attributes = prime_attributes.union(key);
        let derivation = derive(schema, key, all)?;
        check_derivation(schema.fds(), &derivation)?;
        for index in key.iter() {
            let witness = two_tuple_witness(schema, key.without(index), all)?;
            check_two_tuple_witness(schema, &witness)?;
        }
    }

    Ok(KeyAnalysis {
        candidate_keys,
        prime_attributes,
        minimality_tests,
        minimality_tests_decided,
    })
}

/// What the exhaustive completeness sweep measured.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct KeyCompleteness {
    /// How many subsets of the attribute set were examined. Always `2^arity`.
    pub subsets_examined: usize,
    /// How many contained one of the reported candidate keys (and so are
    /// superkeys by monotonicity of closure, needing no separate evidence).
    pub superkey_supersets: usize,
    /// How many were issued a two-row counterexample relation.
    pub counterexamples_built: usize,
    /// How many of those relations passed
    /// [`super::armstrong::check_two_tuple_witness`]. The claim rests on this number
    /// equalling the one above.
    pub counterexamples_checked: usize,
}

/// **Certify that the reported candidate keys are all of them.**
///
/// For every subset `X` of the attributes: either `X` contains one of the
/// reported keys — in which case `X` is a superkey and not a candidate key
/// unless it *is* one of them — or `X` is not a superkey, and that is
/// established by building a two-row relation over `F` whose rows agree on `X`
/// and differ somewhere, then **checking** it.
///
/// # Errors
///
/// If the schema is too wide for the sweep, if a subset containing a reported
/// key turns out not to be a superkey, if a subset containing no reported key
/// turns out to be one (which would mean a key was missed), or if any built
/// counterexample fails its checker.
pub fn certify_key_completeness(
    schema: &Schema,
    keys: &[AttrSet],
) -> Result<KeyCompleteness, DbDesignError> {
    let arity = schema.arity();
    if arity > MAX_EXHAUSTIVE_ARITY {
        return Err(DbDesignError::new(format!(
            "arity {arity} exceeds the exhaustive sweep limit of {MAX_EXHAUSTIVE_ARITY}"
        )));
    }
    let all = schema.all();
    let mut measured = KeyCompleteness {
        subsets_examined: 0,
        superkey_supersets: 0,
        counterexamples_built: 0,
        counterexamples_checked: 0,
    };

    for bits in 0u64..(1u64 << arity) {
        let x = AttrSet::from_indices((0..arity).filter(|index| (bits >> index) & 1 == 1));
        measured.subsets_examined += 1;
        let covers_a_key = keys.iter().any(|key| key.is_subset_of(x));
        if covers_a_key {
            measured.superkey_supersets += 1;
            if schema.closure(x) != all {
                return Err(DbDesignError::new(format!(
                    "{} contains a reported candidate key but is not a superkey",
                    schema.render(x)
                )));
            }
            continue;
        }
        if schema.closure(x) == all {
            return Err(DbDesignError::new(format!(
                "{} is a superkey containing none of the reported candidate keys, so the key \
                 list is incomplete",
                schema.render(x)
            )));
        }
        let witness = two_tuple_witness(schema, x, all)?;
        measured.counterexamples_built += 1;
        check_two_tuple_witness(schema, &witness)?;
        measured.counterexamples_checked += 1;
    }
    Ok(measured)
}

/// A dependency in `F` that puts the schema outside a normal form, with the
/// evidence that it does.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NormalFormViolation {
    /// The offending dependency's label.
    pub fd_name: String,
    /// Its determinant.
    pub lhs: AttrSet,
    /// Its dependent.
    pub rhs: AttrSet,
    /// A two-row relation over `F` whose rows agree on the determinant and
    /// differ elsewhere — so the determinant is not a superkey, which is
    /// precisely the BCNF condition it fails.
    pub not_superkey: TwoTupleWitness,
    /// For 3NF: the attributes of `rhs \ lhs` that belong to no candidate key.
    /// Empty for a violation that is BCNF-only.
    pub non_prime_dependents: AttrSet,
}

/// Is the schema in **BCNF**, and if not, why?
///
/// Only the dependencies *in `F`* are examined, which is sufficient: if every
/// `X → Y` in `F` with `Y ⊄ X` has `X⁺ = R`, then any implied non-trivial
/// `A → B` has `B ⊆ A⁺` and `B ⊄ A`, so growing `A⁺` used some `L → R` of `F`
/// with `L ⊆ A⁺`, whence `A⁺ ⊇ L⁺ = R` and `A` is a superkey too.
///
/// # Errors
///
/// If a violation's counterexample relation fails its checker.
pub fn bcnf_violations(schema: &Schema) -> Result<Vec<NormalFormViolation>, DbDesignError> {
    let all = schema.all();
    let mut violations = Vec::new();
    for fd in schema.fds() {
        if fd.rhs.is_subset_of(fd.lhs) {
            continue; // trivial
        }
        if is_superkey(schema, fd.lhs) {
            continue;
        }
        let witness = two_tuple_witness(schema, fd.lhs, all)?;
        check_two_tuple_witness(schema, &witness)?;
        violations.push(NormalFormViolation {
            fd_name: fd.name.clone(),
            lhs: fd.lhs,
            rhs: fd.rhs,
            not_superkey: witness,
            non_prime_dependents: AttrSet::EMPTY,
        });
    }
    Ok(violations)
}

/// Is the schema in **3NF**, and if not, why?
///
/// A dependency `X → Y` is allowed when `X` is a superkey *or* every attribute
/// of `Y \ X` is prime. So every 3NF violation is a BCNF violation, and the
/// reported set is a subset of [`bcnf_violations`]'s.
///
/// # Errors
///
/// If the key analysis or any counterexample fails.
pub fn third_normal_form_violations(
    schema: &Schema,
    keys: &KeyAnalysis,
) -> Result<Vec<NormalFormViolation>, DbDesignError> {
    let mut violations = Vec::new();
    for mut violation in bcnf_violations(schema)? {
        let dependents = violation.rhs.difference(violation.lhs);
        let non_prime = dependents.difference(keys.prime_attributes);
        if non_prime.is_empty() {
            continue;
        }
        violation.non_prime_dependents = non_prime;
        violations.push(violation);
    }
    Ok(violations)
}

#[cfg(test)]
mod tests {
    use super::super::Fd;
    use super::*;

    fn build(attrs: &[&str], fds: &[(&str, &[usize], &[usize])]) -> Schema {
        let mut schema =
            Schema::new(attrs.iter().map(|name| (*name).to_owned()).collect()).unwrap();
        for (name, lhs, rhs) in fds {
            schema
                .push_fd(Fd {
                    name: (*name).to_owned(),
                    lhs: AttrSet::from_indices(lhs.iter().copied()),
                    rhs: AttrSet::from_indices(rhs.iter().copied()),
                })
                .unwrap();
        }
        schema
    }

    /// The classical two-candidate-key example: `AB -> C`, `C -> A`.
    /// Keys are `{A,B}` and `{B,C}`; not in BCNF because `C` is not a superkey;
    /// in 3NF because `A` is prime.
    fn ab_c() -> Schema {
        build(
            &["A", "B", "C"],
            &[("f1", &[0, 1], &[2]), ("f2", &[2], &[0])],
        )
    }

    #[test]
    fn candidate_keys_are_found_and_minimal() {
        let schema = ab_c();
        let analysis = analyze_keys(&schema).unwrap();
        assert_eq!(
            analysis.candidate_keys,
            vec![AttrSet::from_indices([0, 1]), AttrSet::from_indices([1, 2])]
        );
        assert_eq!(analysis.prime_attributes, AttrSet::full(3));
        assert!(analysis.minimality_is_absolute());
        assert!(analysis.minimality_tests > 0);
    }

    #[test]
    fn completeness_sweep_checks_every_subset() {
        let schema = ab_c();
        let analysis = analyze_keys(&schema).unwrap();
        let measured = certify_key_completeness(&schema, &analysis.candidate_keys).unwrap();
        assert_eq!(measured.subsets_examined, 8);
        assert_eq!(
            measured.counterexamples_built,
            measured.counterexamples_checked
        );
        assert_eq!(
            measured.superkey_supersets + measured.counterexamples_built,
            8
        );
        // {A,B}, {B,C}, {A,B,C} are the supersets of a key.
        assert_eq!(measured.superkey_supersets, 3);
    }

    #[test]
    fn completeness_sweep_rejects_a_short_key_list() {
        let schema = ab_c();
        // Drop one real key: some subset is now a superkey covering none.
        let short = vec![AttrSet::from_indices([0, 1])];
        assert!(certify_key_completeness(&schema, &short).is_err());
        // Add a non-key: it is not a superkey and the sweep says so.
        let padded = vec![
            AttrSet::from_indices([0, 1]),
            AttrSet::from_indices([1, 2]),
            AttrSet::from_indices([0]),
        ];
        assert!(certify_key_completeness(&schema, &padded).is_err());
    }

    #[test]
    fn superkey_certificates_replay() {
        let schema = ab_c();
        let yes = certify_superkey(&schema, AttrSet::from_indices([0, 1])).unwrap();
        assert!(matches!(yes, SuperkeyCertificate::Yes(_)));
        let no = certify_superkey(&schema, AttrSet::from_indices([2])).unwrap();
        let SuperkeyCertificate::No(witness) = no else {
            panic!("C is not a superkey of AB->C, C->A");
        };
        check_two_tuple_witness(&schema, &witness).unwrap();
    }

    #[test]
    fn bcnf_and_3nf_disagree_on_the_classical_example() {
        let schema = ab_c();
        let keys = analyze_keys(&schema).unwrap();
        let bcnf = bcnf_violations(&schema).unwrap();
        assert_eq!(bcnf.len(), 1);
        assert_eq!(bcnf[0].fd_name, "f2");
        let third = third_normal_form_violations(&schema, &keys).unwrap();
        assert!(third.is_empty(), "A is prime, so f2 is legal in 3NF");
    }

    #[test]
    fn a_transitive_dependency_breaks_3nf() {
        // A -> B, B -> C: key is {A}, C depends transitively, B is not prime.
        let schema = build(&["A", "B", "C"], &[("f1", &[0], &[1]), ("f2", &[1], &[2])]);
        let keys = analyze_keys(&schema).unwrap();
        assert_eq!(keys.candidate_keys, vec![AttrSet::from_indices([0])]);
        let third = third_normal_form_violations(&schema, &keys).unwrap();
        assert_eq!(third.len(), 1);
        assert_eq!(third[0].fd_name, "f2");
        assert_eq!(third[0].non_prime_dependents, AttrSet::from_indices([2]));
    }

    #[test]
    fn a_schema_in_bcnf_reports_no_violations() {
        // A -> B C with A the only key.
        let schema = build(&["A", "B", "C"], &[("f1", &[0], &[1, 2])]);
        assert!(bcnf_violations(&schema).unwrap().is_empty());
    }
}
