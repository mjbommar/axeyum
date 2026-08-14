//! Negative controls: plausible-but-wrong mathematics the solver must refute.
//!
//! Every other scenario family in this crate encodes something *true* and asks
//! the solver to agree. This one is the mirror: each scenario states a
//! documented mathematical **misconception** — a claim real learners actually
//! make — and the expected verdict is `unsat`. The stack passes by *refusing*
//! the claim.
//!
//! The source corpus is the `graph/misconceptions/` collection in the sibling
//! `math-education` repository (148 files, 147 live). [`CONTROLS`] records, per
//! scenario, which corpus entries it formalises and which
//! [`crate::MathNode`] curriculum node it exercises, so the curriculum's
//! `decidability` class carries evidence rather than an assertion.
//!
//! # Why an unsat-expecting suite is the one that cannot pass vacuously
//!
//! A suite of things that *should* be provable degrades silently: if the
//! machinery stops working and starts answering `unknown`, or if the suite is
//! accidentally emptied, nothing goes red. This repository has shipped exactly
//! that failure — a corpus gate that ran zero tests for fifteen days while
//! exiting 0. A suite whose expected answers are **refutations** fails as soon
//! as the refutations stop arriving.
//!
//! That property is enforced mechanically here, by four checks rather than by
//! this paragraph:
//!
//! 1. every catalog entry declares its expectation in [`CONTROLS`], and the
//!    table is checked against what is actually built;
//! 2. every refutation must self-check to [`crate::UnsatEvidence::Exhaustive`]
//!    — a finite proof over the whole domain, never a sample;
//! 3. [`MIN_REFUTATIONS`] is a hard floor, so an emptied catalog fails;
//! 4. the **degenerate controls**: three scenarios where the misconception (or
//!    its neighbourhood) is genuinely *satisfiable*, and must come back `sat`
//!    with a witness. If the builders here were emitting malformed queries that
//!    happened to be trivially unsatisfiable, checks 1-3 would still pass and
//!    this one would not.
//!
//! # The two shapes, and why there are two
//!
//! A misconception is usually a false *universal*, and refuting a false
//! universal is a satisfiability question — you exhibit a counterexample. Taken
//! naively, that would make this an entirely `sat`-expecting suite, with the
//! vacuity problem it exists to avoid. So each control is built in one of two
//! shapes, recorded in [`ControlShape`]:
//!
//! - [`ControlShape::UniversallyFalse`] — the misconception's rule fails at
//!   *every* point of a nondegenerate box, so asserting it over the box is
//!   `unsat` and the `unsat` is a real search. `(a+b)^2 = a^2+b^2` for
//!   `a, b >= 1` is this shape.
//! - [`ControlShape::PropertyPinned`] — the rule fails only somewhere, so the
//!   counterexample region is pinned **by properties, not by literals**, and the
//!   rule is asserted there. "A non-square rectangle and a square of equal
//!   perimeter have equal area" is this shape: unsat over the whole box (it is
//!   strict AM-GM), and still a four-symbol search.
//!
//! A misconception that could only be made `unsat` by writing its
//! counterexample in as constants is deliberately **not** built. A one-case
//! "search" would overstate what the suite proves.
//!
//! # Overflow is the live soundness hazard
//!
//! Over `BV(w)` many false identities become *true* by wraparound:
//! `(a+b)^2 = a^2+b^2` holds whenever `2ab = 0 mod 2^w`, for instance at
//! `w = 8, a = 16, b = 8`. Every scenario therefore carries an explicit range
//! constraint chosen so that no intermediate value wraps, and computes in a
//! zero-extended width when the arithmetic needs more headroom than the
//! enumeration budget allows. A wrong bound does not slip through as a comment:
//! [`crate::Scenario::self_check`] enumerates the whole domain and fails on the
//! model it finds.

use axeyum_ir::{Assignment, Sort, TermArena, TermId, Value, eval};
use axeyum_query::Query;

use crate::{Expectation, Family, Scenario, UnsatEvidence};

/// How a control turns a false claim into an unsatisfiable query.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ControlShape {
    /// The misconception's rule is false at every point of a nondegenerate box,
    /// so asserting it over the box is unsatisfiable.
    UniversallyFalse,
    /// The rule is false only in part of its range; the counterexample region is
    /// pinned by properties (never by literal constants) and the rule asserted
    /// there.
    PropertyPinned,
    /// A deliberately satisfiable companion: the degenerate case in which the
    /// misconception, or the neighbourhood it lives in, genuinely holds. These
    /// exist so that a builder emitting trivially-unsatisfiable garbage fails
    /// the suite.
    DegenerateControl,
}

/// One negative control: a scenario plus what it is a control *for*.
#[derive(Debug, Clone, Copy)]
pub struct NegativeControl {
    /// Scenario name suffix, matching [`Scenario::name`] after the `misconception/` prefix.
    pub name: &'static str,
    /// How the false claim was turned into a decidable query.
    pub shape: ControlShape,
    /// `true` when the expected verdict is `unsat` (a refutation).
    pub refutes: bool,
    /// Corpus ids from `math-education`'s `graph/misconceptions/`, without the
    /// `M:` prefix. A control may formalise several entries when they share one
    /// formal core.
    pub misconceptions: &'static [&'static str],
    /// Curriculum node ids from `docs/curriculum/curriculum.toml`.
    pub curriculum_nodes: &'static [&'static str],
    /// One line on what the false claim is.
    pub claim: &'static str,
}

/// The floor on how many refutations the catalog must contain.
///
/// This is the anti-vacuity ratchet: a catalog that is emptied, or silently
/// stops producing refutations, fails rather than passing with nothing to do.
pub const MIN_REFUTATIONS: usize = 30;

/// Every negative control, with its corpus and curriculum links.
pub const CONTROLS: &[NegativeControl] = &[
    NegativeControl {
        name: "binomial_square_spread",
        shape: ControlShape::UniversallyFalse,
        refutes: true,
        misconceptions: &[
            "a-plus-b-squared-equals-a-squared-plus-b-squared",
            "square-root-of-a-sum",
            "vector-addition-just-adds-magnitudes",
        ],
        curriculum_nodes: &["polynomials"],
        claim: "(a + b)^2 = a^2 + b^2",
    },
    NegativeControl {
        name: "distribute_first_only",
        shape: ControlShape::UniversallyFalse,
        refutes: true,
        misconceptions: &["distribute-only-the-first-term"],
        curriculum_nodes: &["polynomials"],
        claim: "k(x + y) = kx + y",
    },
    NegativeControl {
        name: "subtraction_commutes",
        shape: ControlShape::UniversallyFalse,
        refutes: true,
        misconceptions: &["everything-commutes"],
        curriculum_nodes: &["integers", "groups"],
        claim: "x - y = y - x for distinct x, y",
    },
    NegativeControl {
        name: "negative_times_negative",
        shape: ControlShape::UniversallyFalse,
        refutes: true,
        misconceptions: &["negative-times-negative-confusion"],
        curriculum_nodes: &["integers"],
        claim: "(-a)(-b) = -(ab)",
    },
    NegativeControl {
        name: "proper_fraction_scaling",
        shape: ControlShape::UniversallyFalse,
        refutes: true,
        misconceptions: &["multiplication-makes-bigger", "division-makes-smaller"],
        curriculum_nodes: &["rationals"],
        claim: "scaling a positive quantity by p/q with p < q does not decrease it",
    },
    NegativeControl {
        name: "equal_numerators_bigger_denominator",
        shape: ControlShape::UniversallyFalse,
        refutes: true,
        misconceptions: &[
            "bigger-denominator-means-bigger-fraction",
            "fraction-is-two-numbers",
        ],
        curriculum_nodes: &["rationals"],
        claim: "a/b > a/d when b > d",
    },
    NegativeControl {
        name: "mediant_is_the_sum",
        shape: ControlShape::UniversallyFalse,
        refutes: true,
        misconceptions: &["add-numerators-and-denominators"],
        curriculum_nodes: &["rationals"],
        claim: "a/b + c/d = (a + c)/(b + d)",
    },
    NegativeControl {
        name: "reciprocal_distributes",
        shape: ControlShape::UniversallyFalse,
        refutes: true,
        misconceptions: &["distributivity-works-for-any-two-operations"],
        curriculum_nodes: &["rationals", "fields"],
        claim: "1/(a + b) = 1/a + 1/b",
    },
    NegativeControl {
        name: "equal_perimeter_equal_area",
        shape: ControlShape::PropertyPinned,
        refutes: true,
        misconceptions: &["area-and-perimeter-conflated"],
        curriculum_nodes: &["naturals"],
        claim: "a non-square rectangle and a square of equal perimeter have equal area",
    },
    NegativeControl {
        name: "matrix_product_entrywise",
        shape: ControlShape::UniversallyFalse,
        refutes: true,
        misconceptions: &["matrix-multiplication-is-entrywise"],
        curriculum_nodes: &["linear-algebra"],
        claim: "the (1,1) entry of a 2x2 matrix product is a11 * b11",
    },
    NegativeControl {
        name: "plurality_is_a_majority",
        shape: ControlShape::PropertyPinned,
        refutes: true,
        misconceptions: &["winning-most-votes-means-majority"],
        curriculum_nodes: &["naturals"],
        claim: "the leader of a four-way race won by one vote each holds a majority",
    },
    NegativeControl {
        name: "percent_up_then_down",
        shape: ControlShape::UniversallyFalse,
        refutes: true,
        misconceptions: &["percentage-increase-then-decrease-cancels"],
        curriculum_nodes: &["rationals"],
        claim: "a rise of p percent then a fall of p percent returns to the start",
    },
    NegativeControl {
        name: "stacked_discounts_add",
        shape: ControlShape::UniversallyFalse,
        refutes: true,
        misconceptions: &["stacked-percent-discounts-add"],
        curriculum_nodes: &["rationals"],
        claim: "x percent off then y percent off equals (x + y) percent off",
    },
    NegativeControl {
        name: "students_and_professors",
        shape: ControlShape::UniversallyFalse,
        refutes: true,
        misconceptions: &["letters-stand-for-objects"],
        curriculum_nodes: &["naturals"],
        claim: "'six times as many students as professors' is 6S = P",
    },
    NegativeControl {
        name: "doubling_the_side_doubles_area",
        shape: ControlShape::UniversallyFalse,
        refutes: true,
        misconceptions: &["doubling-side-doubles-area"],
        curriculum_nodes: &["naturals"],
        claim: "doubling a square's side doubles its area",
    },
    NegativeControl {
        name: "doubling_the_side_doubles_volume",
        shape: ControlShape::UniversallyFalse,
        refutes: true,
        misconceptions: &["doubling-side-doubles-volume"],
        curriculum_nodes: &["naturals"],
        claim: "doubling a cube's side doubles its volume",
    },
    NegativeControl {
        name: "part_to_part_ratio_is_part_to_whole",
        shape: ControlShape::UniversallyFalse,
        refutes: true,
        misconceptions: &["ratio-is-just-a-fraction-of-the-total"],
        curriculum_nodes: &["rationals"],
        claim: "in a ratio a:b, the first part is a/b of the whole",
    },
    NegativeControl {
        name: "same_letter_two_values",
        shape: ControlShape::UniversallyFalse,
        refutes: true,
        misconceptions: &["same-letter-can-differ"],
        curriculum_nodes: &["integers"],
        claim: "x + x = 7 is solvable if the two x's may differ",
    },
    NegativeControl {
        name: "exponent_is_a_multiplier",
        shape: ControlShape::UniversallyFalse,
        refutes: true,
        misconceptions: &["exponent-means-multiply-by-exponent"],
        curriculum_nodes: &["naturals"],
        claim: "b^2 = 2b",
    },
    NegativeControl {
        name: "exponent_counts_one_extra_factor",
        shape: ControlShape::UniversallyFalse,
        refutes: true,
        misconceptions: &["exponent-means-multiply-by-itself-times"],
        curriculum_nodes: &["naturals"],
        claim: "b^3 has four factors, i.e. b^3 = b^4",
    },
    NegativeControl {
        name: "elapsed_time_is_decimal",
        shape: ControlShape::UniversallyFalse,
        refutes: true,
        misconceptions: &["subtract-clock-digits-like-whole-numbers"],
        curriculum_nodes: &["naturals", "modular-arithmetic"],
        claim: "elapsed minutes equal the difference of the hhmm readings",
    },
    NegativeControl {
        name: "base_rate_neglect",
        shape: ControlShape::UniversallyFalse,
        refutes: true,
        misconceptions: &[
            "base-rate-neglect-error",
            "accurate-test-means-positive-result-is-reliable",
        ],
        curriculum_nodes: &["rationals"],
        claim: "a 99%-accurate test that comes back positive makes the condition 99% likely",
    },
    NegativeControl {
        name: "second_draw_unchanged",
        shape: ControlShape::UniversallyFalse,
        refutes: true,
        misconceptions: &["the-second-probability-stays-the-same"],
        curriculum_nodes: &["rationals", "counting"],
        claim: "drawing twice without replacement squares the first probability",
    },
    NegativeControl {
        name: "complement_is_one_outcome",
        shape: ControlShape::UniversallyFalse,
        refutes: true,
        misconceptions: &[
            "a-complement-is-one-other-outcome",
            "an-event-is-one-outcome",
        ],
        curriculum_nodes: &["sets", "counting"],
        claim: "the complement of a three-outcome event in a six-outcome space has one outcome",
    },
    NegativeControl {
        name: "disjoint_addition_rule",
        shape: ControlShape::UniversallyFalse,
        refutes: true,
        misconceptions: &["different-event-labels-mean-no-overlap"],
        curriculum_nodes: &["sets", "counting"],
        claim: "|A or B| = |A| + |B| even when A and B overlap",
    },
    NegativeControl {
        name: "counterexample_is_an_exception",
        shape: ControlShape::UniversallyFalse,
        refutes: true,
        misconceptions: &[
            "counterexample-is-just-an-exception",
            "one-example-proves-it",
        ],
        curriculum_nodes: &["proof-methods", "predicate-logic"],
        claim: "a universal claim survives a case where it fails",
    },
    NegativeControl {
        name: "small_scope_pattern_trap",
        shape: ControlShape::UniversallyFalse,
        refutes: true,
        misconceptions: &[
            "proof-is-just-checking-lots",
            "examples-are-proof",
            "selected-evidence-proves-a-rule",
        ],
        curriculum_nodes: &["number-theory", "proof-methods"],
        claim: "n^2 - n + 41 has a factor in 2..=40 for some n <= 40 (it does not; the pattern breaks at n = 41)",
    },
    NegativeControl {
        name: "converse_is_the_contrapositive",
        shape: ControlShape::UniversallyFalse,
        refutes: true,
        misconceptions: &["truth-table-only-for-hard-problems"],
        curriculum_nodes: &["propositional-logic"],
        claim: "a conditional and its converse are equivalent",
    },
    NegativeControl {
        name: "two_is_prime",
        shape: ControlShape::UniversallyFalse,
        refutes: true,
        misconceptions: &["all-primes-are-odd"],
        curriculum_nodes: &["divisibility-and-euclid", "number-theory"],
        claim: "2 factors nontrivially (so it could be dismissed as not really prime)",
    },
    NegativeControl {
        name: "one_has_two_distinct_divisors",
        shape: ControlShape::PropertyPinned,
        refutes: true,
        misconceptions: &["one-is-prime"],
        curriculum_nodes: &["divisibility-and-euclid", "number-theory"],
        claim: "1 is prime, i.e. its two factors 1 and itself are distinct",
    },
    NegativeControl {
        name: "odd_plus_odd_is_odd",
        shape: ControlShape::UniversallyFalse,
        refutes: true,
        misconceptions: &["odd-plus-odd-is-odd"],
        curriculum_nodes: &["naturals", "divisibility-and-euclid"],
        claim: "the sum of two odd numbers is odd",
    },
    NegativeControl {
        name: "century_year_is_a_leap_year",
        shape: ControlShape::PropertyPinned,
        refutes: true,
        misconceptions: &["every-fourth-year-is-a-leap-year"],
        curriculum_nodes: &["modular-arithmetic", "divisibility-and-euclid"],
        claim: "every year divisible by four is a leap year",
    },
    // ---- degenerate controls: these must come back `sat`. ----
    NegativeControl {
        name: "binomial_square_degenerate",
        shape: ControlShape::DegenerateControl,
        refutes: false,
        misconceptions: &["a-plus-b-squared-equals-a-squared-plus-b-squared"],
        curriculum_nodes: &["polynomials"],
        claim: "(a + b)^2 = a^2 + b^2 does hold when a = 0",
    },
    NegativeControl {
        name: "converse_degenerate",
        shape: ControlShape::DegenerateControl,
        refutes: false,
        misconceptions: &["truth-table-only-for-hard-problems"],
        curriculum_nodes: &["propositional-logic"],
        claim: "a conditional and its converse do agree when p and q agree",
    },
    NegativeControl {
        name: "small_scope_break_at_41",
        shape: ControlShape::DegenerateControl,
        refutes: false,
        misconceptions: &["proof-is-just-checking-lots"],
        curriculum_nodes: &["number-theory"],
        claim: "n^2 - n + 41 does factor at n = 41",
    },
];

/// Every negative control as a self-checking scenario.
///
/// The refutations expect `unsat`; the three degenerate controls expect `sat`
/// and carry a witness.
///
/// # Panics
///
/// Panics on arena corruption (a builder bug), never on input.
pub fn misconception_catalog() -> Vec<Scenario> {
    let mut out: Vec<Scenario> = REFUTATIONS
        .iter()
        .map(|(name, build)| build().refutation(name))
        .collect();
    out.extend(
        DEGENERATE_CONTROLS
            .iter()
            .map(|(name, build)| build().witnessed(name)),
    );
    out
}

/// A builder constructor: premises plus the misconception's claim, unpackaged.
type Build = fn() -> Builder;

/// The controls whose expected verdict is `unsat`.
const REFUTATIONS: &[(&str, Build)] = &[
    ("binomial_square_spread", binomial_square_spread),
    ("distribute_first_only", distribute_first_only),
    ("subtraction_commutes", subtraction_commutes),
    ("negative_times_negative", negative_times_negative),
    ("proper_fraction_scaling", proper_fraction_scaling),
    (
        "equal_numerators_bigger_denominator",
        equal_numerators_bigger_denominator,
    ),
    ("mediant_is_the_sum", mediant_is_the_sum),
    ("reciprocal_distributes", reciprocal_distributes),
    ("equal_perimeter_equal_area", equal_perimeter_equal_area),
    ("matrix_product_entrywise", matrix_product_entrywise),
    ("plurality_is_a_majority", plurality_is_a_majority),
    ("percent_up_then_down", percent_up_then_down),
    ("stacked_discounts_add", stacked_discounts_add),
    ("students_and_professors", students_and_professors),
    (
        "doubling_the_side_doubles_area",
        doubling_the_side_doubles_area,
    ),
    (
        "doubling_the_side_doubles_volume",
        doubling_the_side_doubles_volume,
    ),
    (
        "part_to_part_ratio_is_part_to_whole",
        part_to_part_ratio_is_part_to_whole,
    ),
    ("same_letter_two_values", same_letter_two_values),
    ("exponent_is_a_multiplier", exponent_is_a_multiplier),
    (
        "exponent_counts_one_extra_factor",
        exponent_counts_one_extra_factor,
    ),
    ("elapsed_time_is_decimal", elapsed_time_is_decimal),
    ("base_rate_neglect", base_rate_neglect),
    ("second_draw_unchanged", second_draw_unchanged),
    ("complement_is_one_outcome", complement_is_one_outcome),
    ("disjoint_addition_rule", disjoint_addition_rule),
    (
        "counterexample_is_an_exception",
        counterexample_is_an_exception,
    ),
    ("small_scope_pattern_trap", small_scope_pattern_trap),
    (
        "converse_is_the_contrapositive",
        converse_is_the_contrapositive,
    ),
    ("two_is_prime", two_is_prime),
    (
        "one_has_two_distinct_divisors",
        one_has_two_distinct_divisors,
    ),
    ("odd_plus_odd_is_odd", odd_plus_odd_is_odd),
    ("century_year_is_a_leap_year", century_year_is_a_leap_year),
];

/// The deliberately satisfiable companions. See the module docs: these are what
/// stop a builder that emits trivially-unsatisfiable garbage from passing.
const DEGENERATE_CONTROLS: &[(&str, Build)] = &[
    ("binomial_square_degenerate", binomial_square_degenerate),
    ("converse_degenerate", converse_degenerate),
    ("small_scope_break_at_41", small_scope_break_at_41),
];

// ---------------------------------------------------------------------------
// Builders. Each declares its symbols at the *narrowest* width that holds its
// range (so enumeration stays cheap) and zero-extends before arithmetic that
// needs headroom.
// ---------------------------------------------------------------------------

/// `(a + b)^2 = a^2 + b^2`, over `1 <= a, b <= 7`.
///
/// The difference is `2ab`, which lies in `[2, 98]` over the box and so is never
/// `0 mod 2^8`. Wraparound is the reason for the upper bound: at width 8 the
/// claim is genuinely *true* at `a = 16, b = 8`.
fn binomial_square_spread() -> Builder {
    let mut b = Builder::new("binomial_square_spread");
    let a = b.sym("a", 3);
    let c = b.sym("b", 3);
    b.between(a, 1, 7);
    b.between(c, 1, 7);
    let (a8, c8) = (b.zext(a, 8), b.zext(c, 8));
    let sum = b.add(a8, c8);
    let lhs = b.mul(sum, sum);
    let aa = b.mul(a8, a8);
    let cc = b.mul(c8, c8);
    let rhs = b.add(aa, cc);
    b.claim_eq(lhs, rhs);
    b
}

/// The same claim in the degenerate case it really does hold: `a = 0`.
fn binomial_square_degenerate() -> Builder {
    let mut b = Builder::new("binomial_square_degenerate");
    let a = b.sym("a", 3);
    let c = b.sym("b", 3);
    b.between(a, 0, 0);
    b.between(c, 1, 7);
    let (a8, c8) = (b.zext(a, 8), b.zext(c, 8));
    let sum = b.add(a8, c8);
    let lhs = b.mul(sum, sum);
    let aa = b.mul(a8, a8);
    let cc = b.mul(c8, c8);
    let rhs = b.add(aa, cc);
    b.claim_eq(lhs, rhs);
    b
}

/// `k(x + y) = kx + y`, over `2 <= k <= 3`, `x <= 7`, `1 <= y <= 7`.
///
/// The difference is `(k - 1)y`, in `[1, 14]`. `k >= 2` and `y >= 1` are both
/// load-bearing: the claim is true at `k = 1` and at `y = 0`.
fn distribute_first_only() -> Builder {
    let mut b = Builder::new("distribute_first_only");
    let k = b.sym("k", 2);
    let x = b.sym("x", 3);
    let y = b.sym("y", 3);
    b.between(k, 2, 3);
    b.between(x, 0, 7);
    b.between(y, 1, 7);
    let (k8, x8, y8) = (b.zext(k, 8), b.zext(x, 8), b.zext(y, 8));
    let inner = b.add(x8, y8);
    let lhs = b.mul(k8, inner);
    let kx = b.mul(k8, x8);
    let rhs = b.add(kx, y8);
    b.claim_eq(lhs, rhs);
    b
}

/// `x - y = y - x` for distinct `x, y`, over `BV(5)` with both below `2^4`.
///
/// Over `BV(w)` the two sides agree exactly when `x - y` is `0` or `2^(w-1)`.
/// Restricting both operands below `2^(w-1)` and requiring them distinct rules
/// out both, which is what makes the refutation sound rather than accidental.
fn subtraction_commutes() -> Builder {
    let mut b = Builder::new("subtraction_commutes");
    let x = b.sym("x", 5);
    let y = b.sym("y", 5);
    b.between(x, 0, 15);
    b.between(y, 0, 15);
    b.distinct(x, y);
    let lhs = b.sub(x, y);
    let rhs = b.sub(y, x);
    b.claim_eq(lhs, rhs);
    b
}

/// `(-a)(-b) = -(ab)`, over `1 <= a, b <= 7` in two's complement at width 8.
///
/// Both sides are equal exactly when `2ab` wraps to zero; `ab <= 49` keeps it
/// far from `2^8`.
fn negative_times_negative() -> Builder {
    let mut b = Builder::new("negative_times_negative");
    let a = b.sym("a", 4);
    let c = b.sym("b", 4);
    b.between(a, 1, 7);
    b.between(c, 1, 7);
    let (a8, c8) = (b.zext(a, 8), b.zext(c, 8));
    let na = b.neg(a8);
    let nc = b.neg(c8);
    let lhs = b.mul(na, nc);
    let prod = b.mul(a8, c8);
    let rhs = b.neg(prod);
    b.claim_eq(lhs, rhs);
    b
}

/// Scaling a positive `v` by `p/q` with `p < q` does not decrease it.
///
/// Cross-multiplied: `p*v >= q*v`. This is the shared formal core of "dividing
/// always makes smaller" read through the reciprocal.
fn proper_fraction_scaling() -> Builder {
    let mut b = Builder::new("proper_fraction_scaling");
    let p = b.sym("p", 3);
    let q = b.sym("q", 3);
    let v = b.sym("v", 3);
    b.between(p, 1, 7);
    b.between(q, 1, 7);
    b.between(v, 1, 7);
    b.lt(p, q);
    let (p8, q8, v8) = (b.zext(p, 8), b.zext(q, 8), b.zext(v, 8));
    let lhs = b.mul(p8, v8);
    let rhs = b.mul(q8, v8);
    b.claim_uge(lhs, rhs);
    b
}

/// `a/b > a/d` when `b > d`, cross-multiplied to `a*d > a*b`.
///
/// Equal numerators are the corpus's own second distractor (`3/10 > 3/5`).
fn equal_numerators_bigger_denominator() -> Builder {
    let mut b = Builder::new("equal_numerators_bigger_denominator");
    let a = b.sym("a", 3);
    let bb = b.sym("b", 3);
    let d = b.sym("d", 3);
    b.between(a, 1, 7);
    b.between(bb, 1, 7);
    b.between(d, 1, 7);
    b.lt(d, bb);
    let (a8, b8, d8) = (b.zext(a, 8), b.zext(bb, 8), b.zext(d, 8));
    let lhs = b.mul(a8, d8);
    let rhs = b.mul(a8, b8);
    b.claim_ugt(lhs, rhs);
    b
}

/// `a/b + c/d = (a + c)/(b + d)`, cross-multiplied.
///
/// `(ad + cb)(b + d) - (a + c)bd = ad^2 + cb^2`, strictly positive for positive
/// parts, so the claim fails everywhere in the box.
fn mediant_is_the_sum() -> Builder {
    let mut b = Builder::new("mediant_is_the_sum");
    let a = b.sym("a", 2);
    let bb = b.sym("b", 2);
    let c = b.sym("c", 2);
    let d = b.sym("d", 2);
    for s in [a, bb, c, d] {
        b.between(s, 1, 3);
    }
    let (a16, b16, c16, d16) = (b.zext(a, 16), b.zext(bb, 16), b.zext(c, 16), b.zext(d, 16));
    let ad = b.mul(a16, d16);
    let cb = b.mul(c16, b16);
    let num = b.add(ad, cb);
    let bd = b.add(b16, d16);
    let lhs = b.mul(num, bd);
    let ac = b.add(a16, c16);
    let bmuld = b.mul(b16, d16);
    let rhs = b.mul(ac, bmuld);
    b.claim_eq(lhs, rhs);
    b
}

/// `1/(a + b) = 1/a + 1/b`, cross-multiplied to `ab = (a + b)^2`.
fn reciprocal_distributes() -> Builder {
    let mut b = Builder::new("reciprocal_distributes");
    let a = b.sym("a", 3);
    let c = b.sym("b", 3);
    b.between(a, 1, 7);
    b.between(c, 1, 7);
    let (a16, c16) = (b.zext(a, 16), b.zext(c, 16));
    let lhs = b.mul(a16, c16);
    let sum = b.add(a16, c16);
    let rhs = b.mul(sum, sum);
    b.claim_eq(lhs, rhs);
    b
}

/// A non-square rectangle and a square of equal perimeter have equal area.
///
/// Property-pinned: `a < b`, `c = d`, `a + b = c + d`, and the claim `ab = cd`.
/// Unsatisfiable by strict AM-GM. The premises alone are satisfiable
/// (`a = 1, b = 3, c = d = 2`), which the `premises_are_satisfiable` test checks
/// so a typo in the constraints cannot make this pass for the wrong reason.
fn equal_perimeter_equal_area() -> Builder {
    let mut b = Builder::new("equal_perimeter_equal_area");
    let a = b.sym("a", 3);
    let bb = b.sym("b", 3);
    let c = b.sym("c", 3);
    let d = b.sym("d", 3);
    for s in [a, bb, c, d] {
        b.between(s, 1, 7);
    }
    b.lt(a, bb);
    b.eq_terms(c, d);
    let (a8, b8, c8, d8) = (b.zext(a, 8), b.zext(bb, 8), b.zext(c, 8), b.zext(d, 8));
    let per1 = b.add(a8, b8);
    let per2 = b.add(c8, d8);
    b.premise_eq(per1, per2);
    let area1 = b.mul(a8, b8);
    let area2 = b.mul(c8, d8);
    b.claim_eq(area1, area2);
    b
}

/// The `(1,1)` entry of a 2x2 matrix product is `a11 * b11`.
///
/// The true entry is `a11*b11 + a12*b21`; with every entry at least `1` the
/// cross term is nonzero, so the entrywise reading fails everywhere.
fn matrix_product_entrywise() -> Builder {
    let mut b = Builder::new("matrix_product_entrywise");
    // Only the four entries the (1,1) product touches are declared; an unused
    // symbol would quadruple the enumeration domain and prove nothing.
    let names = ["a11", "a12", "b11", "b21"];
    let syms: Vec<TermId> = names.iter().map(|n| b.sym(n, 2)).collect();
    for &s in &syms {
        b.between(s, 1, 3);
    }
    let a11 = b.zext(syms[0], 8);
    let a12 = b.zext(syms[1], 8);
    let b11 = b.zext(syms[2], 8);
    let b21 = b.zext(syms[3], 8);
    let entrywise = b.mul(a11, b11);
    let cross = b.mul(a12, b21);
    let rowcol = b.add(entrywise, cross);
    b.claim_eq(entrywise, rowcol);
    b
}

/// In a four-way race where the leader beats each rival by exactly one vote,
/// the leader holds a majority.
///
/// Property-pinned: rivals all on `k >= 1`, leader on `k + 1`, and the claim
/// `2 * leader > total`. This reduces to `1 > 2k`, false for every `k >= 1`.
fn plurality_is_a_majority() -> Builder {
    let mut b = Builder::new("plurality_is_a_majority");
    let k = b.sym("k", 6);
    b.between(k, 1, 60);
    let k8 = b.zext(k, 16);
    let one = b.constant(16, 1);
    let leader = b.add(k8, one);
    let three_k = {
        let two_k = b.add(k8, k8);
        b.add(two_k, k8)
    };
    let total = b.add(leader, three_k);
    let twice_leader = b.add(leader, leader);
    b.claim_ugt(twice_leader, total);
    b
}

/// A rise of `p` percent then a fall of `p` percent returns to the start.
///
/// Scaled by `10000`: the claim is `v(100 + p)(100 - p) >= v * 10000`, i.e.
/// `v(10000 - p^2) >= v * 10000`, false for every `v, p >= 1`.
fn percent_up_then_down() -> Builder {
    let mut b = Builder::new("percent_up_then_down");
    let v = b.sym("v", 5);
    let p = b.sym("p", 5);
    b.between(v, 1, 31);
    b.between(p, 1, 31);
    let v32 = b.zext(v, 32);
    let p32 = b.zext(p, 32);
    let hundred = b.constant(32, 100);
    let up = b.add(hundred, p32);
    let down = b.sub(hundred, p32);
    let scaled = {
        let t = b.mul(v32, up);
        b.mul(t, down)
    };
    let ten_k = b.constant(32, 10_000);
    let original = b.mul(v32, ten_k);
    b.claim_uge(scaled, original);
    b
}

/// `x` percent off then `y` percent off equals `(x + y)` percent off.
///
/// `(100 - x)(100 - y) - (100 - x - y) * 100 = xy > 0`, so the stacked price is
/// strictly higher and the claim's `<=` fails everywhere.
fn stacked_discounts_add() -> Builder {
    let mut b = Builder::new("stacked_discounts_add");
    let x = b.sym("x", 5);
    let y = b.sym("y", 5);
    b.between(x, 1, 20);
    b.between(y, 1, 20);
    let x16 = b.zext(x, 16);
    let y16 = b.zext(y, 16);
    let hundred = b.constant(16, 100);
    let keep_x = b.sub(hundred, x16);
    let keep_y = b.sub(hundred, y16);
    let stacked = b.mul(keep_x, keep_y);
    let combined = {
        let xy = b.add(x16, y16);
        let keep = b.sub(hundred, xy);
        b.mul(keep, hundred)
    };
    b.claim_ule(stacked, combined);
    b
}

/// "Six times as many students as professors" written as `6S = P`.
///
/// Asserting the misconception's equation alongside the true relation
/// `S = 6P` forces `35P = 0`, impossible for `1 <= P <= 7`.
fn students_and_professors() -> Builder {
    let mut b = Builder::new("students_and_professors");
    let s = b.sym("s", 6);
    let p = b.sym("p", 3);
    b.between(s, 1, 63);
    b.between(p, 1, 7);
    let s16 = b.zext(s, 16);
    let p16 = b.zext(p, 16);
    let six = b.constant(16, 6);
    let six_p = b.mul(six, p16);
    b.premise_eq(s16, six_p);
    let six_s = b.mul(six, s16);
    b.claim_eq(six_s, p16);
    b
}

/// Doubling a square's side doubles its area: `(2s)^2 = 2 s^2`.
fn doubling_the_side_doubles_area() -> Builder {
    let mut b = Builder::new("doubling_the_side_doubles_area");
    let s = b.sym("s", 4);
    b.between(s, 1, 15);
    let s16 = b.zext(s, 16);
    let two = b.constant(16, 2);
    let doubled = b.mul(two, s16);
    let lhs = b.mul(doubled, doubled);
    let area = b.mul(s16, s16);
    let rhs = b.mul(two, area);
    b.claim_eq(lhs, rhs);
    b
}

/// Doubling a cube's side doubles its volume: `(2s)^3 = 2 s^3`.
fn doubling_the_side_doubles_volume() -> Builder {
    let mut b = Builder::new("doubling_the_side_doubles_volume");
    let s = b.sym("s", 3);
    b.between(s, 1, 7);
    let s16 = b.zext(s, 16);
    let two = b.constant(16, 2);
    let doubled = b.mul(two, s16);
    let lhs = {
        let sq = b.mul(doubled, doubled);
        b.mul(sq, doubled)
    };
    let rhs = {
        let sq = b.mul(s16, s16);
        let cube = b.mul(sq, s16);
        b.mul(two, cube)
    };
    b.claim_eq(lhs, rhs);
    b
}

/// In a ratio `a:b`, the first part is `a/b` of the whole.
///
/// The whole is `a + b` parts, so the claim cross-multiplies to `ab = a(a + b)`,
/// i.e. `a^2 = 0`.
fn part_to_part_ratio_is_part_to_whole() -> Builder {
    let mut b = Builder::new("part_to_part_ratio_is_part_to_whole");
    let a = b.sym("a", 3);
    let c = b.sym("b", 3);
    b.between(a, 1, 7);
    b.between(c, 1, 7);
    let (a16, c16) = (b.zext(a, 16), b.zext(c, 16));
    let lhs = b.mul(a16, c16);
    let whole = b.add(a16, c16);
    let rhs = b.mul(a16, whole);
    b.claim_eq(lhs, rhs);
    b
}

/// `x + x = 7`: unsatisfiable over the whole 8-bit domain, by parity.
///
/// This one needs no range constraint at all — `x + x` is even for every `x`,
/// including the wrapping cases, so the refutation covers all 256 values.
fn same_letter_two_values() -> Builder {
    let mut b = Builder::new("same_letter_two_values");
    let x = b.sym("x", 8);
    let sum = b.add(x, x);
    let seven = b.constant(8, 7);
    b.claim_eq(sum, seven);
    b
}

/// `b^2 = 2b`, over `3 <= b <= 15`.
///
/// The lower bound is load-bearing and is the interesting part: the claim is
/// genuinely true at `b = 0` and `b = 2`, which is why "3^2 = 3 x 2" feels
/// consistent to a learner who first met it as "2^2 = 2 x 2".
fn exponent_is_a_multiplier() -> Builder {
    let mut b = Builder::new("exponent_is_a_multiplier");
    let base = b.sym("b", 4);
    b.between(base, 3, 15);
    let b16 = b.zext(base, 16);
    let two = b.constant(16, 2);
    let lhs = b.mul(b16, b16);
    let rhs = b.mul(two, b16);
    b.claim_eq(lhs, rhs);
    b
}

/// `b^3 = b^4`, over `2 <= b <= 7` — the off-by-one factor count.
fn exponent_counts_one_extra_factor() -> Builder {
    let mut b = Builder::new("exponent_counts_one_extra_factor");
    let base = b.sym("b", 3);
    b.between(base, 2, 7);
    let b16 = b.zext(base, 16);
    let sq = b.mul(b16, b16);
    let cube = b.mul(sq, b16);
    let fourth = b.mul(cube, b16);
    b.claim_eq(cube, fourth);
    b
}

/// Elapsed minutes equal the difference of the `hhmm` readings.
///
/// `(100 h2 + m2) - (100 h1 + m1)` minus the true `(60 h2 + m2) - (60 h1 + m1)`
/// is `40(h2 - h1)`, nonzero for every `h1 < h2` — the base-60 gap, in the open.
fn elapsed_time_is_decimal() -> Builder {
    let mut b = Builder::new("elapsed_time_is_decimal");
    let h2 = b.sym("h2", 2);
    let m1 = b.sym("m1", 6);
    let m2 = b.sym("m2", 6);
    b.between(h2, 1, 3);
    b.between(m1, 0, 59);
    b.between(m2, 0, 59);
    let h1w = b.constant(16, 0);
    let h2w = b.zext(h2, 16);
    let m1w = b.zext(m1, 16);
    let m2w = b.zext(m2, 16);
    let hundred = b.constant(16, 100);
    let sixty = b.constant(16, 60);
    let dec1 = {
        let t = b.mul(hundred, h1w);
        b.add(t, m1w)
    };
    let dec2 = {
        let t = b.mul(hundred, h2w);
        b.add(t, m2w)
    };
    let true1 = {
        let t = b.mul(sixty, h1w);
        b.add(t, m1w)
    };
    let true2 = {
        let t = b.mul(sixty, h2w);
        b.add(t, m2w)
    };
    let dec_gap = b.sub(dec2, dec1);
    let true_gap = b.sub(true2, true1);
    b.claim_eq(dec_gap, true_gap);
    b
}

/// A 99%-accurate test that comes back positive makes the condition 99% likely.
///
/// With prevalence `p` per thousand, sensitivity and specificity both `99/100`,
/// the posterior is `99p / (98p + 1000)`. Claiming it reaches `99/100`
/// cross-multiplies to `198p >= 99000`, i.e. `p >= 500` — a prevalence of 50%.
/// The box caps `p` at 100 (10%), so the claim fails throughout.
fn base_rate_neglect() -> Builder {
    let mut b = Builder::new("base_rate_neglect");
    let p = b.sym("p", 7);
    b.between(p, 1, 100);
    let p32 = b.zext(p, 32);
    let c99 = b.constant(32, 99);
    let c98 = b.constant(32, 98);
    let c100 = b.constant(32, 100);
    let c1000 = b.constant(32, 1000);
    // 100 * (99 * p)  >=  99 * (98 * p + 1000)
    let lhs = {
        let t = b.mul(c99, p32);
        b.mul(c100, t)
    };
    let rhs = {
        let t = b.mul(c98, p32);
        let s = b.add(t, c1000);
        b.mul(c99, s)
    };
    b.claim_uge(lhs, rhs);
    b
}

/// Drawing twice without replacement squares the first probability.
///
/// `(r - 1)(r + b) = r(r + b - 1)` reduces to `b = 0`, so with at least one
/// non-target item the claim fails everywhere.
fn second_draw_unchanged() -> Builder {
    let mut b = Builder::new("second_draw_unchanged");
    let r = b.sym("r", 3);
    let other = b.sym("b", 3);
    b.between(r, 2, 7);
    b.between(other, 1, 7);
    let r16 = b.zext(r, 16);
    let o16 = b.zext(other, 16);
    let one = b.constant(16, 1);
    let total = b.add(r16, o16);
    let r_minus = b.sub(r16, one);
    let total_minus = b.sub(total, one);
    let lhs = b.mul(r_minus, total);
    let rhs = b.mul(r16, total_minus);
    b.claim_eq(lhs, rhs);
    b
}

/// The complement of a three-outcome event in a six-outcome space has one
/// outcome.
///
/// The event is a subset bitmask over the six die faces; the complement has
/// `6 - 3 = 3` outcomes, never 1.
fn complement_is_one_outcome() -> Builder {
    let mut b = Builder::new("complement_is_one_outcome");
    let a = b.sym("a", 6);
    let pop_a = b.popcount(a, 8);
    let three = b.constant(8, 3);
    b.premise_eq(pop_a, three);
    let not_a = b.bv_not(a);
    let pop_not = b.popcount(not_a, 8);
    let one = b.constant(8, 1);
    b.claim_eq(pop_not, one);
    b
}

/// `|A or B| = |A| + |B|` even when `A` and `B` overlap.
fn disjoint_addition_rule() -> Builder {
    let mut b = Builder::new("disjoint_addition_rule");
    let a = b.sym("a", 6);
    let c = b.sym("b", 6);
    let inter = b.bv_and(a, c);
    let zero6 = b.constant(6, 0);
    b.premise_distinct(inter, zero6);
    let union = b.bv_or(a, c);
    let pop_union = b.popcount(union, 8);
    let pop_a = b.popcount(a, 8);
    let pop_c = b.popcount(c, 8);
    let sum = b.add(pop_a, pop_c);
    b.claim_eq(pop_union, sum);
    b
}

/// A universal claim survives a case where it fails.
///
/// `p` is the truth table of a predicate over a 12-point domain. The premise is
/// the universal "P holds at every even point" — satisfiable, with 64 models.
/// The claim adds "and P fails at 6". Every one of those 64 models is rejected.
fn counterexample_is_an_exception() -> Builder {
    let mut b = Builder::new("counterexample_is_an_exception");
    let p = b.sym("p", 12);
    let one1 = b.constant(1, 1);
    let zero1 = b.constant(1, 0);
    for point in (0u32..12).step_by(2) {
        let bit = b.extract(point, p);
        b.premise_eq(bit, one1);
    }
    let counter = b.extract(6, p);
    b.claim_eq(counter, zero1);
    b
}

/// `n^2 - n + 41` has a factor in `2..=40` for some `n <= 40`.
///
/// It does not: Euler's polynomial is prime at every one of those 41 points, and
/// every value is at most 1601, so a composite one would have had a factor in
/// range. This control is the *small-scope trap* itself — the pattern really
/// does survive every check a patient learner would run, and the refutation here
/// is what "checked forty cases" actually buys. Its companion
/// [`small_scope_break_at_41`] is the `sat` case one step further out.
fn small_scope_pattern_trap() -> Builder {
    let mut b = Builder::new("small_scope_pattern_trap");
    let n = b.sym("n", 6);
    let d = b.sym("d", 6);
    b.between(n, 0, 40);
    b.between(d, 2, 40);
    let n16 = b.zext(n, 16);
    let d16 = b.zext(d, 16);
    let c41 = b.constant(16, 41);
    let value = {
        let sq = b.mul(n16, n16);
        let t = b.sub(sq, n16);
        b.add(t, c41)
    };
    let rem = b.urem(value, d16);
    let zero = b.constant(16, 0);
    b.claim_eq(rem, zero);
    b
}

/// The same polynomial one step further out: at `n = 41` it factors as `41 * 41`.
///
/// A degenerate control in the sense that matters here — it must come back
/// `sat`, with a witness the evaluator confirms.
fn small_scope_break_at_41() -> Builder {
    let mut b = Builder::new("small_scope_break_at_41");
    let d = b.sym("d", 6);
    let e = b.sym("e", 6);
    b.between(d, 2, 60);
    b.between(e, 2, 60);
    let n16 = b.constant(16, 41);
    let d16 = b.zext(d, 16);
    let e16 = b.zext(e, 16);
    let c41 = b.constant(16, 41);
    let value = {
        let sq = b.mul(n16, n16);
        let t = b.sub(sq, n16);
        b.add(t, c41)
    };
    let prod = b.mul(d16, e16);
    b.claim_eq(value, prod);
    b
}

/// A conditional and its converse are equivalent.
///
/// Instantiated at the shape that separates them: the premise is `not p and q`,
/// where `p -> q` holds and `q -> p` does not.
fn converse_is_the_contrapositive() -> Builder {
    let mut b = Builder::new("converse_is_the_contrapositive");
    let p = b.bool_sym("p");
    let q = b.bool_sym("q");
    let np = b.not(p);
    b.premise(np);
    b.premise(q);
    let fwd = b.implies(p, q);
    let back = b.implies(q, p);
    b.claim_eq(fwd, back);
    b
}

/// The case where a conditional and its converse really do agree: `p = q`.
fn converse_degenerate() -> Builder {
    let mut b = Builder::new("converse_degenerate");
    let p = b.bool_sym("p");
    let q = b.bool_sym("q");
    let same = b.eq_bool(p, q);
    b.premise(same);
    let fwd = b.implies(p, q);
    let back = b.implies(q, p);
    b.claim_eq(fwd, back);
    b
}

/// 2 factors nontrivially.
///
/// It does not, which is exactly why "primes are odd" has to dismiss 2 as an
/// anomaly rather than accept it. The refutation searches every `(d, e)` pair in
/// `[2, 40]^2` and rejects all of them.
fn two_is_prime() -> Builder {
    let mut b = Builder::new("two_is_prime");
    let d = b.sym("d", 6);
    let e = b.sym("e", 6);
    b.between(d, 2, 40);
    b.between(e, 2, 40);
    let d16 = b.zext(d, 16);
    let e16 = b.zext(e, 16);
    let prod = b.mul(d16, e16);
    let two = b.constant(16, 2);
    b.claim_eq(prod, two);
    b
}

/// 1 is prime: its "two factors, 1 and itself" are distinct.
///
/// Property-pinned. The premise `d * e = 1` is satisfiable (`d = e = 1`); the
/// claim that the two factors differ is not. That gap is the whole content of
/// the "exactly two distinct positive divisors" definition.
fn one_has_two_distinct_divisors() -> Builder {
    let mut b = Builder::new("one_has_two_distinct_divisors");
    let d = b.sym("d", 4);
    let e = b.sym("e", 4);
    b.between(d, 1, 15);
    b.between(e, 1, 15);
    let d16 = b.zext(d, 16);
    let e16 = b.zext(e, 16);
    let prod = b.mul(d16, e16);
    let one = b.constant(16, 1);
    b.premise_eq(prod, one);
    b.claim_distinct(d, e);
    b
}

/// The sum of two odd numbers is odd.
///
/// No range constraint is needed: parity survives wraparound, so the refutation
/// covers all 256 assignments rather than a chosen box.
fn odd_plus_odd_is_odd() -> Builder {
    let mut b = Builder::new("odd_plus_odd_is_odd");
    let a = b.sym("a", 4);
    let c = b.sym("b", 4);
    let a8 = b.zext(a, 8);
    let c8 = b.zext(c, 8);
    let two = b.constant(8, 2);
    let one = b.constant(8, 1);
    let odd_a = {
        let t = b.mul(two, a8);
        b.add(t, one)
    };
    let odd_c = {
        let t = b.mul(two, c8);
        b.add(t, one)
    };
    let sum = b.add(odd_a, odd_c);
    let rem = b.urem(sum, two);
    b.claim_eq(rem, one);
    b
}

/// Every year divisible by four is a leap year.
///
/// Property-pinned by the century exception — divisible by 100 but not by 400 —
/// rather than by writing 1900 in as a literal. Under those premises the correct
/// Gregorian predicate is false at every one of the 2048 candidate years.
fn century_year_is_a_leap_year() -> Builder {
    let mut b = Builder::new("century_year_is_a_leap_year");
    let y = b.sym("y", 11);
    let four = b.constant(11, 4);
    let hundred = b.constant(11, 100);
    let four_hundred = b.constant(11, 400);
    let zero = b.constant(11, 0);
    let r4 = b.urem(y, four);
    let r100 = b.urem(y, hundred);
    let r400 = b.urem(y, four_hundred);
    b.premise_eq(r4, zero);
    b.premise_eq(r100, zero);
    b.premise_distinct(r400, zero);
    // The Gregorian rule: (y % 4 == 0 and y % 100 != 0) or y % 400 == 0.
    let div4 = b.arena.eq(r4, zero).unwrap();
    let not_div100 = {
        let e = b.arena.eq(r100, zero).unwrap();
        b.arena.not(e).unwrap()
    };
    let ordinary = b.arena.and(div4, not_div100).unwrap();
    let div400 = b.arena.eq(r400, zero).unwrap();
    let leap = b.arena.or(ordinary, div400).unwrap();
    b.set_claim(leap);
    b
}

// ---------------------------------------------------------------------------
// Builder
// ---------------------------------------------------------------------------

/// A small term-building helper that keeps premises and the misconception's own
/// claim separate.
///
/// The separation is not cosmetic: [`Builder::premises_query`] is what lets the
/// `premises_are_satisfiable` test confirm that each control's constraints admit
/// a model *before* the claim is added. Without that, a typo in a range bound
/// would produce an unsatisfiable query that passes the suite for entirely the
/// wrong reason.
struct Builder {
    name: &'static str,
    arena: TermArena,
    premises: Vec<TermId>,
    claim: Option<TermId>,
}

impl Builder {
    fn new(name: &'static str) -> Self {
        Self {
            name,
            arena: TermArena::new(),
            premises: Vec::new(),
            claim: None,
        }
    }

    fn label(&self) -> &'static str {
        self.name
    }

    fn sym(&mut self, name: &str, width: u32) -> TermId {
        let s = self.arena.declare(name, Sort::BitVec(width)).unwrap();
        self.arena.var(s)
    }

    fn bool_sym(&mut self, name: &str) -> TermId {
        let s = self.arena.declare(name, Sort::Bool).unwrap();
        self.arena.var(s)
    }

    fn width_of(&self, t: TermId) -> u32 {
        self.arena
            .sort_of(t)
            .bv_width()
            .expect("misconception builders use bit-vector terms here")
    }

    fn constant(&mut self, width: u32, value: u128) -> TermId {
        self.arena.bv_const(width, value).unwrap()
    }

    /// Zero-extend `t` to `to` bits by concatenating a zero high half.
    fn zext(&mut self, t: TermId, to: u32) -> TermId {
        let from = self.width_of(t);
        assert!(to >= from, "zext must widen");
        if to == from {
            return t;
        }
        let pad = self.constant(to - from, 0);
        self.arena.concat(pad, t).unwrap()
    }

    fn extract(&mut self, bit: u32, t: TermId) -> TermId {
        self.arena.extract(bit, bit, t).unwrap()
    }

    fn add(&mut self, a: TermId, b: TermId) -> TermId {
        self.arena.bv_add(a, b).unwrap()
    }
    fn sub(&mut self, a: TermId, b: TermId) -> TermId {
        self.arena.bv_sub(a, b).unwrap()
    }
    fn mul(&mut self, a: TermId, b: TermId) -> TermId {
        self.arena.bv_mul(a, b).unwrap()
    }
    fn neg(&mut self, a: TermId) -> TermId {
        self.arena.bv_neg(a).unwrap()
    }
    fn urem(&mut self, a: TermId, b: TermId) -> TermId {
        self.arena.bv_urem(a, b).unwrap()
    }
    fn bv_not(&mut self, a: TermId) -> TermId {
        self.arena.bv_not(a).unwrap()
    }
    fn bv_and(&mut self, a: TermId, b: TermId) -> TermId {
        self.arena.bv_and(a, b).unwrap()
    }
    fn bv_or(&mut self, a: TermId, b: TermId) -> TermId {
        self.arena.bv_or(a, b).unwrap()
    }
    fn not(&mut self, a: TermId) -> TermId {
        self.arena.not(a).unwrap()
    }
    fn implies(&mut self, a: TermId, b: TermId) -> TermId {
        self.arena.implies(a, b).unwrap()
    }
    fn eq_bool(&mut self, a: TermId, b: TermId) -> TermId {
        self.arena.eq(a, b).unwrap()
    }

    /// Population count of `t`, widened to `out` bits.
    fn popcount(&mut self, t: TermId, out: u32) -> TermId {
        let width = self.width_of(t);
        let mut acc = self.constant(out, 0);
        for bit in 0..width {
            let b = self.extract(bit, t);
            let wide = self.zext(b, out);
            acc = self.add(acc, wide);
        }
        acc
    }

    // --- premises ---

    fn premise(&mut self, t: TermId) {
        self.premises.push(t);
    }

    fn premise_eq(&mut self, a: TermId, b: TermId) {
        let t = self.arena.eq(a, b).unwrap();
        self.premises.push(t);
    }

    fn premise_distinct(&mut self, a: TermId, b: TermId) {
        let e = self.arena.eq(a, b).unwrap();
        let t = self.arena.not(e).unwrap();
        self.premises.push(t);
    }

    fn eq_terms(&mut self, a: TermId, b: TermId) {
        self.premise_eq(a, b);
    }

    fn distinct(&mut self, a: TermId, b: TermId) {
        self.premise_distinct(a, b);
    }

    fn between(&mut self, t: TermId, lo: u128, hi: u128) {
        let width = self.width_of(t);
        let lo_c = self.constant(width, lo);
        let hi_c = self.constant(width, hi);
        let ge = self.arena.bv_uge(t, lo_c).unwrap();
        let le = self.arena.bv_ule(t, hi_c).unwrap();
        self.premises.push(ge);
        self.premises.push(le);
    }

    fn lt(&mut self, a: TermId, b: TermId) {
        let t = self.arena.bv_ult(a, b).unwrap();
        self.premises.push(t);
    }

    // --- the claim ---

    fn claim_eq(&mut self, a: TermId, b: TermId) {
        let t = self.arena.eq(a, b).unwrap();
        self.set_claim(t);
    }
    fn claim_uge(&mut self, a: TermId, b: TermId) {
        let t = self.arena.bv_uge(a, b).unwrap();
        self.set_claim(t);
    }
    fn claim_ugt(&mut self, a: TermId, b: TermId) {
        let t = self.arena.bv_ugt(a, b).unwrap();
        self.set_claim(t);
    }
    fn claim_distinct(&mut self, a: TermId, b: TermId) {
        let e = self.arena.eq(a, b).unwrap();
        let t = self.arena.not(e).unwrap();
        self.set_claim(t);
    }
    fn claim_ule(&mut self, a: TermId, b: TermId) {
        let t = self.arena.bv_ule(a, b).unwrap();
        self.set_claim(t);
    }

    fn set_claim(&mut self, t: TermId) {
        assert!(self.claim.is_none(), "{}: claim set twice", self.name);
        self.claim = Some(t);
    }

    // --- finishing ---

    fn total_bits(&self) -> u32 {
        self.arena
            .symbols()
            .map(|(_, _, sort)| match sort {
                Sort::Bool => 1,
                Sort::BitVec(w) => w,
                other => unreachable!("misconception scenarios declare no {other:?} symbols"),
            })
            .sum()
    }

    fn build_query(&self, include_claim: bool) -> Query {
        let mut builder = Query::builder(&self.arena);
        for &p in &self.premises {
            builder.assert(p).unwrap();
        }
        if include_claim {
            builder
                .assert(self.claim.expect("claim must be set"))
                .unwrap();
        }
        builder.build()
    }

    /// The premises without the misconception's claim, for the satisfiability
    /// guard.
    #[cfg(test)]
    fn premises_query(&self) -> Query {
        self.build_query(false)
    }

    /// Package as an UNSAT scenario: premises plus the false claim.
    fn refutation(self, name: &str) -> Scenario {
        debug_assert_eq!(name, self.label());
        let bits = self.total_bits();
        assert!(
            bits <= crate::EXHAUSTIVE_BIT_LIMIT,
            "{name}: {bits} bits exceeds the exhaustive budget; a sampled refutation is not a proof"
        );
        let query = self.build_query(true);
        Scenario {
            name: format!("misconception/{name}"),
            family: Family::Misconception,
            width: bits,
            seed: 0,
            arena: self.arena,
            query,
            expectation: Expectation::Unsat {
                evidence: UnsatEvidence::Exhaustive {
                    cases: 1u64 << bits,
                },
            },
        }
    }

    /// Package as a SAT scenario, finding the witness by enumeration.
    fn witnessed(self, name: &str) -> Scenario {
        debug_assert_eq!(name, self.label());
        let query = self.build_query(true);
        let witness = find_model(&self.arena, &query)
            .unwrap_or_else(|| panic!("{name}: degenerate control has no model"));
        let bits = self.total_bits();
        Scenario {
            name: format!("misconception/{name}"),
            family: Family::Misconception,
            width: bits,
            seed: 0,
            arena: self.arena,
            query,
            expectation: Expectation::Sat { witness },
        }
    }
}

/// Enumerates the (small) symbol domain and returns the first satisfying
/// assignment, judged only by the evaluator.
fn find_model(arena: &TermArena, query: &Query) -> Option<Assignment> {
    let symbols: Vec<(axeyum_ir::SymbolId, Sort)> = arena
        .symbols()
        .map(|(symbol, _name, sort)| (symbol, sort))
        .collect();
    let bits: u32 = symbols
        .iter()
        .map(|(_, s)| match s {
            Sort::Bool => 1,
            Sort::BitVec(w) => *w,
            other => unreachable!("misconception scenarios declare no {other:?} symbols"),
        })
        .sum();
    assert!(bits <= 24, "find_model domain too large ({bits} bits)");
    for code in 0..(1u64 << bits) {
        let mut assignment = Assignment::new();
        let mut rest = u128::from(code);
        for (symbol, sort) in &symbols {
            match sort {
                Sort::Bool => {
                    assignment.set(*symbol, Value::Bool(rest & 1 == 1));
                    rest >>= 1;
                }
                Sort::BitVec(w) => {
                    let mask = (1u128 << w) - 1;
                    assignment.set(
                        *symbol,
                        Value::Bv {
                            width: *w,
                            value: rest & mask,
                        },
                    );
                    rest >>= w;
                }
                other => unreachable!("misconception scenarios declare no {other:?} symbols"),
            }
        }
        let ok = query
            .solver_terms()
            .all(|term| matches!(eval(arena, term, &assignment), Ok(Value::Bool(true))));
        if ok {
            return Some(assignment);
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeSet;

    #[test]
    fn every_control_self_checks_and_refutations_are_exhaustive() {
        let scenarios = misconception_catalog();
        assert!(!scenarios.is_empty(), "the catalog must not be empty");
        let mut refutations = 0usize;
        let mut witnesses = 0usize;
        for scenario in &scenarios {
            let evidence = scenario
                .self_check()
                .unwrap_or_else(|e| panic!("{} failed self-check: {e}", scenario.name));
            match &scenario.expectation {
                Expectation::Unsat { .. } => {
                    // A sampled refutation is not a proof; require the finite one.
                    assert!(
                        matches!(evidence, UnsatEvidence::Exhaustive { .. }),
                        "{} was only refuted by sampling: {evidence:?}",
                        scenario.name
                    );
                    refutations += 1;
                }
                Expectation::Sat { .. } => witnesses += 1,
            }
        }
        assert!(
            refutations >= MIN_REFUTATIONS,
            "only {refutations} refutations; the floor is {MIN_REFUTATIONS}. \
             An unsat-expecting suite that stops refuting has stopped working."
        );
        assert!(
            witnesses >= 3,
            "the degenerate controls are what stop a trivially-unsatisfiable \
             builder passing; found only {witnesses}"
        );
    }

    #[test]
    fn control_table_matches_what_is_built() {
        let built: BTreeSet<String> = misconception_catalog()
            .into_iter()
            .map(|s| {
                s.name
                    .strip_prefix("misconception/")
                    .expect("scenario names carry the family prefix")
                    .to_string()
            })
            .collect();
        let declared: BTreeSet<String> = CONTROLS.iter().map(|c| c.name.to_string()).collect();
        assert_eq!(
            built, declared,
            "CONTROLS and misconception_catalog() have drifted apart"
        );
    }

    #[test]
    fn declared_expectations_match_the_scenarios() {
        for scenario in misconception_catalog() {
            let short = scenario.name.strip_prefix("misconception/").unwrap();
            let control = CONTROLS
                .iter()
                .find(|c| c.name == short)
                .unwrap_or_else(|| panic!("no CONTROLS row for {short}"));
            assert_eq!(
                control.refutes,
                scenario.expectation.is_unsat(),
                "{short}: CONTROLS says refutes={}, scenario says unsat={}",
                control.refutes,
                scenario.expectation.is_unsat()
            );
            assert_eq!(
                control.shape == ControlShape::DegenerateControl,
                scenario.expectation.is_sat(),
                "{short}: only degenerate controls may expect sat"
            );
        }
    }

    #[test]
    fn every_control_cites_a_corpus_entry_and_a_curriculum_node() {
        for control in CONTROLS {
            assert!(
                !control.misconceptions.is_empty(),
                "{} cites no misconception",
                control.name
            );
            assert!(
                !control.curriculum_nodes.is_empty(),
                "{} cites no curriculum node",
                control.name
            );
            for node in control.curriculum_nodes {
                assert!(
                    crate::math_node(node).is_some(),
                    "{} cites unknown curriculum node {node}",
                    control.name
                );
            }
        }
    }

    #[test]
    fn premises_alone_are_satisfiable() {
        // The guard against passing for the wrong reason: if a range bound were
        // mistyped so that the constraints themselves were contradictory, every
        // refutation would still come back unsat and the suite would look
        // healthy. Requiring a model of the premises alone catches that.
        for (name, build) in REFUTATIONS {
            let b = build();
            let query = b.premises_query();
            assert!(
                find_model(&b.arena, &query).is_some(),
                "{name}: the premises alone are unsatisfiable, so its refutation \
                 proves nothing about the misconception"
            );
        }
    }

    #[test]
    fn refutations_outnumber_witnesses() {
        // The identity of this suite in one assertion: it is an unsat-expecting
        // suite, not a mixed one.
        let scenarios = misconception_catalog();
        let unsat = scenarios
            .iter()
            .filter(|s| s.expectation.is_unsat())
            .count();
        let sat = scenarios.iter().filter(|s| s.expectation.is_sat()).count();
        assert!(unsat > sat * 4, "{unsat} refutations vs {sat} witnesses");
    }
}
