//! The canonicalizer's quantifier rules, and an exhaustive replay of them.
//!
//! Two rules are under test (`F:quantifier-negation-duality`):
//!
//! * `quant.negation_duality.v1` — `not (forall x. b)` becomes
//!   `exists x. not b`, and dually.
//! * `eq.alpha_equivalent.v1` — an `=` between two quantified formulas that
//!   differ only in bound-variable names (or by the duality above) folds to
//!   `true`.
//!
//! The interesting half is not that they fire, but that they preserve
//! denotation on shapes the unit examples do not cover. The canonicalizer's own
//! precondition guard samples four assignments; [`replay_is_exhaustive`] instead
//! enumerates **every** assignment to the free symbols of a family of quantified
//! Bool/BV formulas and compares the original against the canonical form through
//! the `axeyum-ir` evaluator, which enumerates the bound domains itself. A rule
//! that is wrong on any of these shapes cannot hide behind sparse sampling.

use axeyum_ir::{Assignment, Op, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval};
use axeyum_rewrite::canonicalize;

/// Bit-width of every symbol in the replay family: narrow enough that the
/// evaluator enumerates bound domains cheaply, wide enough that `bvult`,
/// `bvadd` and equality all discriminate.
const WIDTH: u32 = 2;

fn canonical(arena: &mut TermArena, term: TermId) -> TermId {
    canonicalize(arena, term).expect("canonicalize").term
}

// ---------------------------------------------------------------------------
// The rules fire, and produce exactly the dual.
// ---------------------------------------------------------------------------

#[test]
fn negated_universal_becomes_the_dual_existential() {
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::BitVec(WIDTH)).unwrap();
    let a = arena.bv_var("a", WIDTH).unwrap();
    let xv = arena.var(x);
    let body = arena.eq(xv, a).unwrap();
    let universal = arena.forall(x, body).unwrap();
    let negated = arena.not(universal).unwrap();

    let out = canonical(&mut arena, negated);
    let TermNode::App {
        op: Op::Exists(bound),
        args,
    } = arena.node(out).clone()
    else {
        panic!("expected an existential, got {:?}", arena.node(out));
    };
    assert_eq!(bound, x, "the binder is reused verbatim, never renamed");
    assert!(matches!(
        arena.node(args[0]),
        TermNode::App {
            op: Op::BoolNot,
            ..
        }
    ));
}

#[test]
fn negated_existential_becomes_the_dual_universal() {
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::BitVec(WIDTH)).unwrap();
    let a = arena.bv_var("a", WIDTH).unwrap();
    let xv = arena.var(x);
    let body = arena.eq(xv, a).unwrap();
    let existential = arena.exists(x, body).unwrap();
    let negated = arena.not(existential).unwrap();

    let out = canonical(&mut arena, negated);
    assert!(matches!(
        arena.node(out),
        TermNode::App {
            op: Op::Forall(_),
            ..
        }
    ));
}

/// The whole point: the duality identity, written with independently fresh
/// binders as the SMT-LIB front end produces them, folds to `true`.
#[test]
fn the_duality_identity_folds_to_true() {
    let mut arena = TermArena::new();
    let x = arena.declare("!q.x.0", Sort::BitVec(WIDTH)).unwrap();
    let y = arena.declare("!q.x.1", Sort::BitVec(WIDTH)).unwrap();
    let a = arena.bv_var("a", WIDTH).unwrap();

    let xv = arena.var(x);
    let px = arena.eq(xv, a).unwrap();
    let left = arena.forall(x, px).unwrap();
    let left = arena.not(left).unwrap();

    let yv = arena.var(y);
    let py = arena.eq(yv, a).unwrap();
    let not_py = arena.not(py).unwrap();
    let right = arena.exists(y, not_py).unwrap();

    assert_ne!(left, right);
    let identity = arena.eq(left, right).unwrap();
    assert_eq!(canonical(&mut arena, identity), arena.bool_const(true));
}

/// SOUNDNESS NEGATIVE. The near-misses of the duality are contingent, so the
/// canonicalizer must not fold either of them to a constant.
///
/// The binders here are `Bool` and the body is `x or a`, chosen so that both
/// misses genuinely take both truth values — over a bit-vector domain they
/// collapse to constants and would prove nothing. `forall x:Bool. (x or a)` is
/// `a`, so the duality gives `not (forall x. x or a) = exists x. not (x or a)`,
/// both `not a`; flipping only the quantifier leaves `not a = true`, and
/// negating only the body leaves `not a = false`. Each of those is contingent
/// in `a`, and the evaluator confirms it rather than the comment asserting it.
#[test]
fn near_misses_of_the_duality_are_not_folded() {
    for (keep_quantifier, negate_body) in [(true, true), (false, false)] {
        let mut arena = TermArena::new();
        let x = arena.declare("!q.x.0", Sort::Bool).unwrap();
        let y = arena.declare("!q.x.1", Sort::Bool).unwrap();
        let a_symbol = arena.declare("a", Sort::Bool).unwrap();
        let a = arena.var(a_symbol);

        let xv = arena.var(x);
        let px = arena.or(xv, a).unwrap();
        let left = arena.forall(x, px).unwrap();
        let left = arena.not(left).unwrap();

        let yv = arena.var(y);
        let py = arena.or(yv, a).unwrap();
        let body = if negate_body {
            arena.not(py).unwrap()
        } else {
            py
        };
        let right = if keep_quantifier {
            arena.forall(y, body).unwrap()
        } else {
            arena.exists(y, body).unwrap()
        };

        let identity = arena.eq(left, right).unwrap();
        // The near-miss is contingent, so *any* constant fold would be wrong.
        let values = exhaustive_values(&arena, identity, &[(a_symbol, Sort::Bool)]);
        assert!(
            values.contains(&true) && values.contains(&false),
            "the near-miss is not contingent, so it is a poor negative test \
             (keep_quantifier={keep_quantifier}, negate_body={negate_body})"
        );

        let folded = canonical(&mut arena, identity);
        assert_ne!(
            folded,
            arena.bool_const(true),
            "a near-miss folded to true (keep_quantifier={keep_quantifier}, \
             negate_body={negate_body})"
        );
        assert_ne!(
            folded,
            arena.bool_const(false),
            "a near-miss folded to false (keep_quantifier={keep_quantifier}, \
             negate_body={negate_body})"
        );
        assert_eq!(
            exhaustive_values(&arena, folded, &[(a_symbol, Sort::Bool)]),
            values,
            "canonicalization changed the near-miss's denotation"
        );
    }
}

/// The genuine duality identity over the same `Bool` shape *is* folded, so the
/// negative above is discriminating rather than a blanket refusal to fold.
#[test]
fn the_bool_shaped_duality_is_still_folded() {
    let mut arena = TermArena::new();
    let x = arena.declare("!q.x.0", Sort::Bool).unwrap();
    let y = arena.declare("!q.x.1", Sort::Bool).unwrap();
    let a_symbol = arena.declare("a", Sort::Bool).unwrap();
    let a = arena.var(a_symbol);

    let xv = arena.var(x);
    let px = arena.or(xv, a).unwrap();
    let left = arena.forall(x, px).unwrap();
    let left = arena.not(left).unwrap();

    let yv = arena.var(y);
    let py = arena.or(yv, a).unwrap();
    let not_py = arena.not(py).unwrap();
    let right = arena.exists(y, not_py).unwrap();

    let identity = arena.eq(left, right).unwrap();
    assert_eq!(
        exhaustive_values(&arena, identity, &[(a_symbol, Sort::Bool)]),
        vec![true, true],
        "the identity is valid, which is what licenses folding it"
    );
    assert_eq!(canonical(&mut arena, identity), arena.bool_const(true));
}

/// A vacuous binder is still a binder: `not (forall x. p)` where `p` does not
/// mention `x` must become `exists x. not p`, not `not p`.
#[test]
fn vacuous_binder_survives_the_duality_push() {
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::BitVec(WIDTH)).unwrap();
    let p = arena.declare("p", Sort::Bool).unwrap();
    let pv = arena.var(p);
    let universal = arena.forall(x, pv).unwrap();
    let negated = arena.not(universal).unwrap();

    let out = canonical(&mut arena, negated);
    assert!(matches!(
        arena.node(out),
        TermNode::App {
            op: Op::Exists(_),
            ..
        }
    ));
}

// ---------------------------------------------------------------------------
// Exhaustive replay.
// ---------------------------------------------------------------------------

/// Canonicalization must not change the value of any formula in the family, at
/// any assignment to its free symbols. The evaluator enumerates the bound
/// domains, so this checks the quantifier semantics, not merely the skeleton.
#[test]
fn replay_is_exhaustive() {
    let mut checked = 0usize;
    for shape in 0..FAMILY_SIZE {
        let mut arena = TermArena::new();
        let (term, free) = build_shape(&mut arena, shape);
        let folded = canonical(&mut arena, term);
        let before = exhaustive_values(&arena, term, &free);
        let after = exhaustive_values(&arena, folded, &free);
        assert_eq!(
            before, after,
            "canonicalization changed the denotation of family shape {shape}"
        );
        assert!(
            !before.is_empty(),
            "family shape {shape} never evaluated; it proves nothing"
        );
        checked += 1;
    }
    assert_eq!(checked, FAMILY_SIZE);
}

const FAMILY_SIZE: usize = 24;

/// Builds family member `shape` and returns it with its free symbols.
///
/// Each member wraps a quantified core in a different amount of negation and a
/// different quantifier/connective nesting, so the duality rule fires at varying
/// depth and polarity, sometimes twice on one path.
fn build_shape(arena: &mut TermArena, shape: usize) -> (TermId, Vec<(SymbolId, Sort)>) {
    let bound = arena.declare("!q.x.0", Sort::BitVec(WIDTH)).unwrap();
    let inner_bound = arena.declare("!q.y.0", Sort::BitVec(WIDTH)).unwrap();
    let a_symbol = arena.declare("a", Sort::BitVec(WIDTH)).unwrap();
    let b_symbol = arena.declare("b", Sort::BitVec(WIDTH)).unwrap();
    let a = arena.var(a_symbol);
    let b = arena.var(b_symbol);
    let x = arena.var(bound);
    let y = arena.var(inner_bound);

    // Six cores, some with a nested quantifier and some with a free-symbol
    // dependence, so the binder correspondence has something to get wrong.
    let core = match shape % 6 {
        0 => arena.eq(x, a).unwrap(),
        1 => arena.bv_ult(x, a).unwrap(),
        2 => {
            let sum = arena.bv_add(x, a).unwrap();
            arena.eq(sum, b).unwrap()
        }
        3 => {
            let inner = arena.eq(x, y).unwrap();
            arena.exists(inner_bound, inner).unwrap()
        }
        4 => {
            let inner = arena.bv_ult(y, x).unwrap();
            arena.forall(inner_bound, inner).unwrap()
        }
        _ => {
            let left = arena.eq(x, a).unwrap();
            let right = arena.bv_ult(x, b).unwrap();
            arena.or(left, right).unwrap()
        }
    };

    // Four wrappers: universal/existential, each negated once or twice.
    let quantified = if (shape / 6).is_multiple_of(2) {
        arena.forall(bound, core).unwrap()
    } else {
        arena.exists(bound, core).unwrap()
    };
    let term = arena.not(quantified).unwrap();
    let term = if (shape / 12).is_multiple_of(2) {
        term
    } else {
        // A second negation on the outside, plus an equality against the
        // un-negated quantifier, which the alpha rule may or may not reach.
        let doubled = arena.not(term).unwrap();
        arena.eq(doubled, quantified).unwrap()
    };
    (
        term,
        vec![
            (a_symbol, Sort::BitVec(WIDTH)),
            (b_symbol, Sort::BitVec(WIDTH)),
        ],
    )
}

/// Every value `term` takes as `free` ranges over its full domain.
///
/// Assignments where the evaluator declines (an unsupported domain) are skipped
/// rather than counted as agreement; the caller asserts the result is non-empty
/// so a shape that never evaluated cannot masquerade as a passing test.
fn exhaustive_values(arena: &TermArena, term: TermId, free: &[(SymbolId, Sort)]) -> Vec<bool> {
    let sizes: Vec<u64> = free
        .iter()
        .map(|&(_, sort)| match sort {
            Sort::Bool => 2,
            Sort::BitVec(width) => 1u64 << width,
            other => panic!("no enumeration for {other}"),
        })
        .collect();
    let total: u64 = sizes.iter().product();
    let mut seen = Vec::new();
    for index in 0..total {
        let mut assignment = Assignment::new();
        let mut rest = index;
        for (&(symbol, sort), &size) in free.iter().zip(&sizes) {
            let raw = rest % size;
            rest /= size;
            let value = match sort {
                Sort::Bool => Value::Bool(raw == 1),
                Sort::BitVec(width) => Value::Bv {
                    width,
                    value: u128::from(raw),
                },
                other => panic!("no enumeration for {other}"),
            };
            assignment.set(symbol, value);
        }
        if let Ok(Value::Bool(value)) = eval(arena, term, &assignment) {
            seen.push(value);
        }
    }
    seen
}
