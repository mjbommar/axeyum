//! Soundness firewall: a crafted user `declare-fun` whose name collides with a
//! reduction's fresh internal helper must NOT alias it.
//!
//! Solver/rewrite reductions mint fresh placeholder symbols keyed by *predictable*
//! names (`!nia_0`, `!sk_0`, `!int_bv_0`, …). Before the internal-symbol namespace
//! firewall these were minted on the user `declare`/`symbol_lookup` path, so a
//! user symbol of the exact helper name aliased the placeholder and could pin an
//! otherwise-free value — forging a wrong verdict (the same class as the
//! `fp.min`/`fp.max` ±0 wrong-`unsat`). These tests declare the helper name as a
//! user symbol and assert the reduction's verdict is unchanged.
#![cfg(feature = "full")]

use axeyum_ir::{Sort, TermArena, TermId};
use axeyum_solver::{CheckResult, SolverConfig, solve};

/// `x*y = 6 ∧ 1 ≤ x,y ≤ 6` is satisfiable (e.g. x=2, y=3). The NIA linearizer
/// abstracts the product `x*y` to a fresh internal `!nia_0`. A user symbol named
/// `!nia_0`, pinned to a value the real product can never take, must stay
/// independent — under the old aliasing bug it would force `x*y = 999`
/// (impossible in `[1,36]`) and forge a WRONG `unsat`.
#[test]
fn user_declare_cannot_alias_nia_product_abstraction() {
    let mut arena = TermArena::new();

    // The attacker declares `!nia_0` as a user Int symbol up front — exactly what
    // the SMT-LIB parser does for `(declare-fun !nia_0 () Int)`.
    let user = arena.declare("!nia_0", Sort::Int).unwrap();
    let user_v = arena.var(user);

    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let y_sym = arena.declare("y", Sort::Int).unwrap();
    let x = arena.var(x_sym);
    let y = arena.var(y_sym);
    let one = arena.int_const(1);
    let six = arena.int_const(6);
    let big = arena.int_const(999);

    let prod = arena.int_mul(x, y).unwrap();
    let prod_eq = arena.eq(prod, six).unwrap();
    let xlo = arena.int_ge(x, one).unwrap();
    let xhi = arena.int_le(x, six).unwrap();
    let ylo = arena.int_ge(y, one).unwrap();
    let yhi = arena.int_le(y, six).unwrap();
    // The adversarial pin on the user's `!nia_0` — inconsistent with any real
    // in-range product, so aliasing would flip SAT to UNSAT.
    let user_pin = arena.eq(user_v, big).unwrap();

    let assertions = [prod_eq, xlo, xhi, ylo, yhi, user_pin];
    let result = solve(&mut arena, &assertions, &SolverConfig::default()).expect("solve");

    assert!(
        !matches!(result, CheckResult::Unsat),
        "user `!nia_0` aliased the NIA product abstraction — a wrong `unsat` \
         means the internal-symbol firewall was breached (got {result:?})",
    );

    // When the abstraction actually minted its helper, it must be a distinct
    // SymbolId from the user's `!nia_0`.
    if let Some(internal) = arena.find_internal_symbol("!nia_0") {
        assert_ne!(
            internal, user,
            "the NIA `!nia_0` helper aliased the user symbol of the same name",
        );
    }
    assert_eq!(arena.find_symbol("!nia_0"), Some(user));
}

/// A tiny existential `∃x. x = 5` is valid, so its negation-free skolemization
/// (auto's `!sk_*` fresh constants) resolves to SAT. A user `!sk_0` pinned to a
/// different value must not interfere with the fresh skolem constant.
#[test]
fn user_declare_cannot_alias_skolem_constant() {
    let mut arena = TermArena::new();

    let user = arena.declare("!sk_0", Sort::Int).unwrap();
    let user_v = arena.var(user);
    let seven = arena.int_const(7);
    let user_pin = arena.eq(user_v, seven).unwrap();

    // ∃x. x = 5
    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let x = arena.var(x_sym);
    let five = arena.int_const(5);
    let body = arena.eq(x, five).unwrap();
    let exists: TermId = arena.exists(x_sym, body).unwrap();

    let result = solve(&mut arena, &[exists, user_pin], &SolverConfig::default()).expect("solve");
    assert!(
        !matches!(result, CheckResult::Unsat),
        "user `!sk_0` aliased the skolem constant — wrong `unsat` (got {result:?})",
    );
    if let Some(internal) = arena.find_internal_symbol("!sk_0") {
        assert_ne!(internal, user, "skolem `!sk_0` aliased the user symbol");
    }
    assert_eq!(arena.find_symbol("!sk_0"), Some(user));
}
