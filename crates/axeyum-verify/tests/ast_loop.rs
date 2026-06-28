//! C4.3 — verify an actual AST loop via the warm BMC route: `loop_system` lowers
//! the loop's guard / per-variable updates / asserts (real restricted-Rust
//! expressions) into a `ScalarLoopSystem`, re-lowering each BMC step against the
//! step's pre-state. This is the AST→warm-`bounded_model_check` integration.

use axeyum_solver::SolverConfig;
use axeyum_verify::ast::{BinOp, Expr, Ty};
use axeyum_verify::bmc::{LoopSafety, run_loop};
use axeyum_verify::loop_system::{AstLoop, loop_system};

const U8: Ty = Ty::Int {
    width: 8,
    signed: false,
};
const U4: Ty = Ty::Int {
    width: 4,
    signed: false,
};

fn var(n: &str) -> Expr {
    Expr::Var(n.to_string())
}
fn lit(value: u128, ty: Ty) -> Expr {
    Expr::IntLit { value, ty }
}
fn bin(op: BinOp, l: Expr, r: Expr) -> Expr {
    Expr::Binary {
        op,
        lhs: Box::new(l),
        rhs: Box::new(r),
    }
}

/// `let mut i = 0; while i < limit { i += 1; assert!(i != bad); }` over `u8`.
fn counter_loop(bad: u128) -> AstLoop {
    AstLoop {
        vars: vec![("i".into(), U8), ("limit".into(), U8)],
        init: vec![Some(0), None], // i = 0; limit is a free input
        guard: bin(BinOp::Lt, var("i"), var("limit")),
        updates: vec![bin(BinOp::Add, var("i"), lit(1, U8)), var("limit")],
        asserts: vec![bin(BinOp::Ne, var("i"), lit(bad, U8))],
    }
}

#[test]
fn ast_counter_loop_finds_assertion_violation() {
    let sys = loop_system(counter_loop(5)).expect("scalar fragment");
    match run_loop(&sys, 10, &SolverConfig::default()).expect("run") {
        LoopSafety::BugReachable { steps, .. } => {
            assert_eq!(steps, 5, "i reaches 5 in 5 iterations");
        }
        other => panic!("expected BugReachable, got {other:?}"),
    }
}

#[test]
fn ast_counter_loop_safe_within_bound() {
    // The forbidden value 200 is out of reach within a 10-iteration bound.
    let sys = loop_system(counter_loop(200)).expect("scalar fragment");
    match run_loop(&sys, 10, &SolverConfig::default()).expect("run") {
        LoopSafety::SafeWithinBound { bound } => assert_eq!(bound, 10),
        other => panic!("expected SafeWithinBound, got {other:?}"),
    }
}

#[test]
fn ast_loop_update_overflow_is_a_bad_state() {
    // `while true { i += 1 }` over u4: the increment overflows at i == 15. The
    // update's overflow panic class is folded into the bad predicate, so it is
    // found (a small width keeps the bound tiny).
    let spec = AstLoop {
        vars: vec![("i".into(), U4)],
        init: vec![Some(0)],
        guard: Expr::BoolLit(true),
        updates: vec![bin(BinOp::Add, var("i"), lit(1, U4))],
        asserts: vec![],
    };
    let sys = loop_system(spec).expect("scalar fragment");
    match run_loop(&sys, 20, &SolverConfig::default()).expect("run") {
        LoopSafety::BugReachable { steps, .. } => assert_eq!(steps, 15, "u4 i+1 overflows at i=15"),
        other => panic!("expected BugReachable (overflow), got {other:?}"),
    }
}
