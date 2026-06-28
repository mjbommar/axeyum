//! C4.4 — auto-route a `#[verify]` `let* ; while` Program through the warm BMC
//! loop system, and cross-check it against the existing unroll route
//! (`verify_program`): the two must agree on bug-vs-safe.

use axeyum_solver::SolverConfig;
use axeyum_verify::ast::{BinOp, Expr, Param, Program, Stmt, Ty};
use axeyum_verify::bmc::LoopSafety;
use axeyum_verify::loop_system::check_program_loop;
use axeyum_verify::{Verdict, verify_program};

const U8: Ty = Ty::Int {
    width: 8,
    signed: false,
};

fn var(n: &str) -> Expr {
    Expr::Var(n.to_string())
}
fn lit(value: u128) -> Expr {
    Expr::IntLit { value, ty: U8 }
}
fn bin(op: BinOp, l: Expr, r: Expr) -> Expr {
    Expr::Binary {
        op,
        lhs: Box::new(l),
        rhs: Box::new(r),
    }
}

/// `fn f(limit: u8) { let mut i = 0; while i < limit { i = i + 1; assert!(i != bad); } }`.
fn program(bad: u128) -> Program {
    Program {
        name: "f".to_string(),
        params: vec![Param {
            name: "limit".to_string(),
            ty: U8,
        }],
        arrays: vec![],
        body: vec![
            Stmt::Let {
                name: "i".to_string(),
                ty: U8,
                value: lit(0),
            },
            Stmt::While {
                cond: bin(BinOp::Lt, var("i"), var("limit")),
                bound: 10,
                body: vec![
                    Stmt::Assign {
                        name: "i".to_string(),
                        value: bin(BinOp::Add, var("i"), lit(1)),
                    },
                    Stmt::Assert(bin(BinOp::Ne, var("i"), lit(bad))),
                ],
            },
        ],
    }
}

#[test]
fn warm_route_matches_unroll_route_on_a_buggy_loop() {
    let cfg = SolverConfig::default();
    let prog = program(5);

    // Warm BMC route (C4.4 auto-routing).
    let warm = check_program_loop(&prog, 10, &cfg)
        .expect("in the loop fragment")
        .expect("no solver error");
    let warm_bug = matches!(warm, LoopSafety::BugReachable { .. });

    // Unroll route (the established path).
    let unroll = verify_program(&prog, &cfg).expect("verify");
    let unroll_bug = matches!(unroll, Verdict::Counterexample { .. });

    assert!(
        warm_bug,
        "warm route must find the i==5 assertion violation, got {warm:?}"
    );
    assert_eq!(
        warm_bug, unroll_bug,
        "warm and unroll routes must agree (both find the bug)"
    );
}

#[test]
fn warm_route_matches_unroll_route_on_a_safe_loop() {
    let cfg = SolverConfig::default();
    let prog = program(200); // out of reach within bound 10

    let warm = check_program_loop(&prog, 10, &cfg)
        .expect("in the loop fragment")
        .expect("no solver error");
    let warm_safe = matches!(warm, LoopSafety::SafeWithinBound { .. });

    let unroll = verify_program(&prog, &cfg).expect("verify");
    let unroll_safe = matches!(unroll, Verdict::Verified { .. });

    assert!(
        warm_safe,
        "warm route must prove safe within bound, got {warm:?}"
    );
    assert_eq!(
        warm_safe, unroll_safe,
        "warm and unroll routes must agree (both safe)"
    );
}
