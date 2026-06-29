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

/// `fn f(limit: u8) { let mut i = 0; let mut x = 0;
///    while i < limit { if i < 3 { x += 10 } else { x += 1 } i += 1; assert!(x != bad) } }`
fn program_if(bad: u128) -> Program {
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
            Stmt::Let {
                name: "x".to_string(),
                ty: U8,
                value: lit(0),
            },
            Stmt::While {
                cond: bin(BinOp::Lt, var("i"), var("limit")),
                bound: 10,
                body: vec![
                    Stmt::If {
                        cond: bin(BinOp::Lt, var("i"), lit(3)),
                        then: vec![Stmt::Assign {
                            name: "x".to_string(),
                            value: bin(BinOp::Add, var("x"), lit(10)),
                        }],
                        els: vec![Stmt::Assign {
                            name: "x".to_string(),
                            value: bin(BinOp::Add, var("x"), lit(1)),
                        }],
                    },
                    Stmt::Assign {
                        name: "i".to_string(),
                        value: bin(BinOp::Add, var("i"), lit(1)),
                    },
                    Stmt::Assert(bin(BinOp::Ne, var("x"), lit(bad))),
                ],
            },
        ],
    }
}

#[test]
fn nested_if_loop_warm_matches_unroll() {
    // C4.5: the in-loop `if` folds into x' = ite(i<3, x+10, x+1). x hits 30 at
    // i==3 (10,20,30), so assert!(x != 30) is violated; both routes must agree.
    let cfg = SolverConfig::default();
    let prog = program_if(30);
    let warm = check_program_loop(&prog, 10, &cfg)
        .expect("in the loop fragment")
        .expect("no solver error");
    let warm_bug = matches!(warm, LoopSafety::BugReachable { .. });
    let unroll_bug = matches!(
        verify_program(&prog, &cfg).expect("verify"),
        Verdict::Counterexample { .. }
    );
    assert!(
        warm_bug,
        "warm route must find the x==30 violation, got {warm:?}"
    );
    assert_eq!(
        warm_bug, unroll_bug,
        "warm and unroll routes must agree on the nested-if loop"
    );
}

#[test]
fn warm_entry_matches_direct_verify() {
    use axeyum_verify::loop_system::verify_program_warm;
    let cfg = SolverConfig::default();
    for bad in [5u128, 200] {
        let p = program(bad);
        let warm = verify_program_warm(&p, 10, &cfg).expect("warm entry");
        let direct = verify_program(&p, &cfg).expect("direct verify");
        assert_eq!(
            matches!(warm, Verdict::Counterexample { .. }),
            matches!(direct, Verdict::Counterexample { .. }),
            "warm entry and direct verify must agree (counterexample) for bad={bad}"
        );
        assert_eq!(
            matches!(warm, Verdict::Verified { .. }),
            matches!(direct, Verdict::Verified { .. }),
            "warm entry and direct verify must agree (verified) for bad={bad}"
        );
    }
}
