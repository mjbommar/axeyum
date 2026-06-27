//! Edge-case tests locking the `if`/`else` environment-merge semantics.
//!
//! At a branch join, [`axeyum_verify::lower`] merges the two arm environments:
//! a binding keeps its value if both arms agree, becomes `ite(cond, then, else)`
//! if both reassign it (same type), and otherwise (reassigned on only one side,
//! or only the pre-branch binding survives) keeps a well-defined value. These
//! tests pin each case via the *observable* verdict — a wrong merge would either
//! miss a reachable panic (unsound) or flag a spurious one (over-approx), so the
//! `Verified`/`Counterexample` outcome is the oracle.

use axeyum_verify::ast::{BinOp, Expr, Param, Program, Stmt, Ty, UnOp};
use axeyum_verify::{Verdict, Witness, default_config, verify_program};

fn u(width: u32) -> Ty {
    Ty::Int {
        width,
        signed: false,
    }
}

fn var(name: &str) -> Expr {
    Expr::Var(name.to_string())
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

fn run(p: &Program) -> Verdict {
    verify_program(p, &default_config()).expect("solver should not hard-error")
}

fn int_bits(inputs: &[Witness], name: &str) -> u128 {
    inputs
        .iter()
        .find_map(|w| match w {
            Witness::Int { name: n, bits, .. } if n == name => Some(*bits),
            _ => None,
        })
        .unwrap_or_else(|| panic!("no int witness `{name}` in {inputs:?}"))
}

// ---- partial reassignment: only the THEN arm reassigns `q` ---------------------

/// `let q = 0; if c { q = 1; } assert!(q <= 1);` — after the join,
/// `q = ite(c, 1, 0)`, both ≤ 1, so the assert holds on every path. A merge that
/// dropped the then-arm value (kept `q = 0`) would still pass here, so we pair it
/// with the dual below that *requires* the merged value.
#[test]
fn partial_reassign_merges_then_value() {
    // let q: u8 = 0; if c { q = 1; } assert!(q == 1 || q == 0);
    let p = Program {
        name: "partial".into(),
        params: vec![Param {
            name: "c".into(),
            ty: Ty::Bool,
        }],
        arrays: vec![],
        body: vec![
            Stmt::Let {
                name: "q".into(),
                ty: u(8),
                value: lit(0, u(8)),
            },
            Stmt::If {
                cond: var("c"),
                then: vec![Stmt::Assign {
                    name: "q".into(),
                    value: lit(1, u(8)),
                }],
                els: vec![],
            },
            // The merged value must be exactly ite(c, 1, 0).
            Stmt::Assert(Expr::Binary {
                op: BinOp::Or,
                lhs: Box::new(bin(BinOp::Eq, var("q"), lit(1, u(8)))),
                rhs: Box::new(bin(BinOp::Eq, var("q"), lit(0, u(8)))),
            }),
        ],
    };
    match run(&p) {
        Verdict::Verified { .. } => {}
        other => panic!("partial-reassign merge must verify, got {other:?}"),
    }
}

/// The dual: `let q = 0; if c { q = 1; } assert!(q == 0);` — this is **false**
/// when `c` (then `q == 1`), so a correct merge yields a counterexample with
/// `c == true`. A merge that wrongly kept `q = 0` would mis-verify this.
#[test]
fn partial_reassign_then_value_is_observed() {
    let p = Program {
        name: "partial_bug".into(),
        params: vec![Param {
            name: "c".into(),
            ty: Ty::Bool,
        }],
        arrays: vec![],
        body: vec![
            Stmt::Let {
                name: "q".into(),
                ty: u(8),
                value: lit(0, u(8)),
            },
            Stmt::If {
                cond: var("c"),
                then: vec![Stmt::Assign {
                    name: "q".into(),
                    value: lit(1, u(8)),
                }],
                els: vec![],
            },
            Stmt::Assert(bin(BinOp::Eq, var("q"), lit(0, u(8)))),
        ],
    };
    let Verdict::Counterexample { class, inputs } = run(&p) else {
        panic!("q==1 on the then-path must violate assert!(q==0)");
    };
    assert_eq!(class, "assert! violated");
    let c = inputs.iter().find_map(|w| match w {
        Witness::Bool { name, value } if name == "c" => Some(*value),
        _ => None,
    });
    assert_eq!(c, Some(true), "the violating path takes the then-branch");
}

// ---- both arms reassign to different values ------------------------------------

/// `let q = 0; if c { q = 10; } else { q = 20; } assert!(q != 10);` — false on the
/// then-path; a correct `ite(c, 10, 20)` merge sees the violation with `c == true`.
#[test]
fn both_arms_reassign_ite_merge() {
    let p = Program {
        name: "both".into(),
        params: vec![Param {
            name: "c".into(),
            ty: Ty::Bool,
        }],
        arrays: vec![],
        body: vec![
            Stmt::Let {
                name: "q".into(),
                ty: u(8),
                value: lit(0, u(8)),
            },
            Stmt::If {
                cond: var("c"),
                then: vec![Stmt::Assign {
                    name: "q".into(),
                    value: lit(10, u(8)),
                }],
                els: vec![Stmt::Assign {
                    name: "q".into(),
                    value: lit(20, u(8)),
                }],
            },
            Stmt::Assert(Expr::Unary {
                op: UnOp::Not,
                operand: Box::new(bin(BinOp::Eq, var("q"), lit(10, u(8)))),
            }),
        ],
    };
    let Verdict::Counterexample { class, inputs } = run(&p) else {
        panic!("q==10 on the then-path must violate the assert");
    };
    assert_eq!(class, "assert! violated");
    let c = inputs.iter().find_map(|w| match w {
        Witness::Bool { name, value } if name == "c" => Some(*value),
        _ => None,
    });
    assert_eq!(c, Some(true));
}

// ---- shadowing: a binding declared INSIDE an arm does not leak out -------------

/// `let q = 5; if c { let q = 99; } assert!(q == 5);` — the inner `q` shadows the
/// outer only within the arm; after the join the outer `q == 5` is restored, so
/// the assert holds. A merge that leaked the shadow would spuriously fail.
#[test]
fn arm_local_shadow_does_not_leak() {
    let p = Program {
        name: "shadow".into(),
        params: vec![Param {
            name: "c".into(),
            ty: Ty::Bool,
        }],
        arrays: vec![],
        body: vec![
            Stmt::Let {
                name: "q".into(),
                ty: u(8),
                value: lit(5, u(8)),
            },
            Stmt::If {
                cond: var("c"),
                // A fresh `let q` inside the then-arm: a new binding, not a
                // reassignment of the outer `q`.
                then: vec![Stmt::Let {
                    name: "q".into(),
                    ty: u(8),
                    value: lit(99, u(8)),
                }],
                els: vec![],
            },
            Stmt::Assert(bin(BinOp::Eq, var("q"), lit(5, u(8)))),
        ],
    };
    match run(&p) {
        Verdict::Verified { .. } => {}
        other => panic!("arm-local shadow must not leak; expected Verified, got {other:?}"),
    }
}

// ---- a panic INSIDE one arm is still reachable through the merge ---------------

/// `if c { let _ = a / b; }` with symbolic `b`: the ÷0 bad state lives on the
/// then-path; a correct merge keeps it reachable (witness `c == true, b == 0`).
#[test]
fn panic_inside_arm_remains_reachable() {
    let p = Program {
        name: "arm_div".into(),
        params: vec![
            Param {
                name: "c".into(),
                ty: Ty::Bool,
            },
            Param {
                name: "a".into(),
                ty: u(8),
            },
            Param {
                name: "b".into(),
                ty: u(8),
            },
        ],
        arrays: vec![],
        body: vec![Stmt::If {
            cond: var("c"),
            then: vec![Stmt::Eval(bin(BinOp::Div, var("a"), var("b")))],
            els: vec![],
        }],
    };
    let Verdict::Counterexample { class, inputs } = run(&p) else {
        panic!("the ÷0 on the then-path must be reachable");
    };
    assert_eq!(class, "division by zero");
    // The witness must take the then-branch and set b == 0.
    let c = inputs.iter().find_map(|w| match w {
        Witness::Bool { name, value } if name == "c" => Some(*value),
        _ => None,
    });
    assert_eq!(c, Some(true), "÷0 only reachable on the then-path");
    assert_eq!(int_bits(&inputs, "b"), 0);
}
