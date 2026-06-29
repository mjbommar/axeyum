//! Adversarial differential fuzz for `axeyum-verify` over the arithmetic
//! fragment, with a *trivially-correct* concrete evaluator as the soundness
//! oracle: for a single `let c = a <op> b;` and a random concrete `(a, b)`, if the
//! operation panics (overflow / underflow / ÷0) on that input, then
//! `verify_program` must **never** return `Verified` — a reachable panic forbids a
//! safety claim (the verify analog of a wrong `unsat`). Deterministic, no deps.
// Intentional casts in the PRNG / two's-complement bit-pattern math.
#![allow(
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    clippy::cast_possible_wrap
)]

use axeyum_solver::SolverConfig;
use axeyum_verify::ast::{BinOp, Expr, Param, Program, Stmt, Ty};
use axeyum_verify::{Verdict, verify_program};

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0 ^ (self.0 >> 31)
    }
}

/// Widths kept ≤ 32 so `a + b` / `a * b` cannot overflow the `u128` we evaluate in.
const WIDTHS: &[u32] = &[8, 16, 32];
const OPS: &[BinOp] = &[BinOp::Add, BinOp::Sub, BinOp::Mul, BinOp::Div, BinOp::Rem];

/// Ground truth: does `a <op> b` panic at unsigned width `w` (the panic classes
/// `verify` models for these ops)?
fn panics(op: BinOp, w: u32, a: u128, b: u128) -> bool {
    let mask: u128 = if w == 128 {
        u128::MAX
    } else {
        (1u128 << w) - 1
    };
    match op {
        BinOp::Add => a + b > mask,
        BinOp::Sub => a < b,
        BinOp::Mul => a * b > mask,
        BinOp::Div | BinOp::Rem => b == 0,
        _ => false,
    }
}

fn program(op: BinOp, w: u32, a: u128, b: u128) -> Program {
    let ty = Ty::Int {
        width: w,
        signed: false,
    };
    // `fn f() { let a = <a>; let b = <b>; let c = a <op> b; }` — concrete inputs so
    // the single witnessing assignment matches the evaluator's (a, b).
    Program {
        name: "f".to_string(),
        params: vec![Param {
            name: "x".to_string(),
            ty,
        }],
        arrays: vec![],
        body: vec![
            Stmt::Let {
                name: "a".to_string(),
                ty,
                value: Expr::IntLit { value: a, ty },
            },
            Stmt::Let {
                name: "b".to_string(),
                ty,
                value: Expr::IntLit { value: b, ty },
            },
            Stmt::Let {
                name: "c".to_string(),
                ty,
                value: Expr::Binary {
                    op,
                    lhs: Box::new(Expr::Var("a".to_string())),
                    rhs: Box::new(Expr::Var("b".to_string())),
                },
            },
        ],
    }
}

#[test]
fn reachable_arithmetic_panic_is_never_verified() {
    let cfg = SolverConfig::default();
    let mut rng = Rng(0x00d1_f7e5_7a11_0001);
    let mut checked = 0u32;
    for _ in 0..400 {
        let op = OPS[(rng.next() as usize) % OPS.len()];
        let w = WIDTHS[(rng.next() as usize) % WIDTHS.len()];
        let mask: u128 = (1u128 << w) - 1;
        let mut a = u128::from(rng.next()) & mask;
        let mut b = u128::from(rng.next()) & mask;
        // Occasionally force the ÷0 / underflow edges so they are exercised.
        if rng.next() % 4 == 0 {
            b = 0;
        }
        if rng.next() % 4 == 0 {
            a = a.min(b);
        }
        if !panics(op, w, a, b) {
            continue;
        }
        checked += 1;
        let verdict = verify_program(&program(op, w, a, b), &cfg).expect("verify");
        assert!(
            !matches!(verdict, Verdict::Verified { .. }),
            "wrong-safe: {a} {op:?} {b} (u{w}) panics but verify returned {verdict:?}"
        );
    }
    assert!(
        checked >= 10,
        "fuzz exercised too few panicking cases ({checked})"
    );
}

/// Signed ground truth: does `a <op> b` panic at signed width `w`?
fn panics_signed(op: BinOp, w: u32, a: i128, b: i128) -> bool {
    let min = -(1i128 << (w - 1));
    let max = (1i128 << (w - 1)) - 1;
    let oob = |r: i128| r < min || r > max;
    match op {
        BinOp::Add => oob(a + b),
        BinOp::Sub => oob(a - b),
        BinOp::Mul => oob(a * b),
        BinOp::Div => b == 0 || (a == min && b == -1),
        BinOp::Rem => b == 0,
        _ => false,
    }
}

/// Two's-complement bit pattern of signed `v` at width `w` (what `IntLit` wants).
fn bits(v: i128, w: u32) -> u128 {
    let mask: u128 = (1u128 << w) - 1;
    (v as u128) & mask
}

#[test]
fn reachable_signed_arithmetic_panic_is_never_verified() {
    let cfg = SolverConfig::default();
    let mut rng = Rng(0x5167_0000_0000_0009);
    let mut checked = 0u32;
    for _ in 0..400 {
        let op = OPS[(rng.next() as usize) % OPS.len()];
        let w = WIDTHS[(rng.next() as usize) % WIDTHS.len()];
        let min = -(1i128 << (w - 1));
        let max = (1i128 << (w - 1)) - 1;
        let span = (max - min + 1) as u128;
        let mut a = min + ((u128::from(rng.next()) % span) as i128);
        let mut b = min + ((u128::from(rng.next()) % span) as i128);
        // Force the MIN/-1 and ÷0 edges occasionally.
        if rng.next() % 5 == 0 {
            a = min;
            b = -1;
        }
        if rng.next() % 5 == 0 {
            b = 0;
        }
        if !panics_signed(op, w, a, b) {
            continue;
        }
        checked += 1;
        let ty = Ty::Int {
            width: w,
            signed: true,
        };
        let prog = Program {
            name: "f".to_string(),
            params: vec![Param {
                name: "x".to_string(),
                ty,
            }],
            arrays: vec![],
            body: vec![
                Stmt::Let {
                    name: "a".to_string(),
                    ty,
                    value: Expr::IntLit {
                        value: bits(a, w),
                        ty,
                    },
                },
                Stmt::Let {
                    name: "b".to_string(),
                    ty,
                    value: Expr::IntLit {
                        value: bits(b, w),
                        ty,
                    },
                },
                Stmt::Let {
                    name: "c".to_string(),
                    ty,
                    value: Expr::Binary {
                        op,
                        lhs: Box::new(Expr::Var("a".to_string())),
                        rhs: Box::new(Expr::Var("b".to_string())),
                    },
                },
            ],
        };
        let verdict = verify_program(&prog, &cfg).expect("verify");
        assert!(
            !matches!(verdict, Verdict::Verified { .. }),
            "wrong-safe (signed): {a} {op:?} {b} (i{w}) panics but verify returned {verdict:?}"
        );
    }
    assert!(
        checked >= 10,
        "signed fuzz exercised too few panicking cases ({checked})"
    );
}

/// Build the nested if/else *dispatch* chain that `match scrut { k => .., _ => .. }`
/// desugars to: a right-fold where each literal arm is `if scrut == k { body }
/// else { <rest> }` and the wildcard is the innermost else. Each arm body is a
/// single `let c = a <op> b;` (the op that may panic). `scrut` is a concrete let,
/// so exactly one arm is reachable.
fn dispatch_program(
    w: u32,
    scrut: u128,
    arms: &[(u128, BinOp, u128, u128)],
    wild: (BinOp, u128, u128),
) -> Program {
    let ty = Ty::Int {
        width: w,
        signed: false,
    };
    let arm_body = |op: BinOp, a: u128, b: u128| -> Vec<Stmt> {
        vec![Stmt::Let {
            name: "c".to_string(),
            ty,
            value: Expr::Binary {
                op,
                lhs: Box::new(Expr::IntLit { value: a, ty }),
                rhs: Box::new(Expr::IntLit { value: b, ty }),
            },
        }]
    };
    // Innermost else = wildcard; fold the literal arms outward (as the macro does).
    let (wop, wa, wb) = wild;
    let mut els: Vec<Stmt> = arm_body(wop, wa, wb);
    for &(k, op, a, b) in arms.iter().rev() {
        let if_stmt = Stmt::If {
            cond: Expr::Binary {
                op: BinOp::Eq,
                lhs: Box::new(Expr::Var("s".to_string())),
                rhs: Box::new(Expr::IntLit { value: k, ty }),
            },
            then: arm_body(op, a, b),
            els,
        };
        els = vec![if_stmt];
    }
    Program {
        name: "f".to_string(),
        params: vec![],
        arrays: vec![],
        body: {
            let mut body = vec![Stmt::Let {
                name: "s".to_string(),
                ty,
                value: Expr::IntLit { value: scrut, ty },
            }];
            body.extend(els);
            body
        },
    }
}

#[test]
fn reachable_panic_in_dispatch_arm_is_never_verified() {
    // The soundness floor for the `match`-on-int desugar: if the concretely-selected
    // arm's op panics, verify must never return Verified. Exercises the nested
    // if/else chain + per-branch panic-predicate folding the macro produces.
    let cfg = SolverConfig::default();
    let mut rng = Rng(0x_3a7c_4a7c_0000_0011);
    let mut checked = 0u32;
    for _ in 0..400 {
        let w = WIDTHS[(rng.next() as usize) % WIDTHS.len()];
        let mask: u128 = (1u128 << w) - 1;
        // 2–3 distinct literal keys plus a wildcard.
        let n_arms = 2 + (rng.next() as usize) % 2;
        let mk_arm = |rng: &mut Rng, k: u128| {
            let op = OPS[(rng.next() as usize) % OPS.len()];
            let mut a = u128::from(rng.next()) & mask;
            let mut b = u128::from(rng.next()) & mask;
            if rng.next() % 3 == 0 {
                b = 0; // force ÷0 / underflow edges
            }
            if rng.next() % 3 == 0 {
                a = a.min(b);
            }
            (k, op, a, b)
        };
        let arms: Vec<(u128, BinOp, u128, u128)> =
            (0..n_arms).map(|i| mk_arm(&mut rng, i as u128 + 1)).collect();
        let wild = {
            let (_, op, a, b) = mk_arm(&mut rng, 0);
            (op, a, b)
        };
        // Scrutinee: sometimes hit a key, sometimes fall through to the wildcard.
        let scrut = if rng.next() % 2 == 0 {
            arms[(rng.next() as usize) % arms.len()].0
        } else {
            (n_arms as u128) + 5 // distinct from all keys → wildcard
        };
        // Oracle: which arm is selected, and does its op panic?
        let (sel_op, sel_a, sel_b) = arms
            .iter()
            .find(|&&(k, ..)| k == scrut)
            .map_or(wild, |&(_, op, a, b)| (op, a, b));
        if !panics(sel_op, w, sel_a, sel_b) {
            continue;
        }
        checked += 1;
        let prog = dispatch_program(w, scrut, &arms, wild);
        let verdict = verify_program(&prog, &cfg).expect("verify");
        assert!(
            !matches!(verdict, Verdict::Verified { .. }),
            "wrong-safe (dispatch): scrut={scrut} selects {sel_a} {sel_op:?} {sel_b} (u{w}) \
             which panics, but verify returned {verdict:?}"
        );
    }
    assert!(
        checked >= 10,
        "dispatch fuzz exercised too few panicking selections ({checked})"
    );
}

#[test]
fn reachable_index_out_of_bounds_is_never_verified() {
    // `let i = <const>; let x = arr[i];` over arr: [u8; N]. If i >= N the index
    // panics (OOB); verify must then never return Verified.
    use axeyum_verify::ast::ArrayParam;
    let cfg = SolverConfig::default();
    let mut rng = Rng(0x1d_e000_0000_0007);
    let u8t = Ty::Int {
        width: 8,
        signed: false,
    };
    let mut checked = 0u32;
    for _ in 0..300 {
        let n = [1u128, 2, 4, 8][(rng.next() as usize) % 4];
        let i = u128::from(rng.next() & 0xff);
        if i < n {
            continue; // in bounds — no panic to require
        }
        checked += 1;
        let prog = Program {
            name: "f".to_string(),
            params: vec![],
            arrays: vec![ArrayParam {
                name: "arr".to_string(),
                elem: u8t,
                len: n,
            }],
            body: vec![
                Stmt::Let {
                    name: "i".to_string(),
                    ty: u8t,
                    value: Expr::IntLit { value: i, ty: u8t },
                },
                Stmt::Let {
                    name: "x".to_string(),
                    ty: u8t,
                    value: Expr::Index {
                        array: "arr".to_string(),
                        index: Box::new(Expr::Var("i".to_string())),
                        ty: u8t,
                    },
                },
            ],
        };
        let verdict = verify_program(&prog, &cfg).expect("verify");
        assert!(
            !matches!(verdict, Verdict::Verified { .. }),
            "wrong-safe (index): arr[{i}] on [u8; {n}] is OOB but verify returned {verdict:?}"
        );
    }
    assert!(
        checked >= 10,
        "index fuzz exercised too few OOB cases ({checked})"
    );
}
