//! Adversarial differential fuzz for `axeyum-verify` over the arithmetic
//! fragment, with a *trivially-correct* concrete evaluator as the soundness
//! oracle: for a single `let c = a <op> b;` and a random concrete `(a, b)`, if the
//! operation panics (overflow / underflow / ÷0) on that input, then
//! `verify_program` must **never** return `Verified` — a reachable panic forbids a
//! safety claim (the verify analog of a wrong `unsat`). Deterministic, no deps.
#![allow(clippy::cast_possible_truncation)] // intentional in the PRNG

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
