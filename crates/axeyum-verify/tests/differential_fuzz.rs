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

/// Concrete modular result of a wrapping op at unsigned width `w`.
fn wrapped(op: BinOp, w: u32, a: u128, b: u128) -> u128 {
    let mask: u128 = (1u128 << w) - 1;
    let r = match op {
        BinOp::WrappingAdd => a.wrapping_add(b),
        BinOp::WrappingSub => a.wrapping_sub(b),
        BinOp::WrappingMul => a.wrapping_mul(b),
        _ => unreachable!("wrapped() only handles wrapping ops"),
    };
    r & mask
}

#[test]
fn wrapping_value_matches_concrete_modular_result() {
    // Soundness floor for `wrapping_*`: the lowered value must equal the concrete
    // modular result. We assert the always-false `c != <concrete wrapped>`; since
    // `c` *is* that value, the assertion is reachably violated on every input, so
    // verify must never return Verified. (A wrong wrapped value would make the
    // assert pass and verify would wrongly prove safety.)
    let cfg = SolverConfig::default();
    let wops = [BinOp::WrappingAdd, BinOp::WrappingSub, BinOp::WrappingMul];
    let mut rng = Rng(0x_a7a7_d00d_0000_0005);
    let mut checked = 0u32;
    for _ in 0..400 {
        let op = wops[(rng.next() as usize) % wops.len()];
        let w = WIDTHS[(rng.next() as usize) % WIDTHS.len()];
        let mask: u128 = (1u128 << w) - 1;
        let a = u128::from(rng.next()) & mask;
        let b = u128::from(rng.next()) & mask;
        let expect = wrapped(op, w, a, b);
        let ty = Ty::Int {
            width: w,
            signed: false,
        };
        let prog = Program {
            name: "f".to_string(),
            params: vec![],
            arrays: vec![],
            body: vec![
                Stmt::Let {
                    name: "c".to_string(),
                    ty,
                    value: Expr::Binary {
                        op,
                        lhs: Box::new(Expr::IntLit { value: a, ty }),
                        rhs: Box::new(Expr::IntLit { value: b, ty }),
                    },
                },
                // Always-false: `c != expect` (c is exactly `expect`).
                Stmt::Assert(Expr::Binary {
                    op: BinOp::Ne,
                    lhs: Box::new(Expr::Var("c".to_string())),
                    rhs: Box::new(Expr::IntLit {
                        value: expect,
                        ty,
                    }),
                }),
            ],
        };
        checked += 1;
        let verdict = verify_program(&prog, &cfg).expect("verify");
        assert!(
            !matches!(verdict, Verdict::Verified { .. }),
            "wrong-safe (wrapping): {a} {op:?} {b} (u{w}) = {expect}; the always-false \
             assert `c != {expect}` must be reachable, but verify returned {verdict:?}"
        );
    }
    assert!(checked >= 10, "wrapping fuzz exercised too few cases");
}

/// Concrete saturating result at unsigned width `w`.
fn saturated_unsigned(op: BinOp, w: u32, a: u128, b: u128) -> u128 {
    let mask: u128 = (1u128 << w) - 1;
    match op {
        BinOp::SaturatingAdd => (a + b).min(mask),
        BinOp::SaturatingSub => a.saturating_sub(b),
        BinOp::SaturatingMul => (a * b).min(mask),
        _ => unreachable!(),
    }
}

/// Concrete saturating result at signed width `w` (clamped to `[min, max]`).
fn saturated_signed(op: BinOp, w: u32, a: i128, b: i128) -> i128 {
    let min = -(1i128 << (w - 1));
    let max = (1i128 << (w - 1)) - 1;
    let r = match op {
        BinOp::SaturatingAdd => a + b,
        BinOp::SaturatingSub => a - b,
        BinOp::SaturatingMul => a * b,
        _ => unreachable!(),
    };
    r.clamp(min, max)
}

#[test]
fn saturating_value_matches_concrete_clamp() {
    // Soundness floor for `saturating_*` (the signed clamp direction is the
    // delicate part): the lowered value must equal the concrete clamped result.
    // We assert the always-false `c != <concrete>`; it must be reachable, so
    // verify must never return Verified. Covers both signednesses.
    let cfg = SolverConfig::default();
    let sops = [
        BinOp::SaturatingAdd,
        BinOp::SaturatingSub,
        BinOp::SaturatingMul,
    ];
    let mut rng = Rng(0x_5a7c_c1a3_0000_0007);
    let mut checked_u = 0u32;
    let mut checked_s = 0u32;
    for _ in 0..600 {
        let op = sops[(rng.next() as usize) % sops.len()];
        let w = WIDTHS[(rng.next() as usize) % WIDTHS.len()];
        let signed = rng.next() % 2 == 0;
        let (val, expect, ty) = if signed {
            let min = -(1i128 << (w - 1));
            let max = (1i128 << (w - 1)) - 1;
            let span = (max - min + 1) as u128;
            let a = min + ((u128::from(rng.next()) % span) as i128);
            let b = min + ((u128::from(rng.next()) % span) as i128);
            let e = saturated_signed(op, w, a, b);
            checked_s += 1;
            (
                (a, b),
                bits(e, w),
                Ty::Int {
                    width: w,
                    signed: true,
                },
            )
        } else {
            let mask: u128 = (1u128 << w) - 1;
            let a = u128::from(rng.next()) & mask;
            let b = u128::from(rng.next()) & mask;
            let e = saturated_unsigned(op, w, a, b);
            checked_u += 1;
            (
                (a as i128, b as i128),
                e,
                Ty::Int {
                    width: w,
                    signed: false,
                },
            )
        };
        let (a_pat, b_pat) = if signed {
            (bits(val.0, w), bits(val.1, w))
        } else {
            (val.0 as u128, val.1 as u128)
        };
        let prog = Program {
            name: "f".to_string(),
            params: vec![],
            arrays: vec![],
            body: vec![
                Stmt::Let {
                    name: "c".to_string(),
                    ty,
                    value: Expr::Binary {
                        op,
                        lhs: Box::new(Expr::IntLit { value: a_pat, ty }),
                        rhs: Box::new(Expr::IntLit { value: b_pat, ty }),
                    },
                },
                Stmt::Assert(Expr::Binary {
                    op: BinOp::Ne,
                    lhs: Box::new(Expr::Var("c".to_string())),
                    rhs: Box::new(Expr::IntLit { value: expect, ty }),
                }),
            ],
        };
        let verdict = verify_program(&prog, &cfg).expect("verify");
        assert!(
            !matches!(verdict, Verdict::Verified { .. }),
            "wrong saturating value: {op:?} signed={signed} (w{w}) expected bit-pattern \
             {expect}, but the always-false assert was proved unreachable ({verdict:?})"
        );
    }
    assert!(
        checked_u >= 10 && checked_s >= 10,
        "saturating fuzz under-exercised (u={checked_u}, s={checked_s})"
    );
}

#[test]
fn min_max_value_matches_concrete() {
    // `min`/`max` must select the signedness-correct operand. Assert the
    // always-false `c != <concrete min/max>`; it must stay reachable (a wrong
    // selection would make verify wrongly prove safety). Both signednesses.
    let cfg = SolverConfig::default();
    let mut rng = Rng(0x_d1d4_0000_0000_0003);
    let mut checked_u = 0u32;
    let mut checked_s = 0u32;
    for _ in 0..600 {
        let is_max = rng.next() % 2 == 0;
        let w = WIDTHS[(rng.next() as usize) % WIDTHS.len()];
        let signed = rng.next() % 2 == 0;
        let (a_pat, b_pat, expect, ty) = if signed {
            let min = -(1i128 << (w - 1));
            let max = (1i128 << (w - 1)) - 1;
            let span = (max - min + 1) as u128;
            let a = min + ((u128::from(rng.next()) % span) as i128);
            let b = min + ((u128::from(rng.next()) % span) as i128);
            let e = if is_max { a.max(b) } else { a.min(b) };
            checked_s += 1;
            (
                bits(a, w),
                bits(b, w),
                bits(e, w),
                Ty::Int {
                    width: w,
                    signed: true,
                },
            )
        } else {
            let mask: u128 = (1u128 << w) - 1;
            let a = u128::from(rng.next()) & mask;
            let b = u128::from(rng.next()) & mask;
            let e = if is_max { a.max(b) } else { a.min(b) };
            checked_u += 1;
            (
                a,
                b,
                e,
                Ty::Int {
                    width: w,
                    signed: false,
                },
            )
        };
        let op = if is_max { BinOp::Max } else { BinOp::Min };
        let prog = Program {
            name: "f".to_string(),
            params: vec![],
            arrays: vec![],
            body: vec![
                Stmt::Let {
                    name: "c".to_string(),
                    ty,
                    value: Expr::Binary {
                        op,
                        lhs: Box::new(Expr::IntLit { value: a_pat, ty }),
                        rhs: Box::new(Expr::IntLit { value: b_pat, ty }),
                    },
                },
                Stmt::Assert(Expr::Binary {
                    op: BinOp::Ne,
                    lhs: Box::new(Expr::Var("c".to_string())),
                    rhs: Box::new(Expr::IntLit { value: expect, ty }),
                }),
            ],
        };
        let verdict = verify_program(&prog, &cfg).expect("verify");
        assert!(
            !matches!(verdict, Verdict::Verified { .. }),
            "wrong min/max value: {op:?} signed={signed} (w{w}) expected {expect}, got {verdict:?}"
        );
    }
    assert!(
        checked_u >= 10 && checked_s >= 10,
        "min/max fuzz under-exercised (u={checked_u}, s={checked_s})"
    );
}

#[test]
fn abs_desugar_min_overflow_and_value() {
    // The `.abs()` desugar shape `ite(a < 0, -a, a)`: at `a == iN::MIN` the `-a`
    // arm records the negation-overflow panic (reachable → never Verified); for
    // any other `a` the value must equal `|a|`, checked by an always-false assert.
    use axeyum_verify::ast::UnOp;
    let cfg = SolverConfig::default();
    let mut rng = Rng(0x_ab50_0000_0000_000b);
    let mut checked_min = 0u32;
    let mut checked_val = 0u32;
    for _ in 0..500 {
        let w = WIDTHS[(rng.next() as usize) % WIDTHS.len()];
        let min = -(1i128 << (w - 1));
        let max = (1i128 << (w - 1)) - 1;
        let span = (max - min + 1) as u128;
        let a = if rng.next() % 4 == 0 {
            min // force the overflow edge
        } else {
            min + ((u128::from(rng.next()) % span) as i128)
        };
        let is_min = a == min;
        if is_min {
            checked_min += 1;
        } else {
            checked_val += 1;
        }
        let ty = Ty::Int {
            width: w,
            signed: true,
        };
        let a_expr = Expr::IntLit { value: bits(a, w), ty };
        // ite(a < 0, -a, a)
        let abs_expr = Expr::Ite {
            cond: Box::new(Expr::Binary {
                op: BinOp::Lt,
                lhs: Box::new(a_expr.clone()),
                rhs: Box::new(Expr::IntLit { value: 0, ty }),
            }),
            then: Box::new(Expr::Unary {
                op: UnOp::Neg,
                operand: Box::new(a_expr.clone()),
            }),
            els: Box::new(a_expr.clone()),
        };
        // For non-MIN, the always-false `c != |a|` must be reachable. For MIN the
        // Neg-overflow alone makes the program non-Verified (expect is unused).
        let expect = if is_min { 0 } else { bits(a.abs(), w) };
        let prog = Program {
            name: "f".to_string(),
            params: vec![],
            arrays: vec![],
            body: vec![
                Stmt::Let {
                    name: "c".to_string(),
                    ty,
                    value: abs_expr,
                },
                Stmt::Assert(Expr::Binary {
                    op: BinOp::Ne,
                    lhs: Box::new(Expr::Var("c".to_string())),
                    rhs: Box::new(Expr::IntLit { value: expect, ty }),
                }),
            ],
        };
        let verdict = verify_program(&prog, &cfg).expect("verify");
        assert!(
            !matches!(verdict, Verdict::Verified { .. }),
            "abs desugar wrong-safe: a={a} (i{w}, is_min={is_min}) returned {verdict:?}"
        );
    }
    assert!(
        checked_min >= 5 && checked_val >= 10,
        "abs fuzz under-exercised (min={checked_min}, val={checked_val})"
    );
}

#[test]
#[allow(clippy::too_many_lines)] // a flat fuzz body over both signednesses
fn overflows_node_and_unwrap_or_value() {
    // The `checked_*.unwrap_or(d)` desugar `ite(!Overflows(op,a,b), wrapping_op, d)`
    // must compute: the real result when no overflow, else the default. Checked
    // against a concrete oracle over both signednesses by asserting the always-
    // false `c != expected` (must stay reachable → never Verified). This also
    // pins the `Overflows` predicate's direction.
    use axeyum_verify::ast::UnOp;
    let cfg = SolverConfig::default();
    let ops = [
        (BinOp::Add, BinOp::WrappingAdd),
        (BinOp::Sub, BinOp::WrappingSub),
        (BinOp::Mul, BinOp::WrappingMul),
    ];
    let default_pat: u128 = 7;
    let mut rng = Rng(0x_0f10_0000_0000_000du64);
    let mut checked_u = 0u32;
    let mut checked_s = 0u32;
    let mut hit_overflow = 0u32;
    for _ in 0..800 {
        let (ovf_op, wrap_op) = ops[(rng.next() as usize) % ops.len()];
        let w = WIDTHS[(rng.next() as usize) % WIDTHS.len()];
        let signed = rng.next() % 2 == 0;
        let (a_pat, b_pat, expect, ty) = if signed {
            let min = -(1i128 << (w - 1));
            let max = (1i128 << (w - 1)) - 1;
            let span = (max - min + 1) as u128;
            let a = min + ((u128::from(rng.next()) % span) as i128);
            let b = min + ((u128::from(rng.next()) % span) as i128);
            let ovf = panics_signed(ovf_op, w, a, b);
            if ovf {
                hit_overflow += 1;
            }
            let real = match ovf_op {
                BinOp::Add => a.wrapping_add(b),
                BinOp::Sub => a.wrapping_sub(b),
                BinOp::Mul => a.wrapping_mul(b),
                _ => unreachable!(),
            };
            let e = if ovf { default_pat } else { bits(real, w) };
            checked_s += 1;
            (
                bits(a, w),
                bits(b, w),
                e,
                Ty::Int {
                    width: w,
                    signed: true,
                },
            )
        } else {
            let mask: u128 = (1u128 << w) - 1;
            let a = u128::from(rng.next()) & mask;
            let b = u128::from(rng.next()) & mask;
            let ovf = panics(ovf_op, w, a, b);
            if ovf {
                hit_overflow += 1;
            }
            let e = if ovf {
                default_pat
            } else {
                wrapped(wrap_op, w, a, b)
            };
            checked_u += 1;
            (
                a,
                b,
                e,
                Ty::Int {
                    width: w,
                    signed: false,
                },
            )
        };
        let a_e = Expr::IntLit { value: a_pat, ty };
        let b_e = Expr::IntLit { value: b_pat, ty };
        let desugar = Expr::Ite {
            cond: Box::new(Expr::Unary {
                op: UnOp::Not,
                operand: Box::new(Expr::Overflows {
                    op: ovf_op,
                    lhs: Box::new(a_e.clone()),
                    rhs: Box::new(b_e.clone()),
                }),
            }),
            then: Box::new(Expr::Binary {
                op: wrap_op,
                lhs: Box::new(a_e.clone()),
                rhs: Box::new(b_e.clone()),
            }),
            els: Box::new(Expr::IntLit {
                value: default_pat,
                ty,
            }),
        };
        let prog = Program {
            name: "f".to_string(),
            params: vec![],
            arrays: vec![],
            body: vec![
                Stmt::Let {
                    name: "c".to_string(),
                    ty,
                    value: desugar,
                },
                Stmt::Assert(Expr::Binary {
                    op: BinOp::Ne,
                    lhs: Box::new(Expr::Var("c".to_string())),
                    rhs: Box::new(Expr::IntLit { value: expect, ty }),
                }),
            ],
        };
        let verdict = verify_program(&prog, &cfg).expect("verify");
        assert!(
            !matches!(verdict, Verdict::Verified { .. }),
            "unwrap_or desugar wrong-safe: {ovf_op:?} signed={signed} (w{w}) expected {expect}, \
             got {verdict:?}"
        );
    }
    assert!(
        checked_u >= 10 && checked_s >= 10 && hit_overflow >= 10,
        "unwrap_or fuzz under-exercised (u={checked_u}, s={checked_s}, ovf={hit_overflow})"
    );
}

/// Width-`w` rotation oracle (`by` taken modulo `w`).
fn rotated(left: bool, w: u32, x: u128, by: u32) -> u128 {
    let mask: u128 = (1u128 << w) - 1;
    let by = by % w;
    if by == 0 {
        return x & mask;
    }
    let r = if left {
        (x << by) | (x >> (w - by))
    } else {
        (x >> by) | (x << (w - by))
    };
    r & mask
}

#[test]
fn rotate_value_matches_concrete() {
    // `Expr::Rotate` must equal the width-correct rotation. Assert the always-false
    // `c != <concrete rotate>`; it must stay reachable → never Verified.
    let cfg = SolverConfig::default();
    let mut rng = Rng(0x_7012_a7e0_0000_0001);
    let mut checked = 0u32;
    for _ in 0..400 {
        let left = rng.next() % 2 == 0;
        let w = WIDTHS[(rng.next() as usize) % WIDTHS.len()];
        let mask: u128 = (1u128 << w) - 1;
        let x = u128::from(rng.next()) & mask;
        let by = (rng.next() % u64::from(w + 3)) as u32; // include by >= w (mod)
        let expect = rotated(left, w, x, by);
        let ty = Ty::Int {
            width: w,
            signed: false,
        };
        let prog = Program {
            name: "f".to_string(),
            params: vec![],
            arrays: vec![],
            body: vec![
                Stmt::Let {
                    name: "c".to_string(),
                    ty,
                    value: Expr::Rotate {
                        left,
                        by,
                        operand: Box::new(Expr::IntLit { value: x, ty }),
                    },
                },
                Stmt::Assert(Expr::Binary {
                    op: BinOp::Ne,
                    lhs: Box::new(Expr::Var("c".to_string())),
                    rhs: Box::new(Expr::IntLit { value: expect, ty }),
                }),
            ],
        };
        checked += 1;
        let verdict = verify_program(&prog, &cfg).expect("verify");
        assert!(
            !matches!(verdict, Verdict::Verified { .. }),
            "wrong rotate: left={left} x={x} by={by} (w{w}) expected {expect}, got {verdict:?}"
        );
    }
    assert!(checked >= 10, "rotate fuzz under-exercised");
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
