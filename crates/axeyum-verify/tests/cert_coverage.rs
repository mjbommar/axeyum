//! Lean-certificate coverage — the headline moat metric.
//!
//! For each `Verified` result, [`axeyum_verify::cert_coverage`] reports the
//! fraction carrying a self-contained Lean 4 module (`Verdict::Verified.lean_module`)
//! re-proving the bounded-safety refutation — the certificate Kani / CBMC cannot
//! produce. This file runs a small set of *safe* (verifiable) functions, tallies
//! the coverage, and prints it like the property scoreboard.
//!
//! The fraction is currently capped by the upstream Lean reconstructor's
//! fragment (see `UPSTREAM-FEEDBACK` U1/U4): a separate-conjunct comparison
//! contradiction over `QF_BV` reconstructs; a single bitwise-bounded refutation
//! routes through `DRAT` and declines the Lean emitter. We assert the *measured*
//! number is reported honestly (`lean_module.is_some()` ⟺ a real, reconstructed
//! module), never a false promise.

use axeyum_verify::ast::{BinOp, Expr, Param, Program, Stmt, Ty, UnOp};
use axeyum_verify::{Verdict, cert_coverage, default_config, verify_program};

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

/// `let r = x & 0x0f; assert!(r <= 15);` — a bitwise bound (`QF_BV`).
fn masked_clamp() -> Program {
    Program {
        name: "clamp".into(),
        params: vec![Param {
            name: "x".into(),
            ty: u(8),
        }],
        arrays: vec![],
        body: vec![
            Stmt::Let {
                name: "r".into(),
                ty: u(8),
                value: bin(BinOp::BitAnd, var("x"), lit(0x0f, u(8))),
            },
            Stmt::Assert(bin(BinOp::Le, var("r"), lit(15, u(8)))),
        ],
    }
}

/// `assert!(x | 0xff == 0xff)` over `u8` — another bitwise `QF_BV` bound.
fn or_saturates() -> Program {
    Program {
        name: "or_sat".into(),
        params: vec![Param {
            name: "x".into(),
            ty: u(8),
        }],
        arrays: vec![],
        body: vec![Stmt::Assert(bin(
            BinOp::Eq,
            bin(BinOp::BitOr, var("x"), lit(0xff, u(8))),
            lit(0xff, u(8)),
        ))],
    }
}

/// `assert!((x & 1) <= 1)` — a low-bit bound.
fn low_bit() -> Program {
    Program {
        name: "low_bit".into(),
        params: vec![Param {
            name: "x".into(),
            ty: u(8),
        }],
        arrays: vec![],
        body: vec![Stmt::Assert(bin(
            BinOp::Le,
            bin(BinOp::BitAnd, var("x"), lit(1, u(8))),
            lit(1, u(8)),
        ))],
    }
}

/// `fn f(a:u8,b:u8) { if a <= b { assert!(!(b < a)); } }` — antisymmetry of the
/// unsigned order. Its safety refutation `[a ≤ b, b < a]` is exactly the
/// separate-conjunct comparison-contradiction shape the `QF_BV` Lean
/// reconstructor covers, so this verified result **carries a Lean module** (see
/// `UPSTREAM-FEEDBACK` U1 for why the shape matters).
fn antisymmetry() -> Program {
    Program {
        name: "antisymmetry".into(),
        params: vec![
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
            cond: bin(BinOp::Le, var("a"), var("b")),
            // assert!(!(b < a)) — the double-negation reduces to the positive
            // comparison literal the reconstructor keys off.
            then: vec![Stmt::Assert(Expr::Unary {
                op: UnOp::Not,
                operand: Box::new(bin(BinOp::Lt, var("b"), var("a"))),
            })],
            els: vec![],
        }],
    }
}

#[test]
fn antisymmetry_carries_a_lean_module() {
    match run(&antisymmetry()) {
        Verdict::Verified {
            certified,
            lean_module,
        } => {
            assert!(certified, "antisymmetry proof must re-check");
            let module = lean_module.expect(
                "the comparison-contradiction safety proof must carry a Lean module \
                 (the headline moat artifact)",
            );
            assert!(
                module.contains("theorem axeyum_refutation") && module.contains("False"),
                "the Lean module must be the real refutation module"
            );
        }
        other => panic!("antisymmetry must verify, got {other:?}"),
    }
}

#[test]
fn lean_cert_coverage_is_reported_and_sound() {
    let programs = [masked_clamp(), or_saturates(), low_bit(), antisymmetry()];
    let verdicts: Vec<Verdict> = programs.iter().map(run).collect();

    // Every one must verify with a re-checked certificate (the soundness floor
    // for `Verified`).
    for (p, v) in programs.iter().zip(&verdicts) {
        match v {
            Verdict::Verified { certified, .. } => {
                assert!(certified, "`{}` proof must re-check", p.name);
            }
            other => panic!("`{}` must verify, got {other:?}", p.name),
        }
    }

    let cov = cert_coverage(&verdicts);
    assert_eq!(cov.verified, programs.len());
    assert_eq!(cov.certified, programs.len());

    // Headline moat number, printed like the property scoreboard.
    eprintln!(
        "axeyum-verify Lean-cert coverage: {}/{} verified carry a Lean module ({:.1}%); \
         {}/{} re-checked their in-tree certificate.",
        cov.lean_certified,
        cov.verified,
        cov.lean_fraction() * 100.0,
        cov.certified,
        cov.verified,
    );

    // Soundness of the metric: a reported Lean module must be a *real*,
    // non-empty Lean 4 module (never a false promise). The exact count is capped
    // by the upstream reconstructor (UPSTREAM-FEEDBACK U1/U4), so we assert the
    // *shape* of any module that IS produced rather than a fixed count.
    for v in &verdicts {
        if let Verdict::Verified {
            lean_module: Some(m),
            ..
        } = v
        {
            assert!(
                m.contains("theorem axeyum_refutation") && m.contains("False"),
                "a produced Lean module must be the real refutation module"
            );
        }
    }

    // The metric must be in range and consistent.
    assert!(cov.lean_certified <= cov.verified);
    assert!((0.0..=1.0).contains(&cov.lean_fraction()));
}
