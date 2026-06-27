//! Runtime (AST-level) tests for the verifier, independent of the proc-macro.
//!
//! These build [`Program`]s by hand (what the macro will emit) and confirm the
//! verdicts, then — for every counterexample — concretely re-execute the modeled
//! semantics on the witness and confirm the panic class actually fires
//! (DISAGREE = 0, the soundness floor).

use axeyum_verify::ast::{BinOp, Expr, Param, Program, Stmt, Ty, UnOp};
use axeyum_verify::{Verdict, Witness, default_config, signed_value, verify_program};

fn u(width: u32) -> Ty {
    Ty::Int {
        width,
        signed: false,
    }
}
fn i(width: u32) -> Ty {
    Ty::Int {
        width,
        signed: true,
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

/// Pull out the integer witness for `name`.
fn int_witness(inputs: &[Witness], name: &str) -> (u32, bool, u128) {
    for w in inputs {
        if let Witness::Int {
            name: n,
            width,
            signed,
            bits,
        } = w
        {
            if n == name {
                return (*width, *signed, *bits);
            }
        }
    }
    panic!("no integer witness for `{name}` in {inputs:?}");
}

// ---- (a) unsigned add overflow: `fn add(a:u8,b:u8)->u8 { a+b }` ----------------

#[test]
fn u8_add_overflows_with_reproducing_witness() {
    // body: let _ = a + b;
    let p = Program {
        name: "add".into(),
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
        body: vec![Stmt::Eval(bin(BinOp::Add, var("a"), var("b")))],
    };
    let Verdict::Counterexample { class, inputs } = run(&p) else {
        panic!("u8 add should overflow somewhere");
    };
    assert_eq!(class, "add overflow");
    let (_, _, a) = int_witness(&inputs, "a");
    let (_, _, b) = int_witness(&inputs, "b");
    // DISAGREE=0: the witness must actually overflow u8 addition.
    assert!(
        u8::try_from(a)
            .unwrap()
            .checked_add(u8::try_from(b).unwrap())
            .is_none(),
        "witness a={a}, b={b} must overflow u8::add"
    );
}

// ---- (b) safe fn: `fn clamp(x:u8)->u8 { let r = x & 0x0f; assert!(r<=15); r }` --

#[test]
fn masked_value_is_bounded_and_verified() {
    let p = Program {
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
    };
    match run(&p) {
        Verdict::Verified { certified, .. } => assert!(certified, "safety proof must re-check"),
        other => panic!("clamp must be verified, got {other:?}"),
    }
}

// ---- (c) assert! inside a #[unwind(K)] loop that can fail ----------------------

#[test]
fn unwound_loop_assert_can_fail() {
    // for i in 0..4 { let s = x + i; assert!(s != 200); }  (x:u16)
    // Reachable when x == 200, 199, 198, or 197 (s wraps in u16 but stays small).
    let body = vec![
        Stmt::Let {
            name: "s".into(),
            ty: u(16),
            value: bin(BinOp::Add, var("x"), var("idx")),
        },
        Stmt::Assert(Expr::Unary {
            op: UnOp::Not,
            operand: Box::new(bin(BinOp::Eq, var("s"), lit(200, u(16)))),
        }),
    ];
    let p = Program {
        name: "loopy".into(),
        params: vec![Param {
            name: "x".into(),
            ty: u(16),
        }],
        arrays: vec![],
        body: vec![Stmt::For {
            var: "idx".into(),
            var_ty: u(16),
            bound: 4,
            body,
        }],
    };
    let Verdict::Counterexample { class, inputs } = run(&p) else {
        panic!("the loop assert should be violable");
    };
    assert_eq!(class, "assert! violated");
    let (_, _, x) = int_witness(&inputs, "x");
    // DISAGREE=0: re-execute the modeled loop; some i in 0..4 hits s==200.
    let xw = u16::try_from(x).expect("u16 witness fits");
    let hit = (0u16..4).any(|idx| xw.wrapping_add(idx) == 200);
    assert!(
        hit,
        "witness x={x} must reach assert! (s==200) within unwind 4"
    );
}

// ---- signed overflow uses signed predicate (i8 MIN - 1 underflows) -------------

#[test]
fn i8_sub_signed_overflow_detected() {
    let p = Program {
        name: "ssub".into(),
        params: vec![
            Param {
                name: "a".into(),
                ty: i(8),
            },
            Param {
                name: "b".into(),
                ty: i(8),
            },
        ],
        arrays: vec![],
        body: vec![Stmt::Eval(bin(BinOp::Sub, var("a"), var("b")))],
    };
    let Verdict::Counterexample { class, inputs } = run(&p) else {
        panic!("i8 sub can overflow");
    };
    assert_eq!(class, "sub overflow");
    let (wa, _, a) = int_witness(&inputs, "a");
    let (wb, _, b) = int_witness(&inputs, "b");
    let sa = i8::try_from(signed_value(wa, a)).unwrap();
    let sb = i8::try_from(signed_value(wb, b)).unwrap();
    assert!(
        sa.checked_sub(sb).is_none(),
        "witness {sa}-{sb} must overflow i8"
    );
}

// ---- explicit divide-by-zero (BV div is total, so we check it) -----------------

#[test]
fn division_by_zero_is_flagged() {
    let p = Program {
        name: "dz".into(),
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
        body: vec![Stmt::Eval(bin(BinOp::Div, var("a"), var("b")))],
    };
    let Verdict::Counterexample { class, inputs } = run(&p) else {
        panic!("a/b with symbolic b can be ÷0");
    };
    assert_eq!(class, "division by zero");
    let (_, _, b) = int_witness(&inputs, "b");
    assert_eq!(b, 0, "the ÷0 witness must set the divisor to 0");
}

// ---- a genuinely safe division (guarded) is verified ---------------------------

#[test]
fn guarded_division_is_verified() {
    // if b != 0 { let _ = a / b; }
    let p = Program {
        name: "safediv".into(),
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
            cond: Expr::Unary {
                op: UnOp::Not,
                operand: Box::new(bin(BinOp::Eq, var("b"), lit(0, u(8)))),
            },
            then: vec![Stmt::Eval(bin(BinOp::Div, var("a"), var("b")))],
            els: vec![],
        }],
    };
    match run(&p) {
        Verdict::Verified { certified, .. } => assert!(certified),
        other => panic!("guarded division must be verified, got {other:?}"),
    }
}

// ---- unwrap-on-None is a reachable panic ---------------------------------------

#[test]
fn unwrap_on_none_is_flagged() {
    // let _ = opt.unwrap();  where opt = Some(x) iff `present` (a bool input).
    let p = Program {
        name: "unwrapper".into(),
        params: vec![
            Param {
                name: "present".into(),
                ty: Ty::Bool,
            },
            Param {
                name: "x".into(),
                ty: u(8),
            },
        ],
        arrays: vec![],
        body: vec![Stmt::Eval(Expr::UnwrapOption {
            is_some: Box::new(var("present")),
            value: Box::new(var("x")),
        })],
    };
    let Verdict::Counterexample { class, inputs } = run(&p) else {
        panic!("unwrap can hit None");
    };
    assert_eq!(class, "unwrap on None");
    let present = inputs.iter().find_map(|w| match w {
        Witness::Bool { name, value } if name == "present" => Some(*value),
        _ => None,
    });
    assert_eq!(present, Some(false), "the None witness sets present=false");
}
