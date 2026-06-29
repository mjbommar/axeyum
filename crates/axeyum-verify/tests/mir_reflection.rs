//! A3 (direction A frontier): **MIR-text reflection prototype**. Parse the real
//! compiled MIR of a Rust function into an `axeyum-ir` term over symbolic inputs,
//! and exhaustively cross-check that the reflected term computes the *same*
//! function as the real Rust — i.e. we reflected the *compiled* semantics (what
//! the CPU runs) into the solver's IR, faithfully.
//!
//! Design + feasibility: `docs/consumer-track/verify/real-rust-frontend.md`.
//!
//! **Prototype scope, honestly:** the MIR comes from a *committed fixture*
//! (captured once via `rustc --crate-type=lib -Zunpretty=mir`, rustc 1.96-nightly)
//! — NOT invoked at test time, because `-Zunpretty` is nightly-only and CI runs
//! stable/MSRV; a fixture keeps this test toolchain-independent. The parser
//! handles only the `switchInt` / `_0 = const` / `goto` / `return` subset that a
//! small lookup/branch function compiles to. The MIR text format is explicitly
//! unstable (rustc prints that warning) — regenerate the fixture if it drifts.
//! This is a proof-of-concept that the MIR pipeline is real, not a maintained
//! front end (that is the deferred `stable_mir` path).

use std::collections::HashMap;

use axeyum_ir::{Assignment, Sort, SymbolId, TermArena, TermId, Value, eval};

/// The real Rust function. Its compiled MIR (below) is what we reflect; the
/// function itself is the reference oracle for the exhaustive cross-check.
fn lut(x: u8) -> u8 {
    match x {
        0 => 5,
        1 => 7,
        _ => 0,
    }
}

/// Committed `rustc --crate-type=lib -Zunpretty=mir lut.rs` output (rustc 1.96).
const LUT_MIR: &str = r"
fn lut(_1: u8) -> u8 {
    debug x => _1;
    let mut _0: u8;

    bb0: {
        switchInt(copy _1) -> [0: bb3, 1: bb2, otherwise: bb1];
    }

    bb1: {
        _0 = const 0_u8;
        goto -> bb4;
    }

    bb2: {
        _0 = const 7_u8;
        goto -> bb4;
    }

    bb3: {
        _0 = const 5_u8;
        goto -> bb4;
    }

    bb4: {
        return;
    }
}
";

/// A parsed `switchInt` terminator: the scrutinee local, the value→block arms, and
/// the `otherwise` block.
struct Switch {
    arms: Vec<(u128, String)>,
    otherwise: String,
}

/// Group the MIR text into `bbN -> [lines]`.
fn blocks(mir: &str) -> HashMap<String, Vec<String>> {
    let mut map = HashMap::new();
    let mut current: Option<String> = None;
    let mut lines: Vec<String> = Vec::new();
    for raw in mir.lines() {
        let line = raw.trim();
        if let Some(name) = line.strip_suffix(": {") {
            current = Some(name.to_string());
            lines = Vec::new();
        } else if line == "}" {
            if let Some(name) = current.take() {
                map.insert(name, std::mem::take(&mut lines));
            }
        } else if current.is_some() && !line.is_empty() {
            lines.push(line.to_string());
        }
    }
    map
}

/// Parse the `switchInt(copy _1) -> [0: bb3, 1: bb2, otherwise: bb1];` terminator
/// in `bb0` (the only switch in this fixture).
fn parse_switch(block: &[String]) -> Switch {
    let line = block
        .iter()
        .find(|l| l.starts_with("switchInt"))
        .expect("bb0 must switch");
    let inside = line
        .split_once('[')
        .and_then(|(_, rest)| rest.split_once(']'))
        .expect("switchInt arms")
        .0;
    let mut arms = Vec::new();
    let mut otherwise = String::new();
    for part in inside.split(", ") {
        let (key, target) = part.split_once(": ").expect("arm `k: bbN`");
        if key == "otherwise" {
            otherwise = target.to_string();
        } else {
            arms.push((key.parse::<u128>().expect("arm value"), target.to_string()));
        }
    }
    Switch { arms, otherwise }
}

/// The `u128` constant a target block assigns to `_0` (each arm block here is
/// `_0 = const K_u8; goto -> bb4;`).
fn block_const(block: &[String]) -> u128 {
    let line = block
        .iter()
        .find(|l| l.starts_with("_0 = const"))
        .expect("arm block assigns _0");
    let lit = line
        .trim_start_matches("_0 = const ")
        .split('_')
        .next()
        .expect("const literal");
    lit.parse::<u128>().expect("u8 const")
}

/// Reflect the fixture's `switchInt` over `_1` into a symbolic `axeyum-ir` term
/// `T(x)`, returning the arena, the input symbol, and `T`.
fn reflect_lut_mir() -> (TermArena, SymbolId, TermId) {
    let map = blocks(LUT_MIR);
    let sw = parse_switch(&map["bb0"]);

    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::BitVec(8)).unwrap();
    let x = arena.var(x_sym);

    // T = ite(x==v0, c0, ite(x==v1, c1, ... otherwise c_oth))
    let mut acc = {
        let c = block_const(&map[&sw.otherwise]);
        arena.bv_const(8, c).unwrap()
    };
    for (val, target) in sw.arms.iter().rev() {
        let c = block_const(&map[target]);
        let then = arena.bv_const(8, c).unwrap();
        let v = arena.bv_const(8, *val).unwrap();
        let cond = arena.eq(x, v).unwrap();
        acc = arena.ite(cond, then, acc).unwrap();
    }
    (arena, x_sym, acc)
}

/// Evaluate the reflected term `T(x)` at a concrete `a`.
fn eval_at(arena: &TermArena, sym: SymbolId, term: TermId, a: u8) -> u128 {
    let mut asg = Assignment::new();
    asg.set(
        sym,
        Value::Bv {
            width: 8,
            value: u128::from(a),
        },
    );
    match eval(arena, term, &asg).unwrap() {
        Value::Bv { value, .. } => value,
        other => panic!("expected a BV value, got {other:?}"),
    }
}

/// The term reflected from `lut`'s real compiled MIR computes **exactly** `lut`
/// on all 256 inputs — the reflection of the compiled semantics into the IR is
/// faithful (verified by exhaustive evaluation against the real Rust oracle).
#[test]
fn mir_reflected_term_matches_real_rust_on_all_inputs() {
    let (arena, sym, term) = reflect_lut_mir();
    for a in 0..=u8::MAX {
        assert_eq!(
            eval_at(&arena, sym, term, a),
            u128::from(lut(a)),
            "MIR-reflected term diverged from real Rust at x={a}"
        );
    }
}

/// A property of the reflected real-compiled code, established over the full
/// domain by the same exhaustive evaluation: `lut`'s result is always one of
/// {0,5,7} — in particular `<= 7`. (For this tiny prototype, exhaustive eval *is*
/// the all-inputs proof; larger functions are the symbolic-solver path.)
#[test]
fn mir_reflected_term_satisfies_a_range_property() {
    let (arena, sym, term) = reflect_lut_mir();
    for a in 0..=u8::MAX {
        assert!(
            eval_at(&arena, sym, term, a) <= 7,
            "reflected lut exceeded its range at x={a}"
        );
    }
}
