//! The shared MIR reflector: parse the `switchInt` / straight-line `BinaryOp`
//! subset of rustc MIR into an `axeyum-ir` term over a caller-provided input
//! symbol `x`. Sharing the signature `(arena, x, mir) -> TermId` with the LLVM
//! `reflect_unary_into` is what lets one function be reflected from *both* its MIR
//! and its LLVM and proved equivalent (translation-validation of rustc lowering).
//!
//! `BinaryOp` rvalues route through the shared `super::binop`, so the op
//! vocabulary is the *same* one the LLVM reflector uses — the DRY point made
//! concrete: `BitAnd` (MIR) and `and` (LLVM) hit the same `bv_and`.
use std::collections::HashMap;

use axeyum_ir::{TermArena, TermId};

use super::binop;

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

/// Read the input/output bit-widths from the `fn name(_1: uN) -> uM` line.
fn parse_widths(mir: &str) -> (u32, u32) {
    let sig = mir
        .lines()
        .map(str::trim)
        .find(|l| l.starts_with("fn "))
        .expect("fn signature");
    let width_after = |marker: &str| -> u32 {
        sig.split_once(marker)
            .and_then(|(_, rest)| rest.split(|c: char| !c.is_ascii_digit()).next())
            .and_then(|d| d.parse().ok())
            .expect("a uN/iN width")
    };
    // Accept either `uN`/`iN`; the input follows `_1: `, the output follows `-> `.
    let after_colon = sig.split_once("_1: ").map_or("", |(_, r)| r);
    let in_w = after_colon
        .trim_start_matches(['u', 'i'])
        .split(|c: char| !c.is_ascii_digit())
        .next()
        .and_then(|d| d.parse().ok())
        .unwrap_or_else(|| width_after("_1: u"));
    let out_tail = sig.split_once("-> ").map_or("", |(_, r)| r);
    let out_w = out_tail
        .trim_start_matches(['u', 'i'])
        .split(|c: char| !c.is_ascii_digit())
        .next()
        .and_then(|d| d.parse().ok())
        .unwrap_or_else(|| width_after("-> u"));
    (in_w, out_w)
}

/// The `u128` constant a target block assigns to `_0` (`_0 = const K_u8; …`).
fn block_const(block: &[String]) -> u128 {
    let line = block
        .iter()
        .find(|l| l.starts_with("_0 = const"))
        .expect("arm block assigns _0");
    line.trim_start_matches("_0 = const ")
        .split('_')
        .next()
        .expect("const literal")
        .parse::<u128>()
        .expect("integer const")
}

/// Resolve a MIR operand (`copy _L` / `move _L` / `const K_uW`) to `(term, width)`.
fn operand(
    arena: &mut TermArena,
    env: &HashMap<u32, (TermId, u32)>,
    tok: &str,
    default_w: u32,
) -> (TermId, u32) {
    let parts: Vec<&str> = tok.split_whitespace().collect();
    match parts.as_slice() {
        ["copy" | "move", loc] => {
            let n: u32 = loc.trim_start_matches('_').parse().expect("local index");
            *env.get(&n)
                .unwrap_or_else(|| panic!("undefined local _{n}"))
        }
        ["const", lit] => {
            // `255_u32` → value 255, width 32; bare `255` → default width.
            let (val_s, ty_s) = lit.split_once('_').unwrap_or((lit, ""));
            let w = ty_s
                .trim_start_matches(['u', 'i'])
                .parse::<u32>()
                .unwrap_or(default_w);
            let v = val_s.parse::<u128>().expect("integer const");
            (arena.bv_const(w, v).unwrap(), w)
        }
        _ => panic!("unsupported MIR operand `{tok}`"),
    }
}

/// Reflect a single-input MIR function into an *existing* arena, using `x` (the
/// input local `_1`) as its parameter, returning the term for `_0`.
///
/// Handles two shapes over `bb0`:
/// - a `switchInt(copy _1) -> [v: bb, …, otherwise: bb]` dispatch whose arm blocks
///   each assign a constant to `_0` (a lookup table), and
/// - a straight line of `_N = BinaryOp(op1, op2);` statements ending in `_0`.
pub fn reflect_mir_unary(arena: &mut TermArena, x: TermId, mir: &str) -> TermId {
    let (in_w, out_w) = parse_widths(mir);
    let map = blocks(mir);
    let bb0 = &map["bb0"];

    if let Some(sw_line) = bb0.iter().find(|l| l.starts_with("switchInt")) {
        // ite(x==v0, c0, ite(x==v1, c1, … otherwise c_oth))
        let inside = sw_line
            .split_once('[')
            .and_then(|(_, rest)| rest.split_once(']'))
            .expect("switchInt arms")
            .0;
        let mut arms: Vec<(u128, &str)> = Vec::new();
        let mut otherwise = "";
        for part in inside.split(", ") {
            let (key, target) = part.split_once(": ").expect("arm `k: bbN`");
            if key == "otherwise" {
                otherwise = target;
            } else {
                arms.push((key.parse::<u128>().expect("arm value"), target));
            }
        }
        let mut acc = arena.bv_const(out_w, block_const(&map[otherwise])).unwrap();
        for (val, target) in arms.iter().rev() {
            let then = arena.bv_const(out_w, block_const(&map[*target])).unwrap();
            let v = arena.bv_const(in_w, *val).unwrap();
            let cond = arena.eq(x, v).unwrap();
            acc = arena.ite(cond, then, acc).unwrap();
        }
        return acc;
    }

    // Straight-line statements: `_N = <rvalue>;`, seeded with `_1 = x`.
    let mut env: HashMap<u32, (TermId, u32)> = HashMap::new();
    env.insert(1, (x, in_w));
    for line in bb0 {
        let stmt = line.trim_end_matches(';');
        let Some((dst, rhs)) = stmt.split_once(" = ") else {
            continue; // `return` / terminators
        };
        let dst_n: u32 = dst.trim_start_matches('_').parse().expect("dst local");
        let (term, width) = if let Some((op, args)) = rhs.split_once('(') {
            // `BitAnd(copy _1, const 255_u32)`
            let inner = args.strip_suffix(')').unwrap_or(args);
            let (lhs, rhs_op) = inner.split_once(", ").expect("two operands");
            let (left, wid) = operand(arena, &env, lhs.trim(), in_w);
            let (right, _) = operand(arena, &env, rhs_op.trim(), wid);
            (binop(arena, op.trim(), left, right), wid)
        } else {
            // A bare `Use`: `copy _1` / `move _2` / `const K_uW`.
            operand(arena, &env, rhs.trim(), in_w)
        };
        env.insert(dst_n, (term, width));
    }
    env.get(&0).expect("MIR must assign _0").0
}
