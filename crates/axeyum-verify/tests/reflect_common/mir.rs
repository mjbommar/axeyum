//! The shared MIR reflector: **symbolic execution over an acyclic MIR CFG** into
//! an `axeyum-ir` term over a caller-provided input symbol `x`. Sharing the
//! signature `(arena, x, mir) -> TermId` with the LLVM `reflect_unary_into` is
//! what lets one function be reflected from *both* its MIR and its LLVM and
//! proved equivalent (translation-validation of rustc lowering).
//!
//! Handled per block: `_N = BinaryOp(a, b)` statements (arithmetic/bitwise/shifts
//! **and** comparisons, sign-aware: `Shr` on a signed local is `ashr`, `Gt` is
//! `sgt`/`ugt` by operand sign), `Use` copies, `StorageLive`/`StorageDead` noise;
//! terminators `return`, `goto`, and `switchInt` (integer dispatch *or* bool
//! branch), joined by recursion into `ite` terms. Loops are out of scope here —
//! cyclic CFGs are the `TransitionSystem` path (a depth cap panics on cycles).
//!
//! All ops route through the shared vocabulary (`super::{binop, compare}`), so
//! `BitAnd` (MIR) and `and` (LLVM) hit the same `bv_and`, and MIR's `Gt` lands on
//! the same map as LLVM's `icmp ugt` — the DRY point made concrete.
use std::collections::HashMap;

use axeyum_ir::{TermArena, TermId};

use super::{binop, compare};

/// `(term, width, signed)` — width 1 = Bool.
type Operand = (TermId, u32, bool);

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

/// `(width, signed)` of a MIR type token (`u32`, `i8`, `bool`).
fn ty_info(ty: &str) -> (u32, bool) {
    let ty = ty.trim().trim_end_matches([' ', '{']).trim();
    if ty == "bool" {
        return (1, false);
    }
    let signed = ty.starts_with('i');
    let width = ty
        .trim_start_matches(['u', 'i'])
        .parse()
        .unwrap_or_else(|_| panic!("unsupported MIR type `{ty}`"));
    (width, signed)
}

/// `(width, signed)` of the input `_1`, from the `fn name(_1: TY) -> TY` line.
fn input_ty(mir: &str) -> (u32, bool) {
    let sig = mir
        .lines()
        .map(str::trim)
        .find(|l| l.starts_with("fn "))
        .expect("fn signature");
    let after = sig.split_once("_1: ").expect("an `_1: TY` parameter").1;
    let ty = after
        .split([',', ')'])
        .next()
        .expect("parameter type")
        .trim();
    ty_info(ty)
}

/// Resolve a MIR operand (`copy _L` / `move _L` / `const K_TY` / `const true`).
fn operand(arena: &mut TermArena, env: &HashMap<u32, Operand>, tok: &str) -> Operand {
    let parts: Vec<&str> = tok.split_whitespace().collect();
    match parts.as_slice() {
        ["copy" | "move", loc] => {
            let n: u32 = loc.trim_start_matches('_').parse().expect("local index");
            *env.get(&n)
                .unwrap_or_else(|| panic!("undefined local _{n}"))
        }
        ["const", "true"] => (arena.bool_const(true), 1, false),
        ["const", "false"] => (arena.bool_const(false), 1, false),
        ["const", lit] => {
            // `255_u32` / `-5_i32` → two's-complement value at the suffix width.
            let (val_s, ty_s) = lit.split_once('_').expect("typed const literal");
            let (w, signed) = ty_info(ty_s);
            let v: i128 = val_s.parse().expect("integer const");
            let value = if v < 0 {
                (v + (1i128 << w)).cast_unsigned()
            } else {
                v.cast_unsigned()
            };
            (arena.bv_const(w, value).unwrap(), w, signed)
        }
        _ => panic!("unsupported MIR operand `{tok}`"),
    }
}

/// The LLVM-vocabulary predicate for a MIR comparison op, sign-selected — so MIR
/// comparisons land on the *same* shared `compare` map LLVM's `icmp` uses.
fn compare_pred(op: &str, signed: bool) -> Option<&'static str> {
    Some(match (op, signed) {
        ("Eq", _) => "eq",
        ("Ne", _) => "ne",
        ("Lt", false) => "ult",
        ("Lt", true) => "slt",
        ("Le", false) => "ule",
        ("Le", true) => "sle",
        ("Gt", false) => "ugt",
        ("Gt", true) => "sgt",
        ("Ge", false) => "uge",
        ("Ge", true) => "sge",
        _ => return None,
    })
}

/// Execute one `_N = RHS` statement into the environment.
fn exec_stmt(arena: &mut TermArena, env: &mut HashMap<u32, Operand>, stmt: &str) {
    let (dst, rhs) = stmt.split_once(" = ").expect("statement `_N = ..`");
    let dst_n: u32 = dst.trim_start_matches('_').parse().expect("dst local");
    let result = match rhs.split_once('(') {
        // `BitAnd(copy _1, const 255_u32)` / `Gt(copy _1, const 100_u32)`
        Some((op, args)) if op.chars().all(char::is_alphanumeric) && !op.is_empty() => {
            let inner = args.strip_suffix(')').unwrap_or(args);
            let (lhs, rhs_op) = inner.split_once(", ").expect("two operands");
            let (a, w, signed) = operand(arena, env, lhs.trim());
            let (b, _, _) = operand(arena, env, rhs_op.trim());
            if let Some(pred) = compare_pred(op, signed) {
                (compare(arena, pred, a, b), 1, false)
            } else if op == "Shr" && signed {
                (binop(arena, "ashr", a, b), w, signed)
            } else {
                (binop(arena, op, a, b), w, signed)
            }
        }
        // A bare `Use`: `copy _1` / `move _2` / `const K_TY`.
        _ => operand(arena, env, rhs.trim()),
    };
    env.insert(dst_n, result);
}

/// Symbolically execute from `bb` to `return`, yielding the value of `_0`.
/// Branches recurse per successor (each on a clone of the environment) and join
/// as `ite`; the depth cap turns a cyclic CFG into a loud panic, not a hang.
fn exec_block(
    arena: &mut TermArena,
    map: &HashMap<String, Vec<String>>,
    mut env: HashMap<u32, Operand>,
    bb: &str,
    depth: usize,
) -> Operand {
    assert!(
        depth < 64,
        "cyclic or too-deep MIR CFG (loops are the TransitionSystem path)"
    );
    let block = map
        .get(bb)
        .unwrap_or_else(|| panic!("undefined block {bb}"));
    for line in block {
        let stmt = line.trim_end_matches(';');
        if stmt.starts_with("StorageLive") || stmt.starts_with("StorageDead") {
            continue;
        }
        if stmt == "return" {
            return *env.get(&0).expect("MIR must assign _0 before return");
        }
        if let Some(target) = stmt.strip_prefix("goto -> ") {
            return exec_block(arena, map, env, target.trim(), depth + 1);
        }
        if let Some(rest) = stmt.strip_prefix("switchInt(") {
            let (scrut_tok, arms_part) = rest.split_once(')').expect("switchInt scrutinee");
            let (scrut, w, _) = operand(arena, &env, scrut_tok.trim());
            let inside = arms_part
                .split_once('[')
                .and_then(|(_, r)| r.split_once(']'))
                .expect("switchInt arms")
                .0;
            let mut arms: Vec<(u128, &str)> = Vec::new();
            let mut otherwise = "";
            for part in inside.split(", ") {
                let (key, target) = part.split_once(": ").expect("arm `k: bbN`");
                if key == "otherwise" {
                    otherwise = target;
                } else {
                    arms.push((key.parse().expect("arm value"), target));
                }
            }
            let mut acc = exec_block(arena, map, env.clone(), otherwise, depth + 1);
            for (val, target) in arms.iter().rev() {
                let then = exec_block(arena, map, env.clone(), target, depth + 1);
                // Bool scrutinee: arm `0` is the false edge, so its guard is ¬scrut.
                let cond = if w == 1 {
                    if *val == 0 {
                        arena.not(scrut).unwrap()
                    } else {
                        scrut
                    }
                } else {
                    let v = arena.bv_const(w, *val).unwrap();
                    arena.eq(scrut, v).unwrap()
                };
                let t = arena.ite(cond, then.0, acc.0).unwrap();
                acc = (t, then.1, then.2);
            }
            return acc;
        }
        exec_stmt(arena, &mut env, stmt);
    }
    panic!("block {bb} fell through without a terminator");
}

/// Reflect a single-input MIR function into an *existing* arena, using `x` (the
/// input local `_1`) as its parameter, returning the term for `_0` at `return`.
pub fn reflect_mir_unary(arena: &mut TermArena, x: TermId, mir: &str) -> TermId {
    let (in_w, in_signed) = input_ty(mir);
    let map = blocks(mir);
    let mut env: HashMap<u32, Operand> = HashMap::new();
    env.insert(1, (x, in_w, in_signed));
    exec_block(arena, &map, env, "bb0", 0).0
}
