//! The shared MIR reflector: **symbolic execution over an acyclic MIR CFG** into
//! an `axeyum-ir` term over caller-provided input symbols. Sharing the signature
//! shape with the LLVM `reflect_into` is what lets one function be reflected from
//! *both* its MIR and its LLVM and proved equivalent (translation-validation of
//! rustc lowering).
//!
//! Handled per block: `_N = BinaryOp(a, b)` statements (arithmetic/bitwise/shifts
//! **and** comparisons, sign-aware: `Shr` on a signed local is `ashr`, `Gt` is
//! `sgt`/`ugt` by operand sign), the `*WithOverflow` checked-arithmetic tuple
//! forms with `(_N.0: TY)` / `(_N.1: bool)` field projections, `as`-casts,
//! `UnaryOp`, `Use` copies, and `StorageLive`/`StorageDead` noise; terminators
//! `return`, `goto`, `switchInt` (integer dispatch *or* bool branch), and
//! **`assert`** (debug-profile overflow/bounds checks — the panic edge becomes a
//! Bool *panic-condition term*, so "this function cannot panic" is a provable
//! goal and a `Disproved` countermodel is a concrete panicking input). Loops are
//! out of scope here — cyclic CFGs are the `TransitionSystem` path (a depth cap
//! panics on cycles).
//!
//! All ops route through the shared vocabulary (`super::{binop, compare}`), so
//! `BitAnd` (MIR) and `and` (LLVM) hit the same `bv_and`, and MIR's `Gt` lands on
//! the same map as LLVM's `icmp ugt` — the DRY point made concrete.
use std::collections::HashMap;

use axeyum_ir::{TermArena, TermId};

use super::{binop, compare};

/// `(term, width, signed)` — width 1 = Bool.
type Operand = (TermId, u32, bool);

/// A local's value: a scalar, the `(value, overflowed)` pair produced by the
/// `*WithOverflow` checked-arithmetic rvalues, or a fixed byte array (`[u8; N]`
/// parameters, one term per element).
#[derive(Clone)]
enum Slot {
    Scalar(Operand),
    Pair(Operand, Operand),
    Bytes(Vec<TermId>),
}

type Env = HashMap<u32, Slot>;

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
    if ty == "usize" {
        return (64, false);
    }
    if ty == "isize" {
        return (64, true);
    }
    let signed = ty.starts_with('i');
    let width = ty
        .trim_start_matches(['u', 'i'])
        .parse()
        .unwrap_or_else(|_| panic!("unsupported MIR type `{ty}`"));
    (width, signed)
}

/// `(width, signed)` of each parameter `_1.._N`, in order, from the
/// `fn name(_1: TY, _2: TY, …) -> TY` line.
fn param_tys(mir: &str) -> Vec<(u32, bool)> {
    let sig = mir
        .lines()
        .map(str::trim)
        .find(|l| l.starts_with("fn "))
        .expect("fn signature");
    let inside = sig
        .split_once('(')
        .and_then(|(_, r)| r.split_once(')'))
        .expect("parameter list")
        .0;
    inside
        .split(',')
        .map(str::trim)
        .filter(|p| !p.is_empty())
        .map(|p| ty_info(p.split_once(": ").expect("`_N: TY`").1))
        .collect()
}

/// The scalar in a slot (a `Pair`/`Bytes` is not a scalar — project/index it).
fn scalar(slot: &Slot, what: &str) -> Operand {
    match slot {
        Slot::Scalar(op) => *op,
        Slot::Pair(..) => panic!("{what}: expected a scalar local, found a tuple"),
        Slot::Bytes(_) => panic!("{what}: expected a scalar local, found an array"),
    }
}

/// Resolve a MIR operand: `copy _L` / `move _L` / `const K_TY` / `const true`,
/// or a checked-arithmetic field projection `copy (_L.0: TY)` / `(_L.1: bool)`.
fn operand(arena: &mut TermArena, env: &Env, tok: &str) -> Operand {
    let parts: Vec<&str> = tok.split_whitespace().collect();
    match parts.as_slice() {
        // `move (_2.0: u32)` / `copy (_2.1: bool)`
        ["copy" | "move", loc, _ty] if loc.starts_with("(_") => {
            let (n_s, field_s) = loc
                .trim_start_matches("(_")
                .split_once('.')
                .expect("tuple projection `(_N.K: TY)`");
            let n: u32 = n_s.parse().expect("local index");
            let field: u32 = field_s.trim_end_matches(':').parse().expect("field index");
            match (env.get(&n), field) {
                (Some(Slot::Pair(v, _)), 0) => *v,
                (Some(Slot::Pair(_, o)), 1) => *o,
                (Some(Slot::Pair(..)), f) => panic!("tuple local _{n} has no field {f}"),
                (Some(_), _) => panic!("local _{n} is not a tuple"),
                (None, _) => panic!("undefined local _{n}"),
            }
        }
        // Array indexing: `copy _1[_2]` — an ite table over the element terms
        // keyed by the index local (the bounds `assert` guards the read; the
        // out-of-range table value is a don't-care).
        ["copy" | "move", loc] if loc.contains('[') => {
            let (base_s, idx_s) = loc.split_once('[').expect("`_B[_I]`");
            let base: u32 = base_s.trim_start_matches('_').parse().expect("array local");
            let idx_n: u32 = idx_s
                .trim_end_matches(']')
                .trim_start_matches('_')
                .parse()
                .expect("index local");
            let (idx, idx_w, _) = scalar(
                env.get(&idx_n)
                    .unwrap_or_else(|| panic!("undefined local _{idx_n}")),
                "array index",
            );
            let Some(Slot::Bytes(bytes)) = env.get(&base) else {
                panic!("local _{base} is not a byte array");
            };
            let bytes = bytes.clone();
            let mut acc = *bytes.first().expect("nonempty array");
            for (k, &byte) in bytes.iter().enumerate().skip(1) {
                let kc = arena.bv_const(idx_w, k as u128).unwrap();
                let cond = arena.eq(idx, kc).unwrap();
                acc = arena.ite(cond, byte, acc).unwrap();
            }
            (acc, 8, false)
        }
        ["copy" | "move", loc] => {
            let n: u32 = loc.trim_start_matches('_').parse().expect("local index");
            scalar(
                env.get(&n)
                    .unwrap_or_else(|| panic!("undefined local _{n}")),
                tok,
            )
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

/// The `(value, overflowed)` pair for a `*WithOverflow` rvalue, sign-selected.
fn with_overflow(
    arena: &mut TermArena,
    op: &str,
    a: TermId,
    b: TermId,
    signed: bool,
) -> Option<(TermId, TermId)> {
    let (val_op, ovf) = match (op, signed) {
        ("AddWithOverflow", false) => ("add", arena.bv_uaddo(a, b).unwrap()),
        ("AddWithOverflow", true) => ("add", arena.bv_saddo(a, b).unwrap()),
        ("SubWithOverflow", false) => ("sub", arena.bv_usubo(a, b).unwrap()),
        ("SubWithOverflow", true) => ("sub", arena.bv_ssubo(a, b).unwrap()),
        ("MulWithOverflow", false) => ("mul", arena.bv_umulo(a, b).unwrap()),
        ("MulWithOverflow", true) => ("mul", arena.bv_smulo(a, b).unwrap()),
        _ => return None,
    };
    Some((binop(arena, val_op, a, b), ovf))
}

/// Execute one `_N = RHS` statement into the environment.
fn exec_stmt(arena: &mut TermArena, env: &mut Env, stmt: &str) {
    let (dst, rhs) = stmt.split_once(" = ").expect("statement `_N = ..`");
    let dst_n: u32 = dst.trim_start_matches('_').parse().expect("dst local");
    // `copy _1 as u32 (IntToInt)` — widen by the SOURCE sign, narrow by extract.
    if let Some((src_tok, rest)) = rhs.split_once(" as ") {
        let ty = rest.split_whitespace().next().expect("cast target type");
        let (dst_w, dst_signed) = ty_info(ty);
        let (a, w, signed) = operand(arena, env, src_tok.trim());
        let term = match dst_w.cmp(&w) {
            std::cmp::Ordering::Greater if signed => arena.sign_ext(dst_w - w, a).unwrap(),
            std::cmp::Ordering::Greater => arena.zero_ext(dst_w - w, a).unwrap(),
            std::cmp::Ordering::Less => arena.extract(dst_w - 1, 0, a).unwrap(),
            std::cmp::Ordering::Equal => a,
        };
        env.insert(dst_n, Slot::Scalar((term, dst_w, dst_signed)));
        return;
    }
    let result = match rhs.split_once('(') {
        // `BitAnd(copy _1, const 255_u32)` / `Gt(..)` / `AddWithOverflow(..)` /
        // unary `Not(..)` / `Neg(..)`
        Some((op, args)) if op.chars().all(char::is_alphanumeric) && !op.is_empty() => {
            let inner = args.strip_suffix(')').unwrap_or(args);
            if let Some((lhs, rhs_op)) = inner.split_once(", ") {
                let (a, w, signed) = operand(arena, env, lhs.trim());
                let (mut b, b_w, _) = operand(arena, env, rhs_op.trim());
                if let Some((val, ovf)) = with_overflow(arena, op, a, b, signed) {
                    env.insert(dst_n, Slot::Pair((val, w, signed), (ovf, 1, false)));
                    return;
                }
                if let Some(pred) = compare_pred(op, signed) {
                    Slot::Scalar((compare(arena, pred, a, b), 1, false))
                } else if w == 1 && matches!(op, "BitAnd" | "BitOr") {
                    // Bool-typed BitAnd/BitOr (rustc chains check conditions
                    // this way, e.g. the signed-division MIN/-1 test).
                    let t = if op == "BitAnd" {
                        arena.and(a, b).unwrap()
                    } else {
                        arena.or(a, b).unwrap()
                    };
                    Slot::Scalar((t, 1, false))
                } else if matches!(op, "Div" | "Rem") {
                    // Sign-selected division (the fixtures carry the div-by-zero
                    // and MIN/-1 asserts separately; the BV op is total).
                    let llvm_op = match (op, signed) {
                        ("Div", true) => "sdiv",
                        ("Div", false) => "udiv",
                        ("Rem", true) => "srem",
                        _ => "urem",
                    };
                    Slot::Scalar((binop(arena, llvm_op, a, b), w, signed))
                } else {
                    // Rust shift amounts are independently typed (`x << 1` is an
                    // `i32` literal) — adjust to the shiftee's width for the BV op.
                    if matches!(op, "Shl" | "Shr") && b_w != w {
                        b = if b_w > w {
                            arena.extract(w - 1, 0, b).unwrap()
                        } else {
                            arena.zero_ext(w - b_w, b).unwrap()
                        };
                    }
                    if op == "Shr" && signed {
                        Slot::Scalar((binop(arena, "ashr", a, b), w, signed))
                    } else {
                        Slot::Scalar((binop(arena, op, a, b), w, signed))
                    }
                }
            } else {
                // UnaryOp: `Not(copy _1)` (logical on bool, bitwise on ints),
                // `Neg(copy _1)` (two's-complement negation).
                let (a, w, signed) = operand(arena, env, inner.trim());
                let t = match (op, w) {
                    ("Not", 1) => arena.not(a).unwrap(),
                    ("Not", _) => arena.bv_not(a).unwrap(),
                    ("Neg", _) => arena.bv_neg(a).unwrap(),
                    _ => panic!("unsupported unary MIR op `{op}`"),
                };
                Slot::Scalar((t, w, signed))
            }
        }
        // A bare `Use`: `copy _1` / `move (_2.0: u32)` / `const K_TY`.
        _ => Slot::Scalar(operand(arena, env, rhs.trim())),
    };
    env.insert(dst_n, result);
}

/// Symbolically execute from `bb` to `return`, yielding `(value of _0, panic)` —
/// `panic` is a Bool term that is true exactly on inputs whose path fails an
/// `assert` (a debug-profile overflow/bounds check). Branches recurse per
/// successor (each on a clone of the environment) and join both the value and
/// the panic condition as `ite`; the depth cap turns a cyclic CFG into a loud
/// panic, not a hang.
fn exec_block(
    arena: &mut TermArena,
    map: &HashMap<String, Vec<String>>,
    mut env: Env,
    bb: &str,
    depth: usize,
) -> (Operand, TermId) {
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
            let ret = scalar(env.get(&0).expect("MIR must assign _0 before return"), "_0");
            return (ret, arena.bool_const(false));
        }
        if let Some(target) = stmt.strip_prefix("goto -> ") {
            return exec_block(arena, map, env, target.trim(), depth + 1);
        }
        // assert(!move (_2.1: bool), "…") -> [success: bb1, unwind continue];
        // Panics exactly when the asserted condition is false.
        if let Some(rest) = stmt.strip_prefix("assert(") {
            let cond_part = rest.split(", \"").next().expect("assert condition").trim();
            let (negated, tok) = match cond_part.strip_prefix('!') {
                Some(inner) => (true, inner),
                None => (false, cond_part),
            };
            let (cond, w, _) = operand(arena, &env, tok.trim());
            assert_eq!(w, 1, "assert condition must be bool");
            // assert(c) panics iff ¬c; assert(!c) panics iff c.
            let panic_here = if negated {
                cond
            } else {
                arena.not(cond).unwrap()
            };
            let success = rest
                .split("success: ")
                .nth(1)
                .expect("assert success target")
                .split([',', ']'])
                .next()
                .expect("success block")
                .trim();
            let (value, rest_panic) = exec_block(arena, map, env, success, depth + 1);
            let panic = arena.or(panic_here, rest_panic).unwrap();
            return (value, panic);
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
            let (mut acc, mut acc_panic) =
                exec_block(arena, map, env.clone(), otherwise, depth + 1);
            for (val, target) in arms.iter().rev() {
                let (then, then_panic) = exec_block(arena, map, env.clone(), target, depth + 1);
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
                acc_panic = arena.ite(cond, then_panic, acc_panic).unwrap();
            }
            return ((acc.0, acc.1, acc.2), acc_panic);
        }
        exec_stmt(arena, &mut env, stmt);
    }
    panic!("block {bb} fell through without a terminator");
}

/// A caller-supplied parameter binding for [`reflect_mir_params_checked`]:
/// a typed scalar, or a fixed `[u8; N]` array as one term per element.
pub enum MirParam {
    Scalar(TermId, u32, bool),
    Bytes(Vec<TermId>),
}

/// Reflect a MIR function whose parameters may include `[u8; N]` arrays —
/// `params[i]` binds local `_{i+1}`; types come from the bindings, not the
/// signature. Returns `(value of _0, panic condition)` like
/// [`reflect_mir_into_checked`].
pub fn reflect_mir_params_checked(
    arena: &mut TermArena,
    params: &[MirParam],
    mir: &str,
) -> (TermId, TermId) {
    let map = blocks(mir);
    let mut env: Env = HashMap::new();
    for (i, p) in params.iter().enumerate() {
        let slot = match p {
            MirParam::Scalar(t, w, signed) => Slot::Scalar((*t, *w, *signed)),
            MirParam::Bytes(v) => Slot::Bytes(v.clone()),
        };
        env.insert(u32::try_from(i).unwrap() + 1, slot);
    }
    let (value, panic) = exec_block(arena, &map, env, "bb0", 0);
    (value.0, panic)
}

/// Reflect a MIR function into an *existing* arena, binding `params[i]` to local
/// `_{i+1}`, returning `(value of _0, panic condition)`. The panic condition is
/// a Bool term true exactly on inputs that fail a debug-profile `assert`
/// (overflow/bounds check) — proving it `== false` is a **panic-freedom proof**;
/// a countermodel is a concrete panicking input.
pub fn reflect_mir_into_checked(
    arena: &mut TermArena,
    params: &[TermId],
    mir: &str,
) -> (TermId, TermId) {
    let tys = param_tys(mir);
    assert_eq!(
        tys.len(),
        params.len(),
        "parameter count mismatch between the MIR signature and the given terms"
    );
    let map = blocks(mir);
    let mut env: Env = HashMap::new();
    for (i, (&term, &(w, signed))) in params.iter().zip(tys.iter()).enumerate() {
        env.insert(
            u32::try_from(i).unwrap() + 1,
            Slot::Scalar((term, w, signed)),
        );
    }
    let (value, panic) = exec_block(arena, &map, env, "bb0", 0);
    (value.0, panic)
}

/// Reflect a MIR function, returning only the `_0` value term (for fixtures
/// without checked arithmetic the panic condition is constant false anyway).
pub fn reflect_mir_into(arena: &mut TermArena, params: &[TermId], mir: &str) -> TermId {
    reflect_mir_into_checked(arena, params, mir).0
}

/// Single-input convenience over [`reflect_mir_into`] (`x` is `_1`).
pub fn reflect_mir_unary(arena: &mut TermArena, x: TermId, mir: &str) -> TermId {
    reflect_mir_into(arena, &[x], mir)
}
