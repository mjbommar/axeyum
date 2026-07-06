//! The shared single-block LLVM-IR reflector: parse `define … { … ret }` into an
//! `axeyum-ir` term. Split out of `llvm_reflection.rs` so the LLVM front end, the
//! loop/buffer reflectors, and the cross-IR equivalence suite all lower through
//! one parser and one op vocabulary (`super::{binop, compare, width_of}`).
use std::collections::HashMap;

use axeyum_ir::{Sort, SymbolId, TermArena, TermId};
use axeyum_solver::{ProofOutcome, SolverConfig, prove};

use super::{binop, compare, width_of};

/// A reflected function: the arena it lives in, its parameters, the SSA
/// environment (every `%name` → `(term, width)`), and the `ret` term.
pub struct Reflected {
    /// The arena the reflected term lives in (owns the reflection).
    pub arena: TermArena,
    /// `(name, symbol, width)` for each function parameter (width 1 = `i1`/Bool).
    pub params: Vec<(String, SymbolId, u32)>,
    /// every SSA name (params + results) → `(term, width)`.
    pub env: HashMap<String, (TermId, u32)>,
    /// The term produced by the function's `ret` — what a property is proved of.
    pub result: TermId,
}

impl Reflected {
    /// The term for parameter `name` (panics if there is no such parameter).
    pub fn param(&self, name: &str) -> TermId {
        self.env[name].0
    }
    /// Prove `goal` over this reflection for all inputs (no hypotheses).
    ///
    /// # Panics
    /// Panics if the solver hard-errors (a resource/config fault, not `unknown`).
    pub fn prove_goal(&mut self, goal: TermId) -> ProofOutcome {
        prove(&mut self.arena, &[], goal, &SolverConfig::default())
            .expect("solver should not hard-error")
    }
}

/// Whether an operand token names an SSA register (`%…`).
pub fn is_reg(tok: &str) -> bool {
    tok.starts_with('%')
}

/// Resolve an operand token to a term of the given width (1 = Bool).
///
/// # Panics
/// Panics if the IR/token is malformed or uses an unsupported construct.
#[allow(clippy::implicit_hasher)] // the reflector's SSA env is always the default-hasher `HashMap`.
pub fn resolve(
    arena: &mut TermArena,
    env: &HashMap<String, (TermId, u32)>,
    tok: &str,
    width: u32,
) -> TermId {
    if is_reg(tok) {
        env.get(tok.trim_start_matches('%'))
            .unwrap_or_else(|| panic!("undefined SSA value {tok}"))
            .0
    } else if width == 1 {
        arena.bool_const(tok == "1" || tok == "true")
    } else {
        // LLVM prints negative constants signed (`xor i32 %x, -1`); wrap them to
        // two's complement at the operand width.
        let value = tok.parse::<u128>().unwrap_or_else(|_| {
            let v: i128 = tok.parse().expect("integer constant");
            assert!(v < 0 && width < 128, "unparseable constant `{tok}`");
            (v + (1i128 << width)).cast_unsigned()
        });
        arena.bv_const(width, value).unwrap()
    }
}

/// Lower one instruction's right-hand side to `(term, width)`.
///
/// # Panics
/// Panics if the IR/token is malformed or uses an unsupported construct.
#[allow(clippy::implicit_hasher)] // the reflector's SSA env is always the default-hasher `HashMap`.
pub fn lower_rhs(
    arena: &mut TermArena,
    env: &HashMap<String, (TermId, u32)>,
    rhs: &str,
) -> (TermId, u32) {
    let rhs_c = rhs.replace(',', "");
    let toks: Vec<&str> = rhs_c.split_whitespace().collect();
    if toks[0] == "select" {
        // select i1 %c, iW %a, iW %b
        let cond = resolve(arena, env, toks[2], 1);
        let w = width_of(toks[3]);
        let a = resolve(arena, env, toks[4], w);
        let b = resolve(arena, env, toks[6], w);
        (arena.ite(cond, a, b).unwrap(), w)
    } else if toks[0] == "icmp" {
        // icmp PRED iW %a, %b  -> Bool (width 1)
        let w = width_of(toks[2]);
        let a = resolve(arena, env, toks[3], w);
        let b = resolve(arena, env, toks[4], w);
        (compare(arena, toks[1], a, b), 1)
    } else if rhs.contains("@llvm.umin") || rhs.contains("@llvm.umax") {
        // ... call iW @llvm.uminN(iW %a, iW K)
        let inside = rhs.split_once('(').unwrap().1.split_once(')').unwrap().0;
        let args: Vec<&str> = inside.split(',').map(str::trim).collect();
        let w = width_of(args[0].split_whitespace().next().unwrap());
        let a = resolve(arena, env, args[0].split_whitespace().nth(1).unwrap(), w);
        let b = resolve(arena, env, args[1].split_whitespace().nth(1).unwrap(), w);
        let cond = if rhs.contains("umin") {
            arena.bv_ule(a, b).unwrap()
        } else {
            arena.bv_uge(a, b).unwrap()
        };
        (arena.ite(cond, a, b).unwrap(), w)
    } else if toks[0] == "zext" || toks[0] == "sext" || toks[0] == "trunc" {
        // zext/sext/trunc [flags..] iSRC %v to iDST  (flags like `nneg`; the two
        // `iN` tokens are the source and target widths, in order).
        let tys: Vec<u32> = toks
            .iter()
            .filter(|t| {
                t.len() > 1 && t.starts_with('i') && t[1..].chars().all(|c| c.is_ascii_digit())
            })
            .map(|t| width_of(t))
            .collect();
        let (src_w, dst_w) = (tys[0], tys[1]);
        let operand = toks
            .iter()
            .find(|t| t.starts_with('%'))
            .expect("cast operand");
        let src = resolve(arena, env, operand, src_w);
        let t = match toks[0] {
            "zext" => arena.zero_ext(dst_w - src_w, src).unwrap(),
            "sext" => arena.sign_ext(dst_w - src_w, src).unwrap(),
            _ => arena.extract(dst_w - 1, 0, src).unwrap(),
        };
        (t, dst_w)
    } else {
        // binary int op: OP [flags..] iW %a, %b   (operands follow the type)
        let op = toks[0];
        let ty_idx = toks[1..]
            .iter()
            .position(|t| t.starts_with('i') && t[1..].chars().all(|c| c.is_ascii_digit()))
            .expect("a type in the binop")
            + 1;
        let w = width_of(toks[ty_idx]);
        let a = resolve(arena, env, toks[ty_idx + 1], w);
        let b = resolve(arena, env, toks[ty_idx + 2], w);
        (binop(arena, op, a, b), w)
    }
}

/// Parse the parameter list of the `define` line into `(name, width)` pairs.
///
/// # Panics
/// Panics if the IR/token is malformed or uses an unsupported construct.
pub fn param_decls(ll: &str) -> Vec<(String, u32)> {
    let define = ll
        .lines()
        .map(str::trim)
        .find(|l| l.starts_with("define"))
        .expect("a `define` line");
    // Parameter list is inside the parens *after* `@name` (not the `range(...)`).
    let params_str = define
        .split_once('@')
        .expect("@name")
        .1
        .split_once('(')
        .expect("param list")
        .1
        .split_once(')')
        .expect("param list close")
        .0;
    params_str
        .split(',')
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .map(|arg| {
            let toks: Vec<&str> = arg.split_whitespace().collect();
            (
                toks.last().unwrap().trim_start_matches('%').to_string(),
                width_of(toks[0]),
            )
        })
        .collect()
}

/// Lower the instruction body (parameters must already be seeded in `env`) to the
/// `(result_term, result_width)` produced by `ret`.
///
/// # Panics
/// Panics if the IR/token is malformed or uses an unsupported construct.
#[allow(clippy::implicit_hasher)] // the reflector's SSA env is always the default-hasher `HashMap`.
pub fn lower_body(
    arena: &mut TermArena,
    env: &mut HashMap<String, (TermId, u32)>,
    ll: &str,
) -> (TermId, u32) {
    let mut result = None;
    let mut result_width = 0;
    let mut in_body = false;
    for raw in ll.lines() {
        let line = raw.trim();
        if line.starts_with("define") {
            in_body = true;
            continue;
        }
        if !in_body || line.is_empty() || line.ends_with(':') || line == "}" {
            continue;
        }
        if let Some(rest) = line.strip_prefix("ret ") {
            let toks: Vec<&str> = rest.split_whitespace().collect();
            let w = width_of(toks[0]);
            result = Some(resolve(arena, env, toks[1], w));
            result_width = w;
            continue;
        }
        let (dst_tok, rhs) = line.split_once(" = ").expect("instruction `%d = ..`");
        let dst = dst_tok.trim_start_matches('%').to_string();
        let (term, width) = lower_rhs(arena, env, rhs);
        env.insert(dst, (term, width));
    }
    (result.expect("a `ret`"), result_width)
}

// ---- CFG execution: `br` / `phi` over labeled blocks ----------------------------

/// Split a `define`'s body into `(label, lines)` blocks (comments stripped). The
/// entry block is whatever precedes the first label — usually empty, since rustc
/// and clang label the entry (`start:` / a numeric label).
fn split_cfg_blocks(ll: &str) -> Vec<(String, Vec<String>)> {
    let mut blocks: Vec<(String, Vec<String>)> = vec![(String::new(), Vec::new())];
    let mut in_body = false;
    for raw in ll.lines() {
        let line = raw.split(';').next().unwrap_or("").trim();
        if line.starts_with("define") {
            in_body = true;
            continue;
        }
        if !in_body || line.is_empty() {
            continue;
        }
        if line == "}" {
            break;
        }
        if let Some(lab) = line.strip_suffix(':') {
            blocks.push((lab.to_string(), Vec::new()));
        } else {
            blocks.last_mut().unwrap().1.push(line.to_string());
        }
    }
    blocks.retain(|(_, lines)| !lines.is_empty());
    blocks
}

/// Lower a `switch iW %x, label %default [ iW K, label %case ... ]` terminator:
/// parse the arm list (advancing `i` past the closing `]`), execute every
/// target on a clone of the environment, and fold the arms right-to-left into
/// a nested `ite` chain over `%x = K` tests with the default as the base.
/// `None` (an `unreachable` target) is a don't-care: that branch is dropped
/// from the join — the verifier assumes the UB path is never taken.
#[expect(clippy::too_many_arguments, reason = "test-scaffold CFG walker state")]
fn exec_switch(
    arena: &mut TermArena,
    blocks: &[(String, Vec<String>)],
    env: &HashMap<String, (TermId, u32)>,
    rest: &str,
    lines: &[String],
    i: &mut usize,
    label: &str,
    depth: usize,
) -> Option<(TermId, u32)> {
    let mut toks = rest.split_whitespace();
    let w = width_of(toks.next().expect("switch type"));
    let scrut_tok = toks.next().expect("switch scrutinee").trim_end_matches(',');
    let scrut = resolve(arena, env, scrut_tok, w);
    let default = rest
        .split("label %")
        .nth(1)
        .expect("switch default")
        .split_whitespace()
        .next()
        .expect("default label");
    let mut arms: Vec<(u128, &str)> = Vec::new();
    while *i < lines.len() && lines[*i] != "]" {
        let arm = &lines[*i];
        *i += 1;
        // `i8 1, label %case1` (values printed signed)
        let val_tok = arm
            .split_whitespace()
            .nth(1)
            .expect("switch arm value")
            .trim_end_matches(',');
        let v: i128 = val_tok.parse().expect("switch arm integer");
        let value = if v < 0 {
            (v + (1i128 << w)).cast_unsigned()
        } else {
            v.cast_unsigned()
        };
        let target = arm
            .split("label %")
            .nth(1)
            .expect("switch arm target")
            .trim();
        arms.push((value, target));
    }
    let mut acc = exec_cfg_block(arena, blocks, env.clone(), default, label, depth + 1);
    for (val, target) in arms.iter().rev() {
        let then = exec_cfg_block(arena, blocks, env.clone(), target, label, depth + 1);
        acc = match (then, acc) {
            (Some(taken), Some(base)) => {
                let arm_val = arena.bv_const(w, *val).unwrap();
                let cond = arena.eq(scrut, arm_val).unwrap();
                Some((arena.ite(cond, taken.0, base.0).unwrap(), taken.1))
            }
            (Some(taken), None) => Some(taken),
            (None, base) => base,
        };
    }
    acc
}

/// Symbolically execute from block `label` (entered from `pred`) to `ret`.
/// `br i1` forks on a clone of the environment and joins as `ite`; `phi` picks
/// the incoming value whose edge label matches `pred`; `unreachable` yields
/// `None` (a don't-care the joins drop — assuming UB paths are never taken).
/// The depth cap turns a cyclic CFG into a loud panic (loops are the
/// `TransitionSystem` path).
fn exec_cfg_block(
    arena: &mut TermArena,
    blocks: &[(String, Vec<String>)],
    mut env: HashMap<String, (TermId, u32)>,
    label: &str,
    pred: &str,
    depth: usize,
) -> Option<(TermId, u32)> {
    assert!(
        depth < 64,
        "cyclic or too-deep LLVM CFG (loops are the TransitionSystem path)"
    );
    let (_, lines) = blocks
        .iter()
        .find(|(l, _)| l == label)
        .unwrap_or_else(|| panic!("undefined block %{label}"));
    let mut i = 0;
    while i < lines.len() {
        let line = &lines[i];
        i += 1;
        if line == "unreachable" {
            return None;
        }
        // Side-effect-only calls (e.g. `tail call void @core::panicking::panic`)
        // produce no SSA value; on the panic path the following `unreachable`
        // makes the whole block a don't-care.
        if line.starts_with("call void") || line.starts_with("tail call void") {
            continue;
        }
        // switch iW %x, label %default [ \n iW K, label %case \n ... ]
        if let Some(rest) = line.strip_prefix("switch ") {
            return exec_switch(arena, blocks, &env, rest, lines, &mut i, label, depth);
        }
        if let Some(rest) = line.strip_prefix("ret ") {
            let toks: Vec<&str> = rest.split_whitespace().collect();
            let w = width_of(toks[0]);
            return Some((resolve(arena, &env, toks[1], w), w));
        }
        if let Some(rest) = line.strip_prefix("br ") {
            if let Some(target) = rest.strip_prefix("label %") {
                return exec_cfg_block(arena, blocks, env, target.trim(), label, depth + 1);
            }
            // br i1 %c, label %t, label %f
            let cond_tok = rest
                .strip_prefix("i1 ")
                .expect("conditional br")
                .split(',')
                .next()
                .expect("br condition")
                .trim();
            let cond = resolve(arena, &env, cond_tok, 1);
            let mut targets = rest
                .split("label %")
                .skip(1)
                .map(|s| s.trim().trim_end_matches(','));
            let t_lab = targets.next().expect("br true target");
            let f_lab = targets.next().expect("br false target");
            let then = exec_cfg_block(arena, blocks, env.clone(), t_lab, label, depth + 1);
            let els = exec_cfg_block(arena, blocks, env, f_lab, label, depth + 1);
            return match (then, els) {
                (Some(tv), Some(ev)) => Some((arena.ite(cond, tv.0, ev.0).unwrap(), tv.1)),
                (Some(tv), None) => Some(tv),
                (None, ev) => ev,
            };
        }
        let (dst_tok, rhs) = line.split_once(" = ").expect("instruction `%d = ..`");
        let dst = dst_tok.trim_start_matches('%').to_string();
        let entry = if let Some(rest) = rhs.strip_prefix("phi ") {
            // phi iW [ %v, %pred1 ], [ %v2, %pred2 ]  — pick the edge we came in on.
            let w = width_of(rest.split_whitespace().next().expect("phi type"));
            let mut picked = None;
            for group in rest.split('[').skip(1) {
                let inner = group.split(']').next().expect("phi incoming");
                let (val, lab) = inner.split_once(',').expect("phi `val, label`");
                if lab.trim().trim_start_matches('%') == pred {
                    picked = Some(resolve(arena, &env, val.trim(), w));
                }
            }
            (
                picked.unwrap_or_else(|| panic!("phi has no incoming edge from %{pred}")),
                w,
            )
        } else {
            lower_rhs(arena, &env, rhs)
        };
        env.insert(dst, entry);
    }
    panic!("block %{label} fell through without a terminator");
}

/// Lower a function body — dispatching to the CFG executor when the body
/// branches (`br`), and the fast single-block path otherwise.
///
/// # Panics
/// Panics if the IR/token is malformed or uses an unsupported construct.
#[allow(clippy::implicit_hasher)] // the reflector's SSA env is always the default-hasher `HashMap`.
pub fn lower_fn(
    arena: &mut TermArena,
    env: &mut HashMap<String, (TermId, u32)>,
    ll: &str,
) -> (TermId, u32) {
    let has_cfg = ll
        .lines()
        .map(str::trim)
        .any(|l| l.starts_with("br ") || l.starts_with("switch ") || l == "unreachable");
    if has_cfg {
        let blocks = split_cfg_blocks(ll);
        let entry = blocks.first().expect("a nonempty body").0.clone();
        exec_cfg_block(arena, &blocks, env.clone(), &entry, "", 0)
            .expect("the function entry must be reachable")
    } else {
        lower_body(arena, env, ll)
    }
}

/// Reflect a whole `define` into a fresh arena, declaring one symbol per
/// parameter, and return the [`Reflected`] bundle (arena + params + `ret` term).
///
/// # Panics
/// Panics if the IR/token is malformed or uses an unsupported construct.
pub fn reflect_ll(ll: &str) -> Reflected {
    let mut arena = TermArena::new();
    let mut env: HashMap<String, (TermId, u32)> = HashMap::new();
    let mut params = Vec::new();
    for (name, width) in param_decls(ll) {
        let sort = if width == 1 {
            Sort::Bool
        } else {
            Sort::BitVec(width)
        };
        let sym = arena.declare(&name, sort).unwrap();
        env.insert(name.clone(), (arena.var(sym), width));
        params.push((name, sym, width));
    }
    let (result, _w) = lower_fn(&mut arena, &mut env, ll);
    Reflected {
        arena,
        params,
        env,
        result,
    }
}

/// Reflect a function into an *existing* arena, binding `params[i]` to the i-th
/// declared parameter — so several functions can be lowered over the *same*
/// symbols and proved equivalent.
///
/// # Panics
/// Panics if the IR/token is malformed or uses an unsupported construct.
pub fn reflect_into(arena: &mut TermArena, params: &[TermId], ll: &str) -> TermId {
    let decls = param_decls(ll);
    assert_eq!(
        decls.len(),
        params.len(),
        "parameter count mismatch between the define line and the given terms"
    );
    let mut env: HashMap<String, (TermId, u32)> = HashMap::new();
    for ((name, width), &term) in decls.iter().zip(params) {
        env.insert(name.clone(), (term, *width));
    }
    lower_fn(arena, &mut env, ll).0
}

/// Single-input convenience over [`reflect_into`] (`x` is the sole parameter).
///
/// # Panics
/// Panics if the IR/token is malformed or uses an unsupported construct.
pub fn reflect_unary_into(arena: &mut TermArena, x: TermId, ll: &str) -> TermId {
    reflect_into(arena, &[x], ll)
}
