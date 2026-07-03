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
    pub arena: TermArena,
    /// `(name, symbol, width)` for each function parameter (width 1 = `i1`/Bool).
    pub params: Vec<(String, SymbolId, u32)>,
    /// every SSA name (params + results) → `(term, width)`.
    pub env: HashMap<String, (TermId, u32)>,
    pub result: TermId,
}

impl Reflected {
    pub fn param(&self, name: &str) -> TermId {
        self.env[name].0
    }
    pub fn prove_goal(&mut self, goal: TermId) -> ProofOutcome {
        prove(&mut self.arena, &[], goal, &SolverConfig::default())
            .expect("solver should not hard-error")
    }
}

pub fn is_reg(tok: &str) -> bool {
    tok.starts_with('%')
}

/// Resolve an operand token to a term of the given width (1 = Bool).
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

/// Symbolically execute from block `label` (entered from `pred`) to `ret`.
/// `br i1` forks on a clone of the environment and joins as `ite`; `phi` picks
/// the incoming value whose edge label matches `pred`. The depth cap turns a
/// cyclic CFG into a loud panic (loops are the `TransitionSystem` path).
fn exec_cfg_block(
    arena: &mut TermArena,
    blocks: &[(String, Vec<String>)],
    mut env: HashMap<String, (TermId, u32)>,
    label: &str,
    pred: &str,
    depth: usize,
) -> (TermId, u32) {
    assert!(
        depth < 64,
        "cyclic or too-deep LLVM CFG (loops are the TransitionSystem path)"
    );
    let (_, lines) = blocks
        .iter()
        .find(|(l, _)| l == label)
        .unwrap_or_else(|| panic!("undefined block %{label}"));
    for line in lines {
        if let Some(rest) = line.strip_prefix("ret ") {
            let toks: Vec<&str> = rest.split_whitespace().collect();
            let w = width_of(toks[0]);
            return (resolve(arena, &env, toks[1], w), w);
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
            let t = targets.next().expect("br true target");
            let f = targets.next().expect("br false target");
            let then = exec_cfg_block(arena, blocks, env.clone(), t, label, depth + 1);
            let els = exec_cfg_block(arena, blocks, env, f, label, depth + 1);
            return (arena.ite(cond, then.0, els.0).unwrap(), then.1);
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
pub fn lower_fn(
    arena: &mut TermArena,
    env: &mut HashMap<String, (TermId, u32)>,
    ll: &str,
) -> (TermId, u32) {
    let has_cfg = ll.lines().any(|l| l.trim().starts_with("br "));
    if has_cfg {
        let blocks = split_cfg_blocks(ll);
        let entry = blocks.first().expect("a nonempty body").0.clone();
        exec_cfg_block(arena, &blocks, env.clone(), &entry, "", 0)
    } else {
        lower_body(arena, env, ll)
    }
}

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
pub fn reflect_unary_into(arena: &mut TermArena, x: TermId, ll: &str) -> TermId {
    reflect_into(arena, &[x], ll)
}
