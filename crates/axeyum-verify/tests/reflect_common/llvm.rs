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
        arena
            .bv_const(width, tok.parse::<u128>().expect("integer constant"))
            .unwrap()
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
    let (result, _w) = lower_body(&mut arena, &mut env, ll);
    Reflected {
        arena,
        params,
        env,
        result,
    }
}

/// Reflect a single-input function into an *existing* arena, using `x` as its
/// parameter — so two functions can be lowered over the *same* symbol and proved
/// equivalent.
pub fn reflect_unary_into(arena: &mut TermArena, x: TermId, ll: &str) -> TermId {
    let decls = param_decls(ll);
    assert_eq!(decls.len(), 1, "reflect_unary_into expects one parameter");
    let mut env: HashMap<String, (TermId, u32)> = HashMap::new();
    env.insert(decls[0].0.clone(), (x, decls[0].1));
    lower_body(arena, &mut env, ll).0
}
