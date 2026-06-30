//! L2 (LLVM-IR front end): reflect **single-basic-block LLVM IR** (the optimized
//! register-SSA a leaf function compiles to) into an `axeyum-ir` term, and prove
//! properties of it **symbolically** — over real *compiled* code, from any
//! LLVM-family language (here Rust; C is added in the two-language demo).
//!
//! Design + feasibility: `docs/consumer-track/verify/llvm-ir-frontend.md`.
//!
//! **Prototype scope, honestly:** fixtures are *committed* `.ll` (captured once
//! via `rustc -O --emit=llvm-ir` / `clang -O1 -S -emit-llvm`) — not invoked at
//! test time, so the tests are toolchain-independent (CI-robust). The reflector
//! handles one basic block of SSA: binary int ops, `icmp`, `select`, the
//! `llvm.umin`/`umax` intrinsics, and `ret`. It models arithmetic as **total /
//! wrapping** BV and **ignores `nsw`/`nuw`/poison** (the UB boundary — Alive2
//! territory; sound for the unsigned/wrapping ops here). Memory (`load`/`store`/
//! `getelementptr`) and `br`/`switch`/`phi` CFG are deferred.

use std::collections::HashMap;

use axeyum_ir::{Assignment, Sort, SymbolId, TermArena, TermId, Value, eval};
use axeyum_solver::{ProofOutcome, SolverConfig, prove};

// ---- committed `.ll` fixtures (rustc 1.96 -O --emit=llvm-ir) --------------------

const CLAMP_RS_LL: &str = r"
define noundef range(i32 0, 101) i32 @clamp(i32 noundef %x) unnamed_addr {
start:
  %.x = tail call i32 @llvm.umin.i32(i32 %x, i32 100)
  ret i32 %.x
}
";

const PICK_LL: &str = r"
define noundef i32 @pick(i1 noundef zeroext %c, i32 noundef %a, i32 noundef %b) unnamed_addr {
start:
  %a.b = select i1 %c, i32 %a, i32 %b
  ret i32 %a.b
}
";

const MASKED_LL: &str = r"
define noundef range(i32 256, 512) i32 @masked(i32 noundef %x) unnamed_addr {
start:
  %_2 = and i32 %x, 255
  %_0 = or disjoint i32 %_2, 256
  ret i32 %_0
}
";

// ---- reference Rust oracles (for the fuzz cross-check) -------------------------

fn clamp(x: u32) -> u32 {
    x.min(100)
}
fn pick(c: bool, a: u32, b: u32) -> u32 {
    if c { a } else { b }
}
fn masked(x: u32) -> u32 {
    (x & 0xff) | 0x100
}

// ---- the single-block `.ll` reflector ------------------------------------------

struct Reflected {
    arena: TermArena,
    /// `(name, symbol, width)` for each function parameter (width 1 = `i1`/Bool).
    params: Vec<(String, SymbolId, u32)>,
    /// every SSA name (params + results) → `(term, width)`.
    env: HashMap<String, (TermId, u32)>,
    result: TermId,
}

fn width_of(ty: &str) -> u32 {
    ty.trim_start_matches('i').parse().expect("iN type")
}

fn is_reg(tok: &str) -> bool {
    tok.starts_with('%')
}

/// Resolve an operand token to a term of the given width (1 = Bool).
fn resolve(
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

fn binop(arena: &mut TermArena, op: &str, a: TermId, b: TermId) -> TermId {
    match op {
        "and" => arena.bv_and(a, b),
        "or" => arena.bv_or(a, b),
        "xor" => arena.bv_xor(a, b),
        "add" => arena.bv_add(a, b),
        "sub" => arena.bv_sub(a, b),
        "mul" => arena.bv_mul(a, b),
        "shl" => arena.bv_shl(a, b),
        "lshr" => arena.bv_lshr(a, b),
        "ashr" => arena.bv_ashr(a, b),
        other => panic!("unsupported binop {other}"),
    }
    .unwrap()
}

fn compare(arena: &mut TermArena, pred: &str, a: TermId, b: TermId) -> TermId {
    match pred {
        "eq" => arena.eq(a, b),
        "ne" => {
            let e = arena.eq(a, b).unwrap();
            return arena.not(e).unwrap();
        }
        "ult" => arena.bv_ult(a, b),
        "ule" => arena.bv_ule(a, b),
        "ugt" => arena.bv_ugt(a, b),
        "uge" => arena.bv_uge(a, b),
        "slt" => arena.bv_slt(a, b),
        "sle" => arena.bv_sle(a, b),
        "sgt" => arena.bv_sgt(a, b),
        "sge" => arena.bv_sge(a, b),
        other => panic!("unsupported icmp predicate {other}"),
    }
    .unwrap()
}

/// Lower one instruction's right-hand side to `(term, width)`.
fn lower_rhs(
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

fn reflect_ll(ll: &str) -> Reflected {
    let mut arena = TermArena::new();
    let mut env: HashMap<String, (TermId, u32)> = HashMap::new();
    let mut params = Vec::new();
    let mut result = None;

    let define = ll
        .lines()
        .map(str::trim)
        .find(|l| l.starts_with("define"))
        .expect("a `define` line");
    // Parameter list is inside the parens *after* `@name` (not the `range(...)`).
    let after_at = define.split_once('@').expect("@name").1;
    let params_str = after_at
        .split_once('(')
        .expect("param list")
        .1
        .split_once(')')
        .expect("param list close")
        .0;
    for arg in params_str
        .split(',')
        .map(str::trim)
        .filter(|s| !s.is_empty())
    {
        let toks: Vec<&str> = arg.split_whitespace().collect();
        let width = width_of(toks[0]);
        let name = toks.last().unwrap().trim_start_matches('%').to_string();
        let sort = if width == 1 {
            Sort::Bool
        } else {
            Sort::BitVec(width)
        };
        let sym = arena.declare(&name, sort).unwrap();
        let term = arena.var(sym);
        env.insert(name.clone(), (term, width));
        params.push((name, sym, width));
    }

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
            result = Some(resolve(&mut arena, &env, toks[1], w));
            continue;
        }
        let (dst_tok, rhs) = line.split_once(" = ").expect("instruction `%d = ..`");
        let dst = dst_tok.trim_start_matches('%').to_string();
        let (term, width) = lower_rhs(&mut arena, &env, rhs);
        env.insert(dst, (term, width));
    }

    Reflected {
        arena,
        params,
        env,
        result: result.expect("a `ret`"),
    }
}

// ---- helpers -------------------------------------------------------------------

impl Reflected {
    fn param(&self, name: &str) -> TermId {
        self.env[name].0
    }
    fn prove_goal(&mut self, goal: TermId) -> ProofOutcome {
        prove(&mut self.arena, &[], goal, &SolverConfig::default())
            .expect("solver should not hard-error")
    }
}

// ---- L2 tests: prove properties of reflected real compiled Rust ----------------

/// `clamp` (reflected from its `@llvm.umin` IR) is `<= 100` for ALL `u32` inputs.
#[test]
fn llvm_clamp_bounded() {
    let mut r = reflect_ll(CLAMP_RS_LL);
    let hundred = r.arena.bv_const(32, 100).unwrap();
    let goal = r.arena.bv_ule(r.result, hundred).unwrap();
    assert!(
        matches!(r.prove_goal(goal), ProofOutcome::Proved(_)),
        "clamp(x) <= 100 must hold for all u32"
    );
}

/// `masked(x) = (x & 0xff) | 0x100` always lands in `[256, 511]` — proven over the
/// reflected `and`/`or` IR for all `u32`.
#[test]
fn llvm_masked_in_range() {
    let mut r = reflect_ll(MASKED_LL);
    let lo = r.arena.bv_const(32, 256).unwrap();
    let hi = r.arena.bv_const(32, 511).unwrap();
    let ge = r.arena.bv_uge(r.result, lo).unwrap();
    let le = r.arena.bv_ule(r.result, hi).unwrap();
    let goal = r.arena.and(ge, le).unwrap();
    assert!(
        matches!(r.prove_goal(goal), ProofOutcome::Proved(_)),
        "masked(x) must be in [256, 511] for all u32"
    );
}

/// `pick(c, a, b)` (reflected from `select`) always returns one of its inputs.
#[test]
fn llvm_pick_returns_an_input() {
    let mut r = reflect_ll(PICK_LL);
    let a = r.param("a");
    let b = r.param("b");
    let eq_a = r.arena.eq(r.result, a).unwrap();
    let eq_b = r.arena.eq(r.result, b).unwrap();
    let goal = r.arena.or(eq_a, eq_b).unwrap();
    assert!(
        matches!(r.prove_goal(goal), ProofOutcome::Proved(_)),
        "pick(c,a,b) must equal a or b"
    );
}

// ---- L2 fuzz cross-check: reflected term vs the real Rust fn -------------------

fn lcg(state: &mut u64) -> u32 {
    *state = state
        .wrapping_mul(6_364_136_223_846_793_005)
        .wrapping_add(1);
    (*state >> 32) as u32
}

fn eval_u32(r: &Reflected, bindings: &[(&str, Value)]) -> u32 {
    let mut asg = Assignment::new();
    for (name, val) in bindings {
        let sym = r
            .params
            .iter()
            .find(|(n, _, _)| n == name)
            .expect("a parameter")
            .1;
        asg.set(sym, val.clone());
    }
    match eval(&r.arena, r.result, &asg).unwrap() {
        Value::Bv { value, .. } => u32::try_from(value).unwrap(),
        other => panic!("expected a BV value, got {other:?}"),
    }
}

/// The reflected LLVM terms compute the *same* function as the real Rust, on a
/// large deterministic sample — concrete execution (the fuzzing oracle) agrees
/// with the reflection, independent of the symbolic proofs above (DISAGREE = 0).
#[test]
fn llvm_reflection_matches_real_rust_under_fuzz() {
    let clamp_r = reflect_ll(CLAMP_RS_LL);
    let masked_r = reflect_ll(MASKED_LL);
    let pick_r = reflect_ll(PICK_LL);
    let mut rng = 0x5DEE_CE66_u64;
    for _ in 0..50_000 {
        let x = lcg(&mut rng);
        assert_eq!(
            eval_u32(
                &clamp_r,
                &[(
                    "x",
                    Value::Bv {
                        width: 32,
                        value: u128::from(x)
                    }
                )]
            ),
            clamp(x),
            "reflected clamp diverged at x={x}"
        );
        assert_eq!(
            eval_u32(
                &masked_r,
                &[(
                    "x",
                    Value::Bv {
                        width: 32,
                        value: u128::from(x)
                    }
                )]
            ),
            masked(x),
            "reflected masked diverged at x={x}"
        );
        let (c, a, b) = (x & 1 == 1, lcg(&mut rng), lcg(&mut rng));
        assert_eq!(
            eval_u32(
                &pick_r,
                &[
                    ("c", Value::Bool(c)),
                    (
                        "a",
                        Value::Bv {
                            width: 32,
                            value: u128::from(a)
                        }
                    ),
                    (
                        "b",
                        Value::Bv {
                            width: 32,
                            value: u128::from(b)
                        }
                    ),
                ]
            ),
            pick(c, a, b),
            "reflected pick diverged at c={c}, a={a}, b={b}"
        );
    }
}
