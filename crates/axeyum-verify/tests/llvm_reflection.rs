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
    } else if toks[0] == "zext" || toks[0] == "sext" || toks[0] == "trunc" {
        // zext/sext/trunc iSRC %v to iDST  (mixed-width: byte<->word field ops)
        let src_w = width_of(toks[1]);
        let src = resolve(arena, env, toks[2], src_w);
        let dst_w = width_of(toks[4]);
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
fn param_decls(ll: &str) -> Vec<(String, u32)> {
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
fn lower_body(
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

fn reflect_ll(ll: &str) -> Reflected {
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
fn reflect_unary_into(arena: &mut TermArena, x: TermId, ll: &str) -> TermId {
    let decls = param_decls(ll);
    assert_eq!(decls.len(), 1, "reflect_unary_into expects one parameter");
    let mut env: HashMap<String, (TermId, u32)> = HashMap::new();
    env.insert(decls[0].0.clone(), (x, decls[0].1));
    lower_body(arena, &mut env, ll).0
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

// ---- L3: one front end, two languages, proved equivalent -----------------------

/// `clamp` from **clang** (C), `clang -O1 -S -emit-llvm`. Note the numeric SSA
/// names (`%0`, `%2`) — the reflector handles them like any other.
const CLAMP_C_LL: &str = r"
define dso_local noundef range(i32 0, 101) i32 @clamp(i32 noundef %0) local_unnamed_addr {
  %2 = tail call i32 @llvm.umin.i32(i32 %0, i32 100)
  ret i32 %2
}
";

/// A hand-written alternative `clamp` in LLVM IR via `icmp`+`select` (the form a
/// less-aggressive compiler emits) — semantically clamp, *structurally different*
/// from the `@llvm.umin` form, so proving them equal is real solver work.
const CLAMP_SELECT_LL: &str = r"
define i32 @clamp_sel(i32 %x) {
entry:
  %c = icmp ugt i32 %x, 100
  %r = select i1 %c, i32 100, i32 %x
  ret i32 %r
}
";

/// One front end, two languages: `clamp` from **C (clang)** and **Rust (rustc)**
/// both reflect through the *same* pipeline, and each is proved `<= 100`.
/// (Measured: at `-O`, LLVM canonicalizes both to `@llvm.umin`, so the two
/// reflections are in fact the identical interned term — the IR converged
/// completely. The point stands: one reflector, the whole LLVM family.)
#[test]
fn c_and_rust_clamp_both_verify() {
    for (ll, lang) in [(CLAMP_RS_LL, "Rust"), (CLAMP_C_LL, "C")] {
        let mut r = reflect_ll(ll);
        let hundred = r.arena.bv_const(32, 100).unwrap();
        let goal = r.arena.bv_ule(r.result, hundred).unwrap();
        assert!(
            matches!(r.prove_goal(goal), ProofOutcome::Proved(_)),
            "{lang} clamp must be <= 100 for all u32"
        );
    }
}

/// Non-trivial symbolic equivalence over LLVM IR: the `@llvm.umin` clamp and the
/// `icmp`+`select` clamp reflect to *different* terms, proved equal for all `u32`
/// by the solver — the equivalence the optimizer happened not to do for us.
#[test]
fn two_llvm_clamp_forms_proved_equivalent() {
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::BitVec(32)).unwrap();
    let x = arena.var(x_sym);
    let umin_t = reflect_unary_into(&mut arena, x, CLAMP_RS_LL);
    let sel_t = reflect_unary_into(&mut arena, x, CLAMP_SELECT_LL);
    let goal = arena.eq(umin_t, sel_t).unwrap();
    assert!(
        matches!(
            prove(&mut arena, &[], goal, &SolverConfig::default()).unwrap(),
            ProofOutcome::Proved(_)
        ),
        "the umin and icmp/select clamp forms must be provably equivalent"
    );
}

// ---- M: mixed width (zext) + if-converted branches -----------------------------

/// `fn be16(hi:u8, lo:u8)->u16 { ((hi as u16)<<8) | (lo as u16) }` — byte→word
/// field packing (`zext` + `shl` + `or`), the shape of every packet-header combine.
const BE16_LL: &str = r"
define noundef i16 @be16(i8 noundef %hi, i8 noundef %lo) unnamed_addr {
start:
  %_4 = zext i8 %hi to i16
  %_3 = shl nuw i16 %_4, 8
  %_5 = zext i8 %lo to i16
  %_0 = or disjoint i16 %_3, %_5
  ret i16 %_0
}
";

/// `if x<10 {1} else if x<100 {2} else {3}` — `-O` if-converts to nested selects.
const CLASSIFY_LL: &str = r"
define noundef range(i32 1, 4) i32 @classify(i32 noundef %x) unnamed_addr {
start:
  %_2 = icmp ult i32 %x, 10
  %_3 = icmp ult i32 %x, 100
  %. = select i1 %_3, i32 2, i32 3
  %_0.sroa.0.0 = select i1 %_2, i32 1, i32 %.
  ret i32 %_0.sroa.0.0
}
";

/// `match x { 0=>7,1=>8,2=>9,_=>0 }` — `-O` lowered the match to `icmp`+`add`+`select`.
const DAY_LL: &str = r"
define noundef range(i32 0, 10) i32 @day(i32 noundef %x) unnamed_addr {
start:
  %0 = icmp ult i32 %x, 3
  %switch.offset = add nsw i32 %x, 7
  %spec.select = select i1 %0, i32 %switch.offset, i32 0
  ret i32 %spec.select
}
";

fn be16(hi: u8, lo: u8) -> u16 {
    (u16::from(hi) << 8) | u16::from(lo)
}
fn classify(x: u32) -> u32 {
    if x < 10 {
        1
    } else if x < 100 {
        2
    } else {
        3
    }
}
fn day(x: u32) -> u32 {
    match x {
        0 => 7,
        1 => 8,
        2 => 9,
        _ => 0,
    }
}

/// Byte↔word field round-trip over the *real compiled* `be16` IR: extracting the
/// two bytes back from the packed `u16` yields exactly the inputs, proven for all
/// `hi`/`lo`. The core correctness property of packet-header field packing.
#[test]
fn llvm_be16_field_roundtrip() {
    let mut r = reflect_ll(BE16_LL);
    let hi = r.param("hi");
    let lo = r.param("lo");
    let hi_back = r.arena.extract(15, 8, r.result).unwrap();
    let lo_back = r.arena.extract(7, 0, r.result).unwrap();
    let g_hi = r.arena.eq(hi_back, hi).unwrap();
    let g_lo = r.arena.eq(lo_back, lo).unwrap();
    let goal = r.arena.and(g_hi, g_lo).unwrap();
    assert!(
        matches!(r.prove_goal(goal), ProofOutcome::Proved(_)),
        "be16 parse∘pack round-trip (high byte == hi, low byte == lo) must hold"
    );
}

/// `classify` (reflected from nested `select`s) always returns `1..=3` — the
/// reflector already spans if-converted branchy leaf functions.
#[test]
fn llvm_classify_in_range() {
    let mut r = reflect_ll(CLASSIFY_LL);
    let one = r.arena.bv_const(32, 1).unwrap();
    let three = r.arena.bv_const(32, 3).unwrap();
    let ge = r.arena.bv_uge(r.result, one).unwrap();
    let le = r.arena.bv_ule(r.result, three).unwrap();
    let goal = r.arena.and(ge, le).unwrap();
    assert!(
        matches!(r.prove_goal(goal), ProofOutcome::Proved(_)),
        "classify(x) must be in 1..=3"
    );
}

/// `day` (reflected from the `icmp`+`add`+`select` the match lowered to) is always
/// `<= 9`.
#[test]
fn llvm_day_bounded() {
    let mut r = reflect_ll(DAY_LL);
    let nine = r.arena.bv_const(32, 9).unwrap();
    let goal = r.arena.bv_ule(r.result, nine).unwrap();
    assert!(
        matches!(r.prove_goal(goal), ProofOutcome::Proved(_)),
        "day(x) must be <= 9"
    );
}

/// The mixed-width / if-converted reflections match the real Rust on a large
/// sample (fuzz cross-check, DISAGREE = 0).
#[test]
fn llvm_mixed_width_matches_real_rust_under_fuzz() {
    let be16_r = reflect_ll(BE16_LL);
    let classify_r = reflect_ll(CLASSIFY_LL);
    let day_r = reflect_ll(DAY_LL);
    let mut rng = 0x1357_9BDF_u64;
    for _ in 0..50_000 {
        let bytes = lcg(&mut rng).to_le_bytes();
        let (hi, lo) = (bytes[1], bytes[0]);
        assert_eq!(
            u16::try_from(eval_u32(
                &be16_r,
                &[
                    (
                        "hi",
                        Value::Bv {
                            width: 8,
                            value: u128::from(hi)
                        }
                    ),
                    (
                        "lo",
                        Value::Bv {
                            width: 8,
                            value: u128::from(lo)
                        }
                    ),
                ]
            ))
            .unwrap(),
            be16(hi, lo),
            "reflected be16 diverged at hi={hi}, lo={lo}"
        );
        let x = lcg(&mut rng);
        let xv = [(
            "x",
            Value::Bv {
                width: 32,
                value: u128::from(x),
            },
        )];
        assert_eq!(
            eval_u32(&classify_r, &xv),
            classify(x),
            "classify diverged at x={x}"
        );
        assert_eq!(eval_u32(&day_r, &xv), day(x), "day diverged at x={x}");
    }
}
