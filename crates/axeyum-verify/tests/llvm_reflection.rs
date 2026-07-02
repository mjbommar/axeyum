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

use std::collections::{HashMap, HashSet};

use axeyum_ir::{Assignment, Sort, SymbolId, TermArena, TermId, Value, eval};
use axeyum_solver::{
    BmcOutcome, ProofOutcome, SafetyOutcome, SolverConfig, SolverError, TransitionSystem,
    bounded_model_check, prove, prove_safety_k_induction,
};

mod reflect_common;
use reflect_common::{binop, compare, width_of};

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

// ---- N: reflect an LLVM loop into a TransitionSystem, prove all iterations ------
//
// A canonical loop (clang -O1 -fno-unroll-loops) has a header/latch block with a
// `phi` per loop-carried variable and a body that computes the back-edge values.
// We reflect it into the solver's `TransitionSystem` (phi -> state var, entry-
// incoming -> init, back-edge-incoming -> trans via `lower_rhs`, a safety spec ->
// bad) and prove the property for EVERY iteration via PDR. Loop-exit guard is
// dropped (a sound over-approximation for safety). Canonical single-loop-block
// form only; real -O unrolled/SCEV-closed/memory loops are the deferred frontier.

/// `unsigned char capsum8(unsigned char n){ unsigned char acc=0;
/// for(unsigned char i=0;i<n;i++){ acc++; if(acc>100) acc=100; } return acc; }` —
/// `clang -O1 -fno-unroll-loops -fno-vectorize`. Block `5` is the loop header/latch
/// (branches back to itself). Modeled at `i8` so PDR/k-induction over the loop
/// state stays fast (the 32-bit version bit-blasts to 64 bits of state and PDR's
/// frame search over the unbounded counter blows up — the same width lesson as the
/// modular-arithmetic proofs; the loop *structure* reflected is width-agnostic).
const CAPSUM_LOOP_LL: &str = r"
define dso_local zeroext range(i8 0, 101) i8 @capsum8(i8 noundef zeroext %0) local_unnamed_addr {
  %2 = icmp eq i8 %0, 0
  br i1 %2, label %3, label %5

3:
  %4 = phi i8 [ 0, %1 ], [ %9, %5 ]
  ret i8 %4

5:
  %6 = phi i8 [ %10, %5 ], [ 0, %1 ]
  %7 = phi i8 [ %9, %5 ], [ 0, %1 ]
  %8 = tail call i8 @llvm.umin.i8(i8 %7, i8 99)
  %9 = add nuw nsw i8 %8, 1
  %10 = add nuw i8 %6, 1
  %11 = icmp eq i8 %10, %0
  br i1 %11, label %3, label %5
}
";

/// A loop-carried variable: its `phi` name, width, the entry-incoming init value,
/// and the register feeding its back-edge.
struct PhiVar {
    name: String,
    width: u32,
    init: String,
    back: String,
}

/// An LLVM loop reflected as a transition system over its loop-carried `phi`s.
struct LoopSystem {
    phis: Vec<PhiVar>,
    body: Vec<String>, // needed body instructions (exit guard excluded)
    bad_idx: usize,    // bad = phis[bad_idx] > bad_bound
    bad_bound: u128,
}

impl LoopSystem {
    fn new(ll: &str, bad_var: &str, bad_bound: u128) -> Self {
        let (phis, body) = parse_loop(ll);
        let bad_idx = phis
            .iter()
            .position(|p| p.name == bad_var)
            .expect("bad var must be a loop phi");
        Self {
            phis,
            body,
            bad_idx,
            bad_bound,
        }
    }
}

/// Split the function body into `(label, lines)` blocks, find the loop block (its
/// `br` targets its own label), and extract its `phi`s + the body instructions
/// transitively needed for the back-edge values (dropping the exit-guard `icmp`).
/// Split the function body into `(label, lines)` basic blocks (the entry block
/// has label `""`).
fn split_blocks(ll: &str) -> Vec<(String, Vec<String>)> {
    let mut blocks: Vec<(String, Vec<String>)> = Vec::new();
    let mut label = String::new();
    let mut lines: Vec<String> = Vec::new();
    let mut in_body = false;
    for raw in ll.lines() {
        let line = raw.trim();
        if line.starts_with("define") {
            in_body = true;
            continue;
        }
        if !in_body || line.is_empty() {
            continue;
        }
        if line == "}" {
            blocks.push((label.clone(), std::mem::take(&mut lines)));
            break;
        }
        // A label line: `N:` with no `=`, the label bare, the rest empty or a comment.
        let is_label = if line.contains('=') {
            None
        } else {
            line.split_once(':').filter(|(lab, rest)| {
                !lab.contains(' ')
                    && !lab.is_empty()
                    && (rest.trim().is_empty() || rest.trim_start().starts_with(';'))
            })
        };
        if let Some((lab, _)) = is_label {
            blocks.push((label.clone(), std::mem::take(&mut lines)));
            label = lab.to_string();
            continue;
        }
        lines.push(line.to_string());
    }
    blocks
}

fn parse_loop(ll: &str) -> (Vec<PhiVar>, Vec<String>) {
    let blocks = split_blocks(ll);
    let (loop_label, loop_lines) = blocks
        .iter()
        .find(|(lab, ls)| {
            !lab.is_empty()
                && ls.iter().any(|l| {
                    l.starts_with("br ")
                        && l.split("label %").skip(1).any(|t| {
                            t.split(|c: char| c == ',' || c.is_whitespace()).next()
                                == Some(lab.as_str())
                        })
                })
        })
        .expect("a self-branching loop block");

    let mut phis = Vec::new();
    for l in loop_lines {
        if !l.contains("= phi") {
            continue;
        }
        let (dst, rhs) = l.split_once(" = ").unwrap();
        let name = dst.trim_start_matches('%').to_string();
        let after = rhs.strip_prefix("phi ").unwrap();
        let width = width_of(after.split_whitespace().next().unwrap());
        let (mut init, mut back) = (String::new(), String::new());
        for chunk in after.split('[').skip(1) {
            let inside = chunk.split(']').next().unwrap();
            let mut it = inside.split(',').map(str::trim);
            let val = it.next().unwrap();
            let lbl = it.next().unwrap().trim_start_matches('%');
            if lbl == loop_label {
                back = val.trim_start_matches('%').to_string();
            } else {
                init = val.to_string();
            }
        }
        phis.push(PhiVar {
            name,
            width,
            init,
            back,
        });
    }

    // Non-phi assignments in the loop block.
    let assigns: Vec<(String, String)> = loop_lines
        .iter()
        .filter(|l| l.contains(" = ") && !l.contains("= phi"))
        .map(|l| {
            let (d, r) = l.split_once(" = ").unwrap();
            (d.trim_start_matches('%').to_string(), r.to_string())
        })
        .collect();

    // Transitive-dependency closure from the back-edge values (drops the guard).
    let mut needed: HashSet<String> = phis.iter().map(|p| p.back.clone()).collect();
    loop {
        let before = needed.len();
        for (d, r) in &assigns {
            if needed.contains(d) {
                for t in r.replace(',', " ").split_whitespace() {
                    if let Some(reg) = t.strip_prefix('%') {
                        needed.insert(reg.to_string());
                    }
                }
            }
        }
        if needed.len() == before {
            break;
        }
    }
    let body = assigns
        .iter()
        .filter(|(d, _)| needed.contains(d))
        .map(|(d, r)| format!("%{d} = {r}"))
        .collect();

    (phis, body)
}

impl TransitionSystem for LoopSystem {
    fn state_vars(&self, arena: &mut TermArena, step: usize) -> Result<Vec<SymbolId>, SolverError> {
        let mut v = Vec::new();
        for p in &self.phis {
            v.push(arena.declare(&format!("{}@{step}", p.name), Sort::BitVec(p.width))?);
        }
        Ok(v)
    }

    fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError> {
        let mut acc: Option<TermId> = None;
        for (k, p) in self.phis.iter().enumerate() {
            let var = arena.var(s0[k]);
            let c = arena.bv_const(p.width, p.init.parse::<u128>().expect("constant init"))?;
            let e = arena.eq(var, c)?;
            acc = Some(match acc {
                None => e,
                Some(a) => arena.and(a, e)?,
            });
        }
        Ok(acc.expect("at least one phi"))
    }

    fn trans(
        &self,
        arena: &mut TermArena,
        pre: &[SymbolId],
        post: &[SymbolId],
    ) -> Result<TermId, SolverError> {
        let mut env: HashMap<String, (TermId, u32)> = HashMap::new();
        for (k, p) in self.phis.iter().enumerate() {
            env.insert(p.name.clone(), (arena.var(pre[k]), p.width));
        }
        for line in &self.body {
            let (dst, rhs) = line.split_once(" = ").unwrap();
            let (t, w) = lower_rhs(arena, &env, rhs);
            env.insert(dst.trim_start_matches('%').to_string(), (t, w));
        }
        let mut acc: Option<TermId> = None;
        for (k, p) in self.phis.iter().enumerate() {
            let next = env.get(&p.back).expect("back-edge value").0;
            let pv = arena.var(post[k]);
            let e = arena.eq(pv, next)?;
            acc = Some(match acc {
                None => e,
                Some(a) => arena.and(a, e)?,
            });
        }
        Ok(acc.expect("at least one phi"))
    }

    fn bad(&self, arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError> {
        let p = &self.phis[self.bad_idx];
        let v = arena.var(s[self.bad_idx]);
        let c = arena.bv_const(p.width, self.bad_bound)?;
        Ok(arena.bv_ugt(v, c)?)
    }
}

/// The capped accumulator's `acc` stays `<= 100` for **every iteration** of the
/// real compiled C loop — proven unbounded by **k-induction** from the reflected
/// LLVM `phi`/back-edge structure (`acc' = umin(acc,99)+1 <= 100` is 1-inductive,
/// so k-induction closes it without PDR's frame search).
#[test]
fn llvm_loop_acc_bounded_all_iterations() {
    let sys = LoopSystem::new(CAPSUM_LOOP_LL, "7", 100);
    let mut arena = TermArena::new();
    let outcome = prove_safety_k_induction(&mut arena, &sys, 4, &SolverConfig::default())
        .expect("solver should not hard-error");
    assert!(
        matches!(outcome, SafetyOutcome::Safe { .. }),
        "acc <= 100 must hold for all loop iterations, got {outcome:?}"
    );
}

/// A (false) bound the loop genuinely exceeds is refuted, not falsely proved: the
/// accumulator climbs past `2` within a few iterations, so bounded model checking
/// finds a concrete `Reachable` counterexample trace.
#[test]
fn llvm_loop_false_bound_is_reachable() {
    let sys = LoopSystem::new(CAPSUM_LOOP_LL, "7", 2);
    let mut arena = TermArena::new();
    let outcome = bounded_model_check(&mut arena, &sys, 8, &SolverConfig::default())
        .expect("solver should not hard-error");
    assert!(
        matches!(outcome, BmcOutcome::Reachable { .. }),
        "acc climbs past 2 within a few steps; expected Reachable, got {outcome:?}"
    );
}

/// Bounded model checking of the loop finds no `acc > 100` within a depth bound
/// (`UnreachableWithinBound`, not a proof), consistent with the unbounded PDR
/// `Safe` — bounded and unbounded agree.
#[test]
fn llvm_loop_bounded_agrees_with_unbounded() {
    let sys = LoopSystem::new(CAPSUM_LOOP_LL, "7", 100);
    let mut arena = TermArena::new();
    let outcome = bounded_model_check(&mut arena, &sys, 8, &SolverConfig::default())
        .expect("solver should not hard-error");
    assert!(
        matches!(outcome, BmcOutcome::UnreachableWithinBound { .. }),
        "no acc>100 within bound (consistent with the unbounded proof), got {outcome:?}"
    );
}

// ---- O: memory — reflect constant-offset buffer reads (the parser primitive) ----
//
// A `readonly` pointer parameter to a size-N buffer is reflected by **partial
// evaluation of memory**: N fresh BV8 symbols (the buffer bytes) plus a pointer
// env mapping each ptr-typed register to a constant byte offset (the param -> 0,
// `getelementptr i8 .. +K` -> offset+K, `load i8` -> the byte symbol at that
// offset). Sound + complete for constant-offset read-only `i8` loads — which IS
// the fixed-offset packet-header idiom. Symbolic indices (array theory), stores,
// wide loads, and a bounds model are the deferred frontier (see the design doc).

/// `unsigned short read_be16(const unsigned char *p){ return (p[0]<<8)|p[1]; }`
/// — `clang -O1`. The canonical big-endian field read: two byte loads combined.
const READ_BE16_LL: &str = r"
define dso_local zeroext i16 @read_be16(ptr noundef readonly captures(none) %0) local_unnamed_addr {
  %2 = load i8, ptr %0, align 1
  %3 = zext i8 %2 to i16
  %4 = shl nuw i16 %3, 8
  %5 = getelementptr inbounds nuw i8, ptr %0, i64 1
  %6 = load i8, ptr %5, align 1
  %7 = zext i8 %6 to i16
  %8 = or disjoint i16 %4, %7
  ret i16 %8
}
";

/// `unsigned ipv4_ihl_bytes(const unsigned char *p){ return (p[0]&0x0f)*4; }` —
/// clang strength-reduced the multiply into `(p[0] << 2) & 60`. Proving the
/// compiled trick equal to the obvious spec is a mini translation-validation.
const IPV4_IHL_LL: &str = r"
define dso_local range(i32 0, 61) i32 @ipv4_ihl_bytes(ptr noundef readonly captures(none) %0) local_unnamed_addr {
  %2 = load i8, ptr %0, align 1
  %3 = shl i8 %2, 2
  %4 = and i8 %3, 60
  %5 = zext nneg i8 %4 to i32
  ret i32 %5
}
";

/// A buffer-reading function reflected over `buf_len` symbolic bytes.
struct BufReflected {
    arena: TermArena,
    /// The buffer bytes `p[0..N)` as BV8 symbols.
    bytes: Vec<SymbolId>,
    result: TermId,
}

/// Reflect a single-`ptr`-parameter, single-block function by partially
/// evaluating its constant-offset `i8` loads over `buf_len` byte symbols.
fn reflect_buf_ll(ll: &str, buf_len: usize) -> BufReflected {
    let mut arena = TermArena::new();

    // The single pointer parameter's register name. Extract the `%`-register
    // directly from the `define` line — naive paren-splitting breaks on attribute
    // parens like `captures(none)`.
    let define = ll
        .lines()
        .map(str::trim)
        .find(|l| l.starts_with("define"))
        .expect("a `define` line");
    assert!(
        define.contains("(ptr "),
        "reflect_buf_ll expects a leading ptr parameter"
    );
    let base = define
        .split_whitespace()
        .find_map(|t| t.strip_prefix('%').map(|r| r.trim_end_matches(')')))
        .expect("a %register parameter")
        .to_string();

    let bytes: Vec<SymbolId> = (0..buf_len)
        .map(|k| arena.declare(&format!("byte{k}"), Sort::BitVec(8)).unwrap())
        .collect();

    let mut env: HashMap<String, (TermId, u32)> = HashMap::new();
    let mut ptrs: HashMap<String, u64> = HashMap::new();
    ptrs.insert(base, 0);

    let mut result = None;
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
        let rhs_c = rhs.replace(',', "");
        let toks: Vec<&str> = rhs_c.split_whitespace().collect();

        if toks[0] == "getelementptr" {
            // getelementptr [flags..] i8, ptr %q, i64 K — byte addressing only.
            let ptr_idx = toks.iter().position(|t| *t == "ptr").expect("ptr token");
            assert_eq!(toks[ptr_idx - 1], "i8", "only i8 (byte) gep is in scope");
            let q = toks[ptr_idx + 1].trim_start_matches('%');
            let k: u64 = toks.last().unwrap().parse().expect("constant gep offset");
            ptrs.insert(dst, ptrs[q] + k);
        } else if toks[0] == "load" {
            // load i8, ptr %q [, align ..] — the byte symbol at the offset.
            assert_eq!(toks[1], "i8", "only i8 loads are in scope");
            let q = toks[3].trim_start_matches('%');
            let off = usize::try_from(ptrs[q]).unwrap();
            assert!(off < bytes.len(), "load at offset {off} exceeds buffer");
            env.insert(dst, (arena.var(bytes[off]), 8));
        } else {
            let (t, w) = lower_rhs(&mut arena, &env, rhs);
            env.insert(dst, (t, w));
        }
    }

    BufReflected {
        arena,
        bytes,
        result: result.expect("a `ret`"),
    }
}

/// Cross-form equivalence over real compiled memory code: the buffer-reading
/// `read_be16(p)` equals the value-passing `be16(hi, lo)` (from the M round) with
/// `hi = p[0]`, `lo = p[1]` — two differently-shaped compiled functions, one of
/// them reading memory, proved to compute the same field for all buffer contents.
#[test]
fn llvm_buffer_read_be16_equals_value_be16() {
    let mut r = reflect_buf_ll(READ_BE16_LL, 2);
    let b0 = r.arena.var(r.bytes[0]);
    let b1 = r.arena.var(r.bytes[1]);
    let mut env: HashMap<String, (TermId, u32)> = HashMap::new();
    env.insert("hi".to_string(), (b0, 8));
    env.insert("lo".to_string(), (b1, 8));
    let (value_form, _w) = lower_body(&mut r.arena, &mut env, BE16_LL);
    let goal = r.arena.eq(r.result, value_form).unwrap();
    assert!(
        matches!(
            prove(&mut r.arena, &[], goal, &SolverConfig::default()).unwrap(),
            ProofOutcome::Proved(_)
        ),
        "buffer read_be16(p) must equal value be16(p[0], p[1]) for all buffers"
    );
}

/// Mini translation-validation: clang compiled `(p[0] & 0x0f) * 4` into
/// `(p[0] << 2) & 60`; prove the compiled trick equals the obvious spec
/// `zext(p[0] & 0x0f) * 4` for every byte.
#[test]
fn llvm_ihl_compiled_trick_equals_spec() {
    let mut r = reflect_buf_ll(IPV4_IHL_LL, 1);
    let b0 = r.arena.var(r.bytes[0]);
    let mask = r.arena.bv_const(8, 0x0f).unwrap();
    let nib = r.arena.bv_and(b0, mask).unwrap();
    let wide = r.arena.zero_ext(24, nib).unwrap();
    let four = r.arena.bv_const(32, 4).unwrap();
    let spec = r.arena.bv_mul(wide, four).unwrap();
    let goal = r.arena.eq(r.result, spec).unwrap();
    assert!(
        matches!(
            prove(&mut r.arena, &[], goal, &SolverConfig::default()).unwrap(),
            ProofOutcome::Proved(_)
        ),
        "the compiled (p0<<2)&60 must equal the spec zext(p0&0x0f)*4"
    );
}

/// Range facts of the compiled IHL: the result is `<= 60` and a multiple of 4
/// (low two bits zero) — exactly what LLVM's own `range(i32 0, 61)` attribute
/// promises, now *proved* rather than trusted.
#[test]
fn llvm_ihl_range_properties() {
    let mut r = reflect_buf_ll(IPV4_IHL_LL, 1);
    let sixty = r.arena.bv_const(32, 60).unwrap();
    let le = r.arena.bv_ule(r.result, sixty).unwrap();
    let three = r.arena.bv_const(32, 3).unwrap();
    let low2 = r.arena.bv_and(r.result, three).unwrap();
    let zero = r.arena.bv_const(32, 0).unwrap();
    let mult4 = r.arena.eq(low2, zero).unwrap();
    let goal = r.arena.and(le, mult4).unwrap();
    assert!(
        matches!(
            prove(&mut r.arena, &[], goal, &SolverConfig::default()).unwrap(),
            ProofOutcome::Proved(_)
        ),
        "ihl must be <= 60 and a multiple of 4"
    );
}

/// The buffer reflections compute the same functions as the C semantics, on a
/// large deterministic sample — the fuzzing-oracle cross-check (DISAGREE = 0),
/// independent of the symbolic proofs above.
#[test]
fn llvm_buffer_reflection_matches_c_under_fuzz() {
    fn read_be16_oracle(b0: u8, b1: u8) -> u16 {
        (u16::from(b0) << 8) | u16::from(b1)
    }
    fn ihl_oracle(b0: u8) -> u32 {
        u32::from(b0 & 0x0f) * 4
    }
    fn eval_bytes(r: &BufReflected, vals: &[u8]) -> u128 {
        let mut asg = Assignment::new();
        for (sym, v) in r.bytes.iter().zip(vals) {
            asg.set(
                *sym,
                Value::Bv {
                    width: 8,
                    value: u128::from(*v),
                },
            );
        }
        match eval(&r.arena, r.result, &asg).unwrap() {
            Value::Bv { value, .. } => value,
            other => panic!("expected a BV value, got {other:?}"),
        }
    }

    let be16_r = reflect_buf_ll(READ_BE16_LL, 2);
    let ihl_r = reflect_buf_ll(IPV4_IHL_LL, 1);
    let mut rng = 0x0DDB_A115_u64;
    for _ in 0..50_000 {
        let bytes = lcg(&mut rng).to_le_bytes();
        assert_eq!(
            eval_bytes(&be16_r, &bytes[..2]),
            u128::from(read_be16_oracle(bytes[0], bytes[1])),
            "reflected read_be16 diverged at {:?}",
            &bytes[..2]
        );
        assert_eq!(
            eval_bytes(&ihl_r, &bytes[..1]),
            u128::from(ihl_oracle(bytes[0])),
            "reflected ihl diverged at {}",
            bytes[0]
        );
    }
}

// ---- P: symbolic buffer indices — bounds safety on compiled code ---------------
//
// `p[i]` with a symbolic index compiles to a `getelementptr` with a *register*
// offset. We track each pointer register's offset as a BV64 term (constant gep ->
// off+K; register gep -> off+reg, the register lowered by the existing zext/and
// handling); a symbolic `load i8` over a known-size-N buffer becomes an ite-table
// select over N byte symbols (stays QF_BV) AND records the offset term, so the
// safety spec "every load offset < N" can be proved or refuted. Fixed-size buffer
// only; an unbounded buffer is the deferred array-theory route.

/// `unsigned char get(const u8 *p, unsigned i){ return p[i]; }` — `clang -O1`.
/// Unguarded index: the load offset is `zext(i)`, so out-of-bounds is reachable.
const GET_LL: &str = r"
define dso_local zeroext i8 @get(ptr noundef readonly captures(none) %0, i32 noundef %1) local_unnamed_addr {
  %3 = zext i32 %1 to i64
  %4 = getelementptr inbounds nuw i8, ptr %0, i64 %3
  %5 = load i8, ptr %4, align 1
  ret i8 %5
}
";

/// `unsigned char get_masked(const u8 *p, unsigned i){ return p[i & 3]; }` — the
/// masked (safe) form: the load offset is `zext(i & 3)`, provably `< 4`.
const GET_MASKED_LL: &str = r"
define dso_local zeroext i8 @get_masked(ptr noundef readonly captures(none) %0, i32 noundef %1) local_unnamed_addr {
  %3 = and i32 %1, 3
  %4 = zext nneg i32 %3 to i64
  %5 = getelementptr inbounds nuw i8, ptr %0, i64 %4
  %6 = load i8, ptr %5, align 1
  ret i8 %6
}
";

/// A symbolic-index buffer read reflected over `buf_len` byte symbols.
struct SymBufReflected {
    arena: TermArena,
    bytes: Vec<SymbolId>,
    /// The non-pointer parameter (the index `i`) as a BV symbol.
    index: SymbolId,
    /// The (single) load's byte offset, as a BV64 term.
    load_offset: TermId,
    result: TermId,
}

/// Reflect a `(ptr, iN idx)` single-load function, tracking the pointer offset as
/// a BV64 term and building an ite-table load over `buf_len` byte symbols.
fn reflect_buf_sym_ll(ll: &str, buf_len: usize) -> SymBufReflected {
    let mut arena = TermArena::new();
    let define = ll
        .lines()
        .map(str::trim)
        .find(|l| l.starts_with("define"))
        .expect("a `define` line");

    // The pointer parameter register and the (single) integer index parameter.
    let regs: Vec<&str> = define
        .split_whitespace()
        .filter_map(|t| t.strip_prefix('%').map(|r| r.trim_end_matches([')', ','])))
        .collect();
    let base = regs[0].to_string();
    let index = arena
        .declare(&format!("idx_{}", regs[1]), Sort::BitVec(32))
        .unwrap();

    let bytes: Vec<SymbolId> = (0..buf_len)
        .map(|k| arena.declare(&format!("byte{k}"), Sort::BitVec(8)).unwrap())
        .collect();

    let mut env: HashMap<String, (TermId, u32)> = HashMap::new();
    env.insert(regs[1].to_string(), (arena.var(index), 32));
    let mut ptr_off: HashMap<String, TermId> = HashMap::new();
    let zero64 = arena.bv_const(64, 0).unwrap();
    ptr_off.insert(base, zero64);

    let mut result = None;
    let mut load_offset = None;
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
        let (dst_tok, rhs) = line.split_once(" = ").expect("instruction");
        let dst = dst_tok.trim_start_matches('%').to_string();
        let rhs_c = rhs.replace(',', "");
        let toks: Vec<&str> = rhs_c.split_whitespace().collect();

        if toks[0] == "getelementptr" {
            // getelementptr [flags] i8, ptr %q, i64 OP  — byte addressing only.
            let ptr_idx = toks.iter().position(|t| *t == "ptr").expect("ptr token");
            assert_eq!(toks[ptr_idx - 1], "i8", "only i8 (byte) gep is in scope");
            let q = toks[ptr_idx + 1].trim_start_matches('%');
            let op = toks.last().unwrap();
            // delta: a register (a BV term, widened to 64) or a constant.
            let delta = if let Some(reg) = op.strip_prefix('%') {
                let (t, w) = env[reg];
                if w < 64 {
                    arena.zero_ext(64 - w, t).unwrap()
                } else {
                    t
                }
            } else {
                arena
                    .bv_const(64, op.parse::<u128>().expect("gep const"))
                    .unwrap()
            };
            let base_off = ptr_off[q];
            ptr_off.insert(dst, arena.bv_add(base_off, delta).unwrap());
        } else if toks[0] == "load" {
            assert_eq!(toks[1], "i8", "only i8 loads are in scope");
            let q = toks[3].trim_start_matches('%');
            let off = ptr_off[q];
            load_offset = Some(off);
            // ite-table select over the byte symbols.
            let mut acc = arena.var(bytes[0]);
            for (k, sym) in bytes.iter().enumerate() {
                let k64 = arena.bv_const(64, k as u128).unwrap();
                let is_k = arena.eq(off, k64).unwrap();
                let byte = arena.var(*sym);
                acc = arena.ite(is_k, byte, acc).unwrap();
            }
            env.insert(dst, (acc, 8));
        } else {
            let (t, w) = lower_rhs(&mut arena, &env, rhs);
            env.insert(dst, (t, w));
        }
    }

    SymBufReflected {
        arena,
        bytes,
        index,
        load_offset: load_offset.expect("a load"),
        result: result.expect("a `ret`"),
    }
}

/// The masked access `p[i & 3]` (over a 4-byte buffer) is provably **in bounds**
/// for all `i`: its compiled load offset is always `< 4` — a memory-safety proof
/// over real compiled LLVM.
#[test]
fn llvm_masked_index_is_in_bounds() {
    let mut r = reflect_buf_sym_ll(GET_MASKED_LL, 4);
    let n = r.arena.bv_const(64, 4).unwrap();
    let goal = r.arena.bv_ult(r.load_offset, n).unwrap();
    assert!(
        matches!(
            prove(&mut r.arena, &[], goal, &SolverConfig::default()).unwrap(),
            ProofOutcome::Proved(_)
        ),
        "p[i & 3] must always be in bounds of a 4-byte buffer"
    );
}

/// The unguarded access `p[i]` is **not** in bounds — the solver refutes
/// `offset < 4` with a concrete `i >= 4` out-of-bounds witness (Heartbleed-shaped,
/// on the compiled code).
#[test]
fn llvm_unguarded_index_is_out_of_bounds() {
    let mut r = reflect_buf_sym_ll(GET_LL, 4);
    let n = r.arena.bv_const(64, 4).unwrap();
    let goal = r.arena.bv_ult(r.load_offset, n).unwrap();
    assert!(
        matches!(
            prove(&mut r.arena, &[], goal, &SolverConfig::default()).unwrap(),
            ProofOutcome::Disproved(_)
        ),
        "p[i] is unguarded; offset<4 must be refuted with an OOB witness"
    );
}

/// The symbolic-index value reflection matches C semantics on a large sample:
/// `get_masked(p, i) == p[i & 3]` (the fuzzing-oracle cross-check, DISAGREE = 0).
#[test]
fn llvm_masked_index_value_matches_c_under_fuzz() {
    let r = reflect_buf_sym_ll(GET_MASKED_LL, 4);
    let mut rng = 0x00A5_5A00_u64;
    for _ in 0..50_000 {
        let raw = lcg(&mut rng);
        let buf = raw.to_le_bytes();
        let i = lcg(&mut rng);
        let mut asg = Assignment::new();
        for (k, sym) in r.bytes.iter().enumerate() {
            asg.set(
                *sym,
                Value::Bv {
                    width: 8,
                    value: u128::from(buf[k]),
                },
            );
        }
        asg.set(
            r.index,
            Value::Bv {
                width: 32,
                value: u128::from(i),
            },
        );
        let got = match eval(&r.arena, r.result, &asg).unwrap() {
            Value::Bv { value, .. } => u8::try_from(value).unwrap(),
            other => panic!("expected BV, got {other:?}"),
        };
        assert_eq!(got, buf[(i & 3) as usize], "masked index diverged at i={i}");
    }
}
