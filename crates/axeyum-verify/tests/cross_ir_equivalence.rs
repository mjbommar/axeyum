//! Cross-IR equivalence: reflect the **same source function** from *both* its
//! rustc **MIR** and its **LLVM IR**, lower both into one `axeyum-ir` arena over a
//! shared input symbol, and **prove them equal for every input**. This is
//! translation-validation of rustc's own MIR→LLVM lowering, and the sharpest
//! demonstration that both front ends land in one term algebra: the proof is
//! `∀x. mir_reflect(f)(x) == llvm_reflect(f)(x)`, discharged by the solver.
//!
//! Both reflectors come from `axeyum_verify::reflect` (the MIR and LLVM parsers over the
//! *shared* op vocabulary), so this file is only fixtures + the equivalence
//! assertions — the DRY payoff realized.
//!
//! Fixtures are committed IR text (captured once from `rustc -Zunpretty=mir` and
//! `rustc -O --emit=llvm-ir`); not invoked at test time, so this is CI-robust.

use axeyum_ir::{Assignment, Sort, TermArena, Value, eval};
use axeyum_solver::{ProofOutcome, SolverConfig, prove};

use axeyum_verify::reflect::llvm::{
    checked::reflect_cfg_into_checked,
    reflect_into, reflect_unary_into,
    syntax::{parse_function, parse_scalar_cfg, render_scalar_cfg},
};
use axeyum_verify::reflect::mir::{reflect_mir_into, reflect_mir_unary};
use axeyum_verify::reflect::oracle::DiffFuzz;

// ---- `masked(x) = (x & 0xff) | 0x100` : straight-line BitAnd/BitOr ~ and/or -----

const MASKED_MIR: &str = r"
fn masked(_1: u32) -> u32 {
    bb0: {
        _2 = BitAnd(copy _1, const 255_u32);
        _0 = BitOr(move _2, const 256_u32);
        return;
    }
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

// ---- `sel(x) = if x > 100 { x & 0xff } else { x | 1 }` : real CFG ---------------
// MIR keeps the branch (a switchInt diamond over a computed bool); `-O` LLVM
// if-converts it to a straight-line `select`. Proving them equal validates
// **if-conversion** — a genuinely structural compiler transform, not just algebra.

const SEL_MIR: &str = r"
fn sel(_1: u32) -> u32 {
    debug x => _1;
    let mut _0: u32;
    let mut _2: bool;

    bb0: {
        StorageLive(_2);
        _2 = Gt(copy _1, const 100_u32);
        switchInt(move _2) -> [0: bb2, otherwise: bb1];
    }

    bb1: {
        _0 = BitAnd(copy _1, const 255_u32);
        goto -> bb3;
    }

    bb2: {
        _0 = BitOr(copy _1, const 1_u32);
        goto -> bb3;
    }

    bb3: {
        StorageDead(_2);
        return;
    }
}
";

const SEL_LL: &str = r"
define i32 @sel(i32 %x) unnamed_addr {
start:
  %c = icmp ugt i32 %x, 100
  %a = and i32 %x, 255
  %b = or i32 %x, 1
  %_0 = select i1 %c, i32 %a, i32 %b
  ret i32 %_0
}
";

/// The **unoptimized** (`-O0`-shape) LLVM form of `sel`: a real `br i1` diamond
/// with a `phi` join — the same CFG shape as the MIR. Reflecting this exercises
/// the LLVM-side CFG executor (branch fork + phi resolved by incoming edge).
const SEL_BR_LL: &str = r"
define i32 @sel(i32 %x) unnamed_addr {
start:
  %c = icmp ugt i32 %x, 100
  br i1 %c, label %then, label %else

then:                                             ; preds = %start
  %a = and i32 %x, 255
  br label %join

else:                                             ; preds = %start
  %b = or i32 %x, 1
  br label %join

join:                                             ; preds = %else, %then
  %r = phi i32 [ %a, %then ], [ %b, %else ]
  ret i32 %r
}
";

// ---- `sar(x: i32) = x >> 4` : signed MIR `Shr` ~ LLVM `ashr` ---------------------
// Sign-aware lowering: MIR's `Shr` is arithmetic on a signed local; the shared
// reflector must pick `ashr` (not `lshr`) from the `i32` signature.

const SAR_MIR: &str = r"
fn sar(_1: i32) -> i32 {
    debug x => _1;
    let mut _0: i32;

    bb0: {
        _0 = Shr(copy _1, const 4_i32);
        return;
    }
}
";

const SAR_LL: &str = r"
define i32 @sar(i32 %x) unnamed_addr {
start:
  %_0 = ashr i32 %x, 4
  ret i32 %_0
}
";

// ---- `scale(x) = x*4 + 1` : MIR `Mul` ~ LLVM strength-reduced `shl` -------------

/// Release/optimized MIR keeps the multiply.
const SCALE_MIR: &str = r"
fn scale(_1: u32) -> u32 {
    bb0: {
        _2 = Mul(copy _1, const 4_u32);
        _0 = Add(move _2, const 1_u32);
        return;
    }
}
";

/// `-O` LLVM strength-reduces `* 4` to `<< 2`. Proving this equals the MIR
/// `Mul`-form validates LLVM's strength reduction (mod 2^32).
const SCALE_LL: &str = r"
define i32 @scale(i32 %x) unnamed_addr {
start:
  %m = shl i32 %x, 2
  %_0 = add i32 %m, 1
  ret i32 %_0
}
";

// ---- `lut(x) = match x { 0=>5, 1=>7, _=>0 }` : switchInt ~ icmp+select -----------

const LUT_MIR: &str = r"
fn lut(_1: u8) -> u8 {
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

/// The `-O` if-converted form: two chained `select`s (equivalent to the match).
const LUT_LL: &str = r"
define noundef i8 @lut(i8 noundef %x) unnamed_addr {
start:
  %c1 = icmp eq i8 %x, 1
  %s1 = select i1 %c1, i8 7, i8 0
  %c0 = icmp eq i8 %x, 0
  %_0 = select i1 %c0, i8 5, i8 %s1
  ret i8 %_0
}
";

/// The **unoptimized** LLVM form of `lut`: a real `switch` instruction with a
/// `phi` join — the direct structural cousin of MIR's `switchInt`.
const LUT_SWITCH_LL: &str = r"
define i8 @lut(i8 %x) unnamed_addr {
start:
  switch i8 %x, label %otherwise [
    i8 0, label %ret5
    i8 1, label %ret7
  ]

otherwise:                                        ; preds = %start
  br label %join

ret5:                                             ; preds = %start
  br label %join

ret7:                                             ; preds = %start
  br label %join

join:                                             ; preds = %ret7, %ret5, %otherwise
  %r = phi i8 [ 0, %otherwise ], [ 5, %ret5 ], [ 7, %ret7 ]
  ret i8 %r
}
";

/// Prove `mir(f) == llvm(f)` for all inputs, and separately exhaustively/fuzz the
/// two reflected terms agree — belt and suspenders across proof and execution.
fn assert_equivalent(width: u32, mir: &str, ll: &str, samples: &[u128]) {
    let canonical = canonical_llvm(ll);
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::BitVec(width)).unwrap();
    let x = arena.var(x_sym);

    let from_mir = reflect_mir_unary(&mut arena, x, mir);
    let from_llvm = reflect_cfg_into_checked(&mut arena, &[x], &canonical)
        .expect("LLVM fixture must satisfy checked CFG reflection");

    let defined = prove(&mut arena, &[], from_llvm.defined, &SolverConfig::default())
        .expect("solver should not hard-error");
    assert!(
        matches!(defined, ProofOutcome::Proved(_)),
        "LLVM fixture must be defined for every {width}-bit input, got {defined:?}"
    );

    // Symbolic: ∀x. mir(x) == llvm(x).
    let eq = arena.eq(from_mir, from_llvm.value).unwrap();
    let outcome =
        prove(&mut arena, &[], eq, &SolverConfig::default()).expect("solver should not hard-error");
    assert!(
        matches!(outcome, ProofOutcome::Proved(_)),
        "MIR and LLVM reflections must be provably equal for all {width}-bit inputs, got {outcome:?}"
    );

    // Concrete cross-check at chosen samples (independent of the proof).
    for &v in samples {
        let mut asg = Assignment::new();
        asg.set(x_sym, Value::Bv { width, value: v });
        let m = match eval(&arena, from_mir, &asg).unwrap() {
            Value::Bv { value, .. } => value,
            other => panic!("mir eval not BV: {other:?}"),
        };
        let l = match eval(&arena, from_llvm.value, &asg).unwrap() {
            Value::Bv { value, .. } => value,
            other => panic!("llvm eval not BV: {other:?}"),
        };
        assert_eq!(m, l, "mir/llvm disagree at x={v}");
    }
}

fn canonical_llvm(ll: &str) -> String {
    let function = parse_function(ll).expect("LLVM fixture must have structured function syntax");
    let graph = parse_scalar_cfg(&function).expect("LLVM fixture must satisfy typed scalar CFG");
    let rendered = render_scalar_cfg(&graph);
    let reparsed = parse_function(&rendered).expect("canonical LLVM fixture must reparse");
    let reparsed = parse_scalar_cfg(&reparsed).expect("canonical LLVM CFG must revalidate");
    assert_eq!(rendered, render_scalar_cfg(&reparsed));
    rendered
}

/// `masked`: straight-line MIR `BitAnd`/`BitOr` == LLVM `and`/`or`, for all `u32`.
/// The MIR side exercises the new shared straight-line `BinaryOp` path, routing
/// `BitAnd`/`BitOr` through the *same* `binop` vocabulary the LLVM side uses.
#[test]
fn masked_mir_equals_llvm() {
    assert_equivalent(
        32,
        MASKED_MIR,
        MASKED_LL,
        &[0, 1, 0xff, 0x100, 0xdead_beef, u128::from(u32::MAX)],
    );
}

/// `sel`: branch-preserving MIR (switchInt diamond over a computed `Gt` bool) ==
/// LLVM's if-converted straight-line `select`, for all u32 — the solver validates
/// **if-conversion**, with real CFG on the MIR side (statements in arm blocks,
/// a bool scrutinee, `goto` join, Storage noise skipped).
#[test]
fn sel_mir_diamond_equals_llvm_select() {
    assert_equivalent(
        32,
        SEL_MIR,
        SEL_LL,
        &[
            0,
            1,
            100,
            101,
            0xff,
            0x100,
            0xdead_beef,
            u128::from(u32::MAX),
        ],
    );
}

/// `sel`, CFG on **both** sides: the branch-preserving MIR diamond == the
/// unoptimized LLVM `br`+`phi` diamond, for all u32. Both symbolic executors
/// walk a real CFG and land in one term algebra.
#[test]
fn sel_mir_diamond_equals_llvm_br_phi() {
    assert_equivalent(
        32,
        SEL_MIR,
        SEL_BR_LL,
        &[0, 100, 101, 0xdead_beef, u128::from(u32::MAX)],
    );
}

/// LLVM O0 vs O2, one platform: the `br`+`phi` diamond == the if-converted
/// `select` form, for all u32 — the solver validates LLVM's own optimization
/// pipeline (translation-validation *within* LLVM, à la Alive2, on our stack).
#[test]
fn sel_llvm_br_phi_equals_llvm_select() {
    let o0_text = canonical_llvm(SEL_BR_LL);
    let o2_text = canonical_llvm(SEL_LL);
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::BitVec(32)).unwrap();
    let x = arena.var(x_sym);
    let o0 = reflect_cfg_into_checked(&mut arena, &[x], &o0_text).unwrap();
    let o2 = reflect_cfg_into_checked(&mut arena, &[x], &o2_text).unwrap();
    let both_defined = arena.and(o0.defined, o2.defined).unwrap();
    let eq = arena.eq(o0.value, o2.value).unwrap();
    let obligation = arena.and(both_defined, eq).unwrap();
    let outcome = prove(&mut arena, &[], obligation, &SolverConfig::default())
        .expect("solver should not hard-error");
    assert!(
        matches!(outcome, ProofOutcome::Proved(_)),
        "O0 br+phi and O2 select forms of sel must be provably equal, got {outcome:?}"
    );
}

/// `sar`: signed MIR `Shr` on `i32` == LLVM `ashr`, for all i32 — sign-aware
/// lowering picked from the MIR signature (an `lshr` mismatch would be refuted
/// at any negative input).
#[test]
fn sar_signed_shift_mir_equals_llvm() {
    assert_equivalent(
        32,
        SAR_MIR,
        SAR_LL,
        &[0, 1, 16, 0x7fff_ffff, 0x8000_0000, u128::from(u32::MAX)],
    );
}

/// `scale`: MIR `Mul(x, 4)` == LLVM strength-reduced `x << 2` (then `+1`), for all
/// `u32` — the solver *validates LLVM's strength reduction* through the shared
/// arithmetic vocabulary (`Mul`/`Add` vs `shl`/`add` land in one BV algebra).
#[test]
fn scale_mir_equals_llvm() {
    assert_equivalent(
        32,
        SCALE_MIR,
        SCALE_LL,
        &[0, 1, 2, 0x4000_0000, 0x8000_0000, u128::from(u32::MAX)],
    );
}

/// `lut`: MIR `switchInt` dispatch == LLVM if-converted `icmp`+`select`, for all
/// `u8` — proving rustc's two representations of a match compute one function.
#[test]
fn lut_mir_equals_llvm() {
    assert_equivalent(8, LUT_MIR, LUT_LL, &(0u128..=255).collect::<Vec<_>>());
}

/// `lut`, both dispatchers: MIR `switchInt` == LLVM's `switch` instruction (the
/// direct structural cousin, O0 shape with a 3-way `phi` join), for all u8.
#[test]
fn lut_mir_switchint_equals_llvm_switch() {
    assert_equivalent(
        8,
        LUT_MIR,
        LUT_SWITCH_LL,
        &(0u128..=255).collect::<Vec<_>>(),
    );
}

/// LLVM O0 vs O2 for `lut`: the `switch`+`phi` form == the if-converted chained
/// `select` form, for all u8 — switch elimination validated within LLVM.
#[test]
fn lut_llvm_switch_equals_llvm_selects() {
    let o0_text = canonical_llvm(LUT_SWITCH_LL);
    let o2_text = canonical_llvm(LUT_LL);
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::BitVec(8)).unwrap();
    let x = arena.var(x_sym);
    let o0 = reflect_cfg_into_checked(&mut arena, &[x], &o0_text).unwrap();
    let o2 = reflect_cfg_into_checked(&mut arena, &[x], &o2_text).unwrap();
    let both_defined = arena.and(o0.defined, o2.defined).unwrap();
    let eq = arena.eq(o0.value, o2.value).unwrap();
    let obligation = arena.and(both_defined, eq).unwrap();
    let outcome = prove(&mut arena, &[], obligation, &SolverConfig::default())
        .expect("solver should not hard-error");
    assert!(
        matches!(outcome, ProofOutcome::Proved(_)),
        "switch+phi and select forms of lut must be provably equal, got {outcome:?}"
    );
}

// ---- `lut3` with an `unreachable` default: hypothesis-conditioned equivalence ----

/// MIR of `match x { 0=>5, 1=>7, 2=>9, _=>0 }` — a TOTAL function.
const LUT3_MIR: &str = r"
fn lut3(_1: u8) -> u8 {
    bb0: {
        switchInt(copy _1) -> [0: bb4, 1: bb3, 2: bb2, otherwise: bb1];
    }
    bb1: {
        _0 = const 0_u8;
        goto -> bb5;
    }
    bb2: {
        _0 = const 9_u8;
        goto -> bb5;
    }
    bb3: {
        _0 = const 7_u8;
        goto -> bb5;
    }
    bb4: {
        _0 = const 5_u8;
        goto -> bb5;
    }
    bb5: {
        return;
    }
}
";

/// LLVM where the compiler KNOWS `x <= 2` (an enum-like invariant): the default
/// is `unreachable`. The reflector treats that path as don't-care — assuming
/// the UB edge is never taken.
const LUT3_UNREACH_LL: &str = r"
define i8 @lut3(i8 %x) unnamed_addr {
start:
  switch i8 %x, label %unreach [
    i8 0, label %r5
    i8 1, label %r7
    i8 2, label %r9
  ]

unreach:
  unreachable

r5:                                               ; preds = %start
  br label %join

r7:                                               ; preds = %start
  br label %join

r9:                                               ; preds = %start
  br label %join

join:                                             ; preds = %r9, %r7, %r5
  %r = phi i8 [ 5, %r5 ], [ 7, %r7 ], [ 9, %r9 ]
  ret i8 %r
}
";

/// With the compiler's invariant supplied as a HYPOTHESIS (`x < 3`), the total
/// MIR and the unreachable-default LLVM are provably equal; without it they are
/// undefined outside that range. The checked reflector keeps the modular value
/// separate from the executable-semantics obligation, so no claim is made about
/// its deterministic placeholder on the `unreachable` path.
#[test]
fn lut3_equivalence_holds_exactly_under_the_range_hypothesis() {
    let canonical = canonical_llvm(LUT3_UNREACH_LL);
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::BitVec(8)).unwrap();
    let x = arena.var(x_sym);
    let from_mir = reflect_mir_unary(&mut arena, x, LUT3_MIR);
    let from_llvm = reflect_cfg_into_checked(&mut arena, &[x], &canonical).unwrap();
    let eq = arena.eq(from_mir, from_llvm.value).unwrap();

    let three = arena.bv_const(8, 3).unwrap();
    let hyp = arena.bv_ult(x, three).unwrap();
    let under_hyp = prove(&mut arena, &[hyp], eq, &SolverConfig::default())
        .expect("solver should not hard-error");
    assert!(
        matches!(under_hyp, ProofOutcome::Proved(_)),
        "under x<3 the two must be equal, got {under_hyp:?}"
    );

    let defined_under_hyp = prove(
        &mut arena,
        &[hyp],
        from_llvm.defined,
        &SolverConfig::default(),
    )
    .expect("solver should not hard-error");
    assert!(
        matches!(defined_under_hyp, ProofOutcome::Proved(_)),
        "under x<3 the LLVM CFG must be defined, got {defined_under_hyp:?}"
    );

    let unconditional = prove(&mut arena, &[], from_llvm.defined, &SolverConfig::default())
        .expect("solver should not hard-error");
    assert!(
        matches!(unconditional, ProofOutcome::Disproved(_)),
        "without the range hypothesis LLVM definedness must be refuted, got {unconditional:?}"
    );
}

/// Deterministic differential fuzz over EVERY paired fixture: reflect both sides,
/// evaluate at pseudo-random inputs, and require bit-for-bit agreement. This is
/// the concrete-execution oracle (independent of the symbolic proofs above) —
/// the DISAGREE=0 discipline applied to the two front ends themselves.
#[test]
fn differential_fuzz_mir_vs_llvm_reflections() {
    let pairs: &[(&str, &str, &str, u32)] = &[
        ("masked", MASKED_MIR, MASKED_LL, 32),
        ("sel/select", SEL_MIR, SEL_LL, 32),
        ("sel/br+phi", SEL_MIR, SEL_BR_LL, 32),
        ("sar", SAR_MIR, SAR_LL, 32),
        ("scale", SCALE_MIR, SCALE_LL, 32),
        ("lut", LUT_MIR, LUT_LL, 8),
    ];
    for (name, mir, ll, width) in pairs {
        let _canonical = canonical_llvm(ll);
        let mut arena = TermArena::new();
        let x_sym = arena.declare("x", Sort::BitVec(*width)).unwrap();
        let x = arena.var(x_sym);
        let from_mir = reflect_mir_unary(&mut arena, x, mir);
        let from_llvm = reflect_unary_into(&mut arena, x, ll);
        // The reflection == reflection shape, via the shared oracle harness.
        DiffFuzz::new(vec![(x_sym, *width)], 10_000)
            .check_agree(&arena, from_mir, from_llvm)
            .assert_agreed(&format!("{name}: mir/llvm reflections"));
    }
}

// ---- `ext(x: u8) -> u32 = (x as u32) << 1` : Cast + independently-typed shift ----
// MIR keeps the `as` cast (`IntToInt`) and a shift whose amount is an `i32`
// literal (Rust's default); LLVM emits `zext` + a same-width `shl`.

const EXT_MIR: &str = r"
fn ext(_1: u8) -> u32 {
    debug x => _1;
    let mut _0: u32;
    let mut _2: u32;

    bb0: {
        _2 = copy _1 as u32 (IntToInt);
        _0 = Shl(move _2, const 1_i32);
        return;
    }
}
";

const EXT_LL: &str = r"
define noundef range(i32 0, 511) i32 @ext(i8 noundef %x) unnamed_addr {
start:
  %_2 = zext i8 %x to i32
  %_0 = shl nuw nsw i32 %_2, 1
  ret i32 %_0
}
";

// ---- `notx(x) = !x` : MIR `UnaryOp(Not)` ~ LLVM `xor %x, -1` ---------------------
// LLVM has no bitwise-not instruction; it canonicalizes to xor with all-ones,
// printed as a NEGATIVE constant — exercising signed-const parsing.

const NOTX_MIR: &str = r"
fn notx(_1: u32) -> u32 {
    debug x => _1;
    let mut _0: u32;

    bb0: {
        _0 = Not(copy _1);
        return;
    }
}
";

const NOTX_LL: &str = r"
define noundef i32 @notx(i32 noundef %x) unnamed_addr {
start:
  %_0 = xor i32 %x, -1
  ret i32 %_0
}
";

// ---- `negate(x: i32) = -x` (wrapping) : MIR `UnaryOp(Neg)` ~ LLVM `sub 0, %x` ----

const NEG_MIR: &str = r"
fn negate(_1: i32) -> i32 {
    debug x => _1;
    let mut _0: i32;

    bb0: {
        _0 = Neg(copy _1);
        return;
    }
}
";

const NEG_LL: &str = r"
define noundef i32 @negate(i32 noundef %x) unnamed_addr {
start:
  %_0 = sub i32 0, %x
  ret i32 %_0
}
";

// ---- `umin(a, b) = if a < b { a } else { b }` : TWO parameters -------------------
// MIR keeps the Lt-diamond; `-O` LLVM recognizes the idiom and emits the
// `@llvm.umin` intrinsic. Proving them equal exercises multi-parameter
// reflection on both sides AND validates the min-idiom recognition.

const UMIN_MIR: &str = r"
fn umin(_1: u32, _2: u32) -> u32 {
    debug a => _1;
    debug b => _2;
    let mut _0: u32;
    let mut _3: bool;

    bb0: {
        StorageLive(_3);
        _3 = Lt(copy _1, copy _2);
        switchInt(move _3) -> [0: bb2, otherwise: bb1];
    }

    bb1: {
        _0 = copy _1;
        goto -> bb3;
    }

    bb2: {
        _0 = copy _2;
        goto -> bb3;
    }

    bb3: {
        StorageDead(_3);
        return;
    }
}
";

const UMIN_LL: &str = r"
define noundef i32 @umin(i32 noundef %a, i32 noundef %b) unnamed_addr {
start:
  %r = tail call i32 @llvm.umin.i32(i32 %a, i32 %b)
  ret i32 %r
}
";

/// `ext`: MIR `as`-cast (`IntToInt`) + an `i32`-typed shift amount == LLVM
/// `zext`+`shl`, for all u8 — casts and Rust's independently-typed shift
/// literals land correctly in the one BV algebra.
#[test]
fn ext_cast_mir_equals_llvm() {
    assert_equivalent(8, EXT_MIR, EXT_LL, &[0, 1, 0x7f, 0x80, 0xff]);
}

/// `notx`: MIR `UnaryOp(Not)` == LLVM's canonical `xor %x, -1`, for all u32 —
/// bitwise-not across two spellings, incl. LLVM's signed-printed constant.
#[test]
fn notx_mir_equals_llvm() {
    assert_equivalent(
        32,
        NOTX_MIR,
        NOTX_LL,
        &[0, 1, 0xffff_ffff, 0xdead_beef, 0x8000_0000],
    );
}

/// `negate`: MIR `UnaryOp(Neg)` == LLVM `sub 0, %x`, for all i32 (wrapping
/// two's-complement negation, including `i32::MIN`).
#[test]
fn negate_mir_equals_llvm() {
    assert_equivalent(
        32,
        NEG_MIR,
        NEG_LL,
        &[0, 1, 0x7fff_ffff, 0x8000_0000, u128::from(u32::MAX)],
    );
}

/// `umin`, two parameters: MIR `Lt`-diamond over (_1, _2) == LLVM's recognized
/// `@llvm.umin` intrinsic, for all (u32, u32) — multi-parameter reflection on
/// both platforms over the same two symbols, and the min-idiom validated.
#[test]
fn umin_two_param_mir_equals_llvm() {
    let mut arena = TermArena::new();
    let a_sym = arena.declare("a", Sort::BitVec(32)).unwrap();
    let b_sym = arena.declare("b", Sort::BitVec(32)).unwrap();
    let a = arena.var(a_sym);
    let b = arena.var(b_sym);

    let from_mir = reflect_mir_into(&mut arena, &[a, b], UMIN_MIR);
    let from_llvm = reflect_into(&mut arena, &[a, b], UMIN_LL);

    let eq = arena.eq(from_mir, from_llvm).unwrap();
    let outcome =
        prove(&mut arena, &[], eq, &SolverConfig::default()).expect("solver should not hard-error");
    assert!(
        matches!(outcome, ProofOutcome::Proved(_)),
        "umin MIR and LLVM reflections must be provably equal for all (u32,u32), got {outcome:?}"
    );

    // Concrete cross-check at corner pairs (independent of the proof).
    for &(va, vb) in &[
        (0u128, 0u128),
        (0, 1),
        (1, 0),
        (7, 7),
        (u128::from(u32::MAX), 0),
        (0xdead_beef, 0xbeef_dead),
    ] {
        let mut asg = Assignment::new();
        asg.set(
            a_sym,
            Value::Bv {
                width: 32,
                value: va,
            },
        );
        asg.set(
            b_sym,
            Value::Bv {
                width: 32,
                value: vb,
            },
        );
        let m = match eval(&arena, from_mir, &asg).unwrap() {
            Value::Bv { value, .. } => value,
            other => panic!("mir eval not BV: {other:?}"),
        };
        let l = match eval(&arena, from_llvm, &asg).unwrap() {
            Value::Bv { value, .. } => value,
            other => panic!("llvm eval not BV: {other:?}"),
        };
        assert_eq!(m, l, "umin mir/llvm disagree at a={va}, b={vb}");
        assert_eq!(m, va.min(vb), "umin wrong value at a={va}, b={vb}");
    }
}

/// A negative control: `masked` MIR must **not** be equivalent to `lut` LLVM — the
/// equivalence prover is discriminating, not vacuously accepting. (Widths differ,
/// so compare each against a deliberately-wrong same-width partner instead.)
#[test]
fn distinct_functions_are_not_equivalent() {
    // masked vs a shifted-mask variant: (x & 0xff) | 0x100  vs  (x & 0xff) | 0x200.
    const MASKED2_LL: &str = r"
define i32 @masked2(i32 %x) {
start:
  %_2 = and i32 %x, 255
  %_0 = or i32 %_2, 512
  ret i32 %_0
}
";
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::BitVec(32)).unwrap();
    let x = arena.var(x_sym);
    let a = reflect_mir_unary(&mut arena, x, MASKED_MIR);
    let b = reflect_unary_into(&mut arena, x, MASKED2_LL);
    let eq = arena.eq(a, b).unwrap();
    let outcome =
        prove(&mut arena, &[], eq, &SolverConfig::default()).expect("solver should not hard-error");
    assert!(
        matches!(outcome, ProofOutcome::Disproved(_)),
        "masked (|0x100) and masked2 (|0x200) must be refuted as unequal, got {outcome:?}"
    );
}
