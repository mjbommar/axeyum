//! A **micro-module end-to-end**, both platforms: the Internet-checksum add
//! step (`sum16`: one's-complement 16-bit addition via a u32 widen + fold) and
//! the header-checksum finalizer (`cksum_pair = !sum16`). Two functions, two
//! parameters each, reflected from paired committed MIR and LLVM fixtures.
//!
//! What gets proved, per platform and across them:
//! - `sum16` and `cksum_pair`: MIR == LLVM for **all** `(u16, u16)` — the
//!   translation-validation baseline, now at module scale;
//! - **composition**: `cksum_pair == ¬sum16` — rustc's MIR inliner composed the
//!   two functions; the proof validates the inlined body against the pieces;
//! - the **receiver property**: `sum16(a,b) + cksum_pair(a,b) == 0xffff` for
//!   all inputs — the actual protocol-level reason the checksum verifies —
//!   proved over the *reflected compiled code*, not the source.
//!
//! This is the shape a network-stack verification takes: reflect the leaf
//! functions the compiler produced, prove the per-function contracts and the
//! protocol identities over them.

use axeyum_ir::{Assignment, Sort, SymbolId, TermArena, TermId, Value, eval};
use axeyum_solver::{ProofOutcome, SolverConfig, prove};

use axeyum_verify::reflect::llvm::{
    checked::{ReflectErrorKind, reflect_scalar_into_checked},
    loops::{
        LoopReflectErrorKind, ScalarCallContract, ScalarContractExpr, VerifiedContractResolver,
        reflect_scalar_into_checked_with_contracts,
    },
    reflect_into,
};
use axeyum_verify::reflect::mir::{
    checked::{
        MirScalarConfig, MirVerifiedContractResolver, ReflectErrorKind as MirReflectErrorKind,
        reflect_scalar_into_checked as reflect_mir_scalar_into_checked,
        reflect_scalar_into_checked_with_contracts as reflect_mir_scalar_with_contracts,
    },
    reflect_mir_into,
};
use axeyum_verify::reflect::oracle::DiffFuzz;

// ---- the real Rust module (concrete oracle) ---------------------------------------

#[allow(clippy::cast_possible_truncation)] // the fold keeps the sum within 16 bits
fn sum16(a: u16, b: u16) -> u16 {
    let s = u32::from(a) + u32::from(b);
    ((s & 0xffff) + (s >> 16)) as u16
}

fn cksum_pair(a: u16, b: u16) -> u16 {
    !sum16(a, b)
}

// ---- committed release-MIR fixtures ------------------------------------------------

const SUM16_MIR: &str = r"
fn sum16(_1: u16, _2: u16) -> u16 {
    debug a => _1;
    debug b => _2;
    let mut _0: u16;
    let mut _3: u32;
    let mut _4: u32;
    let mut _5: u32;
    let mut _6: u32;
    let mut _7: u32;

    bb0: {
        _3 = copy _1 as u32 (IntToInt);
        _4 = copy _2 as u32 (IntToInt);
        _5 = Add(move _3, move _4);
        _6 = BitAnd(copy _5, const 65535_u32);
        _7 = Shr(copy _5, const 16_i32);
        _5 = Add(move _6, move _7);
        _0 = copy _5 as u16 (IntToInt);
        return;
    }
}
";

/// Exact checked-MIR callee for ADR-0315's input-dependent panic experiment.
const CHECKED_INC_MIR: &str = r#"
fn checked_inc(_1: u8) -> u8 {
    let mut _0: u8;
    let mut _2: bool;

    bb0: {
        _2 = Lt(copy _1, const 255_u8);
        assert(move _2, "checked_inc overflow") -> [success: bb1, unwind continue];
    }

    bb1: {
        _0 = Add(copy _1, const 1_u8);
        return;
    }
}
"#;

/// One modular caller using only ADR-0299's assigned direct-call syntax.
const CHECKED_INC_CALL_MIR: &str = r"
fn call_checked_inc(_1: u8) -> u8 {
    let mut _0: u8;
    let mut _2: u8;

    bb0: {
        _2 = checked_inc(copy _1) -> [return: bb1, unwind continue];
    }

    bb1: {
        _0 = copy _2;
        return;
    }
}
";

/// Independent inlined specification for the same call and panic behavior.
const CHECKED_INC_INLINED_MIR: &str = r#"
fn call_checked_inc(_1: u8) -> u8 {
    let mut _0: u8;
    let mut _2: bool;

    bb0: {
        _2 = Lt(copy _1, const 255_u8);
        assert(move _2, "checked_inc overflow") -> [success: bb1, unwind continue];
    }

    bb1: {
        _0 = Add(copy _1, const 1_u8);
        return;
    }
}
"#;

/// `cksum_pair` after the MIR inliner: `sum16`'s body inlined, then `Not`.
const CKSUM_MIR: &str = r"
fn cksum_pair(_1: u16, _2: u16) -> u16 {
    debug a => _1;
    debug b => _2;
    let mut _0: u16;
    let mut _3: u32;
    let mut _4: u32;
    let mut _5: u32;
    let mut _6: u32;
    let mut _7: u32;
    let mut _8: u16;

    bb0: {
        _3 = copy _1 as u32 (IntToInt);
        _4 = copy _2 as u32 (IntToInt);
        _5 = Add(move _3, move _4);
        _6 = BitAnd(copy _5, const 65535_u32);
        _7 = Shr(copy _5, const 16_i32);
        _5 = Add(move _6, move _7);
        _8 = copy _5 as u16 (IntToInt);
        _0 = Not(move _8);
        return;
    }
}
";

/// `cksum_pair` before MIR inlining, with the registered unwind spelling.
const CKSUM_CALL_MIR: &str = r"
fn cksum_pair(_1: u16, _2: u16) -> u16 {
    debug a => _1;
    debug b => _2;
    let mut _0: u16;
    let mut _3: u16;

    bb0: {
        StorageLive(_3);
        _3 = sum16(move _1, move _2) -> [return: bb1, unwind continue];
    }

    bb1: {
        _0 = Not(move _3);
        StorageDead(_3);
        return;
    }
}
";

const PANICKING_SUM16_MIR: &str = r#"
fn sum16(_1: u16, _2: u16) -> u16 {
    let mut _0: u16;
    let mut _3: u32;
    let mut _4: u32;
    let mut _5: u32;
    let mut _6: u32;
    let mut _7: u32;
    let mut _8: bool;

    bb0: {
        _3 = copy _1 as u32 (IntToInt);
        _4 = copy _2 as u32 (IntToInt);
        _5 = Add(move _3, move _4);
        _6 = BitAnd(copy _5, const 65535_u32);
        _7 = Shr(copy _5, const 16_i32);
        _5 = Add(move _6, move _7);
        _0 = copy _5 as u16 (IntToInt);
        _8 = Eq(copy _1, const 0_u16);
        assert(move _8, "selected panic mutation") -> [success: bb1, unwind continue];
    }

    bb1: {
        return;
    }
}
"#;

// ---- committed release-LLVM fixtures -----------------------------------------------

const SUM16_LL: &str = r"
define noundef i16 @sum16(i16 noundef %a, i16 noundef %b) unnamed_addr {
start:
  %_3 = zext i16 %a to i32
  %_4 = zext i16 %b to i32
  %s = add nuw nsw i32 %_3, %_4
  %lo = and i32 %s, 65535
  %hi = lshr i32 %s, 16
  %f = add nuw nsw i32 %lo, %hi
  %_0 = trunc i32 %f to i16
  ret i16 %_0
}
";

const CKSUM_LL: &str = r"
define noundef i16 @cksum_pair(i16 noundef %a, i16 noundef %b) unnamed_addr {
start:
  %_3 = zext i16 %a to i32
  %_4 = zext i16 %b to i32
  %s = add nuw nsw i32 %_3, %_4
  %lo = and i32 %s, 65535
  %hi = lshr i32 %s, 16
  %f = add nuw nsw i32 %lo, %hi
  %t = trunc i32 %f to i16
  %_0 = xor i16 %t, -1
  ret i16 %_0
}
";

/// `cksum_pair` before inlining: the body under test for modular composition.
const CKSUM_CALL_LL: &str = r"
define noundef i16 @cksum_pair(i16 noundef %a, i16 noundef %b) unnamed_addr {
start:
  %sum = call i16 @sum16(i16 noundef %a, i16 noundef %b)
  %_0 = xor i16 %sum, -1
  ret i16 %_0
}
";

fn boxed(expression: ScalarContractExpr) -> Box<ScalarContractExpr> {
    Box::new(expression)
}

fn word(value: u128) -> ScalarContractExpr {
    ScalarContractExpr::BitVec { width: 16, value }
}

fn sum16_contract_value() -> ScalarContractExpr {
    let a = || ScalarContractExpr::Argument(0);
    let b = || ScalarContractExpr::Argument(1);
    let carry = ScalarContractExpr::Ite {
        condition: boxed(ScalarContractExpr::BvUnsignedAddOverflow(
            boxed(a()),
            boxed(b()),
        )),
        when_true: boxed(word(1)),
        when_false: boxed(word(0)),
    };
    ScalarContractExpr::BvAdd(
        boxed(ScalarContractExpr::BvAdd(boxed(a()), boxed(b()))),
        boxed(carry),
    )
}

fn sum16_relational_contract(ensures: ScalarContractExpr) -> ScalarCallContract {
    ScalarCallContract::new_relational(
        "sum16",
        vec![16, 16],
        16,
        ScalarContractExpr::Bool(true),
        ScalarContractExpr::Bool(true),
        ensures,
        ScalarContractExpr::Bool(true),
    )
    .unwrap()
}

fn exact_sum16_relational_contract() -> ScalarCallContract {
    sum16_relational_contract(ScalarContractExpr::Eq(
        boxed(ScalarContractExpr::Result),
        boxed(sum16_contract_value()),
    ))
}

fn checked_inc_contract(panic_value: u128) -> ScalarCallContract {
    let byte = |value| ScalarContractExpr::BitVec { width: 8, value };
    ScalarCallContract::new_relational_with_panic(
        "checked_inc",
        vec![8],
        8,
        ScalarContractExpr::Bool(true),
        ScalarContractExpr::Bool(true),
        ScalarContractExpr::Eq(
            boxed(ScalarContractExpr::Argument(0)),
            boxed(byte(panic_value)),
        ),
        ScalarContractExpr::Eq(
            boxed(ScalarContractExpr::Result),
            boxed(ScalarContractExpr::BvAdd(
                boxed(ScalarContractExpr::Argument(0)),
                boxed(byte(1)),
            )),
        ),
        ScalarContractExpr::Bool(true),
    )
    .unwrap()
}

fn relational_resolver(contract: ScalarCallContract) -> VerifiedContractResolver {
    VerifiedContractResolver::from_contracts(&[(contract, SUM16_LL)])
        .expect("sum16 relational contract must verify against its exact body")
}

fn mir_config(function: &str) -> MirScalarConfig {
    MirScalarConfig::new(function, 64)
}

fn mir_relational_resolver(contract: ScalarCallContract) -> MirVerifiedContractResolver {
    MirVerifiedContractResolver::from_contracts(&[(contract, SUM16_MIR)])
        .expect("sum16 relational contract must verify independently against checked MIR")
}

/// One arena with `(a, b)` symbols and all four reflections over them.
struct Module {
    arena: TermArena,
    a_sym: SymbolId,
    b_sym: SymbolId,
    sum_mir: TermId,
    sum_llvm: TermId,
    cksum_mir: TermId,
    cksum_llvm: TermId,
}

fn reflect_module() -> Module {
    let mut arena = TermArena::new();
    let a_sym = arena.declare("a", Sort::BitVec(16)).unwrap();
    let b_sym = arena.declare("b", Sort::BitVec(16)).unwrap();
    let a = arena.var(a_sym);
    let b = arena.var(b_sym);
    let sum_mir = reflect_mir_into(&mut arena, &[a, b], SUM16_MIR);
    let sum_llvm = reflect_into(&mut arena, &[a, b], SUM16_LL);
    let cksum_mir = reflect_mir_into(&mut arena, &[a, b], CKSUM_MIR);
    let cksum_llvm = reflect_into(&mut arena, &[a, b], CKSUM_LL);
    Module {
        arena,
        a_sym,
        b_sym,
        sum_mir,
        sum_llvm,
        cksum_mir,
        cksum_llvm,
    }
}

fn proved(arena: &mut TermArena, goal: TermId) -> bool {
    matches!(
        prove(arena, &[], goal, &SolverConfig::default()).expect("solver should not hard-error"),
        ProofOutcome::Proved(_)
    )
}

/// Per-function translation validation at module scale: both functions' MIR
/// and LLVM reflections are equal for ALL `(u16, u16)`.
#[test]
fn module_functions_mir_equal_llvm() {
    let mut m = reflect_module();
    let eq_sum = m.arena.eq(m.sum_mir, m.sum_llvm).unwrap();
    assert!(
        proved(&mut m.arena, eq_sum),
        "sum16: MIR and LLVM must be equal for all (u16,u16)"
    );
    let eq_cksum = m.arena.eq(m.cksum_mir, m.cksum_llvm).unwrap();
    assert!(
        proved(&mut m.arena, eq_cksum),
        "cksum_pair: MIR and LLVM must be equal for all (u16,u16)"
    );
}

/// Composition, validating the MIR inliner: the inlined `cksum_pair` is exactly
/// `¬sum16` — on both platforms.
#[test]
fn module_composition_cksum_is_not_sum() {
    let mut m = reflect_module();
    let not_sum_mir = m.arena.bv_not(m.sum_mir).unwrap();
    let goal_mir = m.arena.eq(m.cksum_mir, not_sum_mir).unwrap();
    assert!(
        proved(&mut m.arena, goal_mir),
        "MIR: cksum_pair must equal !sum16"
    );
    let not_sum_llvm = m.arena.bv_not(m.sum_llvm).unwrap();
    let goal_llvm = m.arena.eq(m.cksum_llvm, not_sum_llvm).unwrap();
    assert!(
        proved(&mut m.arena, goal_llvm),
        "LLVM: cksum_pair must equal !sum16"
    );
}

/// The protocol-level receiver property, on the reflected compiled code:
/// `sum16(a,b) + cksum_pair(a,b) == 0xffff` for ALL inputs — why a receiver
/// that re-sums a checksummed header gets all-ones. Proved on both platforms.
#[test]
fn module_receiver_property_sum_plus_cksum_is_all_ones() {
    let mut m = reflect_module();
    let all_ones = m.arena.bv_const(16, 0xffff).unwrap();
    let total_mir = m.arena.bv_add(m.sum_mir, m.cksum_mir).unwrap();
    let goal_mir = m.arena.eq(total_mir, all_ones).unwrap();
    assert!(
        proved(&mut m.arena, goal_mir),
        "MIR: sum16 + cksum_pair must be 0xffff for all inputs"
    );
    let total_llvm = m.arena.bv_add(m.sum_llvm, m.cksum_llvm).unwrap();
    let goal_llvm = m.arena.eq(total_llvm, all_ones).unwrap();
    assert!(
        proved(&mut m.arena, goal_llvm),
        "LLVM: sum16 + cksum_pair must be 0xffff for all inputs"
    );
}

/// Concrete oracle: all four reflections match the real Rust module on a
/// deterministic sample of input pairs (independent of the proofs).
#[test]
fn module_reflections_match_real_rust() {
    let m = reflect_module();
    // Both shapes for all four reflections, via the shared oracle harness: the
    // real Rust module is the oracle (inputs arrive as [a, b] in symbol order).
    let inputs = vec![(m.a_sym, 16), (m.b_sym, 16)];
    let fuzz = DiffFuzz::new(inputs, 2000);
    let ab = |vals: &[u128]| -> (u16, u16) {
        (
            u16::try_from(vals[0]).unwrap(),
            u16::try_from(vals[1]).unwrap(),
        )
    };
    for (term, name, oracle) in [
        (m.sum_mir, "sum_mir", true),
        (m.sum_llvm, "sum_llvm", true),
        (m.cksum_mir, "cksum_mir", false),
        (m.cksum_llvm, "cksum_llvm", false),
    ] {
        fuzz.check_against(&m.arena, term, |vals| {
            let (a, b) = ab(vals);
            let out = if oracle {
                sum16(a, b)
            } else {
                cksum_pair(a, b)
            };
            u128::from(out)
        })
        .assert_agreed(name);
    }
}

fn eval_bool(arena: &TermArena, term: TermId, assignment: &Assignment) -> bool {
    match eval(arena, term, assignment).unwrap() {
        Value::Bool(value) => value,
        other => panic!("expected Bool evaluation, got {other:?}"),
    }
}

fn eval_bv(arena: &TermArena, term: TermId, assignment: &Assignment) -> u128 {
    match eval(arena, term, assignment).unwrap() {
        Value::Bv { value, .. } => value,
        other => panic!("expected BV evaluation, got {other:?}"),
    }
}

fn low_u16(value: u64) -> u16 {
    let [a, b, _, _, _, _, _, _] = value.to_le_bytes();
    u16::from_le_bytes([a, b])
}

fn assert_proved(arena: &mut TermArena, hypotheses: &[TermId], goal: TermId, label: &str) {
    let outcome = prove(arena, hypotheses, goal, &SolverConfig::default())
        .unwrap_or_else(|error| panic!("{label}: solver hard-error: {error}"));
    assert!(
        matches!(outcome, ProofOutcome::Proved(_)),
        "{label}: expected proof, got {outcome:?}"
    );
}

fn independent_sum16_term(arena: &mut TermArena, a: TermId, b: TermId) -> TermId {
    let low = arena.bv_add(a, b).unwrap();
    let overflow = arena.bv_uaddo(a, b).unwrap();
    let one = arena.bv_const(16, 1).unwrap();
    let zero = arena.bv_const(16, 0).unwrap();
    let carry = arena.ite(overflow, one, zero).unwrap();
    arena.bv_add(low, carry).unwrap()
}

#[test]
fn relational_sum16_contract_reproves_checksum_module() {
    let mut default_arena = TermArena::new();
    let default_a = default_arena.declare("a", Sort::BitVec(16)).unwrap();
    let default_b = default_arena.declare("b", Sort::BitVec(16)).unwrap();
    let default_params = [default_arena.var(default_a), default_arena.var(default_b)];
    let default_error =
        reflect_scalar_into_checked(&mut default_arena, &default_params, CKSUM_CALL_LL)
            .unwrap_err();
    assert_eq!(default_error.kind(), ReflectErrorKind::UnsupportedCall);
    assert!(default_error.span().is_some());

    let resolver = relational_resolver(exact_sum16_relational_contract());
    assert_eq!(resolver.contract_names(), vec!["sum16"]);
    let mut arena = TermArena::new();
    let a_sym = arena.declare("a", Sort::BitVec(16)).unwrap();
    let b_sym = arena.declare("b", Sort::BitVec(16)).unwrap();
    let a = arena.var(a_sym);
    let b = arena.var(b_sym);
    let sum_mir = reflect_mir_into(&mut arena, &[a, b], SUM16_MIR);
    let sum_llvm = reflect_into(&mut arena, &[a, b], SUM16_LL);
    let cksum_mir = reflect_mir_into(&mut arena, &[a, b], CKSUM_MIR);
    let cksum_llvm = reflect_into(&mut arena, &[a, b], CKSUM_LL);
    let modular =
        reflect_scalar_into_checked_with_contracts(&mut arena, &[a, b], CKSUM_CALL_LL, &resolver)
            .unwrap();

    assert_eq!(modular.call_sites().len(), 1);
    let site = &modular.call_sites()[0];
    assert_eq!(site.callee(), "sum16");
    assert_eq!(arena.symbol(site.result_symbol()).1, Sort::BitVec(16));
    assert!(CKSUM_CALL_LL[site.span().start..site.span().end].contains("call i16 @sum16"));

    let defined = modular.result.defined;
    assert_proved(&mut arena, &[], defined, "modular checksum definedness");
    assert_proved(
        &mut arena,
        &[],
        site.requirement(),
        "literal-true checksum requirement",
    );

    let expected_sum = independent_sum16_term(&mut arena, a, b);
    let exact_sum = arena.eq(sum_llvm, expected_sum).unwrap();
    assert_proved(
        &mut arena,
        &[],
        exact_sum,
        "widened sum16 body equals independent low-word-plus-carry formula",
    );
    let result = arena.var(site.result_symbol());
    let expected_relation = arena.eq(result, expected_sum).unwrap();
    let relation_equivalent = arena.eq(modular.assumptions, expected_relation).unwrap();
    assert_proved(
        &mut arena,
        &[],
        relation_equivalent,
        "exposed relation equals independent checksum relation",
    );

    let modular_mir = arena.eq(modular.result.value, cksum_mir).unwrap();
    assert_proved(
        &mut arena,
        &[modular.assumptions],
        modular_mir,
        "modular LLVM equals inlined MIR",
    );
    let modular_llvm = arena.eq(modular.result.value, cksum_llvm).unwrap();
    assert_proved(
        &mut arena,
        &[modular.assumptions],
        modular_llvm,
        "modular LLVM equals inlined LLVM",
    );
    let all_ones = arena.bv_const(16, 0xffff).unwrap();
    let receiver_sum = arena.bv_add(sum_mir, modular.result.value).unwrap();
    let receiver = arena.eq(receiver_sum, all_ones).unwrap();
    assert_proved(
        &mut arena,
        &[modular.assumptions],
        receiver,
        "modular checksum receiver identity",
    );
}

#[allow(clippy::too_many_lines)] // one end-to-end proof over both checked IRs
#[test]
fn mir_relational_sum16_contract_reproves_checksum_module() {
    let mut default_arena = TermArena::new();
    let default_a = default_arena.declare("a", Sort::BitVec(16)).unwrap();
    let default_b = default_arena.declare("b", Sort::BitVec(16)).unwrap();
    let default_params = [default_arena.var(default_a), default_arena.var(default_b)];
    let default_error = reflect_mir_scalar_into_checked(
        &mut default_arena,
        &default_params,
        CKSUM_CALL_MIR,
        &mir_config("cksum_pair"),
    )
    .unwrap_err();
    assert_eq!(default_error.kind(), MirReflectErrorKind::UnsupportedCall);
    let default_span = default_error.span().expect("MIR call error span");
    assert!(CKSUM_CALL_MIR[default_span.start..default_span.end].contains("sum16"));

    let mir_resolver = mir_relational_resolver(exact_sum16_relational_contract());
    let llvm_resolver = relational_resolver(exact_sum16_relational_contract());
    assert_eq!(mir_resolver.contract_names(), vec!["sum16"]);

    let mut arena = TermArena::new();
    let a_sym = arena.declare("a", Sort::BitVec(16)).unwrap();
    let b_sym = arena.declare("b", Sort::BitVec(16)).unwrap();
    let a = arena.var(a_sym);
    let b = arena.var(b_sym);
    let params = [a, b];
    let checked_sum =
        reflect_mir_scalar_into_checked(&mut arena, &params, SUM16_MIR, &mir_config("sum16"))
            .unwrap();
    let checked_inlined =
        reflect_mir_scalar_into_checked(&mut arena, &params, CKSUM_MIR, &mir_config("cksum_pair"))
            .unwrap();
    let modular_mir = reflect_mir_scalar_with_contracts(
        &mut arena,
        &params,
        CKSUM_CALL_MIR,
        &mir_config("cksum_pair"),
        &mir_resolver,
    )
    .unwrap();
    let modular_llvm = reflect_scalar_into_checked_with_contracts(
        &mut arena,
        &params,
        CKSUM_CALL_LL,
        &llvm_resolver,
    )
    .unwrap();

    assert_eq!(modular_mir.call_sites().len(), 1);
    let site = &modular_mir.call_sites()[0];
    assert_eq!(site.callee(), "sum16");
    assert_eq!(arena.symbol(site.result_symbol()).1, Sort::BitVec(16));
    assert!(CKSUM_CALL_MIR[site.span().start..site.span().end].contains("sum16"));
    let mir_result = arena.var(site.result_symbol());
    let expected_sum = independent_sum16_term(&mut arena, a, b);
    let expected_relation = arena.eq(mir_result, expected_sum).unwrap();
    let exact_relation = arena
        .eq(modular_mir.assumptions, expected_relation)
        .unwrap();
    assert_proved(
        &mut arena,
        &[],
        exact_relation,
        "checked MIR call exposes the independent checksum relation",
    );

    let no_sum_panic = arena.not(checked_sum.panic).unwrap();
    let no_inlined_panic = arena.not(checked_inlined.panic).unwrap();
    let no_modular_panic = arena.not(modular_mir.panic).unwrap();
    for (goal, label) in [
        (no_sum_panic, "checked MIR sum16 panic freedom"),
        (
            no_inlined_panic,
            "checked MIR inlined checksum panic freedom",
        ),
        (
            no_modular_panic,
            "checked MIR modular checksum panic freedom",
        ),
    ] {
        assert_proved(&mut arena, &[], goal, label);
    }

    let mir_equals_inlined = arena
        .eq(modular_mir.result.value, checked_inlined.result.value)
        .unwrap();
    assert_proved(
        &mut arena,
        &[modular_mir.assumptions],
        mir_equals_inlined,
        "modular checked MIR equals inlined checked MIR",
    );
    let cross_ir = arena
        .eq(modular_mir.result.value, modular_llvm.result.value)
        .unwrap();
    assert_proved(
        &mut arena,
        &[modular_mir.assumptions, modular_llvm.assumptions],
        cross_ir,
        "independently verified MIR and LLVM modular callers agree",
    );
    let all_ones = arena.bv_const(16, 0xffff).unwrap();
    let receiver_sum = arena
        .bv_add(checked_sum.result.value, modular_mir.result.value)
        .unwrap();
    let receiver = arena.eq(receiver_sum, all_ones).unwrap();
    assert_proved(
        &mut arena,
        &[modular_mir.assumptions],
        receiver,
        "modular checked MIR receiver identity",
    );
}

#[test]
fn mir_panic_contract_matches_inlined_caller_and_exposes_callee_panic() {
    let resolver = MirVerifiedContractResolver::from_contracts(&[(
        checked_inc_contract(255),
        CHECKED_INC_MIR,
    )])
    .expect("checked_inc panic contract must verify exactly");
    let mut arena = TermArena::new();
    let input_symbol = arena.declare("input", Sort::BitVec(8)).unwrap();
    let input = arena.var(input_symbol);
    let modular = reflect_mir_scalar_with_contracts(
        &mut arena,
        &[input],
        CHECKED_INC_CALL_MIR,
        &mir_config("call_checked_inc"),
        &resolver,
    )
    .unwrap();
    let inlined = reflect_mir_scalar_into_checked(
        &mut arena,
        &[input],
        CHECKED_INC_INLINED_MIR,
        &mir_config("call_checked_inc"),
    )
    .unwrap();

    assert_eq!(modular.call_sites().len(), 1);
    let call = &modular.call_sites()[0];
    assert_eq!(call.callee(), "checked_inc");
    let panic_equal = arena.eq(modular.panic, inlined.panic).unwrap();
    assert_proved(
        &mut arena,
        &[],
        panic_equal,
        "modular and inlined MIR panic predicates",
    );
    let site_panic_equal = arena.eq(call.callee_panic(), inlined.panic).unwrap();
    assert_proved(
        &mut arena,
        &[],
        site_panic_equal,
        "call metadata exposes the exact callee panic predicate",
    );
    let result_equal = arena
        .eq(modular.result.value, inlined.result.value)
        .unwrap();
    let normal = arena.not(modular.panic).unwrap();
    assert_proved(
        &mut arena,
        &[modular.assumptions, normal],
        result_equal,
        "normal-return modular result equals the inlined result",
    );
}

#[test]
fn mir_panic_contract_exhaustively_replays_complete_u8_domain() {
    let resolver = MirVerifiedContractResolver::from_contracts(&[(
        checked_inc_contract(255),
        CHECKED_INC_MIR,
    )])
    .unwrap();
    let mut arena = TermArena::new();
    let input_symbol = arena.declare("input", Sort::BitVec(8)).unwrap();
    let input = arena.var(input_symbol);
    let modular = reflect_mir_scalar_with_contracts(
        &mut arena,
        &[input],
        CHECKED_INC_CALL_MIR,
        &mir_config("call_checked_inc"),
        &resolver,
    )
    .unwrap();
    let call = &modular.call_sites()[0];
    let mut normal_rows = 0_u32;
    let mut panic_rows = 0_u32;

    for value in 0_u128..=255 {
        let expected_panic = value == 255;
        let expected_result = (value + 1) & 0xff;
        let mut assignment = Assignment::new();
        assignment.set(input_symbol, Value::Bv { width: 8, value });
        assignment.set(
            call.result_symbol(),
            Value::Bv {
                width: 8,
                value: expected_result,
            },
        );
        assert_eq!(
            eval_bool(&arena, modular.panic, &assignment),
            expected_panic,
            "caller panic at input {value}"
        );
        assert_eq!(
            eval_bool(&arena, call.callee_panic(), &assignment),
            expected_panic,
            "callee panic metadata at input {value}"
        );
        assert!(
            eval_bool(&arena, modular.assumptions, &assignment),
            "guarded relation at input {value}"
        );
        if expected_panic {
            panic_rows += 1;
        } else {
            normal_rows += 1;
            assert_eq!(
                eval_bv(&arena, modular.result.value, &assignment),
                expected_result,
                "normal result at input {value}"
            );
        }
    }
    assert_eq!((normal_rows, panic_rows), (255, 1));

    // A panicking execution has no normal destination value. The exposed
    // relation remains true for an arbitrary result, while the unguarded
    // postcondition has real teeth and rejects it.
    let mut panic_assignment = Assignment::new();
    panic_assignment.set(
        input_symbol,
        Value::Bv {
            width: 8,
            value: 255,
        },
    );
    panic_assignment.set(call.result_symbol(), Value::Bv { width: 8, value: 1 });
    assert!(eval_bool(&arena, modular.assumptions, &panic_assignment));
    let one = arena.bv_const(8, 1).unwrap();
    let expected = arena.bv_add(input, one).unwrap();
    let result = arena.var(call.result_symbol());
    let unguarded = arena.eq(result, expected).unwrap();
    assert!(!eval_bool(&arena, unguarded, &panic_assignment));
}

#[test]
fn mir_panic_contract_mutations_and_invalid_boundaries_fail_closed() {
    let wrong_body = CHECKED_INC_MIR.replace("const 255_u8", "const 254_u8");
    let error = MirVerifiedContractResolver::from_contracts(&[(
        checked_inc_contract(255),
        wrong_body.as_str(),
    )])
    .unwrap_err();
    assert_eq!(error.kind(), MirReflectErrorKind::ContractDisproved);

    let error = MirVerifiedContractResolver::from_contracts(&[(
        checked_inc_contract(254),
        CHECKED_INC_MIR,
    )])
    .unwrap_err();
    assert_eq!(error.kind(), MirReflectErrorKind::ContractDisproved);

    let total_contract = ScalarCallContract::new_relational(
        "checked_inc",
        vec![8],
        8,
        ScalarContractExpr::Bool(true),
        ScalarContractExpr::Bool(true),
        ScalarContractExpr::Eq(
            boxed(ScalarContractExpr::Result),
            boxed(ScalarContractExpr::BvAdd(
                boxed(ScalarContractExpr::Argument(0)),
                boxed(ScalarContractExpr::BitVec { width: 8, value: 1 }),
            )),
        ),
        ScalarContractExpr::Bool(true),
    )
    .unwrap();
    let error = MirVerifiedContractResolver::from_contracts(&[(total_contract, CHECKED_INC_MIR)])
        .unwrap_err();
    assert_eq!(error.kind(), MirReflectErrorKind::ContractDisproved);

    let ill_sorted = ScalarCallContract::new_relational_with_panic(
        "checked_inc",
        vec![8],
        8,
        ScalarContractExpr::Bool(true),
        ScalarContractExpr::Bool(true),
        ScalarContractExpr::Argument(0),
        ScalarContractExpr::Bool(true),
        ScalarContractExpr::Bool(true),
    )
    .unwrap();
    let error =
        MirVerifiedContractResolver::from_contracts(&[(ill_sorted, CHECKED_INC_MIR)]).unwrap_err();
    assert_eq!(error.kind(), MirReflectErrorKind::InvalidContract);

    let result_in_panic = ScalarCallContract::new_relational_with_panic(
        "checked_inc",
        vec![8],
        8,
        ScalarContractExpr::Bool(true),
        ScalarContractExpr::Bool(true),
        ScalarContractExpr::Eq(
            boxed(ScalarContractExpr::Result),
            boxed(ScalarContractExpr::Argument(0)),
        ),
        ScalarContractExpr::Bool(true),
        ScalarContractExpr::Bool(true),
    )
    .unwrap_err();
    assert_eq!(
        result_in_panic.kind(),
        LoopReflectErrorKind::InvalidContract
    );

    let limited = SolverConfig::default().with_node_budget(0);
    let error = MirVerifiedContractResolver::from_contracts_with_config(
        &[(checked_inc_contract(255), CHECKED_INC_MIR)],
        &limited,
    )
    .unwrap_err();
    assert_eq!(error.kind(), MirReflectErrorKind::ContractUnknown);
}

#[test]
fn relational_checksum_havoc_gate_classifies_100000_rows() {
    let resolver = relational_resolver(exact_sum16_relational_contract());
    let mut arena = TermArena::new();
    let a_sym = arena.declare("a", Sort::BitVec(16)).unwrap();
    let b_sym = arena.declare("b", Sort::BitVec(16)).unwrap();
    let a = arena.var(a_sym);
    let b = arena.var(b_sym);
    let sum_mir = reflect_mir_into(&mut arena, &[a, b], SUM16_MIR);
    let sum_llvm = reflect_into(&mut arena, &[a, b], SUM16_LL);
    let cksum_mir = reflect_mir_into(&mut arena, &[a, b], CKSUM_MIR);
    let cksum_llvm = reflect_into(&mut arena, &[a, b], CKSUM_LL);
    let modular =
        reflect_scalar_into_checked_with_contracts(&mut arena, &[a, b], CKSUM_CALL_LL, &resolver)
            .unwrap();
    let result_sym = modular.call_sites()[0].result_symbol();

    let mut state = 0x8f13_68b7_2c95_4a61_u64;
    let mut valid = 0_usize;
    let mut relation_violations = 0_usize;
    let mut carry = 0_usize;
    let mut no_carry = 0_usize;
    for index in 0..100_000_usize {
        let (a_value, b_value) = match index {
            0 => (0_u16, 0_u16),
            1 => (u16::MAX, 0),
            2 => (u16::MAX, 1),
            3 => (u16::MAX, u16::MAX),
            _ => {
                state = state
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1_442_695_040_888_963_407);
                let a = low_u16(state);
                state = state
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1_442_695_040_888_963_407);
                (a, low_u16(state))
            }
        };
        if u32::from(a_value) + u32::from(b_value) > u32::from(u16::MAX) {
            carry += 1;
        } else {
            no_carry += 1;
        }
        let sum = sum16(a_value, b_value);
        let checksum = cksum_pair(a_value, b_value);
        let mut assignment = Assignment::new();
        assignment.set(
            a_sym,
            Value::Bv {
                width: 16,
                value: u128::from(a_value),
            },
        );
        assignment.set(
            b_sym,
            Value::Bv {
                width: 16,
                value: u128::from(b_value),
            },
        );
        assignment.set(
            result_sym,
            Value::Bv {
                width: 16,
                value: u128::from(sum),
            },
        );
        assert!(eval_bool(&arena, modular.assumptions, &assignment));
        assert!(eval_bool(&arena, modular.result.defined, &assignment));
        assert_eq!(eval_bv(&arena, sum_mir, &assignment), u128::from(sum));
        assert_eq!(eval_bv(&arena, sum_llvm, &assignment), u128::from(sum));
        assert_eq!(
            eval_bv(&arena, modular.result.value, &assignment),
            u128::from(checksum)
        );
        assert_eq!(
            eval_bv(&arena, cksum_mir, &assignment),
            u128::from(checksum)
        );
        assert_eq!(
            eval_bv(&arena, cksum_llvm, &assignment),
            u128::from(checksum)
        );
        valid += 1;

        assignment.set(
            result_sym,
            Value::Bv {
                width: 16,
                value: u128::from(sum ^ 1),
            },
        );
        assert!(!eval_bool(&arena, modular.assumptions, &assignment));
        assert!(eval_bool(&arena, modular.result.defined, &assignment));
        relation_violations += 1;
    }
    assert_eq!(valid, 100_000);
    assert_eq!(relation_violations, 100_000);
    assert_eq!(valid + relation_violations, 200_000);
    assert!(carry > 0 && no_carry > 0);
}

#[allow(clippy::too_many_lines)] // one flat, auditable 200k-row classification gate
#[test]
fn mir_relational_checksum_havoc_gate_classifies_100000_rows() {
    let resolver = mir_relational_resolver(exact_sum16_relational_contract());
    let mut arena = TermArena::new();
    let a_sym = arena.declare("a", Sort::BitVec(16)).unwrap();
    let b_sym = arena.declare("b", Sort::BitVec(16)).unwrap();
    let a = arena.var(a_sym);
    let b = arena.var(b_sym);
    let params = [a, b];
    let sum_mir =
        reflect_mir_scalar_into_checked(&mut arena, &params, SUM16_MIR, &mir_config("sum16"))
            .unwrap();
    let cksum_mir =
        reflect_mir_scalar_into_checked(&mut arena, &params, CKSUM_MIR, &mir_config("cksum_pair"))
            .unwrap();
    let sum_llvm = reflect_into(&mut arena, &params, SUM16_LL);
    let cksum_llvm = reflect_into(&mut arena, &params, CKSUM_LL);
    let modular = reflect_mir_scalar_with_contracts(
        &mut arena,
        &params,
        CKSUM_CALL_MIR,
        &mir_config("cksum_pair"),
        &resolver,
    )
    .unwrap();
    let result_sym = modular.call_sites()[0].result_symbol();

    let mut state = 0x19f6_ea73_d24c_850b_u64;
    let mut valid = 0_usize;
    let mut relation_violations = 0_usize;
    let mut carry = 0_usize;
    let mut no_carry = 0_usize;
    for index in 0..100_000_usize {
        let (a_value, b_value) = match index {
            0 => (0_u16, 0_u16),
            1 => (u16::MAX, 0),
            2 => (u16::MAX, 1),
            3 => (u16::MAX, u16::MAX),
            _ => {
                state = state
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1_442_695_040_888_963_407);
                let a = low_u16(state);
                state = state
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1_442_695_040_888_963_407);
                (a, low_u16(state))
            }
        };
        if u32::from(a_value) + u32::from(b_value) > u32::from(u16::MAX) {
            carry += 1;
        } else {
            no_carry += 1;
        }
        let sum = sum16(a_value, b_value);
        let checksum = cksum_pair(a_value, b_value);
        let mut assignment = Assignment::new();
        assignment.set(
            a_sym,
            Value::Bv {
                width: 16,
                value: u128::from(a_value),
            },
        );
        assignment.set(
            b_sym,
            Value::Bv {
                width: 16,
                value: u128::from(b_value),
            },
        );
        assignment.set(
            result_sym,
            Value::Bv {
                width: 16,
                value: u128::from(sum),
            },
        );
        assert!(eval_bool(&arena, modular.assumptions, &assignment));
        assert!(!eval_bool(&arena, modular.panic, &assignment));
        assert!(!eval_bool(&arena, sum_mir.panic, &assignment));
        assert!(!eval_bool(&arena, cksum_mir.panic, &assignment));
        assert_eq!(
            eval_bv(&arena, sum_mir.result.value, &assignment),
            u128::from(sum)
        );
        assert_eq!(eval_bv(&arena, sum_llvm, &assignment), u128::from(sum));
        assert_eq!(
            eval_bv(&arena, modular.result.value, &assignment),
            u128::from(checksum)
        );
        assert_eq!(
            eval_bv(&arena, cksum_mir.result.value, &assignment),
            u128::from(checksum)
        );
        assert_eq!(
            eval_bv(&arena, cksum_llvm, &assignment),
            u128::from(checksum)
        );
        valid += 1;

        assignment.set(
            result_sym,
            Value::Bv {
                width: 16,
                value: u128::from(sum ^ 1),
            },
        );
        assert!(!eval_bool(&arena, modular.assumptions, &assignment));
        assert!(!eval_bool(&arena, modular.panic, &assignment));
        relation_violations += 1;
    }
    assert_eq!(valid, 100_000);
    assert_eq!(relation_violations, 100_000);
    assert_eq!(valid + relation_violations, 200_000);
    assert!(carry > 0 && no_carry > 0);
}

#[test]
fn weak_relational_contract_exposes_real_havoc_countermodel() {
    let resolver = relational_resolver(sum16_relational_contract(ScalarContractExpr::Bool(true)));
    let mut arena = TermArena::new();
    let a_sym = arena.declare("a", Sort::BitVec(16)).unwrap();
    let b_sym = arena.declare("b", Sort::BitVec(16)).unwrap();
    let a = arena.var(a_sym);
    let b = arena.var(b_sym);
    let inlined = reflect_into(&mut arena, &[a, b], CKSUM_LL);
    let modular =
        reflect_scalar_into_checked_with_contracts(&mut arena, &[a, b], CKSUM_CALL_LL, &resolver)
            .unwrap();
    let relation = modular.assumptions;
    assert_proved(&mut arena, &[], relation, "weak relation is tautological");
    let equality = arena.eq(modular.result.value, inlined).unwrap();
    let outcome = prove(
        &mut arena,
        &[modular.assumptions],
        equality,
        &SolverConfig::default(),
    )
    .unwrap();
    let ProofOutcome::Disproved(model) = outcome else {
        panic!("weak postcondition must expose arbitrary-result countermodel, got {outcome:?}");
    };
    let result_sym = modular.call_sites()[0].result_symbol();
    let a_value = model.get(a_sym).expect("countermodel a");
    let b_value = model.get(b_sym).expect("countermodel b");
    let result_value = model.get(result_sym).expect("countermodel havoc result");
    let mut assignment = Assignment::new();
    assignment.set(a_sym, a_value);
    assignment.set(b_sym, b_value);
    assignment.set(result_sym, result_value);
    assert!(eval_bool(&arena, modular.assumptions, &assignment));
    assert!(eval_bool(&arena, modular.result.defined, &assignment));
    assert_ne!(
        eval_bv(&arena, modular.result.value, &assignment),
        eval_bv(&arena, inlined, &assignment),
        "replayed weak-contract model must distinguish havoc from the exact body"
    );
}

#[test]
fn mir_weak_relational_contract_exposes_real_havoc_countermodel() {
    let resolver =
        mir_relational_resolver(sum16_relational_contract(ScalarContractExpr::Bool(true)));
    let mut arena = TermArena::new();
    let a_sym = arena.declare("a", Sort::BitVec(16)).unwrap();
    let b_sym = arena.declare("b", Sort::BitVec(16)).unwrap();
    let params = [arena.var(a_sym), arena.var(b_sym)];
    let inlined =
        reflect_mir_scalar_into_checked(&mut arena, &params, CKSUM_MIR, &mir_config("cksum_pair"))
            .unwrap();
    let modular = reflect_mir_scalar_with_contracts(
        &mut arena,
        &params,
        CKSUM_CALL_MIR,
        &mir_config("cksum_pair"),
        &resolver,
    )
    .unwrap();
    assert_proved(
        &mut arena,
        &[],
        modular.assumptions,
        "weak checked MIR relation is tautological",
    );
    let equality = arena
        .eq(modular.result.value, inlined.result.value)
        .unwrap();
    let outcome = prove(
        &mut arena,
        &[modular.assumptions],
        equality,
        &SolverConfig::default(),
    )
    .unwrap();
    let ProofOutcome::Disproved(model) = outcome else {
        panic!("weak MIR postcondition must expose arbitrary-result countermodel, got {outcome:?}");
    };
    let result_sym = modular.call_sites()[0].result_symbol();
    let mut assignment = Assignment::new();
    assignment.set(a_sym, model.get(a_sym).expect("countermodel a"));
    assignment.set(b_sym, model.get(b_sym).expect("countermodel b"));
    assignment.set(
        result_sym,
        model
            .get(result_sym)
            .expect("countermodel MIR havoc result"),
    );
    assert!(eval_bool(&arena, modular.assumptions, &assignment));
    assert!(!eval_bool(&arena, modular.panic, &assignment));
    assert_ne!(
        eval_bv(&arena, modular.result.value, &assignment),
        eval_bv(&arena, inlined.result.value, &assignment),
        "replayed weak MIR model must distinguish havoc from the exact body"
    );
}

#[test]
fn relational_contract_expression_and_body_mutations_fail_closed() {
    let off_by_one = ScalarContractExpr::Eq(
        boxed(ScalarContractExpr::Result),
        boxed(ScalarContractExpr::BvAdd(
            boxed(sum16_contract_value()),
            boxed(word(1)),
        )),
    );
    let error = VerifiedContractResolver::from_contracts(&[(
        sum16_relational_contract(off_by_one),
        SUM16_LL,
    )])
    .unwrap_err();
    assert_eq!(error.kind(), LoopReflectErrorKind::ContractDisproved);

    let mutated_body = SUM16_LL.replace("%f = add nuw nsw i32 %lo, %hi", "%f = sub i32 %lo, %hi");
    let error = VerifiedContractResolver::from_contracts(&[(
        exact_sum16_relational_contract(),
        mutated_body.as_str(),
    )])
    .unwrap_err();
    assert_eq!(error.kind(), LoopReflectErrorKind::ContractDisproved);

    for forbidden in [
        ScalarCallContract::new(
            "sum16",
            vec![16, 16],
            16,
            ScalarContractExpr::Result,
            ScalarContractExpr::Bool(true),
            word(0),
            ScalarContractExpr::Bool(true),
        ),
        ScalarCallContract::new(
            "sum16",
            vec![16, 16],
            16,
            ScalarContractExpr::Bool(true),
            ScalarContractExpr::Result,
            word(0),
            ScalarContractExpr::Bool(true),
        ),
        ScalarCallContract::new(
            "sum16",
            vec![16, 16],
            16,
            ScalarContractExpr::Bool(true),
            ScalarContractExpr::Bool(true),
            ScalarContractExpr::Result,
            ScalarContractExpr::Bool(true),
        ),
        ScalarCallContract::new(
            "sum16",
            vec![16, 16],
            16,
            ScalarContractExpr::Bool(true),
            ScalarContractExpr::Bool(true),
            word(0),
            ScalarContractExpr::Result,
        ),
    ] {
        assert_eq!(
            forbidden.unwrap_err().kind(),
            LoopReflectErrorKind::InvalidContract
        );
    }

    let non_boolean_ensures = sum16_relational_contract(ScalarContractExpr::Result);
    let error =
        VerifiedContractResolver::from_contracts(&[(non_boolean_ensures, SUM16_LL)]).unwrap_err();
    assert_eq!(error.kind(), LoopReflectErrorKind::InvalidContract);
    let ill_sorted_eq = sum16_relational_contract(ScalarContractExpr::Eq(
        boxed(ScalarContractExpr::Result),
        boxed(ScalarContractExpr::Bool(true)),
    ));
    let error = VerifiedContractResolver::from_contracts(&[(ill_sorted_eq, SUM16_LL)]).unwrap_err();
    assert_eq!(error.kind(), LoopReflectErrorKind::InvalidContract);
    let ill_sorted_ite = sum16_relational_contract(ScalarContractExpr::Eq(
        boxed(ScalarContractExpr::Result),
        boxed(ScalarContractExpr::Ite {
            condition: boxed(word(0)),
            when_true: boxed(word(1)),
            when_false: boxed(word(0)),
        }),
    ));
    let error =
        VerifiedContractResolver::from_contracts(&[(ill_sorted_ite, SUM16_LL)]).unwrap_err();
    assert_eq!(error.kind(), LoopReflectErrorKind::InvalidContract);
}

#[test]
fn mir_relational_contract_body_panic_and_totality_mutations_fail_closed() {
    let off_by_one = ScalarContractExpr::Eq(
        boxed(ScalarContractExpr::Result),
        boxed(ScalarContractExpr::BvAdd(
            boxed(sum16_contract_value()),
            boxed(word(1)),
        )),
    );
    let error = MirVerifiedContractResolver::from_contracts(&[(
        sum16_relational_contract(off_by_one),
        SUM16_MIR,
    )])
    .unwrap_err();
    assert_eq!(
        error.kind(),
        MirReflectErrorKind::ContractDisproved,
        "{error}"
    );

    let shifted_body = SUM16_MIR.replace("const 16_i32", "const 15_i32");
    let error = MirVerifiedContractResolver::from_contracts(&[(
        exact_sum16_relational_contract(),
        shifted_body.as_str(),
    )])
    .unwrap_err();
    assert_eq!(error.kind(), MirReflectErrorKind::ContractDisproved);

    let error = MirVerifiedContractResolver::from_contracts(&[(
        exact_sum16_relational_contract(),
        PANICKING_SUM16_MIR,
    )])
    .unwrap_err();
    assert_eq!(
        error.kind(),
        MirReflectErrorKind::ContractDisproved,
        "{error}"
    );

    let signed_shift = SUM16_MIR.replace("let mut _5: u32;", "let mut _5: i32;");
    let error = MirVerifiedContractResolver::from_contracts(&[(
        exact_sum16_relational_contract(),
        signed_shift.as_str(),
    )])
    .unwrap_err();
    assert!(matches!(
        error.kind(),
        MirReflectErrorKind::TypeMismatch | MirReflectErrorKind::ContractDisproved
    ));

    let exact = ScalarCallContract::new(
        "sum16",
        vec![16, 16],
        16,
        ScalarContractExpr::Bool(true),
        ScalarContractExpr::Bool(true),
        sum16_contract_value(),
        ScalarContractExpr::Bool(true),
    )
    .unwrap();
    let error = MirVerifiedContractResolver::from_contracts(&[(exact, SUM16_MIR)]).unwrap_err();
    assert_eq!(error.kind(), MirReflectErrorKind::InvalidContract);

    let non_total = ScalarCallContract::new_relational(
        "sum16",
        vec![16, 16],
        16,
        ScalarContractExpr::Bool(false),
        ScalarContractExpr::Bool(true),
        ScalarContractExpr::Bool(true),
        ScalarContractExpr::Bool(true),
    )
    .unwrap();
    let error = MirVerifiedContractResolver::from_contracts(&[(non_total, SUM16_MIR)]).unwrap_err();
    assert_eq!(error.kind(), MirReflectErrorKind::InvalidContract);
}

#[test]
fn relational_contract_resolver_and_call_boundaries_fail_closed() {
    let duplicate = VerifiedContractResolver::from_contracts(&[
        (exact_sum16_relational_contract(), SUM16_LL),
        (exact_sum16_relational_contract(), SUM16_LL),
    ])
    .unwrap_err();
    assert_eq!(duplicate.kind(), LoopReflectErrorKind::InvalidContract);
    let limited = SolverConfig::default().with_node_budget(0);
    let unknown = VerifiedContractResolver::from_contracts_with_config(
        &[(exact_sum16_relational_contract(), SUM16_LL)],
        &limited,
    )
    .unwrap_err();
    assert_eq!(unknown.kind(), LoopReflectErrorKind::ContractUnknown);

    let empty = VerifiedContractResolver::from_contracts(&[]).unwrap();
    let mut arena = TermArena::new();
    let a_sym = arena.declare("a", Sort::BitVec(16)).unwrap();
    let b_sym = arena.declare("b", Sort::BitVec(16)).unwrap();
    let params = [arena.var(a_sym), arena.var(b_sym)];
    let error =
        reflect_scalar_into_checked_with_contracts(&mut arena, &params, CKSUM_CALL_LL, &empty)
            .unwrap_err();
    assert_eq!(error.kind(), LoopReflectErrorKind::UnsupportedCall);
    assert!(error.span().is_some());

    let resolver = relational_resolver(exact_sum16_relational_contract());
    for mutation in [
        CKSUM_CALL_LL.replace(
            "@sum16(i16 noundef %a, i16 noundef %b)",
            "@sum16(i16 noundef %a, i8 noundef %b)",
        ),
        CKSUM_CALL_LL.replace(
            "@sum16(i16 noundef %a, i16 noundef %b)",
            "@sum16(i16 %a, i16 noundef %b)",
        ),
        CKSUM_CALL_LL.replace("call i16 @sum16", "call i8 @sum16"),
    ] {
        let error =
            reflect_scalar_into_checked_with_contracts(&mut arena, &params, &mutation, &resolver)
                .unwrap_err();
        assert_eq!(error.kind(), LoopReflectErrorKind::UnsupportedCall);
        assert!(error.span().is_some());
    }
}

#[test]
fn mir_contract_resolver_and_call_boundaries_fail_closed() {
    let duplicate = MirVerifiedContractResolver::from_contracts(&[
        (exact_sum16_relational_contract(), SUM16_MIR),
        (exact_sum16_relational_contract(), SUM16_MIR),
    ])
    .unwrap_err();
    assert_eq!(duplicate.kind(), MirReflectErrorKind::InvalidContract);

    let limited = SolverConfig::default().with_node_budget(0);
    let unknown = MirVerifiedContractResolver::from_contracts_with_config(
        &[(exact_sum16_relational_contract(), SUM16_MIR)],
        &limited,
    )
    .unwrap_err();
    assert_eq!(unknown.kind(), MirReflectErrorKind::ContractUnknown);

    let empty = MirVerifiedContractResolver::from_contracts(&[]).unwrap();
    let mut arena = TermArena::new();
    let a_sym = arena.declare("a", Sort::BitVec(16)).unwrap();
    let b_sym = arena.declare("b", Sort::BitVec(16)).unwrap();
    let params = [arena.var(a_sym), arena.var(b_sym)];
    let error = reflect_mir_scalar_with_contracts(
        &mut arena,
        &params,
        CKSUM_CALL_MIR,
        &mir_config("cksum_pair"),
        &empty,
    )
    .unwrap_err();
    assert_eq!(error.kind(), MirReflectErrorKind::UnsupportedCall);
    assert!(error.span().is_some());

    let resolver = mir_relational_resolver(exact_sum16_relational_contract());
    let multiple_calls = CKSUM_CALL_MIR.replace(
        "    bb1: {\n        _0 = Not(move _3);",
        "    bb1: {\n        _3 = sum16(copy _1, copy _2) -> [return: bb2, unwind continue];\n    }\n\n    bb2: {\n        _0 = Not(move _3);",
    );
    for (mutation, expected) in [
        (
            CKSUM_CALL_MIR.replace("sum16(move", "sum17(move"),
            MirReflectErrorKind::UnsupportedCall,
        ),
        (
            CKSUM_CALL_MIR.replace("move _2) ->", "const 0_i16) ->"),
            MirReflectErrorKind::UnsupportedCall,
        ),
        (
            CKSUM_CALL_MIR.replace("let mut _3: u16;", "let mut _3: i16;"),
            MirReflectErrorKind::UnsupportedCall,
        ),
        (
            CKSUM_CALL_MIR.replace("return: bb1", "return: bb9"),
            MirReflectErrorKind::UndefinedBlock,
        ),
        (
            CKSUM_CALL_MIR.replace("unwind continue", "unwind unreachable"),
            MirReflectErrorKind::Syntax,
        ),
        (multiple_calls, MirReflectErrorKind::UnsupportedCall),
        (
            CKSUM_CALL_MIR.replace("return: bb1", "return: bb0"),
            MirReflectErrorKind::CyclicControlFlow,
        ),
    ] {
        let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            reflect_mir_scalar_with_contracts(
                &mut arena,
                &params,
                &mutation,
                &mir_config("cksum_pair"),
                &resolver,
            )
        }));
        let error = caught
            .expect("malformed checked MIR must never panic")
            .unwrap_err();
        assert_eq!(error.kind(), expected, "mutation:\n{mutation}");
        assert!(error.span().is_some());
    }
}

#[test]
fn relational_result_symbols_are_deterministic_isolated_and_fresh() {
    let resolver = relational_resolver(exact_sum16_relational_contract());
    let reflect_once = |arena: &mut TermArena| {
        let a_sym = arena.declare("a", Sort::BitVec(16)).unwrap();
        let b_sym = arena.declare("b", Sort::BitVec(16)).unwrap();
        let params = [arena.var(a_sym), arena.var(b_sym)];
        reflect_scalar_into_checked_with_contracts(arena, &params, CKSUM_CALL_LL, &resolver)
            .unwrap()
    };

    let mut first_arena = TermArena::new();
    let first = reflect_once(&mut first_arena);
    let first_symbol = first.call_sites()[0].result_symbol();
    let first_name = first_arena.symbol(first_symbol).0.to_owned();
    let second = reflect_once(&mut first_arena);
    let second_symbol = second.call_sites()[0].result_symbol();
    let second_name = first_arena.symbol(second_symbol).0.to_owned();
    assert_ne!(first_symbol, second_symbol);
    assert_eq!(second_name, format!("{first_name}.1"));

    let mut fresh_arena = TermArena::new();
    let fresh = reflect_once(&mut fresh_arena);
    let fresh_name = fresh_arena.symbol(fresh.call_sites()[0].result_symbol()).0;
    assert_eq!(fresh_name, first_name);

    let mut collision_arena = TermArena::new();
    let user_symbol = collision_arena
        .declare(&first_name, Sort::BitVec(16))
        .unwrap();
    let collision = reflect_once(&mut collision_arena);
    let internal_symbol = collision.call_sites()[0].result_symbol();
    assert_ne!(user_symbol, internal_symbol);
    assert_eq!(collision_arena.symbol(user_symbol).0, first_name);
    assert_eq!(collision_arena.symbol(internal_symbol).0, first_name);
    assert_eq!(collision_arena.find_symbol(&first_name), Some(user_symbol));
    assert_eq!(
        collision_arena.find_internal_symbol(&first_name),
        Some(internal_symbol)
    );
}

#[test]
fn mir_relational_result_symbols_are_deterministic_isolated_and_fresh() {
    let resolver = mir_relational_resolver(exact_sum16_relational_contract());
    let reflect_once = |arena: &mut TermArena| {
        let a_sym = arena.declare("a", Sort::BitVec(16)).unwrap();
        let b_sym = arena.declare("b", Sort::BitVec(16)).unwrap();
        let params = [arena.var(a_sym), arena.var(b_sym)];
        reflect_mir_scalar_with_contracts(
            arena,
            &params,
            CKSUM_CALL_MIR,
            &mir_config("cksum_pair"),
            &resolver,
        )
        .unwrap()
    };

    let mut first_arena = TermArena::new();
    let first = reflect_once(&mut first_arena);
    let first_symbol = first.call_sites()[0].result_symbol();
    let first_name = first_arena.symbol(first_symbol).0.to_owned();
    let second = reflect_once(&mut first_arena);
    let second_symbol = second.call_sites()[0].result_symbol();
    let second_name = first_arena.symbol(second_symbol).0.to_owned();
    assert_ne!(first_symbol, second_symbol);
    assert_eq!(second_name, format!("{first_name}.1"));

    let mut fresh_arena = TermArena::new();
    let fresh = reflect_once(&mut fresh_arena);
    assert_eq!(
        fresh_arena.symbol(fresh.call_sites()[0].result_symbol()).0,
        first_name
    );

    let mut collision_arena = TermArena::new();
    let user_symbol = collision_arena
        .declare(&first_name, Sort::BitVec(16))
        .unwrap();
    let collision = reflect_once(&mut collision_arena);
    let internal_symbol = collision.call_sites()[0].result_symbol();
    assert_ne!(user_symbol, internal_symbol);
    assert_eq!(collision_arena.symbol(user_symbol).0, first_name);
    assert_eq!(collision_arena.symbol(internal_symbol).0, first_name);
    assert_eq!(collision_arena.find_symbol(&first_name), Some(user_symbol));
    assert_eq!(
        collision_arena.find_internal_symbol(&first_name),
        Some(internal_symbol)
    );
}
