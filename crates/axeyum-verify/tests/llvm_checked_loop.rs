//! ADR-0291 acceptance gates for the typed canonical LLVM self-loop bridge.

use axeyum_ir::{Assignment, Sort, TermArena, Value, eval};
use axeyum_solver::{
    BmcOutcome, ProofOutcome, SafetyOutcome, SolverConfig, TransitionSystem, bounded_model_check,
    prove, prove_safety_k_induction,
};
use axeyum_verify::reflect::llvm::{
    loops::{
        LoopReflectErrorKind, LoopStateRole, UnsignedPhiUpperBound, reflect_canonical_loop_checked,
    },
    syntax::{BlockId, ParseErrorKind, parse_function, parse_scalar_cfg, render_scalar_cfg},
};

const CAPSUM_LOOP_LL: &str = include_str!("fixtures/llvm/clang_capsum8.ll");

fn capsum8(n: u8) -> u8 {
    let mut acc = 0_u8;
    for _ in 0..n {
        acc = acc.min(99) + 1;
    }
    acc
}

fn capsum_system(bound: u128) -> axeyum_verify::reflect::llvm::loops::CanonicalLoopSystem {
    reflect_canonical_loop_checked(CAPSUM_LOOP_LL, UnsignedPhiUpperBound::new("7", bound))
        .expect("the exact compiler fixture must satisfy the canonical loop profile")
}

#[test]
fn compiler_implicit_entry_slot_is_strict_and_round_trips() {
    let parsed = parse_scalar_cfg(&parse_function(CAPSUM_LOOP_LL).unwrap()).unwrap();
    assert_eq!(parsed.entry, BlockId::Entry);
    assert_eq!(parsed.implicit_entry_label.as_deref(), Some("1"));
    let loop_block = parsed
        .blocks
        .iter()
        .find(|block| block.id == BlockId::Label("5".to_owned()))
        .unwrap();
    assert!(loop_block.phis.iter().all(|phi| {
        phi.incomings
            .iter()
            .any(|incoming| incoming.predecessor == BlockId::Entry)
    }));

    let rendered = render_scalar_cfg(&parsed);
    assert!(rendered.contains("[ 0, %\"1\" ]"));
    assert!(!rendered.contains("<entry>"));
    let reparsed = parse_scalar_cfg(&parse_function(&rendered).unwrap()).unwrap();
    assert_eq!(reparsed.implicit_entry_label.as_deref(), Some("1"));
    assert_eq!(rendered, render_scalar_cfg(&reparsed));

    let disagreeing = CAPSUM_LOOP_LL.replacen("[ 0, %1 ]", "[ 0, %12 ]", 1);
    let error = parse_scalar_cfg(&parse_function(&disagreeing).unwrap()).unwrap_err();
    assert_eq!(error.kind(), ParseErrorKind::InvalidPhi);
    assert!(error.span().line > 0 && error.span().column > 0);

    let named = CAPSUM_LOOP_LL.replace("[ 0, %1 ]", "[ 0, %entry_alias ]");
    let error = parse_scalar_cfg(&parse_function(&named).unwrap()).unwrap_err();
    assert_eq!(error.kind(), ParseErrorKind::UndefinedBlockLabel);
    assert!(error.span().line > 0 && error.span().column > 0);

    let duplicate = CAPSUM_LOOP_LL.replacen("[ 0, %1 ]", "[ 0, %5 ]", 1);
    let error = parse_scalar_cfg(&parse_function(&duplicate).unwrap()).unwrap_err();
    assert_eq!(error.kind(), ParseErrorKind::InvalidPhi);

    let unrelated = CAPSUM_LOOP_LL.replacen("[ %10, %5 ]", "[ %10, %12 ]", 1);
    let error = parse_scalar_cfg(&parse_function(&unrelated).unwrap()).unwrap_err();
    assert_eq!(error.kind(), ParseErrorKind::UndefinedBlockLabel);

    let extant = CAPSUM_LOOP_LL.replace("}\n", "1:\n  ret i8 0\n}\n");
    let error = parse_scalar_cfg(&parse_function(&extant).unwrap()).unwrap_err();
    assert_eq!(error.kind(), ParseErrorKind::InvalidPhi);
}

#[test]
fn canonical_metadata_and_state_order_are_deterministic() {
    let first = capsum_system(100);
    let second = capsum_system(100);
    assert_eq!(first.function_name(), "capsum8");
    assert_eq!(first.loop_block(), &BlockId::Label("5".to_owned()));
    assert_eq!(first.exit_block(), &BlockId::Label("3".to_owned()));
    assert!(first.exit_is_overapproximated());
    assert_eq!(first.state_components(), second.state_components());
    assert_eq!(
        first
            .state_components()
            .iter()
            .map(|component| (component.name.as_str(), component.width, component.role))
            .collect::<Vec<_>>(),
        vec![
            ("6", 8, LoopStateRole::Phi),
            ("7", 8, LoopStateRole::Phi),
            ("0", 8, LoopStateRole::Parameter),
        ]
    );
    assert_eq!(first.state_component_index("7"), Some(1));
}

#[test]
fn capsum_safe_and_bounded_results_reproduce_automatically() {
    let system = capsum_system(100);
    let mut arena = TermArena::new();
    let unbounded = prove_safety_k_induction(&mut arena, &system, 4, &SolverConfig::default())
        .expect("solver should not hard-error");
    assert!(
        matches!(unbounded, SafetyOutcome::Safe { .. }),
        "acc <= 100 must be inductive, got {unbounded:?}"
    );

    let mut arena = TermArena::new();
    let bounded = bounded_model_check(&mut arena, &system, 8, &SolverConfig::default())
        .expect("solver should not hard-error");
    assert!(
        matches!(bounded, BmcOutcome::UnreachableWithinBound { bound: 8 }),
        "acc > 100 must be unreachable through depth 8, got {bounded:?}"
    );
}

#[test]
fn abstract_reachability_is_separately_replayed_in_source() {
    let system = capsum_system(2);
    let mut arena = TermArena::new();
    let outcome = bounded_model_check(&mut arena, &system, 8, &SolverConfig::default())
        .expect("solver should not hard-error");
    let BmcOutcome::Reachable { steps, model } = outcome else {
        panic!("abstract recurrence must reach acc > 2");
    };
    assert_eq!(steps, 3);
    let acc = arena.find_symbol("llvm.loop.capsum8.7@3").unwrap();
    assert_eq!(model.get(acc), Some(Value::Bv { width: 8, value: 3 }));

    // This is deliberately separate from the recurrence model: n=3 executes
    // three ordinary source iterations and reaches the same acc=3 state.
    assert_eq!(capsum8(3), 3);
}

#[test]
fn automatic_formulas_equal_an_independent_recurrence_spec() {
    let system = capsum_system(100);
    let mut arena = TermArena::new();
    let pre = system.state_vars(&mut arena, 0).unwrap();
    let post = system.state_vars(&mut arena, 1).unwrap();
    let actual_init = system.init(&mut arena, &pre).unwrap();
    let actual_trans = system.trans(&mut arena, &pre, &post).unwrap();
    let actual_bad = system.bad(&mut arena, &pre).unwrap();

    let zero = arena.bv_const(8, 0).unwrap();
    let one = arena.bv_const(8, 1).unwrap();
    let max = arena.bv_const(8, 255).unwrap();
    let ninety_nine = arena.bv_const(8, 99).unwrap();
    let hundred = arena.bv_const(8, 100).unwrap();
    let i = arena.var(pre[0]);
    let acc = arena.var(pre[1]);
    let n = arena.var(pre[2]);
    let next_i = arena.bv_add(i, one).unwrap();
    let capped = arena.bv_ule(acc, ninety_nine).unwrap();
    let capped_acc = arena.ite(capped, acc, ninety_nine).unwrap();
    let next_acc = arena.bv_add(capped_acc, one).unwrap();
    let i_is_max = arena.eq(i, max).unwrap();
    let i_defined = arena.not(i_is_max).unwrap();
    let init_i = arena.eq(i, zero).unwrap();
    let init_acc = arena.eq(acc, zero).unwrap();
    let expected_init = arena.and(init_i, init_acc).unwrap();
    let post_i = arena.var(post[0]);
    let post_acc = arena.var(post[1]);
    let post_n = arena.var(post[2]);
    let step_i = arena.eq(post_i, next_i).unwrap();
    let step_acc = arena.eq(post_acc, next_acc).unwrap();
    let keep_n = arena.eq(post_n, n).unwrap();
    let acc_and_n = arena.and(step_acc, keep_n).unwrap();
    let updates = arena.and(step_i, acc_and_n).unwrap();
    let expected_trans = arena.and(i_defined, updates).unwrap();
    let expected_bad = arena.bv_ugt(acc, hundred).unwrap();

    for (actual, expected) in [
        (actual_init, expected_init),
        (actual_trans, expected_trans),
        (actual_bad, expected_bad),
    ] {
        let equivalent = arena.eq(actual, expected).unwrap();
        assert!(matches!(
            prove(&mut arena, &[], equivalent, &SolverConfig::default()).unwrap(),
            ProofOutcome::Proved(_)
        ));
    }
}

#[test]
fn concrete_recurrence_fuzz_has_zero_disagreements() {
    let system = capsum_system(100);
    let mut arena = TermArena::new();
    let pre = system.state_vars(&mut arena, 0).unwrap();
    let post = system.state_vars(&mut arena, 1).unwrap();
    let transition = system.trans(&mut arena, &pre, &post).unwrap();
    let mut seed = 0x51f1_5e1f_0bad_cafe_u64;
    let mut disagree = 0_u64;
    for _ in 0..20_000 {
        seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
        let [i, acc, n, post_i, post_acc, post_n, _, _] = seed.to_le_bytes();
        let expected = i != u8::MAX
            && post_i == i.wrapping_add(1)
            && post_acc == acc.min(99) + 1
            && post_n == n;
        let mut assignment = Assignment::new();
        for (symbol, value) in pre
            .iter()
            .chain(&post)
            .copied()
            .zip([i, acc, n, post_i, post_acc, post_n])
        {
            assignment.set(
                symbol,
                Value::Bv {
                    width: 8,
                    value: value.into(),
                },
            );
        }
        let actual = eval(&arena, transition, &assignment).unwrap() == Value::Bool(true);
        disagree += u64::from(actual != expected);
    }
    assert_eq!(disagree, 0, "DISAGREE must remain zero");
}

#[test]
fn poison_immediate_ub_and_undefined_branch_cannot_transition() {
    let flagged = r"
define i8 @flagged(i8 %n) {
  br label %loop
loop:
  %x = phi i8 [ 255, %0 ], [ 0, %loop ]
  %next = add nuw i8 %x, 1
  %c = icmp eq i8 %next, %n
  br i1 %c, label %done, label %loop
done:
  ret i8 %x
}
";
    let system =
        reflect_canonical_loop_checked(flagged, UnsignedPhiUpperBound::new("x", 254)).unwrap();
    let mut arena = TermArena::new();
    let pre = system.state_vars(&mut arena, 0).unwrap();
    let post = system.state_vars(&mut arena, 1).unwrap();
    let transition = system.trans(&mut arena, &pre, &post).unwrap();
    let mut assignment = Assignment::new();
    for (symbol, value) in pre.iter().chain(&post).copied().zip([255_u8, 0, 0, 0]) {
        assignment.set(
            symbol,
            Value::Bv {
                width: 8,
                value: value.into(),
            },
        );
    }
    assert_eq!(
        eval(&arena, transition, &assignment).unwrap(),
        Value::Bool(false)
    );

    let division = flagged
        .replace("%next = add nuw i8 %x, 1", "%next = udiv i8 1, %x")
        .replace("[ 255, %0 ]", "[ 0, %0 ]");
    let system =
        reflect_canonical_loop_checked(&division, UnsignedPhiUpperBound::new("x", 254)).unwrap();
    let mut arena = TermArena::new();
    let pre = system.state_vars(&mut arena, 0).unwrap();
    let post = system.state_vars(&mut arena, 1).unwrap();
    let transition = system.trans(&mut arena, &pre, &post).unwrap();
    let mut assignment = Assignment::new();
    for symbol in pre.iter().chain(&post).copied() {
        assignment.set(symbol, Value::Bv { width: 8, value: 0 });
    }
    assert_eq!(
        eval(&arena, transition, &assignment).unwrap(),
        Value::Bool(false)
    );
}

#[test]
fn unsupported_shapes_and_dependencies_fail_closed_with_spans() {
    let no_loop = "define i8 @f(i8 %x) {\n  ret i8 %x\n}\n";
    let error =
        reflect_canonical_loop_checked(no_loop, UnsignedPhiUpperBound::new("x", 1)).unwrap_err();
    assert_eq!(error.kind(), LoopReflectErrorKind::NoCycle);
    assert!(error.span().is_some());

    let two_loops = r"
define i8 @two(i1 %choose) {
  br i1 %choose, label %a, label %b
a:
  %x = phi i8 [ 0, %0 ], [ %xa, %a ]
  %xa = add i8 %x, 1
  %ca = icmp eq i8 %xa, 10
  br i1 %ca, label %done, label %a
b:
  %y = phi i8 [ 0, %0 ], [ %yb, %b ]
  %yb = add i8 %y, 1
  %cb = icmp eq i8 %yb, 10
  br i1 %cb, label %done, label %b
done:
  ret i8 0
}
";
    let error =
        reflect_canonical_loop_checked(two_loops, UnsignedPhiUpperBound::new("x", 7)).unwrap_err();
    assert_eq!(error.kind(), LoopReflectErrorKind::MultipleCycles);
    assert!(error.span().is_some());

    let multi_block = r"
define i8 @multi(i8 %n) {
  br label %header
header:
  %x = phi i8 [ 0, %0 ], [ %next, %latch ]
  br label %latch
latch:
  %next = add i8 %x, 1
  %c = icmp eq i8 %next, %n
  br i1 %c, label %done, label %header
done:
  ret i8 %x
}
";
    let error = reflect_canonical_loop_checked(multi_block, UnsignedPhiUpperBound::new("x", 7))
        .unwrap_err();
    assert_eq!(error.kind(), LoopReflectErrorKind::NonCanonicalCycle);
    assert!(error.span().is_some());

    let self_only = r"
define i8 @forever() {
  br label %loop
loop:
  %x = phi i8 [ 0, %0 ], [ %next, %loop ]
  %next = add i8 %x, 1
  br label %loop
}
";
    let error =
        reflect_canonical_loop_checked(self_only, UnsignedPhiUpperBound::new("x", 7)).unwrap_err();
    assert_eq!(error.kind(), LoopReflectErrorKind::NonCanonicalCycle);
    assert!(error.span().is_some());

    let external = r"
define i8 @f(i8 %n) {
  br label %loop
loop:
  %x = phi i8 [ 0, %0 ], [ %next, %loop ]
  %next = add i8 %outside, 1
  %c = icmp eq i8 %x, %n
  br i1 %c, label %done, label %loop
done:
  ret i8 %x
}
";
    let error =
        reflect_canonical_loop_checked(external, UnsignedPhiUpperBound::new("x", 7)).unwrap_err();
    assert_eq!(error.kind(), LoopReflectErrorKind::ExternalSsaDependency);
    assert!(error.span().is_some());

    let external_init = external
        .replace("[ 0, %0 ]", "[ %preheader, %0 ]")
        .replace("%next = add i8 %outside, 1", "%next = add i8 %x, 1");
    let error = reflect_canonical_loop_checked(&external_init, UnsignedPhiUpperBound::new("x", 7))
        .unwrap_err();
    assert_eq!(error.kind(), LoopReflectErrorKind::UnsupportedInitializer);
    assert!(error.span().is_some());

    let memory = external.replace(
        "%next = add i8 %outside, 1",
        "%next = load i8, ptr %outside, align 1",
    );
    let error =
        reflect_canonical_loop_checked(&memory, UnsignedPhiUpperBound::new("x", 7)).unwrap_err();
    assert_eq!(error.kind(), LoopReflectErrorKind::UnsupportedMemory);
    assert!(error.span().is_some());

    let error =
        reflect_canonical_loop_checked(CAPSUM_LOOP_LL, UnsignedPhiUpperBound::new("missing", 7))
            .unwrap_err();
    assert_eq!(error.kind(), LoopReflectErrorKind::InvalidProperty);
    assert!(error.span().is_some());

    let error =
        reflect_canonical_loop_checked(CAPSUM_LOOP_LL, UnsignedPhiUpperBound::new("7", 256))
            .unwrap_err();
    assert_eq!(error.kind(), LoopReflectErrorKind::InvalidProperty);
    assert!(error.span().is_some());
}

#[test]
fn deterministic_malformed_inputs_never_panic() {
    let mutations = [
        CAPSUM_LOOP_LL.replace("label %5", "label %missing"),
        CAPSUM_LOOP_LL.replace("[ %10, %5 ],", "[ %10, %5 ], [ 1, %5 ],"),
        CAPSUM_LOOP_LL.replace("%7 = phi", "%6 = phi"),
        CAPSUM_LOOP_LL.replace("br i1 %11, label %3, label %5", "br label %5"),
        CAPSUM_LOOP_LL.replace("%9 = add nuw nsw", "%9 = load"),
    ];
    for llvm in mutations {
        let result = std::panic::catch_unwind(|| {
            reflect_canonical_loop_checked(&llvm, UnsignedPhiUpperBound::new("7", 100))
        });
        let reflected = result.expect("source input must never panic");
        let error = reflected.expect_err("mutation must fail closed");
        assert!(error.span().is_some());
    }
}

#[test]
fn state_sorts_match_the_typed_layout() {
    let system = capsum_system(100);
    let mut arena = TermArena::new();
    let state = system.state_vars(&mut arena, 0).unwrap();
    assert_eq!(state.len(), 3);
    assert!(
        state
            .iter()
            .all(|symbol| arena.symbol(*symbol).1 == Sort::BitVec(8))
    );
}
