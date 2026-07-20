//! ADR-0291 acceptance gates for the typed canonical LLVM self-loop bridge.

use std::fmt::Write as _;

use axeyum_ir::{Assignment, Sort, TermArena, Value, eval};
use axeyum_solver::{
    BmcOutcome, ProofOutcome, SafetyOutcome, SolverConfig, TransitionSystem, bounded_model_check,
    prove, prove_safety_k_induction,
};
use axeyum_verify::reflect::llvm::{
    loops::{
        LoopReflectErrorKind, LoopStateRole, UnsignedPhiUpperBound, reflect_canonical_loop_checked,
        reflect_single_latch_loop_checked,
    },
    syntax::{BlockId, ParseErrorKind, parse_function, parse_scalar_cfg, render_scalar_cfg},
};

const CAPSUM_LOOP_LL: &str = include_str!("fixtures/llvm/clang_capsum8.ll");
const CAPDIV_LOOP_LL: &str = include_str!("fixtures/llvm/clang21_capdiv_natural_loop.ll");

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

fn capdiv(n: u8, d: u8) -> u8 {
    let mut acc = 0_u8;
    for i in 0..n {
        if i & 1 != 0 {
            acc = acc.wrapping_add(i / d).min(100);
        }
    }
    acc
}

fn capdiv_system(bound: u128) -> axeyum_verify::reflect::llvm::loops::CanonicalLoopSystem {
    reflect_single_latch_loop_checked(CAPDIV_LOOP_LL, UnsignedPhiUpperBound::new("7", bound))
        .expect("the exact compiler fixture must satisfy the single-latch profile")
}

fn assign_bytes(
    assignment: &mut Assignment,
    symbols: impl IntoIterator<Item = axeyum_ir::SymbolId>,
    values: impl IntoIterator<Item = u8>,
) {
    for (symbol, value) in symbols.into_iter().zip(values) {
        assignment.set(
            symbol,
            Value::Bv {
                width: 8,
                value: value.into(),
            },
        );
    }
}

fn exploding_paths_loop(diamonds: usize) -> String {
    assert!(diamonds > 0);
    let mut llvm = String::from(
        "define i8 @many(i1 %c) {\n  br label %header\nheader:\n  %x = phi i8 [ 0, %0 ], [ %next, %latch ]\n  br i1 %c, label %a0, label %b0\n",
    );
    for index in 0..diamonds {
        let _ = write!(
            llvm,
            "a{index}:\n  br label %join{index}\nb{index}:\n  br label %join{index}\njoin{index}:\n"
        );
        if index + 1 == diamonds {
            llvm.push_str("  br label %latch\n");
        } else {
            let _ = writeln!(
                llvm,
                "  br i1 %c, label %a{}, label %b{}",
                index + 1,
                index + 1
            );
        }
    }
    llvm.push_str(
        "latch:\n  %next = add i8 %x, 1\n  %done = icmp eq i8 %next, 10\n  br i1 %done, label %exit, label %header\nexit:\n  ret i8 %x\n}\n",
    );
    llvm
}

fn oversized_linear_path_loop(internal_blocks: usize) -> String {
    assert!(internal_blocks > 0);
    let mut llvm = String::from(
        "define i8 @long_path() {\n  br label %header\nheader:\n  %x = phi i8 [ 0, %0 ], [ %next, %latch ]\n  br label %b0\n",
    );
    for index in 0..internal_blocks {
        let target = if index + 1 == internal_blocks {
            "latch".to_owned()
        } else {
            format!("b{}", index + 1)
        };
        let _ = writeln!(llvm, "b{index}:\n  br label %{target}");
    }
    llvm.push_str(
        "latch:\n  %next = add i8 %x, 1\n  %done = icmp eq i8 %next, 10\n  br i1 %done, label %exit, label %header\nexit:\n  ret i8 %x\n}\n",
    );
    llvm
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

#[test]
fn natural_loop_fixture_round_trips_with_entry_and_loop_metadata() {
    let parsed = parse_scalar_cfg(&parse_function(CAPDIV_LOOP_LL).unwrap()).unwrap();
    assert_eq!(parsed.entry, BlockId::Entry);
    assert_eq!(parsed.implicit_entry_label.as_deref(), Some("2"));
    let latch = parsed
        .blocks
        .iter()
        .find(|block| block.id == BlockId::Label("15".to_owned()))
        .unwrap();
    assert_eq!(latch.terminator.metadata, vec!["!llvm.loop !5"]);

    let rendered = render_scalar_cfg(&parsed);
    assert!(rendered.contains("[ 0, %\"2\" ]"));
    assert!(rendered.contains("!llvm.loop !5"));
    let reparsed = parse_scalar_cfg(&parse_function(&rendered).unwrap()).unwrap();
    assert_eq!(reparsed.implicit_entry_label.as_deref(), Some("2"));
    assert_eq!(rendered, render_scalar_cfg(&reparsed));
}

#[test]
fn natural_loop_metadata_paths_and_state_order_are_deterministic() {
    let parsed = parse_scalar_cfg(&parse_function(CAPDIV_LOOP_LL).unwrap()).unwrap();
    let registered_back_edges = parsed
        .blocks
        .iter()
        .flat_map(|block| {
            block
                .successors
                .iter()
                .map(move |successor| (&block.id, successor))
        })
        .filter(|(source, target)| {
            **source == BlockId::Label("15".to_owned())
                && **target == BlockId::Label("6".to_owned())
        })
        .count();
    assert_eq!(registered_back_edges, 1);

    let first = capdiv_system(100);
    let second = capdiv_system(100);
    assert_eq!(first.function_name(), "capdiv");
    assert_eq!(first.loop_block(), &BlockId::Label("6".to_owned()));
    assert_eq!(first.latch_block(), &BlockId::Label("15".to_owned()));
    assert_eq!(first.exit_block(), &BlockId::Label("4".to_owned()));
    assert_eq!(first.iteration_paths(), second.iteration_paths());
    assert_eq!(
        first
            .iteration_paths()
            .iter()
            .map(|path| path.blocks().to_vec())
            .collect::<Vec<_>>(),
        vec![
            vec![
                BlockId::Label("6".to_owned()),
                BlockId::Label("15".to_owned()),
            ],
            vec![
                BlockId::Label("6".to_owned()),
                BlockId::Label("11".to_owned()),
                BlockId::Label("15".to_owned()),
            ],
        ]
    );
    assert_eq!(
        first
            .state_components()
            .iter()
            .map(|component| (component.name.as_str(), component.width, component.role))
            .collect::<Vec<_>>(),
        vec![
            ("7", 8, LoopStateRole::Phi),
            ("8", 8, LoopStateRole::Phi),
            ("0", 8, LoopStateRole::Parameter),
            ("1", 8, LoopStateRole::Parameter),
        ]
    );
}

#[test]
fn new_constructor_preserves_the_prior_self_loop_route() {
    let prior = capsum_system(100);
    let generalized =
        reflect_single_latch_loop_checked(CAPSUM_LOOP_LL, UnsignedPhiUpperBound::new("7", 100))
            .unwrap();
    assert_eq!(prior.loop_block(), generalized.loop_block());
    assert_eq!(prior.latch_block(), generalized.latch_block());
    assert_eq!(prior.iteration_paths(), generalized.iteration_paths());
    assert_eq!(prior.state_components(), generalized.state_components());

    let mut arena = TermArena::new();
    let pre = prior.state_vars(&mut arena, 0).unwrap();
    let post = prior.state_vars(&mut arena, 1).unwrap();
    let prior_init = prior.init(&mut arena, &pre).unwrap();
    let generalized_init = generalized.init(&mut arena, &pre).unwrap();
    let prior_trans = prior.trans(&mut arena, &pre, &post).unwrap();
    let generalized_trans = generalized.trans(&mut arena, &pre, &post).unwrap();
    let prior_bad = prior.bad(&mut arena, &pre).unwrap();
    let generalized_bad = generalized.bad(&mut arena, &pre).unwrap();
    assert_eq!(prior_init, generalized_init);
    assert_eq!(prior_trans, generalized_trans);
    assert_eq!(prior_bad, generalized_bad);

    let error =
        reflect_canonical_loop_checked(CAPDIV_LOOP_LL, UnsignedPhiUpperBound::new("7", 100))
            .unwrap_err();
    assert_eq!(error.kind(), LoopReflectErrorKind::NonCanonicalCycle);
}

#[test]
fn path_conditioned_division_ub_preserves_the_even_zero_divisor_path() {
    let system = capdiv_system(100);
    let mut arena = TermArena::new();
    let pre = system.state_vars(&mut arena, 0).unwrap();
    let post = system.state_vars(&mut arena, 1).unwrap();
    let transition = system.trans(&mut arena, &pre, &post).unwrap();
    let zero = arena.bv_const(8, 0).unwrap();
    let divisor = arena.var(pre[3]);
    let divisor_zero = arena.eq(divisor, zero).unwrap();
    let divisor_nonzero = arena.not(divisor_zero).unwrap();
    let deliberately_eager_ub = arena.and(transition, divisor_nonzero).unwrap();

    let mut even = Assignment::new();
    assign_bytes(
        &mut even,
        pre.iter().chain(&post).copied(),
        [9, 2, 10, 0, 9, 3, 10, 0],
    );
    assert_eq!(eval(&arena, transition, &even).unwrap(), Value::Bool(true));
    assert_eq!(
        eval(&arena, deliberately_eager_ub, &even).unwrap(),
        Value::Bool(false),
        "globally conjoining division UB must be refuted by the even d=0 path"
    );

    let mut odd = Assignment::new();
    assign_bytes(
        &mut odd,
        pre.iter().chain(&post).copied(),
        [9, 3, 10, 0, 9, 4, 10, 0],
    );
    assert_eq!(eval(&arena, transition, &odd).unwrap(), Value::Bool(false));
}

#[test]
fn natural_loop_formulas_equal_an_independent_path_spec() {
    let system = capdiv_system(100);
    let mut arena = TermArena::new();
    let pre = system.state_vars(&mut arena, 0).unwrap();
    let post = system.state_vars(&mut arena, 1).unwrap();
    let actual_init = system.init(&mut arena, &pre).unwrap();
    let actual_trans = system.trans(&mut arena, &pre, &post).unwrap();
    let actual_bad = system.bad(&mut arena, &pre).unwrap();

    let zero = arena.bv_const(8, 0).unwrap();
    let one = arena.bv_const(8, 1).unwrap();
    let hundred = arena.bv_const(8, 100).unwrap();
    let max = arena.bv_const(8, 255).unwrap();
    let acc = arena.var(pre[0]);
    let i = arena.var(pre[1]);
    let n = arena.var(pre[2]);
    let d = arena.var(pre[3]);
    let post_acc = arena.var(post[0]);
    let post_i = arena.var(post[1]);
    let post_n = arena.var(post[2]);
    let post_d = arena.var(post[3]);

    let init_acc = arena.eq(acc, zero).unwrap();
    let init_i = arena.eq(i, zero).unwrap();
    let expected_init = arena.and(init_acc, init_i).unwrap();
    let masked = arena.bv_and(i, one).unwrap();
    let even = arena.eq(masked, zero).unwrap();
    let not_even = arena.not(even).unwrap();
    let divisor_zero = arena.eq(d, zero).unwrap();
    let divisor_nonzero = arena.not(divisor_zero).unwrap();
    let quotient = arena.bv_udiv(i, d).unwrap();
    let sum = arena.bv_add(acc, quotient).unwrap();
    let below_cap = arena.bv_ule(sum, hundred).unwrap();
    let capped = arena.ite(below_cap, sum, hundred).unwrap();
    let even_acc = arena.eq(post_acc, acc).unwrap();
    let odd_acc = arena.eq(post_acc, capped).unwrap();
    let odd_defined = arena.and(not_even, divisor_nonzero).unwrap();
    let odd_path = arena.and(odd_defined, odd_acc).unwrap();
    let even_path = arena.and(even, even_acc).unwrap();
    let path_update = arena.or(even_path, odd_path).unwrap();
    let next_i = arena.bv_add(i, one).unwrap();
    let update_i = arena.eq(post_i, next_i).unwrap();
    let keep_n = arena.eq(post_n, n).unwrap();
    let keep_d = arena.eq(post_d, d).unwrap();
    let i_is_max = arena.eq(i, max).unwrap();
    let i_defined = arena.not(i_is_max).unwrap();
    let scalar_updates = arena.and(update_i, keep_n).unwrap();
    let state_updates = arena.and(scalar_updates, keep_d).unwrap();
    let defined_updates = arena.and(i_defined, state_updates).unwrap();
    let expected_trans = arena.and(path_update, defined_updates).unwrap();
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
fn natural_loop_recurrence_fuzz_has_zero_disagreements() {
    let system = capdiv_system(100);
    let mut arena = TermArena::new();
    let pre = system.state_vars(&mut arena, 0).unwrap();
    let post = system.state_vars(&mut arena, 1).unwrap();
    let transition = system.trans(&mut arena, &pre, &post).unwrap();
    let mut seed = 0xc4ad_d17e_5eed_0292_u64;
    let mut disagree = 0_u64;
    for _ in 0..50_000 {
        seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
        let [acc, i, n, d, post_acc, post_i, post_n, post_d] = seed.to_le_bytes();
        let expected_acc = if i & 1 == 0 {
            Some(acc)
        } else {
            i.checked_div(d)
                .map(|quotient| acc.wrapping_add(quotient).min(100))
        };
        let expected = i != u8::MAX
            && expected_acc == Some(post_acc)
            && post_i == i.wrapping_add(1)
            && post_n == n
            && post_d == d;
        let mut assignment = Assignment::new();
        assign_bytes(
            &mut assignment,
            pre.iter().chain(&post).copied(),
            [acc, i, n, d, post_acc, post_i, post_n, post_d],
        );
        let actual = eval(&arena, transition, &assignment).unwrap() == Value::Bool(true);
        disagree += u64::from(actual != expected);
    }
    assert_eq!(disagree, 0, "DISAGREE must remain zero over 50,000 tuples");
}

#[test]
fn natural_loop_safety_bmc_and_source_replay_are_distinct() {
    let safe = capdiv_system(100);
    let mut arena = TermArena::new();
    let unbounded = prove_safety_k_induction(&mut arena, &safe, 4, &SolverConfig::default())
        .expect("solver should not hard-error");
    assert!(matches!(unbounded, SafetyOutcome::Safe { .. }));

    let mut arena = TermArena::new();
    let bounded = bounded_model_check(&mut arena, &safe, 8, &SolverConfig::default())
        .expect("solver should not hard-error");
    assert!(matches!(
        bounded,
        BmcOutcome::UnreachableWithinBound { bound: 8 }
    ));

    let reachable = capdiv_system(0);
    let mut arena = TermArena::new();
    let outcome = bounded_model_check(&mut arena, &reachable, 4, &SolverConfig::default())
        .expect("solver should not hard-error");
    let BmcOutcome::Reachable { steps, .. } = outcome else {
        panic!("abstract recurrence must reach acc > 0");
    };
    assert_eq!(steps, 2);
    assert_eq!(capdiv(2, 1), 1);
}

#[test]
fn latch_phis_bind_simultaneously_for_the_selected_predecessor() {
    let llvm = r"
define i8 @swap(i8 %a, i8 %b) {
  br label %header
header:
  %x = phi i8 [ %a, %0 ], [ %lx, %latch ]
  %y = phi i8 [ %b, %0 ], [ %ly, %latch ]
  br label %latch
latch:
  %lx = phi i8 [ %y, %header ]
  %ly = phi i8 [ %x, %header ]
  %done = icmp eq i8 %lx, 0
  br i1 %done, label %exit, label %header
exit:
  ret i8 %x
}
";
    let system =
        reflect_single_latch_loop_checked(llvm, UnsignedPhiUpperBound::new("x", u8::MAX.into()))
            .unwrap();
    assert_eq!(
        system
            .iteration_paths()
            .iter()
            .map(|path| path.blocks().to_vec())
            .collect::<Vec<_>>(),
        vec![vec![
            BlockId::Label("header".to_owned()),
            BlockId::Label("latch".to_owned()),
        ]]
    );
    let mut arena = TermArena::new();
    let pre = system.state_vars(&mut arena, 0).unwrap();
    let post = system.state_vars(&mut arena, 1).unwrap();
    let transition = system.trans(&mut arena, &pre, &post).unwrap();
    let mut assignment = Assignment::new();
    assign_bytes(
        &mut assignment,
        pre.iter().chain(&post).copied(),
        [2, 9, 2, 9, 9, 2, 2, 9],
    );
    assert_eq!(
        eval(&arena, transition, &assignment).unwrap(),
        Value::Bool(true)
    );
}

#[test]
fn internal_phi_poison_is_constrained_only_when_observed() {
    let unused = r"
define i8 @unused_poison() {
  br label %header
header:
  %x = phi i8 [ 255, %0 ], [ %x, %latch ]
  %poison = add nuw i8 %x, 1
  br label %latch
latch:
  %unused = phi i8 [ %poison, %header ]
  %done = icmp eq i8 %x, 0
  br i1 %done, label %exit, label %header
exit:
  ret i8 %x
}
";
    let system =
        reflect_single_latch_loop_checked(unused, UnsignedPhiUpperBound::new("x", u8::MAX.into()))
            .unwrap();
    let mut arena = TermArena::new();
    let pre = system.state_vars(&mut arena, 0).unwrap();
    let post = system.state_vars(&mut arena, 1).unwrap();
    let transition = system.trans(&mut arena, &pre, &post).unwrap();
    let mut assignment = Assignment::new();
    assign_bytes(
        &mut assignment,
        pre.iter().chain(&post).copied(),
        [u8::MAX, u8::MAX],
    );
    assert_eq!(
        eval(&arena, transition, &assignment).unwrap(),
        Value::Bool(true),
        "an unobserved poison PHI must not become immediate UB"
    );

    let observed = unused.replace("%done = icmp eq i8 %x, 0", "%done = icmp eq i8 %unused, 0");
    let system = reflect_single_latch_loop_checked(
        &observed,
        UnsignedPhiUpperBound::new("x", u8::MAX.into()),
    )
    .unwrap();
    let mut arena = TermArena::new();
    let pre = system.state_vars(&mut arena, 0).unwrap();
    let post = system.state_vars(&mut arena, 1).unwrap();
    let transition = system.trans(&mut arena, &pre, &post).unwrap();
    let mut assignment = Assignment::new();
    assign_bytes(
        &mut assignment,
        pre.iter().chain(&post).copied(),
        [u8::MAX, u8::MAX],
    );
    assert_eq!(
        eval(&arena, transition, &assignment).unwrap(),
        Value::Bool(false),
        "the latch branch must require its observed poison condition to be defined"
    );
}

#[test]
#[expect(
    clippy::too_many_lines,
    reason = "one gate keeps the exact fail-closed loop-profile boundary matrix visible"
)]
fn natural_loop_rejection_boundaries_are_located_and_stable() {
    let no_cycle = "define i8 @f(i8 %x) {\n  ret i8 %x\n}\n";
    let error = reflect_single_latch_loop_checked(no_cycle, UnsignedPhiUpperBound::new("x", 1))
        .unwrap_err();
    assert_eq!(error.kind(), LoopReflectErrorKind::NoCycle);
    assert!(error.span().is_some());

    let two_loops = r"
define i8 @two(i1 %choose) {
  br i1 %choose, label %a, label %b
a:
  %x = phi i8 [ 0, %0 ], [ %xa, %a ]
  %xa = add i8 %x, 1
  %ca = icmp eq i8 %xa, 10
  br i1 %ca, label %exit, label %a
b:
  %y = phi i8 [ 0, %0 ], [ %yb, %b ]
  %yb = add i8 %y, 1
  %cb = icmp eq i8 %yb, 10
  br i1 %cb, label %exit, label %b
exit:
  ret i8 0
}
";
    let error = reflect_single_latch_loop_checked(two_loops, UnsignedPhiUpperBound::new("x", 10))
        .unwrap_err();
    assert_eq!(error.kind(), LoopReflectErrorKind::MultipleCycles);
    assert!(error.span().is_some());

    let multiple_latches = r"
define i8 @latches(i1 %choose) {
  br label %header
header:
  %x = phi i8 [ 0, %0 ], [ %xa, %left ], [ %xb, %right ]
  br i1 %choose, label %left, label %right
left:
  %xa = add i8 %x, 1
  %ca = icmp eq i8 %xa, 10
  br i1 %ca, label %exit, label %header
right:
  %xb = add i8 %x, 2
  %cb = icmp eq i8 %xb, 10
  br i1 %cb, label %exit, label %header
exit:
  ret i8 %x
}
";
    let error =
        reflect_single_latch_loop_checked(multiple_latches, UnsignedPhiUpperBound::new("x", 10))
            .unwrap_err();
    assert_eq!(error.kind(), LoopReflectErrorKind::NonCanonicalCycle);
    assert!(error.span().is_some());

    let no_exit = r"
define i8 @cycle() {
  br label %a
a:
  %x = phi i8 [ 0, %0 ], [ %next, %b ]
  br label %b
b:
  %next = add i8 %x, 1
  br label %a
}
";
    let error = reflect_single_latch_loop_checked(no_exit, UnsignedPhiUpperBound::new("x", 10))
        .unwrap_err();
    assert_eq!(error.kind(), LoopReflectErrorKind::NonCanonicalCycle);
    assert!(error.span().is_some());

    let early_exit = r"
define i8 @early(i1 %c) {
  br label %header
header:
  %x = phi i8 [ 0, %0 ], [ %next, %latch ]
  br i1 %c, label %latch, label %exit
latch:
  %next = add i8 %x, 1
  %done = icmp eq i8 %next, 10
  br i1 %done, label %exit, label %header
exit:
  ret i8 %x
}
";
    let error = reflect_single_latch_loop_checked(early_exit, UnsignedPhiUpperBound::new("x", 10))
        .unwrap_err();
    assert_eq!(error.kind(), LoopReflectErrorKind::NonCanonicalLoopRegion);
    assert!(error.span().is_some());

    let switch = r"
define i8 @sw(i1 %c) {
  br label %header
header:
  %x = phi i8 [ 0, %0 ], [ %next, %latch ]
  switch i1 %c, label %left [ i1 1, label %right ]
left:
  br label %latch
right:
  br label %latch
latch:
  %next = add i8 %x, 1
  %done = icmp eq i8 %next, 10
  br i1 %done, label %exit, label %header
exit:
  ret i8 %x
}
";
    let error =
        reflect_single_latch_loop_checked(switch, UnsignedPhiUpperBound::new("x", 10)).unwrap_err();
    assert_eq!(error.kind(), LoopReflectErrorKind::UnsupportedBody);
    assert!(error.span().is_some());

    let external_predecessor = r"
define i8 @outside(i1 %c) {
  br i1 %c, label %header, label %body
header:
  %x = phi i8 [ 0, %0 ], [ %next, %latch ]
  br label %body
body:
  br label %latch
latch:
  %next = add i8 %x, 1
  %done = icmp eq i8 %next, 10
  br i1 %done, label %exit, label %header
exit:
  ret i8 %x
}
";
    let error = reflect_single_latch_loop_checked(
        external_predecessor,
        UnsignedPhiUpperBound::new("x", 10),
    )
    .unwrap_err();
    assert_eq!(error.kind(), LoopReflectErrorKind::NonCanonicalLoopRegion);
    assert!(error.span().is_some());

    let memory = CAPDIV_LOOP_LL.replace("%12 = udiv i8 %8, %1", "%12 = load i8, ptr %1");
    let error = reflect_single_latch_loop_checked(&memory, UnsignedPhiUpperBound::new("7", 100))
        .unwrap_err();
    assert_eq!(error.kind(), LoopReflectErrorKind::UnsupportedMemory);
    assert!(error.span().is_some());

    let external_ssa = CAPDIV_LOOP_LL.replace("%13 = add i8 %12, %7", "%13 = add i8 %12, %outside");
    let error =
        reflect_single_latch_loop_checked(&external_ssa, UnsignedPhiUpperBound::new("7", 100))
            .unwrap_err();
    assert_eq!(error.kind(), LoopReflectErrorKind::ExternalSsaDependency);
    assert!(error.span().is_some());

    let missing_dominance = r"
define i8 @dominance(i1 %c) {
  br label %header
header:
  %x = phi i8 [ 0, %0 ], [ %selected, %latch ]
  br i1 %c, label %left, label %right
left:
  %left_value = add i8 %x, 1
  br label %latch
right:
  br label %latch
latch:
  %selected = phi i8 [ %x, %left ], [ %left_value, %right ]
  %done = icmp eq i8 %selected, 10
  br i1 %done, label %exit, label %header
exit:
  ret i8 %x
}
";
    let error =
        reflect_single_latch_loop_checked(missing_dominance, UnsignedPhiUpperBound::new("x", 10))
            .unwrap_err();
    assert_eq!(error.kind(), LoopReflectErrorKind::ExternalSsaDependency);
    assert!(error.span().is_some());

    let wrong_width = CAPDIV_LOOP_LL.replace("%17 = add nuw i8 %8, 1", "%17 = add nuw i16 %8, 1");
    let error =
        reflect_single_latch_loop_checked(&wrong_width, UnsignedPhiUpperBound::new("7", 100))
            .unwrap_err();
    assert_eq!(error.kind(), LoopReflectErrorKind::UnsupportedBody);
    assert!(error.span().is_some());

    let duplicate = CAPDIV_LOOP_LL.replace("%13 = add i8 %12, %7", "%12 = add i8 %12, %7");
    let error = reflect_single_latch_loop_checked(&duplicate, UnsignedPhiUpperBound::new("7", 100))
        .unwrap_err();
    assert_eq!(error.kind(), LoopReflectErrorKind::UnsupportedBody);
    assert!(error.span().is_some());

    let error = reflect_single_latch_loop_checked(
        &exploding_paths_loop(7),
        UnsignedPhiUpperBound::new("x", 10),
    )
    .unwrap_err();
    assert_eq!(error.kind(), LoopReflectErrorKind::PathLimit);
    assert!(error.span().is_some());

    let error = reflect_single_latch_loop_checked(
        &oversized_linear_path_loop(4_095),
        UnsignedPhiUpperBound::new("x", 10),
    )
    .unwrap_err();
    assert_eq!(error.kind(), LoopReflectErrorKind::PathLimit);
    assert!(error.span().is_some());
}

#[test]
fn natural_loop_malformed_mutations_never_panic() {
    let mutations = [
        CAPDIV_LOOP_LL.replace("label %15", "label %missing"),
        CAPDIV_LOOP_LL.replace("[ %16, %15 ], [ 0, %2 ]", "[ %16, %15 ]"),
        CAPDIV_LOOP_LL.replace("%17 = add nuw", "%16 = add nuw"),
        CAPDIV_LOOP_LL.replace("br i1 %18, label %4, label %6", "br label %6"),
        CAPDIV_LOOP_LL.replace("%12 = udiv", "%12 = load"),
    ];
    for llvm in mutations {
        let result = std::panic::catch_unwind(|| {
            reflect_single_latch_loop_checked(&llvm, UnsignedPhiUpperBound::new("7", 100))
        });
        let reflected = result.expect("source input must never panic");
        let error = reflected.expect_err("mutation must fail closed");
        assert!(error.span().is_some());
    }
}
