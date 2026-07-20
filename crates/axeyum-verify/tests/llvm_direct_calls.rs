//! ADR-0295 acceptance gates for opt-in checked direct-body LLVM calls.

use axeyum_ir::{Assignment, TermArena, TermId, Value, eval};
use axeyum_solver::{
    BmcOutcome, ProofOutcome, SafetyOutcome, SolverConfig, TransitionSystem, bounded_model_check,
    prove, prove_safety_k_induction,
};
use axeyum_verify::reflect::llvm::{
    loops::{
        DirectCallResolver, LoopReflectErrorKind, UnsignedPhiUpperBound,
        reflect_single_latch_loop_checked, reflect_single_latch_loop_with_direct_calls_checked,
    },
    syntax::{
        ParseErrorKind, ScalarInstructionKind, SemanticFlag, parse_function, parse_scalar_cfg,
        render_scalar_cfg,
    },
};
use sha2::{Digest, Sha256};
use std::fmt::Write as _;

const PAC_SOURCE: &str = include_str!("fixtures/llvm/clang21_glaurung_pac.c");
const PAC_MODULE: &str = include_str!("fixtures/llvm/clang21_glaurung_pac.ll");

fn sha256(bytes: &[u8]) -> String {
    let mut output = String::with_capacity(64);
    for byte in Sha256::digest(bytes) {
        write!(output, "{byte:02x}").expect("writing to a String cannot fail");
    }
    output
}

fn signed(value: u32) -> i32 {
    i32::from_ne_bytes(value.to_ne_bytes())
}

fn unsigned(value: i32) -> u32 {
    u32::from_ne_bytes(value.to_ne_bytes())
}

fn low_word(value: u64) -> u32 {
    let [a, b, c, d, _, _, _, _] = value.to_le_bytes();
    u32::from_le_bytes([a, b, c, d])
}

fn high_word(value: u64) -> u32 {
    let [_, _, _, _, e, f, g, h] = value.to_le_bytes();
    u32::from_le_bytes([e, f, g, h])
}

fn function<'a>(module: &'a str, name: &str) -> &'a str {
    let marker = format!("@{name}(");
    let marker_start = module
        .find(&marker)
        .unwrap_or_else(|| panic!("fixture has no function `{name}`"));
    let start = module[..marker_start]
        .rfind("define ")
        .expect("fixture function has a definition start");
    let relative_end = module[marker_start..]
        .find("\n}\n")
        .expect("fixture function has a closing brace");
    let end = marker_start + relative_end + 3;
    &module[start..end]
}

fn resolver() -> DirectCallResolver {
    DirectCallResolver::from_bodies(&[function(PAC_MODULE, "leaf")])
        .expect("the exact leaf body must satisfy the checked direct-call profile")
}

fn system(
    caller: &str,
    phi: &str,
    bound: u128,
) -> axeyum_verify::reflect::llvm::loops::CanonicalLoopSystem {
    reflect_single_latch_loop_with_direct_calls_checked(
        function(PAC_MODULE, caller),
        UnsignedPhiUpperBound::new(phi, bound),
        &resolver(),
    )
    .unwrap_or_else(|error| panic!("exact `{caller}` loop must reflect: {error}"))
}

fn proved(arena: &mut TermArena, goal: TermId) -> bool {
    matches!(
        prove(arena, &[], goal, &SolverConfig::default()).unwrap(),
        ProofOutcome::Proved(_)
    )
}

fn conjoin(arena: &mut TermArena, terms: &[TermId]) -> TermId {
    let mut result = arena.bool_const(true);
    for term in terms {
        result = arena.and(result, *term).unwrap();
    }
    result
}

fn expected_formulas(
    arena: &mut TermArena,
    pre: &[axeyum_ir::SymbolId],
    post: &[axeyum_ir::SymbolId],
    bound: u128,
) -> (TermId, TermId, TermId) {
    let zero = arena.bv_const(32, 0).unwrap();
    let one = arena.bv_const(32, 1).unwrap();
    let bound = arena.bv_const(32, bound).unwrap();
    let i = arena.var(pre[0]);
    let acc = arena.var(pre[1]);
    let n = arena.var(pre[2]);
    let post_i = arena.var(post[0]);
    let post_acc = arena.var(post[1]);
    let post_n = arena.var(post[2]);

    let init_i = arena.eq(i, zero).unwrap();
    let init_acc = arena.eq(acc, zero).unwrap();
    let init = arena.and(init_i, init_acc).unwrap();

    // Independent reconstruction of the exact compiler flags:
    // leaf: mul nsw; add nuw nsw. caller: add nsw. counter: add nuw nsw.
    let square = arena.bv_mul(i, i).unwrap();
    let square_smulo = arena.bv_smulo(i, i).unwrap();
    let square_defined = arena.not(square_smulo).unwrap();
    let leaf = arena.bv_add(square, one).unwrap();
    let leaf_overflow = [
        arena.bv_uaddo(square, one).unwrap(),
        arena.bv_saddo(square, one).unwrap(),
    ];
    let leaf_definedness = [
        arena.not(leaf_overflow[0]).unwrap(),
        arena.not(leaf_overflow[1]).unwrap(),
    ];
    let leaf_defined = conjoin(
        arena,
        &[square_defined, leaf_definedness[0], leaf_definedness[1]],
    );

    let next_acc = arena.bv_add(leaf, acc).unwrap();
    let acc_overflow = arena.bv_saddo(leaf, acc).unwrap();
    let acc_defined = arena.not(acc_overflow).unwrap();
    let next_i = arena.bv_add(i, one).unwrap();
    let counter_overflow = [
        arena.bv_uaddo(i, one).unwrap(),
        arena.bv_saddo(i, one).unwrap(),
    ];
    let counter_definedness = [
        arena.not(counter_overflow[0]).unwrap(),
        arena.not(counter_overflow[1]).unwrap(),
    ];
    let update_i = arena.eq(post_i, next_i).unwrap();
    let update_acc = arena.eq(post_acc, next_acc).unwrap();
    let keep_n = arena.eq(post_n, n).unwrap();
    let trans = conjoin(
        arena,
        &[
            leaf_defined,
            acc_defined,
            counter_definedness[0],
            counter_definedness[1],
            update_i,
            update_acc,
            keep_n,
        ],
    );
    let bad = arena.bv_ugt(acc, bound).unwrap();
    (init, trans, bad)
}

fn expected_step(i: u32, acc: u32) -> Option<(u32, u32)> {
    let square = unsigned(signed(i).checked_mul(signed(i))?);
    let leaf_unsigned = square.checked_add(1)?;
    let leaf_signed = signed(square).checked_add(1)?;
    if leaf_unsigned != unsigned(leaf_signed) {
        return None;
    }
    let next_acc = unsigned(signed(acc).checked_add(leaf_signed)?);
    let next_i_unsigned = i.checked_add(1)?;
    let next_i_signed = unsigned(signed(i).checked_add(1)?);
    (next_i_unsigned == next_i_signed).then_some((next_i_signed, next_acc))
}

fn assign_words(
    assignment: &mut Assignment,
    symbols: impl IntoIterator<Item = axeyum_ir::SymbolId>,
    values: impl IntoIterator<Item = u32>,
) {
    for (symbol, value) in symbols.into_iter().zip(values) {
        assignment.set(
            symbol,
            Value::Bv {
                width: 32,
                value: value.into(),
            },
        );
    }
}

fn concrete_compute(n: i32) -> Option<i32> {
    if n <= 0 {
        return Some(0);
    }
    let mut acc = 0_i32;
    for i in 0..n {
        let leaf = i.checked_mul(i)?.checked_add(1)?;
        acc = acc.checked_add(leaf)?;
    }
    Some(acc)
}

#[test]
fn exact_glaurung_provenance_call_shape_and_canonical_syntax_are_frozen() {
    assert_eq!(
        sha256(PAC_SOURCE.as_bytes()),
        "dfec0b80f38724b534c5aa9d2cfb699cbbfa33c434c10997b5274ea2c53f2cf4"
    );
    assert_eq!(
        sha256(PAC_MODULE.as_bytes()),
        "a9659be11de15eab708901a68a11479c816b900dd740d0c2ef2e37f02c618c00"
    );
    for (name, digest) in [
        (
            "leaf",
            "5543c27e5c872cd83ca32345a81191820885f4688d2d2e0884d91975247bf30b",
        ),
        (
            "compute",
            "7199a26798d7bb1e59a17f561bbe0628bd6a97c791a885e95f1c10f8c2ce74d4",
        ),
        (
            "main",
            "ee8941ca2380a2b3ab64b75be5021118e0af060923d37249414a95ef645beca3",
        ),
    ] {
        assert_eq!(sha256(function(PAC_MODULE, name).as_bytes()), digest);
    }

    let leaf = parse_scalar_cfg(&parse_function(function(PAC_MODULE, "leaf")).unwrap()).unwrap();
    let flags = leaf.blocks[0]
        .instructions
        .iter()
        .map(|instruction| match &instruction.kind {
            ScalarInstructionKind::Binary { flags, .. } => flags.clone(),
            kind => panic!("unexpected leaf instruction: {kind:?}"),
        })
        .collect::<Vec<_>>();
    assert_eq!(
        flags,
        vec![
            vec![SemanticFlag::Nsw],
            vec![SemanticFlag::Nuw, SemanticFlag::Nsw]
        ]
    );

    for caller in ["compute", "main"] {
        let cfg = parse_scalar_cfg(&parse_function(function(PAC_MODULE, caller)).unwrap()).unwrap();
        let call = cfg
            .blocks
            .iter()
            .flat_map(|block| &block.instructions)
            .find_map(|instruction| match &instruction.kind {
                ScalarInstructionKind::DirectCall {
                    tail,
                    result_width,
                    callee,
                    args,
                    ..
                } => Some((*tail, *result_width, callee, args)),
                _ => None,
            })
            .expect("caller retains one typed direct call");
        assert!(call.0);
        assert_eq!(call.1, 32);
        assert_eq!(call.2, "leaf");
        assert_eq!(call.3.len(), 1);
        assert!(call.3[0].noundef);
        let canonical = render_scalar_cfg(&cfg);
        assert!(canonical.contains("tail call i32 @\"leaf\"(i32 noundef"));
        let reparsed = parse_scalar_cfg(&parse_function(&canonical).unwrap()).unwrap();
        assert_eq!(canonical, render_scalar_cfg(&reparsed));
    }
}

#[test]
fn ordinary_calls_remain_rejected_and_exact_leaf_opt_in_admits_both_loops() {
    for (caller, phi) in [("compute", "7"), ("main", "6")] {
        let error = reflect_single_latch_loop_checked(
            function(PAC_MODULE, caller),
            UnsignedPhiUpperBound::new(phi, u128::from(u32::MAX >> 1)),
        )
        .unwrap_err();
        assert_eq!(error.kind(), LoopReflectErrorKind::UnsupportedCall);
        assert!(error.span().is_some());
        assert!(error.to_string().contains("@leaf"));

        let reflected = system(caller, phi, u128::from(u32::MAX >> 1));
        assert_eq!(reflected.function_name(), caller);
        assert_eq!(reflected.state_components().len(), 3);
        assert_eq!(reflected.state_component_index(phi), Some(1));
    }
    assert_eq!(resolver().callee_names(), vec!["leaf"]);
}

#[test]
fn automatic_call_value_definedness_and_transition_equal_independent_formulas() {
    for (caller, phi) in [("compute", "7"), ("main", "6")] {
        let system = system(caller, phi, u128::from(u32::MAX >> 1));
        let mut arena = TermArena::new();
        let pre = system.state_vars(&mut arena, 0).unwrap();
        let post = system.state_vars(&mut arena, 1).unwrap();
        let actual_init = system.init(&mut arena, &pre).unwrap();
        let actual_trans = system.trans(&mut arena, &pre, &post).unwrap();
        let actual_bad = system.bad(&mut arena, &pre).unwrap();
        let (expected_init, expected_trans, expected_bad) =
            expected_formulas(&mut arena, &pre, &post, u128::from(u32::MAX >> 1));
        for (actual, expected) in [
            (actual_init, expected_init),
            (actual_trans, expected_trans),
            (actual_bad, expected_bad),
        ] {
            let equivalent = arena.eq(actual, expected).unwrap();
            assert!(proved(&mut arena, equivalent), "{caller} formula diverged");
        }
    }
}

#[test]
fn callee_immediate_ub_is_eager_but_unobserved_return_poison_remains_lazy() {
    let caller = r"
define i8 @caller(i8 %n) {
  br label %loop
loop:
  %x = phi i8 [ 0, %0 ], [ %next, %loop ]
  %ignored = call i8 @callee(i8 noundef %x)
  %next = add i8 %x, 1
  %done = icmp eq i8 %next, %n
  br i1 %done, label %exit, label %loop
exit:
  ret i8 %x
}
";
    let transition = |callee: &str, pre_value: u8, post_value: u8| {
        let resolver = DirectCallResolver::from_bodies(&[callee]).unwrap();
        let system = reflect_single_latch_loop_with_direct_calls_checked(
            caller,
            UnsignedPhiUpperBound::new("x", u8::MAX.into()),
            &resolver,
        )
        .unwrap();
        let mut arena = TermArena::new();
        let pre = system.state_vars(&mut arena, 0).unwrap();
        let post = system.state_vars(&mut arena, 1).unwrap();
        let trans = system.trans(&mut arena, &pre, &post).unwrap();
        let mut assignment = Assignment::new();
        for (symbol, value) in pre
            .iter()
            .chain(&post)
            .copied()
            .zip([pre_value, 0, post_value, 0])
        {
            assignment.set(
                symbol,
                Value::Bv {
                    width: 8,
                    value: value.into(),
                },
            );
        }
        eval(&arena, trans, &assignment).unwrap() == Value::Bool(true)
    };

    let immediate = "define i8 @callee(i8 %x) {\n%r = udiv i8 1, %x\nret i8 %r\n}\n";
    assert!(
        !transition(immediate, 0, 1),
        "division by zero in a called body is immediate UB even when its result is unused"
    );

    let poison = "define i8 @callee(i8 %x) {\n%r = add nuw i8 %x, 1\nret i8 %r\n}\n";
    assert!(
        transition(poison, u8::MAX, 0),
        "an unobserved poison return without a noundef result boundary is not immediate UB"
    );
}

#[test]
fn direct_call_transition_fuzz_has_zero_disagreements_over_100000_tuples() {
    const CORNERS: &[(u32, u32)] = &[
        (0, 0),
        (1, 0),
        (46_340, 0),
        (46_341, 0),
        (0, 0x7fff_ffff),
        (u32::MAX, 0),
        (0x7fff_ffff, 0),
        (0x8000_0000, 0),
    ];
    let mut total = 0_u64;
    let mut true_rows = 0_u64;
    let mut mul_overflow = 0_u64;
    let mut caller_add_overflow = 0_u64;
    let mut counter_overflow = 0_u64;
    for (caller, phi, salt) in [
        ("compute", "7", 0x91c5_a11d_d1ec_7001_u64),
        ("main", "6", 0x91c5_a11d_d1ec_7002_u64),
    ] {
        let system = system(caller, phi, u128::from(u32::MAX >> 1));
        let mut arena = TermArena::new();
        let pre = system.state_vars(&mut arena, 0).unwrap();
        let post = system.state_vars(&mut arena, 1).unwrap();
        let transition = system.trans(&mut arena, &pre, &post).unwrap();
        let mut seed = salt;
        for case in 0..50_000_usize {
            seed = seed
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let random_i = low_word(seed);
            seed = seed
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let random_acc = low_word(seed);
            let (i, acc) = if let Some(&corner) = CORNERS.get(case) {
                corner
            } else {
                (random_i, random_acc)
            };
            seed = seed
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let n = low_word(seed);
            let expected_step = expected_step(i, acc);
            mul_overflow += u64::from(signed(i).checked_mul(signed(i)).is_none());
            if let Some(square) = signed(i).checked_mul(signed(i))
                && let Some(leaf) = square.checked_add(1)
            {
                caller_add_overflow += u64::from(signed(acc).checked_add(leaf).is_none());
            }
            counter_overflow +=
                u64::from(i.checked_add(1).is_none() || signed(i).checked_add(1).is_none());

            seed = seed
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let random_post = (low_word(seed), high_word(seed), n ^ 0x55aa_aa55);
            let (post_i, post_acc, post_n) = if case % 2 == 0 {
                expected_step.map_or(random_post, |(next_i, next_acc)| (next_i, next_acc, n))
            } else {
                random_post
            };
            let expected = expected_step == Some((post_i, post_acc)) && post_n == n;
            let mut assignment = Assignment::new();
            assign_words(
                &mut assignment,
                pre.iter().chain(&post).copied(),
                [i, acc, n, post_i, post_acc, post_n],
            );
            let actual = eval(&arena, transition, &assignment).unwrap() == Value::Bool(true);
            assert_eq!(actual, expected, "{caller} tuple {case} disagreed");
            total += 1;
            true_rows += u64::from(actual);
        }
    }
    assert_eq!(total, 100_000);
    assert!(true_rows > 0);
    assert!(mul_overflow > 0);
    assert!(caller_add_overflow > 0);
    assert!(counter_overflow > 0);
}

#[test]
fn safety_bmc_and_reachable_states_are_source_replayed_separately() {
    for (caller, phi) in [("compute", "7"), ("main", "6")] {
        // Exercise both safety APIs with the type-total upper bound. The
        // nontrivial semantics claim lives in the independent formula proof
        // and 100,000-tuple gate above; asking k-induction to rediscover signed
        // nonlinear range facts would make this regression test search-bound.
        let safe = system(caller, phi, u128::from(u32::MAX));
        let mut arena = TermArena::new();
        let unbounded = prove_safety_k_induction(&mut arena, &safe, 1, &SolverConfig::default())
            .expect("solver should not hard-error");
        assert!(
            matches!(unbounded, SafetyOutcome::Safe { .. }),
            "{caller} BV32 value must respect its type-total bound: {unbounded:?}"
        );

        let mut arena = TermArena::new();
        let bounded = bounded_model_check(&mut arena, &safe, 3, &SolverConfig::default())
            .expect("solver should not hard-error");
        assert!(matches!(
            bounded,
            BmcOutcome::UnreachableWithinBound { bound: 3 }
        ));

        let reachable = system(caller, phi, 0);
        let mut arena = TermArena::new();
        let outcome = bounded_model_check(&mut arena, &reachable, 2, &SolverConfig::default())
            .expect("solver should not hard-error");
        let BmcOutcome::Reachable { steps, .. } = outcome else {
            panic!("{caller} abstract recurrence must reach acc > 0");
        };
        assert_eq!(steps, 1);
    }
    assert_eq!(concrete_compute(1), Some(1));
    assert_eq!(concrete_compute(1).map(|value| value & 0xff), Some(1));
}

#[test]
fn direct_call_boundary_mutations_fail_closed_or_refute_semantic_equivalence() {
    let compute = function(PAC_MODULE, "compute");
    let leaf = function(PAC_MODULE, "leaf");
    let property = || UnsignedPhiUpperBound::new("7", u128::from(u32::MAX >> 1));

    let duplicate = DirectCallResolver::from_bodies(&[leaf, leaf]).unwrap_err();
    assert_eq!(duplicate.kind(), LoopReflectErrorKind::UnsupportedCall);
    assert!(duplicate.span().is_some());

    for (mutation, detail) in [
        (compute.replace("@leaf", "@missing"), "no supplied"),
        (
            compute.replace("@leaf(i32 noundef %6)", "@leaf()"),
            "supplies 0 arguments",
        ),
        (
            compute.replace("@leaf(i32 noundef %6)", "@leaf(i16 noundef %6)"),
            "argument 0 declares i16",
        ),
        (
            compute.replace("call i32 @leaf", "call i16 @leaf"),
            "declares i16",
        ),
        (
            compute.replace("i32 noundef %6", "i32 %6"),
            "must retain the `noundef`",
        ),
    ] {
        let error =
            reflect_single_latch_loop_with_direct_calls_checked(&mutation, property(), &resolver())
                .unwrap_err();
        assert_eq!(error.kind(), LoopReflectErrorKind::UnsupportedCall);
        assert!(error.span().is_some());
        assert!(error.to_string().contains(detail), "{error}");
    }

    for body in [
        "define void @leaf(i32 %x) {\nret void\n}\n",
        "define i32 @leaf(ptr %x) {\nret i32 0\n}\n",
        "define i32 @leaf(i32 %x) {\n%r = call i32 @leaf(i32 noundef %x)\nret i32 %r\n}\n",
        "define i32 @leaf(i32 %x) {\n%r = load i32, ptr %p\nret i32 %r\n}\n",
    ] {
        let error = DirectCallResolver::from_bodies(&[body]).unwrap_err();
        assert!(matches!(
            error.kind(),
            LoopReflectErrorKind::UnsupportedCall | LoopReflectErrorKind::Syntax
        ));
        assert!(error.span().is_some());
    }

    let variadic =
        DirectCallResolver::from_bodies(&["define i32 @leaf(i32 %x, ...) {\nret i32 %x\n}\n"])
            .unwrap_err();
    assert_eq!(variadic.kind(), LoopReflectErrorKind::Syntax);
    let indirect = compute.replace("@leaf", "%fp");
    let error = parse_scalar_cfg(&parse_function(&indirect).unwrap()).unwrap_err();
    assert_eq!(error.kind(), ParseErrorKind::MalformedInstruction);
    let attributed = compute.replace("i32 noundef %6", "i32 nonnull %6");
    let error = parse_scalar_cfg(&parse_function(&attributed).unwrap()).unwrap_err();
    assert_eq!(error.kind(), ParseErrorKind::UnsupportedSemantics);

    let mutated_leaf = leaf.replace("%2, 1", "%2, 2");
    let mutated = DirectCallResolver::from_bodies(&[&mutated_leaf]).unwrap();
    let mutated_system =
        reflect_single_latch_loop_with_direct_calls_checked(compute, property(), &mutated).unwrap();
    let mut arena = TermArena::new();
    let pre = mutated_system.state_vars(&mut arena, 0).unwrap();
    let post = mutated_system.state_vars(&mut arena, 1).unwrap();
    let actual = mutated_system.trans(&mut arena, &pre, &post).unwrap();
    let (_, expected, _) = expected_formulas(&mut arena, &pre, &post, u128::from(u32::MAX >> 1));
    let equivalent = arena.eq(actual, expected).unwrap();
    assert!(matches!(
        prove(&mut arena, &[], equivalent, &SolverConfig::default()).unwrap(),
        ProofOutcome::Disproved(_)
    ));
}
