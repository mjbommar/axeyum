//! ADR-2140: which model a `sat` returns is a POLICY, and the shipped policy is
//! today's search.
//!
//! Three claims, each with the test that dies when it is false:
//!
//! 1. **`Any` is byte-for-byte the shipped search.** Every committed `QF_BV`
//!    fixture is solved under `SolverConfig::default()` (the path the front door
//!    takes) and under an explicit `ModelPreference::Any`, and every verdict AND
//!    every model is compared. `the_identity_is_not_vacuous` proves the
//!    comparison can fail: `PreferZero` moves at least one of those models, so
//!    flipping `DEFAULT_MODEL_PREFERENCE` kills the identity and nothing else.
//!    (`PreferZero` moves models through its replay-checked shrink; the SAT-core
//!    forced phase ships off and is exercised here only through its lever.)
//! 2. **A preference never changes a verdict**, and every `sat` under every
//!    preference still replays against the original assertions.
//! 3. **Same input, same policy, same model** -- asserted by running twice.
//!
//! The population is derived from the corpus directories, never from a list,
//! so a fixture added tomorrow is compared tomorrow.
#![cfg(feature = "full")]

use std::path::{Path, PathBuf};
use std::time::Duration;

use axeyum_ir::Value;
use axeyum_solver::smtlib::{
    LEAST_WITNESS_BOUNDS, SmtLibSolved, solve_smtlib_least_witness, solve_smtlib_with_model,
};
use axeyum_solver::{
    CheckResult, DEFAULT_MODEL_PREFERENCE, ModelPreference, SmtLibResponse, SolverConfig,
    check_model, solve_smtlib_session,
};

/// Per-file budget. The fixtures are the committed SMALL corpora: measured
/// 2026-09-16 in release, every one decides (or declines) in <= 110 ms.
/// `corpus/qfbv-curated` is deliberately NOT in the population -- seven of its
/// files are `unknown` at 5 s and would turn this suite into a budget test.
const BUDGET: Duration = Duration::from_secs(5);

fn corpus_dirs() -> Vec<PathBuf> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus");
    ["regression/qf_bv", "regression/cvc5/qf_bv", "micro"]
        .iter()
        .map(|d| root.join(d))
        .collect()
}

fn collect(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    let mut entries: Vec<_> = entries.flatten().map(|e| e.path()).collect();
    entries.sort();
    for path in entries {
        if path.is_dir() {
            collect(&path, out);
        } else if path.extension().is_some_and(|e| e == "smt2") {
            out.push(path);
        }
    }
}

/// Every committed `QF_BV` fixture: `(set-logic QF_BV)` and no scoping, so
/// the flat view the front door decides is the whole script.
fn qf_bv_fixtures() -> Vec<(String, String)> {
    let mut files = Vec::new();
    for dir in corpus_dirs() {
        collect(&dir, &mut files);
    }
    let mut out = Vec::new();
    for path in files {
        let Ok(text) = std::fs::read_to_string(&path) else {
            continue;
        };
        if !text.contains("(set-logic QF_BV)") {
            continue;
        }
        if ["(push", "(pop", "reset-assertions", "(reset"]
            .iter()
            .any(|kw| text.contains(kw))
        {
            continue;
        }
        out.push((path.display().to_string(), text));
    }
    assert!(
        out.len() >= 30,
        "expected the committed QF_BV corpora to hold >= 30 flat fixtures, found {}",
        out.len()
    );
    out
}

/// Solves one fixture, or `None` on a FRONT-END gap (a parse error is a
/// coverage gap, not a model-preference finding; `corpus_regression` skips
/// the same way). Any other error is a failure.
fn solve_or_skip(name: &str, text: &str, config: &SolverConfig) -> Option<SmtLibSolved> {
    match solve_smtlib_with_model(text, config) {
        Ok(solved) => Some(solved),
        Err(axeyum_solver::SolverError::Parse(_)) => None,
        Err(e) => panic!("{name}: {e}"),
    }
}

fn config(preference: ModelPreference) -> SolverConfig {
    SolverConfig::default()
        .with_timeout(BUDGET)
        .with_model_preference(preference)
}

/// The test must run with the lever UNSET: with `AXEYUM_MODEL_PREFERENCE=zero`
/// in the environment `SolverConfig::default()` IS the zero arm, and the
/// identity below would be measuring the lever rather than the default.
fn require_lever_unset() {
    for var in ["AXEYUM_MODEL_PREFERENCE", "AXEYUM_MODEL_PREFERENCE_PHASE"] {
        if let Ok(value) = std::env::var(var) {
            panic!(
                "{var}={value:?} is set; this suite measures the SHIPPED default and must run \
                 with the lever unset (`env -u {var}`)"
            );
        }
    }
}

fn verdict(result: &CheckResult) -> &'static str {
    match result {
        CheckResult::Sat(_) => "sat",
        CheckResult::Unsat => "unsat",
        CheckResult::Unknown(_) => "unknown",
    }
}

fn replays(solved: &SmtLibSolved) -> bool {
    match (&solved.outcome.result, &solved.model) {
        (CheckResult::Sat(_), Some(model)) => {
            check_model(&solved.script.arena, &solved.assertions, model).unwrap_or(false)
        }
        _ => false,
    }
}

/// Claim 1. `Any` is the default, and the default is the shipped search: the
/// two configurations return the same verdict and the same model on every
/// fixture. The count of comparisons is printed so a run that compared nothing
/// is visible.
#[test]
fn any_is_the_shipped_search_on_every_qf_bv_fixture() {
    require_lever_unset();
    assert_eq!(
        DEFAULT_MODEL_PREFERENCE,
        ModelPreference::Any,
        "the shipped default must be `Any` -- a moved default is an ADR, not a diff"
    );
    let mut compared = 0usize;
    let mut sat = 0usize;
    let mut parse_skipped = 0usize;
    for (name, text) in qf_bv_fixtures() {
        let Some(shipped) =
            solve_or_skip(&name, &text, &SolverConfig::default().with_timeout(BUDGET))
        else {
            parse_skipped += 1;
            continue;
        };
        let any = solve_smtlib_with_model(&text, &config(ModelPreference::Any))
            .unwrap_or_else(|e| panic!("{name}: {e}"));
        assert_eq!(
            shipped.outcome.result, any.outcome.result,
            "{name}: `Any` and the shipped default disagree on the verdict or the model"
        );
        assert_eq!(shipped.model, any.model, "{name}: the flat models differ");
        compared += 1;
        if matches!(any.outcome.result, CheckResult::Sat(_)) {
            sat += 1;
        }
    }
    println!(
        "model_preference_2140: identity compared={compared} sat={sat} \
         parse_skipped={parse_skipped}"
    );
    assert!(
        sat >= 5,
        "only {sat} sat fixtures -- the identity compared too few models"
    );
}

/// The identity above can fail: `PreferZero` returns a DIFFERENT model on at
/// least one fixture, so a default flipped to `PreferZero` is caught by
/// `any_is_the_shipped_search_on_every_qf_bv_fixture`. Without this, that
/// test would be a comparison of a value with itself.
///
/// Also claim 2 for `PreferZero`: verdicts never move, every `sat` replays.
#[test]
fn the_identity_is_not_vacuous_and_prefer_zero_only_moves_models() {
    require_lever_unset();
    let mut moved = 0usize;
    let mut sat = 0usize;
    for (name, text) in qf_bv_fixtures() {
        let Some(any) = solve_or_skip(&name, &text, &config(ModelPreference::Any)) else {
            continue;
        };
        let zero = solve_smtlib_with_model(&text, &config(ModelPreference::PreferZero))
            .unwrap_or_else(|e| panic!("{name}: {e}"));
        assert_eq!(
            verdict(&any.outcome.result),
            verdict(&zero.outcome.result),
            "{name}: a model PREFERENCE moved the verdict"
        );
        if matches!(zero.outcome.result, CheckResult::Sat(_)) {
            sat += 1;
            if zero.model.is_some() {
                assert!(
                    replays(&zero),
                    "{name}: the PreferZero model does not replay"
                );
            }
            if any.model != zero.model {
                moved += 1;
            }
        }
    }
    println!("model_preference_2140: prefer_zero sat={sat} models_moved={moved}");
    assert!(
        moved >= 1,
        "PreferZero moved no model on {sat} sat fixtures: the identity test could not fail"
    );
}

/// Claim 3: same input, same policy, same model -- twice, under every policy.
#[test]
fn same_input_same_policy_same_model() {
    require_lever_unset();
    let mut checked = 0usize;
    for (name, text) in qf_bv_fixtures() {
        for preference in [
            ModelPreference::Any,
            ModelPreference::PreferZero,
            ModelPreference::LeastUnsigned,
        ] {
            let Some(first) = solve_or_skip(&name, &text, &config(preference)) else {
                continue;
            };
            let second = solve_smtlib_with_model(&text, &config(preference))
                .unwrap_or_else(|e| panic!("{name}: {e}"));
            assert_eq!(
                first.outcome.result, second.outcome.result,
                "{name} under {preference:?}: two runs differ"
            );
            assert_eq!(
                first.model, second.model,
                "{name} under {preference:?}: models differ"
            );
            checked += 1;
        }
    }
    println!("model_preference_2140: determinism pairs={checked}");
    assert!(checked >= 60);
}

/// Claim 2 for `LeastUnsigned` over the corpus: the verdict is the unbounded
/// one, and the (possibly bounded) model replays against the ORIGINAL
/// assertions.
#[test]
fn least_unsigned_never_moves_a_verdict_and_every_model_replays() {
    require_lever_unset();
    let mut sat = 0usize;
    for (name, text) in qf_bv_fixtures() {
        let Some(any) = solve_or_skip(&name, &text, &config(ModelPreference::Any)) else {
            continue;
        };
        let least = solve_smtlib_with_model(&text, &config(ModelPreference::LeastUnsigned))
            .unwrap_or_else(|e| panic!("{name}: {e}"));
        assert_eq!(
            verdict(&any.outcome.result),
            verdict(&least.outcome.result),
            "{name}: LeastUnsigned moved the verdict"
        );
        if matches!(least.outcome.result, CheckResult::Sat(_)) && least.model.is_some() {
            sat += 1;
            assert!(
                replays(&least),
                "{name}: the LeastUnsigned model does not replay"
            );
        }
    }
    println!("model_preference_2140: least_unsigned replayed sat={sat}");
    assert!(sat >= 5);
}

/// The SAT-core mechanism, observed through the one-shot BV backend with no
/// preprocessing in the way: `(a | b) & (a | -b)` forces `a`; the shipped
/// search decides `b` at its SAVED phase from the retracted `a = false` branch
/// (`true`), and the forced phase decides it `false`. Run in a CHILD process
/// with `AXEYUM_MODEL_PREFERENCE_PHASE=on`, because the SAT-core half ships
/// off and the lever is read once per process; `phase_probe` is the child and
/// is inert without the variable. A broken plumb between `SolverConfig` and
/// `Cdcl.forced_phase` fails HERE and not only in the corpus counts.
#[test]
fn the_forced_phase_reaches_the_one_shot_backend_when_on() {
    let exe = std::env::current_exe().expect("test executable");
    let status = std::process::Command::new(&exe)
        .args(["--exact", "phase_probe", "--quiet"])
        .env("AXEYUM_MODEL_PREFERENCE_PHASE", "on")
        // Silenced for the same reason as in the lever test below: the
        // child's harness lines would be counted by a mutation harness.
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status()
        .expect("spawn the probe");
    assert!(
        status.success(),
        "the forced phase did not reach the one-shot backend"
    );
}

/// The child half of the test above. Inert unless `AXEYUM_MODEL_PREFERENCE_PHASE=on`.
#[test]
fn phase_probe() {
    use axeyum_ir::TermArena;
    use axeyum_solver::{SatBvBackend, SolverBackend};
    if std::env::var("AXEYUM_MODEL_PREFERENCE_PHASE").as_deref() != Ok("on") {
        return;
    }
    let mut arena = TermArena::new();
    let a = arena.bool_var("a").unwrap();
    let b = arena.bool_var("b").unwrap();
    let nb = arena.not(b).unwrap();
    let c1 = arena.or(a, b).unwrap();
    let c2 = arena.or(a, nb).unwrap();
    let b_sym = arena.find_symbol("b").unwrap();
    let value_of_b = |preference: ModelPreference| -> bool {
        let mut backend = SatBvBackend::new();
        let config = SolverConfig::new().with_model_preference(preference);
        match backend.check(&arena, &[c1, c2], &config).expect("check") {
            CheckResult::Sat(model) => match model.get(b_sym) {
                Some(Value::Bool(v)) => v,
                other => panic!("b is not a Bool: {other:?}"),
            },
            other => panic!("expected sat, got {other:?}"),
        }
    };
    assert!(
        value_of_b(ModelPreference::Any),
        "the shipped search keeps the retracted `b = true` through phase saving"
    );
    assert!(
        !value_of_b(ModelPreference::PreferZero),
        "PreferZero with the phase on must decide the free `b` at false"
    );
}

/// The warm engine finishes its model the same way: on the three-witness
/// shape, `Any` returns whatever the search found and `PreferZero` the
/// smallest reachable `y` (`0xF4`), with `check_assuming` still replaying.
#[test]
fn prefer_zero_reaches_the_warm_engine() {
    use axeyum_ir::TermArena;
    use axeyum_solver::IncrementalBvSolver;
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 8).unwrap();
    let y = arena.bv_var("y", 8).unwrap();
    let z = arena.bv_var("z", 8).unwrap();
    let c = |arena: &mut TermArena, v: u128| arena.bv_const(8, v).unwrap();
    let x5 = c(&mut arena, 5);
    let z7 = c(&mut arena, 7);
    let k10 = c(&mut arena, 0x10);
    let kf0 = c(&mut arena, 0xf0);
    let k3 = c(&mut arena, 3);
    let eq_x = arena.eq(x, x5).unwrap();
    let eq_z = arena.eq(z, z7).unwrap();
    let below_low = arena.bv_ult(y, k10).unwrap();
    let above_low = arena.bv_uge(y, k10).unwrap();
    let below_high = arena.bv_ult(y, kf0).unwrap();
    let above_high = arena.bv_uge(y, kf0).unwrap();
    let a1 = arena.or(eq_x, below_low).unwrap();
    let a2 = arena.or(eq_x, above_low).unwrap();
    let a3 = arena.or(eq_z, below_high).unwrap();
    let a4 = arena.or(eq_z, above_high).unwrap();
    let xy = arena.bv_add(x, y).unwrap();
    let xyz = arena.bv_add(xy, z).unwrap();
    let a5 = arena.bv_ult(xyz, k3).unwrap();
    let y_sym = arena.find_symbol("y").unwrap();
    let value_of_y = |preference: ModelPreference| -> u128 {
        let mut warm =
            IncrementalBvSolver::with_config(SolverConfig::new().with_model_preference(preference));
        for a in [a1, a2, a3, a4] {
            warm.assert(&arena, a).unwrap();
        }
        match warm.check_assuming(&arena, &[a5]).expect("check") {
            CheckResult::Sat(model) => match model.get(y_sym) {
                Some(Value::Bv { value, .. }) => value,
                other => panic!("y is not a bit-vector: {other:?}"),
            },
            other => panic!("expected sat, got {other:?}"),
        }
    };
    let any = value_of_y(ModelPreference::Any);
    assert!((0xf4..=0xf6).contains(&any), "Any returned y={any:#x}");
    assert_eq!(value_of_y(ModelPreference::PreferZero), 0xf4);
    assert_eq!(value_of_y(ModelPreference::LeastUnsigned), 0xf4);
}

fn bv_value(solved: &SmtLibSolved, name: &str) -> u128 {
    let model = solved.model.as_ref().expect("a flat model");
    let symbol = solved
        .script
        .model_symbols
        .iter()
        .copied()
        .find(|&s| solved.script.arena.symbol(s).0 == name)
        .unwrap_or_else(|| panic!("no declared `{name}`"));
    match model.get(symbol) {
        Some(Value::Bv { value, .. }) => value,
        other => panic!("`{name}` is not a bit-vector value: {other:?}"),
    }
}

/// The 32-bit two's-complement magnitude of `v`.
fn magnitude32(v: u128) -> u128 {
    if v >= 1 << 31 { (1u128 << 32) - v } else { v }
}

const WRAP_ADD: &str = "(set-logic QF_BV)
(declare-const a (_ BitVec 32))
(declare-const b (_ BitVec 32))
(assert (bvult (bvadd a b) a))
(check-sat)
";

/// The defects example's first shape: `a + b < a` wraps. The unbounded
/// search returns SOME wrap; the ladder's first rung returns one a reader can
/// check by hand -- `a = 0xFFFFFFFF, b = 1` or its mirror.
#[test]
fn least_witness_finds_the_magnitude_one_wrap() {
    require_lever_unset();
    let witness = solve_smtlib_least_witness(WRAP_ADD, &[], &config(ModelPreference::Any))
        .expect("front door");
    assert!(matches!(witness.solved.outcome.result, CheckResult::Sat(_)));
    assert_eq!(witness.bound, Some(1), "the wrap has a magnitude-1 witness");
    let (a, b) = (
        bv_value(&witness.solved, "a"),
        bv_value(&witness.solved, "b"),
    );
    assert!(
        magnitude32(a) <= 1 && magnitude32(b) <= 1,
        "a={a:#x} b={b:#x}"
    );
    assert!(
        (a == 0xFFFF_FFFF && b == 1) || (a == 1 && b == 0xFFFF_FFFF),
        "the only magnitude-1 wraps are (-1, 1) and (1, -1); got a={a:#x} b={b:#x}"
    );
    assert!(
        replays(&witness.solved),
        "the bounded model must replay against the original"
    );
}

const SIGNED_CHECK_BYPASS: &str = "(set-logic QF_BV)
(declare-const len (_ BitVec 32))
(assert (bvsle len (_ bv256 32)))
(assert (bvugt len (_ bv256 32)))
(check-sat)
";

/// The defects example's second shape: a `len > 256` check passes signed and
/// is bypassed unsigned. The witness is `len = -1`.
#[test]
fn least_witness_finds_the_negative_length() {
    require_lever_unset();
    let witness =
        solve_smtlib_least_witness(SIGNED_CHECK_BYPASS, &["len"], &config(ModelPreference::Any))
            .expect("front door");
    assert_eq!(witness.bound, Some(1));
    assert_eq!(bv_value(&witness.solved, "len"), 0xFFFF_FFFF, "len = -1");
    assert!(replays(&witness.solved));
}

/// A witness above every rung comes back unbounded, with the bound reported
/// as `None` -- the ladder reports what it did, never a bound it did not reach.
#[test]
fn least_witness_falls_back_to_the_unbounded_model() {
    require_lever_unset();
    let script = "(set-logic QF_BV)
(declare-const x (_ BitVec 32))
(assert (= x (_ bv100000 32)))
(check-sat)
";
    let witness =
        solve_smtlib_least_witness(script, &[], &config(ModelPreference::Any)).expect("front door");
    assert_eq!(witness.bound, None);
    assert_eq!(bv_value(&witness.solved, "x"), 100_000);
    assert!(LEAST_WITNESS_BOUNDS.iter().all(|&b| b < 100_000));
}

/// Bounding a SUBSET: only `a` is bounded, so `b` is free to be large.
#[test]
fn least_witness_honors_the_symbol_subset() {
    require_lever_unset();
    let witness = solve_smtlib_least_witness(WRAP_ADD, &["a"], &config(ModelPreference::Any))
        .expect("front door");
    assert_eq!(witness.bound, Some(1));
    assert!(magnitude32(bv_value(&witness.solved, "a")) <= 1);
    assert!(replays(&witness.solved));
}

/// `unsat` and `unknown` pass through every policy untouched, with no bound.
#[test]
fn unsat_passes_through_every_policy() {
    require_lever_unset();
    let script = "(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (bvult x (_ bv0 8)))
(check-sat)
";
    for preference in [
        ModelPreference::Any,
        ModelPreference::PreferZero,
        ModelPreference::LeastUnsigned,
    ] {
        let solved = solve_smtlib_with_model(script, &config(preference)).expect("front door");
        assert_eq!(solved.outcome.result, CheckResult::Unsat, "{preference:?}");
    }
    let witness =
        solve_smtlib_least_witness(script, &[], &config(ModelPreference::Any)).expect("front door");
    assert_eq!(witness.solved.outcome.result, CheckResult::Unsat);
    assert_eq!(witness.bound, None);
}

fn model_text(responses: &[SmtLibResponse]) -> String {
    responses
        .iter()
        .find_map(|r| match r {
            SmtLibResponse::Model(text) => Some(text.clone()),
            _ => None,
        })
        .expect("a get-model response")
}

/// `(set-option :model-preference least-unsigned)` in a session: `get-model`
/// answers with the ladder's witness.
#[test]
fn session_option_least_unsigned_changes_get_model() {
    require_lever_unset();
    let script = format!(
        "(set-option :model-preference least-unsigned)\n{SIGNED_CHECK_BYPASS}(get-model)\n"
    );
    let responses = solve_smtlib_session(&script, &config(ModelPreference::Any)).expect("session");
    let model = model_text(&responses);
    assert!(
        model.contains("#xffffffff") || model.contains("#b11111111111111111111111111111111"),
        "expected `len = -1` under least-unsigned, got:\n{model}"
    );
}

/// The option is honored (a `success` under `:print-success`), and a value
/// outside the three is an ERROR naming the option -- not `unsupported`, which
/// would say the option itself is not honored.
#[test]
fn session_option_is_acknowledged_and_a_bad_value_is_an_error() {
    require_lever_unset();
    let script = "(set-option :print-success true)
(set-option :model-preference zero)
(set-option :model-preference any)
(set-option :model-preference least-unsigned)
(set-option :model-preference sideways)
";
    let responses = solve_smtlib_session(script, &SolverConfig::new()).expect("session");
    let kinds: Vec<&str> = responses
        .iter()
        .map(|r| match r {
            SmtLibResponse::Success => "success",
            SmtLibResponse::Error { message, .. } => {
                assert!(message.contains(":model-preference"), "{message}");
                assert!(message.contains("sideways"), "{message}");
                "error"
            }
            SmtLibResponse::Unsupported { .. } => "unsupported",
            _ => "other",
        })
        .collect();
    assert_eq!(kinds, ["success", "success", "success", "success", "error"]);
}

/// The three spellings, round-tripped.
#[test]
fn spellings_round_trip() {
    require_lever_unset();
    for preference in [
        ModelPreference::Any,
        ModelPreference::PreferZero,
        ModelPreference::LeastUnsigned,
    ] {
        assert_eq!(
            ModelPreference::parse(preference.as_str()),
            Some(preference)
        );
    }
    assert_eq!(
        ModelPreference::parse("prefer-zero"),
        Some(ModelPreference::PreferZero)
    );
    assert_eq!(ModelPreference::parse(""), None);
    assert_eq!(ModelPreference::parse("ZERO"), None);
    // The SAT-core half ships OFF: no preference forces the phase unless the
    // process lever says so (`the_env_lever_is_read_and_a_malformed_value_is_refused`).
    assert_eq!(ModelPreference::Any.forced_phase(), None);
    assert_eq!(ModelPreference::PreferZero.forced_phase(), None);
    assert_eq!(ModelPreference::LeastUnsigned.forced_phase(), None);
    assert!(!ModelPreference::Any.finishes_model());
    assert!(ModelPreference::PreferZero.finishes_model());
    assert!(ModelPreference::LeastUnsigned.finishes_model());
}

/// The lever, exercised in a CHILD process because the read is once-per-process
/// and setting the environment in-process is `unsafe` in edition 2024.
///
/// `env_probe` below is the child: a no-op when the variable is unset (so it is
/// inert in the ordinary run), and an assertion about `SolverConfig::default()`
/// when it is set. This parent runs it three times -- `zero`, `least-unsigned`,
/// and a malformed value that must make the child FAIL, because a malformed
/// lever that quietly ran the default arm is the failure the lever contract
/// exists to prevent.
#[test]
fn the_env_lever_is_read_and_a_malformed_value_is_refused() {
    let exe = std::env::current_exe().expect("test executable");
    let run = |value: &str| -> bool {
        std::process::Command::new(&exe)
            .args(["--exact", "env_probe", "--quiet"])
            .env("AXEYUM_MODEL_PREFERENCE", value)
            // The child's own harness lines (`running 1 test`, `test result:`)
            // are silenced: a mutation harness reading this suite's output
            // counts them as extra test binaries and extra deaths, and reports
            // the run INCONSISTENT. The child's exit status is the finding.
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .status()
            .expect("spawn the probe")
            .success()
    };
    assert!(run("zero"), "AXEYUM_MODEL_PREFERENCE=zero was not honored");
    assert!(
        run("least-unsigned"),
        "AXEYUM_MODEL_PREFERENCE=least-unsigned was not honored"
    );
    assert!(run("any"), "AXEYUM_MODEL_PREFERENCE=any was not honored");
    assert!(
        run("sideways"),
        "AXEYUM_MODEL_PREFERENCE=sideways ran the default arm instead of refusing"
    );
    // The second lever: `AXEYUM_MODEL_PREFERENCE_PHASE=off` keeps the shrink
    // and drops the SAT-core half; a malformed value refuses.
    let run_phase = |value: &str| -> bool {
        std::process::Command::new(&exe)
            .args(["--exact", "env_probe", "--quiet"])
            .env("AXEYUM_MODEL_PREFERENCE", "zero")
            .env("AXEYUM_MODEL_PREFERENCE_PHASE", value)
            // The child's own harness lines (`running 1 test`, `test result:`)
            // are silenced: a mutation harness reading this suite's output
            // counts them as extra test binaries and extra deaths, and reports
            // the run INCONSISTENT. The child's exit status is the finding.
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .status()
            .expect("spawn the probe")
            .success()
    };
    assert!(
        run_phase("off"),
        "AXEYUM_MODEL_PREFERENCE_PHASE=off was not honored"
    );
    assert!(
        run_phase("on"),
        "AXEYUM_MODEL_PREFERENCE_PHASE=on was not honored"
    );
    assert!(
        run_phase("maybe"),
        "AXEYUM_MODEL_PREFERENCE_PHASE=maybe ran instead of refusing"
    );
}

/// The child half of the lever test above. Inert when the variable is unset;
/// with it set, the child passes exactly when `SolverConfig::default()` does
/// what the lever contract says: the named arm for a good value, a panic
/// naming the variable for a malformed one.
#[test]
fn env_probe() {
    let Ok(value) = std::env::var("AXEYUM_MODEL_PREFERENCE") else {
        return;
    };
    let observed = std::panic::catch_unwind(|| SolverConfig::default().model_preference);
    if let Some(expected) = ModelPreference::parse(&value) {
        assert_eq!(observed.expect("a good value must not panic"), expected);
        if let Ok(phase) = std::env::var("AXEYUM_MODEL_PREFERENCE_PHASE") {
            let forced = std::panic::catch_unwind(|| expected.forced_phase());
            match phase.as_str() {
                "off" => assert_eq!(forced.expect("`off` must not panic"), None),
                "on" => assert_eq!(
                    forced.expect("`on` must not panic"),
                    if expected == ModelPreference::Any {
                        None
                    } else {
                        Some(false)
                    }
                ),
                _ => {
                    let error = forced.expect_err("a malformed phase value must refuse");
                    let message = error.downcast_ref::<String>().cloned().unwrap_or_default();
                    assert!(
                        message.contains("AXEYUM_MODEL_PREFERENCE_PHASE"),
                        "{message}"
                    );
                }
            }
        }
        return;
    }
    let error = observed.expect_err("a malformed value must refuse, not run");
    let message = error
        .downcast_ref::<String>()
        .cloned()
        .or_else(|| error.downcast_ref::<&str>().map(|s| (*s).to_owned()))
        .unwrap_or_default();
    assert!(
        message.contains("AXEYUM_MODEL_PREFERENCE"),
        "the refusal must name the variable: {message}"
    );
}
