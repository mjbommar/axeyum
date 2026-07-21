//! Cargo-owned checked MIR selection gates (T5.1.3, ADR-0289).

use std::fs;
use std::panic::catch_unwind;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

use axeyum_ir::{TermArena, Value};
use axeyum_solver::{ProofOutcome, SolverConfig, prove};
use axeyum_verify::reflect::mir::checked::{
    CheckedMirMemory, MirMemoryConfig, reflect_bounded_memory_checked,
};

#[path = "fixtures/mir-target-crate/src/lib.rs"]
mod target_fixture;

const BIN: &str = env!("CARGO_BIN_EXE_axeyum-mir-build");
const PACKAGE: &str = "axeyum-mir-target-fixture";
const FUNCTION: &str = "cargo_store_then_load";
const RUSTC_COMMIT: &str = "f53b654a8882fd5fc036c4ca7a4ff41ce32497a6";
static SCRATCH_ID: AtomicUsize = AtomicUsize::new(0);

struct Scratch(PathBuf);

impl Scratch {
    fn new(label: &str) -> Self {
        let id = SCRATCH_ID.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "axeyum-cargo-mir-{label}-{}-{id}",
            std::process::id()
        ));
        if path.exists() {
            fs::remove_dir_all(&path).unwrap();
        }
        fs::create_dir(&path).unwrap();
        Self(fs::canonicalize(path).unwrap())
    }

    fn path(&self, name: &str) -> PathBuf {
        self.0.join(name)
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn manifest() -> PathBuf {
    fs::canonicalize(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/mir-target-crate/Cargo.toml"),
    )
    .unwrap()
}

fn contract_manifest() -> PathBuf {
    fs::canonicalize(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/mir-contract-target/Cargo.toml"),
    )
    .unwrap()
}

fn fsm_manifest() -> PathBuf {
    fs::canonicalize(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/mir-fsm-target/Cargo.toml"),
    )
    .unwrap()
}

fn registered_tools() -> Option<(PathBuf, PathBuf)> {
    let lookup = |name: &str, override_name: &str| -> Option<PathBuf> {
        if let Some(path) = std::env::var_os(override_name) {
            return fs::canonicalize(path).ok();
        }
        let output = Command::new("rustup").args(["which", name]).output().ok()?;
        if !output.status.success() {
            return None;
        }
        let path = String::from_utf8(output.stdout).ok()?;
        fs::canonicalize(path.trim()).ok()
    };
    let cargo = lookup("cargo", "AXEYUM_VERIFY_MIR_CARGO")?;
    let rustc = lookup("rustc", "AXEYUM_VERIFY_MIR_RUSTC")?;
    let version = Command::new(&rustc).arg("-vV").output().ok()?;
    let version = String::from_utf8(version.stdout).ok()?;
    version.contains(RUSTC_COMMIT).then_some((cargo, rustc))
}

fn exact_tools_or_skip() -> Option<(PathBuf, PathBuf)> {
    let tools = registered_tools();
    assert!(
        tools.is_some() || std::env::var_os("AXEYUM_VERIFY_MIR_REQUIRE_CARGO_BUILD").is_none(),
        "registered rustc {RUSTC_COMMIT} is required by AXEYUM_VERIFY_MIR_REQUIRE_CARGO_BUILD"
    );
    if tools.is_none() {
        eprintln!("registered rustc {RUSTC_COMMIT} unavailable; exact Cargo MIR gate skipped");
    }
    tools
}

struct Selection<'a> {
    package: &'a str,
    target: TargetSelection<'a>,
    function: &'a str,
}

enum TargetSelection<'a> {
    Lib,
    Bin(&'a str),
}

fn run(
    selection: &Selection<'_>,
    cargo: &Path,
    rustc: &Path,
    target_dir: &Path,
    output: &Path,
) -> Output {
    run_with_manifest(&manifest(), selection, cargo, rustc, target_dir, output)
}

fn run_with_manifest(
    manifest_path: &Path,
    selection: &Selection<'_>,
    cargo: &Path,
    rustc: &Path,
    target_dir: &Path,
    output: &Path,
) -> Output {
    let mut command = Command::new(BIN);
    command
        .arg("--manifest-path")
        .arg(manifest_path)
        .arg("--package")
        .arg(selection.package);
    match &selection.target {
        TargetSelection::Lib => {
            command.arg("--lib");
        }
        TargetSelection::Bin(name) => {
            command.arg("--bin").arg(name);
        }
    }
    command
        .arg("--function")
        .arg(selection.function)
        .arg("--target-usize-width")
        .arg("64")
        .arg("--cargo")
        .arg(cargo)
        .arg("--rustc")
        .arg(rustc)
        .arg("--target-dir")
        .arg(target_dir)
        .arg("--output")
        .arg(output)
        .current_dir("/")
        .env("RUSTC_WRAPPER", "/bin/false")
        .env("RUSTC_WORKSPACE_WRAPPER", "/bin/false")
        .output()
        .unwrap()
}

fn run_scalar_contract_capture(
    cargo: &Path,
    rustc: &Path,
    target_dir: &Path,
    output: &Path,
) -> Output {
    Command::new(BIN)
        .arg("--manifest-path")
        .arg(contract_manifest())
        .args([
            "--package",
            "axeyum-mir-contract-fixture",
            "--lib",
            "--function",
            "wrapping_inc",
            "--profile",
            "scalar-contract",
            "--target-usize-width",
            "64",
            "--cargo",
        ])
        .arg(cargo)
        .arg("--rustc")
        .arg(rustc)
        .arg("--target-dir")
        .arg(target_dir)
        .arg("--output")
        .arg(output)
        .current_dir("/")
        .env("RUSTC_WRAPPER", "/bin/false")
        .env("RUSTC_WORKSPACE_WRAPPER", "/bin/false")
        .output()
        .unwrap()
}

fn run_scalar_fsm_capture(
    function: &str,
    cargo: &Path,
    rustc: &Path,
    target_dir: &Path,
    output: &Path,
) -> Output {
    Command::new(BIN)
        .arg("--manifest-path")
        .arg(fsm_manifest())
        .args([
            "--package",
            "axeyum-mir-fsm-fixture",
            "--lib",
            "--function",
            function,
            "--profile",
            "scalar-contract",
            "--target-usize-width",
            "64",
            "--cargo",
        ])
        .arg(cargo)
        .arg("--rustc")
        .arg(rustc)
        .arg("--target-dir")
        .arg(target_dir)
        .arg("--output")
        .arg(output)
        .current_dir("/")
        .env("RUSTC_WRAPPER", "/bin/false")
        .env("RUSTC_WORKSPACE_WRAPPER", "/bin/false")
        .output()
        .unwrap()
}

fn assert_class(output: &Output, class: &str) {
    assert!(!output.status.success(), "unexpected success");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains(&format!("\"class\":\"{class}\"")),
        "expected class {class}, got:\n{stderr}"
    );
}

fn param(reflected: &CheckedMirMemory, local: u32) -> axeyum_ir::SymbolId {
    reflected
        .params
        .iter()
        .find(|parameter| parameter.local == local)
        .unwrap()
        .symbol
}

fn proved(arena: &mut TermArena, goal: axeyum_ir::TermId) -> bool {
    matches!(
        prove(arena, &[], goal, &SolverConfig::default()).unwrap(),
        ProofOutcome::Proved(_)
    )
}

fn implies(
    arena: &mut TermArena,
    premise: axeyum_ir::TermId,
    conclusion: axeyum_ir::TermId,
) -> axeyum_ir::TermId {
    let not_premise = arena.not(premise).unwrap();
    arena.or(not_premise, conclusion).unwrap()
}

fn assert_cargo_store_semantics(mir: &str) {
    let mut reflected =
        reflect_bounded_memory_checked(mir, &MirMemoryConfig::new(FUNCTION, 64)).unwrap();
    let index_symbol = param(&reflected, 2);
    let value_symbol = param(&reflected, 3);
    let index = reflected.arena.var(index_symbol);
    let value = reflected.arena.var(value_symbol);
    let four = reflected.arena.bv_const(64, 4).unwrap();
    let in_bounds = reflected.arena.bv_ult(index, four).unwrap();
    let out_of_bounds = reflected.arena.not(in_bounds).unwrap();
    let panic_exact = reflected.arena.eq(reflected.panic, out_of_bounds).unwrap();
    assert!(proved(&mut reflected.arena, panic_exact));
    let result_equal = reflected.arena.eq(reflected.result.value, value).unwrap();
    let safe_result = implies(&mut reflected.arena, in_bounds, result_equal);
    assert!(proved(&mut reflected.arena, safe_result));
    for offset in 0..4 {
        let offset_term = reflected.arena.bv_const(64, offset).unwrap();
        let selected = reflected.arena.eq(index, offset_term).unwrap();
        let input = reflected.arena.var(reflected.region.input[offset as usize]);
        let expected = reflected.arena.ite(selected, value, input).unwrap();
        let exact = reflected
            .arena
            .eq(reflected.region.output[offset as usize], expected)
            .unwrap();
        assert!(proved(&mut reflected.arena, exact));
    }

    for index in 0..4 {
        assert_eq!(
            target_fixture::cargo_store_then_load([1, 2, 3, 4], index, 0xa5),
            0xa5
        );
    }
    let no_panic = reflected.arena.not(reflected.panic).unwrap();
    let outcome = prove(
        &mut reflected.arena,
        &[],
        no_panic,
        &SolverConfig::default(),
    )
    .unwrap();
    let ProofOutcome::Disproved(model) = outcome else {
        panic!("unsafe target must produce an OOB witness: {outcome:?}");
    };
    let witness = match model.get(index_symbol) {
        Some(Value::Bv { width: 64, value }) => usize::try_from(value).unwrap(),
        other => panic!("countermodel has no 64-bit index: {other:?}"),
    };
    assert!(witness >= 4);
    assert!(
        catch_unwind(|| target_fixture::cargo_store_then_load([1, 2, 3, 4], witness, 0xa5))
            .is_err()
    );
}

#[test]
fn one_command_capture_is_reproducible_checked_and_source_replayed() {
    let Some((cargo, rustc)) = exact_tools_or_skip() else {
        return;
    };
    let scratch = Scratch::new("positive");
    let target_dir = scratch.path("cargo-target");
    let first_mir = scratch.path("first.mir");
    let first = run(
        &Selection {
            package: PACKAGE,
            target: TargetSelection::Lib,
            function: FUNCTION,
        },
        &cargo,
        &rustc,
        &target_dir,
        &first_mir,
    );
    assert!(
        first.status.success(),
        "first capture failed:\n{}",
        String::from_utf8_lossy(&first.stderr)
    );
    let first_summary = String::from_utf8(first.stdout).unwrap();
    let first_bytes = fs::read(&first_mir).unwrap();
    assert!(first_summary.contains("\"schema\":\"axeyum.verify-mir-build.v1\""));
    assert!(first_summary.contains(&format!("\"mir_bytes\":{}", first_bytes.len())));
    assert!(first_summary.contains("\"parameter_types\":[\"[u8;4]\",\"usize\",\"u8\"]"));
    assert!(first_summary.contains("\"region_bytes\":4"));
    assert!(first_summary.contains("\"result_width\":8"));

    fs::remove_dir_all(&target_dir).unwrap();
    let second_mir = scratch.path("second.mir");
    let second = run(
        &Selection {
            package: PACKAGE,
            target: TargetSelection::Lib,
            function: FUNCTION,
        },
        &cargo,
        &rustc,
        &target_dir,
        &second_mir,
    );
    assert!(
        second.status.success(),
        "second capture failed:\n{}",
        String::from_utf8_lossy(&second.stderr)
    );
    assert_eq!(first_bytes, fs::read(&second_mir).unwrap());
    assert_eq!(first_summary.as_bytes(), second.stdout);

    assert_cargo_store_semantics(&String::from_utf8(first_bytes).unwrap());
}

#[test]
fn scalar_profile_reproduces_the_committed_root_independent_capture() {
    let Some((cargo, rustc)) = exact_tools_or_skip() else {
        return;
    };
    let scratch = Scratch::new("scalar-contract");
    let captured = scratch.path("wrapping_inc.mir");
    let output =
        run_scalar_contract_capture(&cargo, &rustc, &scratch.path("cargo-target"), &captured);
    assert!(
        output.status.success(),
        "scalar capture failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let fixture = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/mir-contract-target");
    assert_eq!(
        fs::read(captured).unwrap(),
        fs::read(fixture.join("artifacts/wrapping_inc.mir")).unwrap()
    );
    assert_eq!(
        output.stdout,
        fs::read(fixture.join("artifacts/capture-summary.json")).unwrap()
    );
}

#[test]
fn compiler_page_table_selections_reproduce_the_authenticated_raw_module() {
    let Some((cargo, rustc)) = exact_tools_or_skip() else {
        return;
    };
    let scratch = Scratch::new("scope-metadata");
    let started = Instant::now();
    let committed = fs::read(
        manifest()
            .parent()
            .unwrap()
            .join("artifacts/page_table_walks.mir"),
    )
    .unwrap();
    for function in ["walk_frame", "walk_permissions"] {
        let captured = scratch.path(&format!("{function}.mir"));
        let output = run(
            &Selection {
                package: PACKAGE,
                target: TargetSelection::Lib,
                function,
            },
            &cargo,
            &rustc,
            &scratch.path(&format!("{function}-target")),
            &captured,
        );
        assert!(
            output.status.success(),
            "scope-bearing {function} capture failed:\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let summary = String::from_utf8(output.stdout).unwrap();
        assert!(summary.contains(&format!("\"function\":\"{function}\"")));
        assert!(summary.contains("\"mir_bytes\":8218"));
        assert!(summary.contains("\"parameter_types\":[\"[u8;4]\",\"u8\"]"));
        assert!(summary.contains("\"blocks\":4"));
        assert!(summary.contains("\"region_bytes\":4"));
        assert!(summary.contains("\"result_width\":8"));
        let mir = fs::read(&captured).unwrap();
        assert_eq!(mir, committed, "{function} raw MIR drift");
        let mir = String::from_utf8(mir).unwrap();
        assert!(mir.contains("scope 1 {"));
        let reflected = reflect_bounded_memory_checked(&mir, &MirMemoryConfig::new(function, 64))
            .expect("captured scope-bearing walk must remain checked");
        assert_eq!(reflected.region.input.len(), 4);
        assert_eq!(reflected.result.width, 8);
    }
    eprintln!(
        "ADR0320_CAPTURE selections=2 raw_mismatches=0 projection_errors=0 wall_ms={}",
        started.elapsed().as_millis()
    );
}

#[test]
fn compiler_fsm_selections_reproduce_the_authenticated_raw_module() {
    let Some((cargo, rustc)) = exact_tools_or_skip() else {
        return;
    };
    let scratch = Scratch::new("fsm-refinement");
    let started = Instant::now();
    let committed = fs::read(
        fsm_manifest()
            .parent()
            .unwrap()
            .join("artifacts/handshake.mir"),
    )
    .unwrap();
    for (function, blocks) in [("handshake_step", 10), ("handshake_step_bug", 13)] {
        let captured = scratch.path(&format!("{function}.mir"));
        let output = run_scalar_fsm_capture(
            function,
            &cargo,
            &rustc,
            &scratch.path(&format!("{function}-target")),
            &captured,
        );
        assert!(
            output.status.success(),
            "FSM {function} capture failed:\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let summary = String::from_utf8(output.stdout).unwrap();
        assert!(summary.contains("\"profile\":\"scalar-contract\""));
        assert!(summary.contains(&format!("\"function\":\"{function}\"")));
        assert!(summary.contains("\"mir_bytes\":2691"));
        assert!(summary.contains("\"parameter_types\":[\"u8\",\"u8\"]"));
        assert!(summary.contains(&format!("\"blocks\":{blocks}")));
        assert!(summary.contains("\"result_width\":8"));
        assert_eq!(fs::read(&captured).unwrap(), committed, "{function} drift");
    }
    eprintln!(
        "ADR0321_CAPTURE selections=2 raw_mismatches=0 projection_errors=0 wall_ms={}",
        started.elapsed().as_millis()
    );
}

#[test]
fn argument_compiler_and_existing_output_fail_without_partial_state() {
    let no_args = Command::new(BIN).output().unwrap();
    assert_class(&no_args, "missing_argument");
    let help = Command::new(BIN).arg("--help").output().unwrap();
    assert!(help.status.success());
    assert!(
        String::from_utf8_lossy(&help.stdout).contains("may execute that target's build scripts")
    );

    let scratch = Scratch::new("early-failure");
    let target_dir = scratch.path("cargo-target");
    let output = scratch.path("out.mir");
    let true_executable = fs::canonicalize("/usr/bin/true").unwrap();

    let missing_manifest = scratch.path("missing/Cargo.toml");
    let missing = run_with_manifest(
        &missing_manifest,
        &Selection {
            package: PACKAGE,
            target: TargetSelection::Lib,
            function: FUNCTION,
        },
        &true_executable,
        &true_executable,
        &target_dir,
        &output,
    );
    assert_class(&missing, "manifest_path");
    assert!(!target_dir.exists());
    assert!(!output.exists());

    let escaping_manifest = scratch.path("nested/../Cargo.toml");
    let escaping = run_with_manifest(
        &escaping_manifest,
        &Selection {
            package: PACKAGE,
            target: TargetSelection::Lib,
            function: FUNCTION,
        },
        &true_executable,
        &true_executable,
        &target_dir,
        &output,
    );
    assert_class(&escaping, "manifest_path");
    assert!(!target_dir.exists());
    assert!(!output.exists());

    let wrong_compiler = run(
        &Selection {
            package: PACKAGE,
            target: TargetSelection::Lib,
            function: FUNCTION,
        },
        &true_executable,
        &true_executable,
        &target_dir,
        &output,
    );
    assert_class(&wrong_compiler, "compiler_identity");
    assert!(!target_dir.exists());
    assert!(!output.exists());

    fs::write(&output, b"preserve-me").unwrap();
    let existing = run(
        &Selection {
            package: PACKAGE,
            target: TargetSelection::Lib,
            function: FUNCTION,
        },
        &true_executable,
        &true_executable,
        &target_dir,
        &output,
    );
    assert_class(&existing, "output_exists");
    assert_eq!(fs::read(&output).unwrap(), b"preserve-me");
    assert!(!target_dir.exists());

    fs::remove_file(&output).unwrap();
    fs::create_dir(&target_dir).unwrap();
    let existing_target = run(
        &Selection {
            package: PACKAGE,
            target: TargetSelection::Lib,
            function: FUNCTION,
        },
        &true_executable,
        &true_executable,
        &target_dir,
        &output,
    );
    assert_class(&existing_target, "target_dir_exists");
    assert!(!output.exists());
}

#[test]
fn cargo_and_function_selection_fail_closed_with_precise_classes() {
    let Some((cargo, rustc)) = exact_tools_or_skip() else {
        return;
    };
    let scratch = Scratch::new("selection-failure");
    let cases = [
        (
            Selection {
                package: "missing-package",
                target: TargetSelection::Lib,
                function: FUNCTION,
            },
            "wrong_package",
        ),
        (
            Selection {
                package: PACKAGE,
                target: TargetSelection::Bin("missing-bin"),
                function: FUNCTION,
            },
            "wrong_target",
        ),
        (
            Selection {
                package: PACKAGE,
                target: TargetSelection::Lib,
                function: "missing_function",
            },
            "function_missing",
        ),
        (
            Selection {
                package: PACKAGE,
                target: TargetSelection::Lib,
                function: "unsupported_reference",
            },
            "mir_syntax",
        ),
    ];
    for (index, (selection, class)) in cases.into_iter().enumerate() {
        let target_dir = scratch.path(&format!("target-{index}"));
        let output_path = scratch.path(&format!("output-{index}.mir"));
        let result = run(&selection, &cargo, &rustc, &target_dir, &output_path);
        assert_class(&result, class);
        assert!(
            !target_dir.exists(),
            "failed target directory must be removed"
        );
        assert!(!output_path.exists(), "failed capture must not be retained");
    }

    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;

        let fake_cargo = scratch.path("fake-cargo");
        fs::write(
            &fake_cargo,
            b"#!/bin/sh\nif [ \"$1\" = \"-vV\" ]; then printf 'cargo fake\\n'; else printf '\\377'; fi\n",
        )
        .unwrap();
        fs::set_permissions(&fake_cargo, fs::Permissions::from_mode(0o700)).unwrap();
        let fake_cargo = fs::canonicalize(fake_cargo).unwrap();
        let target_dir = scratch.path("target-non-utf8");
        let output_path = scratch.path("output-non-utf8.mir");
        let non_utf8 = run(
            &Selection {
                package: PACKAGE,
                target: TargetSelection::Lib,
                function: FUNCTION,
            },
            &fake_cargo,
            &rustc,
            &target_dir,
            &output_path,
        );
        assert_class(&non_utf8, "mir_encoding");
        assert!(!target_dir.exists());
        assert!(!output_path.exists());

        let read_only = scratch.path("read-only");
        fs::create_dir(&read_only).unwrap();
        fs::set_permissions(&read_only, fs::Permissions::from_mode(0o500)).unwrap();
        let target_dir = scratch.path("target-output-failure");
        let output_path = read_only.join("out.mir");
        let output_failure = run(
            &Selection {
                package: PACKAGE,
                target: TargetSelection::Lib,
                function: FUNCTION,
            },
            &cargo,
            &rustc,
            &target_dir,
            &output_path,
        );
        fs::set_permissions(&read_only, fs::Permissions::from_mode(0o700)).unwrap();
        assert_class(&output_failure, "output_write");
        assert!(!target_dir.exists());
        assert!(!output_path.exists());
    }
}
