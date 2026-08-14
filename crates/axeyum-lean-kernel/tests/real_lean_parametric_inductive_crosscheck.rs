//! Cross-check of a **parametric and indexed** inductive (`Eq`) rendered as a
//! real Lean `inductive` command.
//!
//! Every other real-Lean fixture in this crate declares a flat enum
//! (`add_inductive(name, &[], 0, …)`), so the corpus was structurally incapable
//! of reaching the writer's parameter/index handling — and it did not: until
//! 2026-08-13 `lean_pp` emitted the whole parameter/index telescope *after* the
//! colon, which makes every parameter an index, and Lean then generated a
//! different recursor and rejected the module. This suite closes that hole, and
//! the string assertions below fail on the unfixed writer without needing a Lean
//! binary at all.
//!
//! The Lean invocation is optional locally and mandatory under
//! `AXEYUM_REQUIRE_LEAN=1`, matching the other cross-checks in this crate.

use std::path::PathBuf;
use std::process::Command;

use axeyum_lean_kernel::{Kernel, build_logic_prelude};

fn lean_bin() -> Option<PathBuf> {
    if let Ok(path) = std::env::var("AXEYUM_LEAN_BIN") {
        let path = PathBuf::from(path);
        if path.is_file() {
            return Some(path);
        }
    }
    let path = std::env::var_os("PATH")?;
    std::env::split_paths(&path)
        .map(|directory| directory.join("lean"))
        .find(|candidate| candidate.is_file())
}

/// `Eq True True.intro True.intro`, proved by `Eq.refl`, with both `Eq` (2
/// parameters, 1 index) and `True` emitted as real Lean `inductive`s.
fn parametric_inductive_module() -> String {
    let mut kernel = Kernel::new();
    let logic = build_logic_prelude(&mut kernel).expect("logic prelude must build");
    let zero = kernel.level_zero();
    let true_const = kernel.const_(logic.true_, vec![]);
    let trivial = kernel.const_(logic.true_intro, vec![]);

    let eq = kernel.const_(logic.eq, vec![zero]);
    let goal = kernel.app(eq, true_const);
    let goal = kernel.app(goal, trivial);
    let goal = kernel.app(goal, trivial);

    let refl = kernel.const_(logic.eq_refl, vec![zero]);
    let proof = kernel.app(refl, true_const);
    let proof = kernel.app(proof, trivial);

    let inferred = kernel.infer(proof).expect("refl proof must infer");
    assert!(
        kernel.def_eq(inferred, goal),
        "the in-tree kernel must accept the term before Lean is asked"
    );

    kernel.render_lean_module_with_inductives(
        "axeyum_parametric_inductive_crosscheck",
        goal,
        proof,
        &[logic.true_, logic.eq],
    )
}

#[test]
fn parametric_indexed_inductive_is_rendered_in_lean_s_own_form() {
    let source = parametric_inductive_module();

    // Parameters before the colon, indices after it. The unfixed writer emitted
    // `inductive Eq.{u} : ((x0 : Sort (u)) -> …)`, making both parameters
    // indices.
    assert!(
        source.contains("inductive Eq.{u} (x0 : Sort (u)) (x1 : x0) : "),
        "Eq must declare its 2 parameters before the colon:\n{source}"
    );
    // The self-reference inside the constructor is a local during elaboration,
    // so it carries no explicit universe arguments and no `@`.
    assert!(
        source.contains("\n  | refl : Eq x0 x1 x1"),
        "Eq.refl must restate only its indices, with a bare self-reference:\n{source}"
    );
    assert!(
        !source.contains("| refl : ((Eq.{u}"),
        "an explicit universe on the self-reference is rejected by Lean:\n{source}"
    );
    // Recursor-based definitions are proofs, not programs.
    assert!(
        source.contains("noncomputable section"),
        "codegen must be suppressed for recursor-based definitions:\n{source}"
    );
    // Lean inserts a constructor's implicit parameters as soon as a
    // parenthesized application is complete, so applications must be flat.
    assert!(
        source.contains("@Eq.refl.{0} True @True.intro"),
        "constructor applications must be flat and `@`-applied:\n{source}"
    );
    assert!(!source.contains("sorry"), "{source}");
}

#[test]
fn parametric_indexed_inductive_module_checks_in_real_lean() {
    let source = parametric_inductive_module();
    let Some(lean) = lean_bin() else {
        assert_ne!(
            std::env::var("AXEYUM_REQUIRE_LEAN").as_deref(),
            Ok("1"),
            "AXEYUM_REQUIRE_LEAN=1 but no Lean binary was found"
        );
        eprintln!("[skip] real Lean is optional locally; CI requires it");
        return;
    };

    let directory = std::env::temp_dir().join(format!(
        "axeyum_parametric_inductive_crosscheck_{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&directory).expect("create Lean cross-check directory");
    let file = directory.join("ParametricInductive.lean");
    std::fs::write(&file, &source).expect("write Lean cross-check module");
    let output = Command::new(&lean)
        .arg(&file)
        .output()
        .expect("run Lean cross-check");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "Lean rejected the parametric-inductive module ({})\nstdout:\n{stdout}\nstderr:\n{stderr}",
        lean.display()
    );
    assert!(
        stdout.contains("axeyum_parametric_inductive_crosscheck"),
        "missing #print axioms output: {stdout}"
    );
    assert!(!stdout.contains("sorryAx"), "{stdout}");

    // Negative control, aimed at the defect this suite exists for: Lean makes a
    // constructor's parameters implicit, so dropping the `@` must make the same
    // binary reject the same proof. A pass above is then evidence rather than a
    // module Lean would have accepted however it was written.
    let tampered = source.replace(
        "@Eq.refl.{0} True @True.intro",
        "Eq.refl.{0} True @True.intro",
    );
    assert_ne!(
        tampered, source,
        "the negative control must change the module"
    );
    let tampered_file = directory.join("TamperedParametricInductive.lean");
    std::fs::write(&tampered_file, &tampered).expect("write tampered module");
    let tampered_output = Command::new(&lean)
        .arg(&tampered_file)
        .output()
        .expect("run tampered Lean cross-check");
    assert!(
        !tampered_output.status.success(),
        "Lean accepted a positionally-applied implicit constructor; the `@` rule is unverified"
    );
    let _ = std::fs::remove_dir_all(directory);
}
