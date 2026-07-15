//! Mandatory-in-CI cross-check of an Axeyum-generated restricted `Prop`
//! recursor against Lean's own inductive kernel.
//!
//! Local development may omit Lean; CI sets `AXEYUM_REQUIRE_LEAN=1`, turning a
//! missing binary into a failure. The generated module uses real `inductive`
//! commands, applies Lean's regenerated `Two.rec`, and needs its iota rule to
//! type-check an equality proof.

use std::path::PathBuf;
use std::process::Command;

use axeyum_lean_kernel::{BinderInfo, Kernel, build_logic_prelude};

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

fn restricted_prop_iota_module() -> String {
    let mut kernel = Kernel::new();
    let logic = build_logic_prelude(&mut kernel);
    let anon = kernel.anon();

    // Two : Prop | a : Two | b : Two. Its recursor must have a Prop-valued
    // motive and no fresh elimination-universe argument.
    let two = kernel.name_str(anon, "Two");
    let two_const = kernel.const_(two, vec![]);
    let a_name = kernel.name_str(two, "a");
    let b_name = kernel.name_str(two, "b");
    let prop = kernel.sort_zero();
    kernel
        .add_inductive(
            two,
            &[],
            0,
            prop,
            &[(a_name, two_const), (b_name, two_const)],
        )
        .expect("Two should admit with restricted elimination");

    let true_const = kernel.const_(logic.true_, vec![]);
    let trivial = kernel.const_(logic.true_intro, vec![]);
    let a = kernel.const_(a_name, vec![]);
    let two_rec_name = kernel.name_str(two, "rec");
    let two_rec = kernel.const_(two_rec_name, vec![]);

    // selected := Two.rec (fun _ => True) trivial trivial Two.a : True.
    // Its definitional equality to `trivial` depends on the recursor's iota rule.
    let motive = kernel.lam(anon, two_const, true_const, BinderInfo::Default);
    let selected = kernel.app(two_rec, motive);
    let selected = kernel.app(selected, trivial);
    let selected = kernel.app(selected, trivial);
    let selected = kernel.app(selected, a);

    // goal := Eq.{0} True selected trivial; proof := Eq.refl True trivial.
    let zero = kernel.level_zero();
    let eq = kernel.const_(logic.eq, vec![zero]);
    let goal = kernel.app(eq, true_const);
    let goal = kernel.app(goal, selected);
    let goal = kernel.app(goal, trivial);
    let refl = kernel.const_(logic.eq_refl, vec![zero]);
    let proof = kernel.app(refl, true_const);
    let proof = kernel.app(proof, trivial);
    let inferred = kernel.infer(proof).expect("refl proof should infer");
    assert!(kernel.def_eq(inferred, goal));

    kernel.render_lean_module_with_inductives(
        "axeyum_prop_large_elim_crosscheck",
        goal,
        proof,
        &[logic.true_, two],
    )
}

#[test]
fn restricted_prop_recursor_checks_in_real_lean() {
    let source = restricted_prop_iota_module();
    assert!(source.contains("inductive Two : Prop where"), "{source}");
    assert!(source.contains("inductive True : Prop where"), "{source}");
    assert!(source.contains("@Two.rec"), "{source}");
    assert!(!source.contains("axiom Two.rec"), "{source}");
    assert!(!source.contains("sorryAx"), "{source}");

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
        "axeyum_prop_large_elim_crosscheck_{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&directory).expect("create Lean cross-check directory");
    let file = directory.join("PropLargeElim.lean");
    std::fs::write(&file, &source).expect("write Lean cross-check module");
    let output = Command::new(&lean)
        .arg(&file)
        .output()
        .expect("run Lean cross-check");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "Lean rejected generated module ({})\nstdout:\n{stdout}\nstderr:\n{stderr}\nsource:\n{source}",
        lean.display()
    );
    assert!(!stdout.contains("sorryAx"), "{stdout}");
    assert!(
        stdout.contains("axeyum_prop_large_elim_crosscheck"),
        "missing #print axioms output: {stdout}"
    );
    let _ = std::fs::remove_dir_all(directory);
}
