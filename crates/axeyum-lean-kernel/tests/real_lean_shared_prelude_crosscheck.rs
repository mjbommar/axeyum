//! Cross-check the **split module layout** against a real `lean`: a shared
//! development compiled once to an `.olean`, and a per-query module that
//! `import`s it instead of inlining it.
//!
//! # Why this suite exists
//!
//! Measured 2026-08-18 on the shipped front door, over the constructed reals:
//! the emitted module is 1,304,276 bytes and **the refutation's own theorem term
//! is 4,193 of them** — 0.16%. The other 99.84% is the ℕ/ℤ/ℚ/setoid development,
//! byte-identical for every query over that carrier. Emitting it once and
//! importing it is the remaining order of magnitude
//! (`docs/plan/notes/64-module-size.md`).
//!
//! The saving is arithmetic. What is NOT arithmetic, and is what this suite
//! measures, is whether the two halves are still checkable — and whether the
//! claim they carry is the same one. Three things could go wrong and none of
//! them shows up in a byte count:
//!
//! 1. **A redeclaration.** The query module must skip every constant the import
//!    supplies, including the constructors and recursors Lean regenerates from
//!    an imported `inductive` and Lean's own compiler-internal constants. Emit
//!    one twice and Lean says `has already been declared`.
//! 2. **A missing declaration.** Skip one the import does *not* supply and Lean
//!    says `Unknown constant` — the same class of defect as `a5975725f`, where
//!    non-requested inductives were rendered as opaque `axiom`s.
//! 3. **A weakened claim.** `#print axioms` must still traverse into the
//!    imported proofs. If it did not, a query module could report an empty
//!    footprint while resting on an imported `sorryAx`, and the headline
//!    axiom-freedom result would become unfalsifiable rather than merely wrong.
//!
//! # The cost this suite also records
//!
//! A self-contained module is checked by `lean Query.lean` and nothing else. The
//! split needs the shared module compiled first and found on `LEAN_PATH`, so it
//! is a **strictly weaker artefact** for a third party. The exact two commands
//! are generated from the artefact itself (`LeanPreludeModule::check_script`)
//! and are what this suite runs, so the published recipe is the tested one.
//!
//! The negative control is the point: the query module handed to `lean` with no
//! `LEAN_PATH` must FAIL. Without that, "Lean accepted the query module" would
//! be consistent with Lean having silently found nothing to import.
//!
//! The Lean invocation is optional locally and mandatory under
//! `AXEYUM_REQUIRE_LEAN=1`, matching the other cross-checks in this crate.

use std::collections::BTreeSet;
use std::process::Command;

use axeyum_lean_kernel::{
    BinderInfo, Declaration, Kernel, LeanPreludeModule, NameId, build_logic_prelude,
};

#[path = "support/lean_probe.rs"]
mod lean_probe;

/// The Lean module name the shared development is published under. Must equal
/// the file stem, because Lean resolves `import M` to `M.olean` under a
/// `LEAN_PATH` entry.
const SHARED_MODULE: &str = "AxeyumSharedCrosscheck";

/// The theorem the query module states.
const THEOREM: &str = "axeyum_shared_prelude_crosscheck";

/// A refutation that forces the split to carry an inductive, its constructors
/// **and** its recursor across the import boundary.
///
/// `h1 : Or P Q` is case-split by `@Or.rec`, with both branches absurd. `Or` and
/// `Or.rec` live in the shared development; `P`, `Q` and the four hypotheses are
/// the query's own. Lean makes an inductive's parameters and a recursor's motive
/// implicit, so the kernel's positional application must still be written `@` in
/// the query module even though the `inductive` command is in the other file —
/// which is exactly the decision that could be got wrong by computing the
/// `@`-set over the emitted subset instead of over the whole reachable set.
///
/// Returns `(shared, query)`.
fn split_modules() -> (LeanPreludeModule, String) {
    let mut kernel = Kernel::new();
    let logic = build_logic_prelude(&mut kernel).expect("logic prelude must build");
    // The snapshot that DEFINES "shared": every declaration admitted before any
    // query symbol existed.
    let carrier: Vec<NameId> = kernel.environment().iter().map(|(n, _)| *n).collect();

    let anon = kernel.anon();
    let prop = kernel.sort_zero();
    let false_ = kernel.const_(logic.false_, vec![]);

    let axiom = |kernel: &mut Kernel, name: &str, ty| {
        let declared = kernel.name_str(anon, name);
        kernel
            .add_declaration(Declaration::Axiom {
                name: declared,
                uparams: vec![],
                ty,
            })
            .expect("query axiom admits");
        kernel.const_(declared, vec![])
    };
    let left_prop = axiom(&mut kernel, "P", prop);
    let right_prop = axiom(&mut kernel, "Q", prop);

    let or = kernel.const_(logic.or, vec![]);
    let disjunction = kernel.app(or, left_prop);
    let disjunction = kernel.app(disjunction, right_prop);

    let left_absurd = kernel.pi(anon, left_prop, false_, BinderInfo::Default);
    let right_absurd = kernel.pi(anon, right_prop, false_, BinderInfo::Default);
    let on_left = axiom(&mut kernel, "hp", left_absurd);
    let on_right = axiom(&mut kernel, "hq", right_absurd);
    let major = axiom(&mut kernel, "h1", disjunction);

    let motive = kernel.lam(anon, disjunction, false_, BinderInfo::Default);
    let or_rec = kernel.const_(logic.or_rec, vec![]);
    let spine = kernel.app(or_rec, left_prop);
    let spine = kernel.app(spine, right_prop);
    let spine = kernel.app(spine, motive);
    let spine = kernel.app(spine, on_left);
    let spine = kernel.app(spine, on_right);
    let proof = kernel.app(spine, major);

    // The in-tree kernel accepts the term before Lean is asked anything: only
    // the module LAYOUT is in question here.
    let inferred = kernel.infer(proof).expect("case-split proof must infer");
    assert!(
        kernel.def_eq(inferred, false_),
        "the in-tree kernel must accept the term before Lean is asked"
    );

    let shared = kernel.render_lean_prelude_module(SHARED_MODULE, &carrier);
    let query = kernel.render_lean_module_compact_importing(THEOREM, false_, proof, &[], &shared);
    (shared, query)
}

/// The self-contained rendering of the same refutation, for the size comparison
/// and for the redeclaration control.
fn self_contained_module() -> String {
    let mut kernel = Kernel::new();
    let logic = build_logic_prelude(&mut kernel).expect("logic prelude must build");
    let anon = kernel.anon();
    let prop = kernel.sort_zero();
    let false_ = kernel.const_(logic.false_, vec![]);
    let axiom = |kernel: &mut Kernel, name: &str, ty| {
        let declared = kernel.name_str(anon, name);
        kernel
            .add_declaration(Declaration::Axiom {
                name: declared,
                uparams: vec![],
                ty,
            })
            .expect("query axiom admits");
        kernel.const_(declared, vec![])
    };
    let left_prop = axiom(&mut kernel, "P", prop);
    let right_prop = axiom(&mut kernel, "Q", prop);
    let or = kernel.const_(logic.or, vec![]);
    let disjunction = kernel.app(or, left_prop);
    let disjunction = kernel.app(disjunction, right_prop);
    let left_absurd = kernel.pi(anon, left_prop, false_, BinderInfo::Default);
    let right_absurd = kernel.pi(anon, right_prop, false_, BinderInfo::Default);
    let on_left = axiom(&mut kernel, "hp", left_absurd);
    let on_right = axiom(&mut kernel, "hq", right_absurd);
    let major = axiom(&mut kernel, "h1", disjunction);
    let motive = kernel.lam(anon, disjunction, false_, BinderInfo::Default);
    let or_rec = kernel.const_(logic.or_rec, vec![]);
    let spine = kernel.app(or_rec, left_prop);
    let spine = kernel.app(spine, right_prop);
    let spine = kernel.app(spine, motive);
    let spine = kernel.app(spine, on_left);
    let spine = kernel.app(spine, on_right);
    let proof = kernel.app(spine, major);
    kernel.render_lean_module_compact(THEOREM, false_, proof)
}

/// The query module's `#print axioms` must name the query's own hypotheses and
/// nothing from the shared development — the claim, not the layout.
#[test]
fn the_split_moves_the_development_and_keeps_the_theorem() {
    let (shared, query) = split_modules();
    let whole = self_contained_module();

    // The fixed banner dominates both files at this scale, so the claim here is
    // that the DEVELOPMENT left the query module. The ratio is measured where
    // the development is large -- `examples/shared_prelude_module.rs` on the
    // constructed-real carrier -- and this suite checks the layout is CHECKABLE.
    assert!(
        query.len() < whole.len(),
        "whole {} B, query {} B, shared {} B",
        whole.len(),
        query.len(),
        shared.source().len()
    );
    assert!(
        query.contains(&format!("import {SHARED_MODULE}")),
        "the query module must import the shared development:\n{query}"
    );
    // `Or` moved out; the query's own symbols did not.
    assert!(!query.contains("inductive Or "), "{query}");
    for own in ["axiom P :", "axiom Q :", "axiom hp :", "axiom h1 :"] {
        assert!(
            query.contains(own),
            "the query keeps its own `{own}`:\n{query}"
        );
    }
    // The recursor application stays `@`-saturated even though the `inductive`
    // is in the other file.
    assert!(
        query.contains("@Or.rec "),
        "the imported recursor must still be applied with `@`:\n{query}"
    );
    assert!(
        shared.source().contains("inductive Or "),
        "{}",
        shared.name()
    );
}

#[test]
fn the_split_modules_check_in_real_lean() {
    let (shared, query) = split_modules();
    // Four Lean invocations: compile the shared module, check the query module
    // against it, and two negative controls.
    let Some(lean) = lean_probe::lean_bin_or_skip("shared-prelude", 4) else {
        return;
    };

    let directory = std::env::temp_dir().join(format!(
        "axeyum_shared_prelude_crosscheck_{}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&directory);
    std::fs::create_dir_all(&directory).expect("create Lean cross-check directory");

    let shared_path = directory.join(shared.file_name());
    let olean_path = directory.join(format!("{SHARED_MODULE}.olean"));
    let query_path = directory.join("Query.lean");
    std::fs::write(&shared_path, shared.source()).expect("write shared module");
    std::fs::write(&query_path, &query).expect("write query module");

    // The published recipe is generated from the artefact, so it cannot drift
    // from the module name — and it is what this suite actually runs.
    let script = shared.check_script(&directory.to_string_lossy(), "Query.lean");
    assert!(
        script.contains(&format!("{SHARED_MODULE}.olean"))
            && script.contains("LEAN_PATH=")
            && script.contains("--root"),
        "the published check recipe must name the artefact, the search path, and the \
         module root:\n{script}"
    );

    let run = |arguments: &[&std::path::Path], lean_path: Option<&std::path::Path>| {
        let mut command = Command::new(&lean);
        // Lean derives a module name from the file's path relative to the root
        // directory (default: the working directory), and `cargo test` runs in
        // the crate directory. Without this every invocation below dies with
        // `input file ... must be contained in root directory`, which is why
        // the published recipe carries `--root` too.
        command.arg("--root").arg(&directory);
        for argument in arguments {
            command.arg(argument);
        }
        match lean_path {
            Some(path) => command.env("LEAN_PATH", path),
            // Not merely "unset": an inherited LEAN_PATH from the developer's
            // shell would make the negative control below pass for the wrong
            // reason.
            None => command.env("LEAN_PATH", ""),
        };
        let output = command.output().expect("run Lean");
        (
            output.status.success(),
            String::from_utf8_lossy(&output.stdout).into_owned(),
            String::from_utf8_lossy(&output.stderr).into_owned(),
        )
    };

    // (1) Compile the shared development once.
    let (ok, stdout, stderr) = run(
        &[
            std::path::Path::new("-o"),
            &olean_path,
            shared_path.as_path(),
        ],
        None,
    );
    assert!(
        ok,
        "Lean rejected the shared development module\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        olean_path.exists(),
        "`lean -o` reported success but wrote no {SHARED_MODULE}.olean"
    );

    // (2) Check the query module against it. This is the positive result.
    let (ok, stdout, stderr) = run(&[query_path.as_path()], Some(directory.as_path()));
    assert!(
        ok,
        "Lean rejected the query module against the imported development\n\
         stdout:\n{stdout}\nstderr:\n{stderr}"
    );
    // `#print axioms` traverses the IMPORTED proofs: the reported footprint is
    // the query's own hypotheses, and the shared development contributes none.
    // A layout change that broke this would leave a query module whose audit
    // command reports less than it rests on.
    let audit = stdout
        .lines()
        .find(|line| line.contains("depends on axioms") || line.contains("does not depend"))
        .unwrap_or_else(|| panic!("no `#print axioms` output:\nstdout:\n{stdout}"));
    for hypothesis in ["hp", "hq", "h1"] {
        assert!(
            audit.contains(hypothesis),
            "`#print axioms` must still report the query's own `{hypothesis}`: {audit}"
        );
    }
    assert!(
        !stdout.contains("sorryAx") && !query.contains("sorry"),
        "stdout:\n{stdout}"
    );

    run_negative_controls(&run, &directory, &query_path);

    let _ = std::fs::remove_dir_all(&directory);
    lean_probe::report_checked("shared-prelude", 4);
}

/// The two refusals, split out because `clippy::too_many_lines` fires on STABLE
/// (and is silent on nightly) and this suite's body is over the limit with them
/// inline.
///
/// They are not decoration. Without (3) "Lean accepted the query module" is
/// consistent with the import having done nothing at all, and without (4)
/// suppressing the imported declarations could be a no-op that nothing notices.
fn run_negative_controls<F>(run: &F, directory: &std::path::Path, query_path: &std::path::Path)
where
    F: Fn(&[&std::path::Path], Option<&std::path::Path>) -> (bool, String, String),
{
    // (3) NEGATIVE CONTROL: without LEAN_PATH the import cannot resolve, so the
    // query module must FAIL. Without this, "Lean accepted the query module"
    // would be consistent with the import having done nothing.
    let (ok, stdout, stderr) = run(&[query_path], None);
    assert!(
        !ok,
        "the query module was accepted with NO LEAN_PATH -- then the import is not \
         load-bearing and this suite proves nothing\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    // (4) NEGATIVE CONTROL: the same query module WITHOUT the declaration
    // suppression -- i.e. what the writer would emit if it ignored the set the
    // import provides. Lean must reject it as a redeclaration.
    let unsuppressed = self_contained_module().replacen(
        "\nprelude\n",
        &format!("\nprelude\nimport {SHARED_MODULE}\n"),
        1,
    );
    assert!(
        unsuppressed.contains(&format!("import {SHARED_MODULE}")),
        "the control must actually carry the import"
    );
    let control_path = directory.join("Unsuppressed.lean");
    std::fs::write(&control_path, &unsuppressed).expect("write control module");
    let (ok, stdout, stderr) = run(&[control_path.as_path()], Some(directory));
    assert!(
        !ok,
        "Lean accepted a module that re-declares what its import supplies -- then \
         suppressing them is not load-bearing\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// The suppression set is not guesswork: it is exactly the shared module's
/// reachable declarations, and the two halves partition them.
///
/// Lean enforces this from the other side (a redeclaration is an error), but
/// only where a Lean runs. This holds on every machine.
#[test]
fn the_two_halves_declare_disjoint_names() {
    let (shared, query) = split_modules();
    let declared = |source: &str| -> BTreeSet<String> {
        source
            .lines()
            .filter_map(|line| {
                let rest = line
                    .strip_prefix("axiom ")
                    .or_else(|| line.strip_prefix("unsafe axiom "))
                    .or_else(|| line.strip_prefix("def "))
                    .or_else(|| line.strip_prefix("theorem "))
                    .or_else(|| line.strip_prefix("opaque "))
                    .or_else(|| line.strip_prefix("inductive "))?;
                Some(rest.split([' ', '.']).next()?.to_owned())
            })
            .collect()
    };
    let shared_names = declared(shared.source());
    let query_names = declared(&query);
    assert!(
        shared_names.len() > 5 && query_names.len() >= 5,
        "both halves must declare something, or the disjointness below is vacuous: \
         shared {}, query {}",
        shared_names.len(),
        query_names.len()
    );
    let both: Vec<&String> = shared_names.intersection(&query_names).collect();
    assert!(both.is_empty(), "declared in both halves: {both:?}");
}
