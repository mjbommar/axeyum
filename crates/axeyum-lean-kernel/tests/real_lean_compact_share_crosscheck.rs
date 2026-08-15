//! Cross-check that the **compact** (proof-sharing) writer never hoists a
//! *proper prefix* of an application spine whose head is a constant Lean
//! regenerates — a constructor or recursor of a real `inductive`.
//!
//! Why this suite exists, measured on 2026-08-14. `lean_crosscheck`'s
//! `quant_bv_source_instance_set` family was the 1 of 70 proof families a real
//! Lean 4.30.0 rejected, with 101 errors of two shapes:
//!
//! ```text
//! error: Application type mismatch: The argument axeyum_proof_share_33
//!   has type Prop of sort `Type` but is expected to have type
//!   ∀ (x2 : axeyum_proof_share_69), ?m.5 ⋯ of sort `Prop`
//! error(lean.unknownIdentifier): Unknown identifier `axeyum_proof_share_160`
//! ```
//!
//! The kernel term was **well typed** — the in-tree kernel infers `False` for it
//! and nothing about reconstruction changed to fix this. The module *text* was
//! wrong. The compact writer had hoisted `Or.rec P` (1 of its 6 arguments) into
//! `def axeyum_proof_share_149 := @Or.rec P`. Lean makes an inductive's
//! parameters and a recursor's motive **implicit**, so that `def` gets type
//! `{x1 : Prop} → {motive : Or P x1 → Prop} → …`, and the *bare* reference
//! `axeyum_proof_share_149 Q` then inserts metavariables for both and checks `Q`
//! against the `inl` minor premise. The `@` that keeps the head application flat
//! does not survive being cut in half. The unknown-identifier errors are the
//! cascade: a `def` that fails to elaborate never enters the environment.
//!
//! The Lean invocation is optional locally and mandatory under
//! `AXEYUM_REQUIRE_LEAN=1`, matching the other cross-checks in this crate.

use std::process::Command;

use axeyum_lean_kernel::{BinderInfo, Declaration, Kernel, build_logic_prelude};

#[path = "support/lean_probe.rs"]
mod lean_probe;

/// `And False False`, proved twice through `Or.rec` over a Prop large enough to
/// be hoisted, so the recursor spine prefix `Or.rec P` occurs twice and is a
/// share candidate on the pre-fix writer.
fn compact_share_module() -> String {
    let mut kernel = Kernel::new();
    let logic = build_logic_prelude(&mut kernel).expect("logic prelude must build");
    let anon = kernel.anon();
    let prop = kernel.sort_zero();
    let false_ = kernel.const_(logic.false_, vec![]);

    let atom = |kernel: &mut Kernel, name: &str| {
        let declared = kernel.name_str(anon, name);
        kernel
            .add_declaration(Declaration::Axiom {
                name: declared,
                uparams: vec![],
                ty: prop,
            })
            .expect("atom admits");
        kernel.const_(declared, vec![])
    };
    let atom_a = atom(&mut kernel, "A");
    let atom_b = atom(&mut kernel, "B");
    let atom_c = atom(&mut kernel, "C");
    let atom_d = atom(&mut kernel, "D");
    let right_prop = atom(&mut kernel, "Q");

    // `P := And A (And B (And C D))`: 13 expression nodes, comfortably over the
    // writer's 8-node sharing floor, so `P` itself is hoisted and the prefix
    // `Or.rec P` clears the floor too.
    let and = kernel.const_(logic.and, vec![]);
    let conj = |kernel: &mut Kernel, left, right| {
        let partial = kernel.app(and, left);
        kernel.app(partial, right)
    };
    let inner = conj(&mut kernel, atom_c, atom_d);
    let middle = conj(&mut kernel, atom_b, inner);
    let left_prop = conj(&mut kernel, atom_a, middle);

    let or = kernel.const_(logic.or, vec![]);
    let disjunction = kernel.app(or, left_prop);
    let disjunction = kernel.app(disjunction, right_prop);

    let hypothesis = |kernel: &mut Kernel, name: &str, ty| {
        let declared = kernel.name_str(anon, name);
        kernel
            .add_declaration(Declaration::Axiom {
                name: declared,
                uparams: vec![],
                ty,
            })
            .expect("hypothesis admits");
        kernel.const_(declared, vec![])
    };
    let left_absurd = kernel.pi(anon, left_prop, false_, BinderInfo::Default);
    let right_absurd = kernel.pi(anon, right_prop, false_, BinderInfo::Default);
    let on_left = hypothesis(&mut kernel, "hp", left_absurd);
    let on_right = hypothesis(&mut kernel, "hq", right_absurd);
    // Two DISTINCT majors, so the two saturated spines differ only in their last
    // argument and every shorter prefix is shared.
    let major_one = hypothesis(&mut kernel, "h1", disjunction);
    let major_two = hypothesis(&mut kernel, "h2", disjunction);

    let motive = kernel.lam(anon, disjunction, false_, BinderInfo::Default);
    let or_rec = kernel.const_(logic.or_rec, vec![]);
    let case_split = |kernel: &mut Kernel, major| {
        let spine = kernel.app(or_rec, left_prop);
        let spine = kernel.app(spine, right_prop);
        let spine = kernel.app(spine, motive);
        let spine = kernel.app(spine, on_left);
        let spine = kernel.app(spine, on_right);
        kernel.app(spine, major)
    };
    let first = case_split(&mut kernel, major_one);
    let second = case_split(&mut kernel, major_two);

    let goal = kernel.app(and, false_);
    let goal = kernel.app(goal, false_);
    let and_intro = kernel.const_(logic.and_intro, vec![]);
    let proof = kernel.app(and_intro, false_);
    let proof = kernel.app(proof, false_);
    let proof = kernel.app(proof, first);
    let proof = kernel.app(proof, second);

    // The classification this suite records: the KERNEL accepts the term. Only
    // the rendering was ever in question.
    let inferred = kernel.infer(proof).expect("case-split proof must infer");
    assert!(
        kernel.def_eq(inferred, goal),
        "the in-tree kernel must accept the term before Lean is asked"
    );

    kernel.render_lean_module_compact("axeyum_compact_share_crosscheck", goal, proof)
}

/// The first argument token of the module's flat `@Or.rec` spine.
fn first_or_rec_argument(source: &str) -> String {
    let at = source
        .find("@Or.rec ")
        .unwrap_or_else(|| panic!("the module must apply `Or.rec` with `@`:\n{source}"));
    let rest = &source[at + "@Or.rec ".len()..];
    rest.split([' ', '\n'])
        .next()
        .expect("a first argument")
        .to_owned()
}

#[test]
fn compact_writer_keeps_regenerated_constant_spines_saturated() {
    let source = compact_share_module();

    // Sharing is still ON: the large `P` is hoisted, which is what makes the
    // prefix `Or.rec P` a candidate at all.
    assert!(
        source.contains("def axeyum_proof_share_"),
        "the compact writer must still hoist shared closed subterms:\n{source}"
    );
    // ... but the recursor spine stays flat and saturated. On the pre-fix writer
    // this module contained `def axeyum_proof_share_N :=\n  @Or.rec <one arg>`
    // and Lean rejected it.
    let argument = first_or_rec_argument(&source);
    assert!(
        !source.contains(&format!("@Or.rec {argument}\n")),
        "a proper prefix of the `Or.rec` spine was hoisted; Lean re-implicits it:\n{source}"
    );
    assert!(
        !source.contains("@Or.inl\n") && !source.contains("@Or.inr\n"),
        "constructor spines must not be hoisted bare either:\n{source}"
    );
    assert!(!source.contains("sorry"), "{source}");
}

#[test]
fn compact_share_module_checks_in_real_lean() {
    let source = compact_share_module();
    // Two Lean invocations: the module, and the hoisted-prefix negative control.
    let Some(lean) = lean_probe::lean_bin_or_skip("compact-share", 2) else {
        return;
    };

    let directory = std::env::temp_dir().join(format!(
        "axeyum_compact_share_crosscheck_{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&directory).expect("create Lean cross-check directory");

    let check = |name: &str, text: &str| {
        let file = directory.join(name);
        std::fs::write(&file, text).expect("write Lean module");
        let output = Command::new(&lean)
            .arg(&file)
            .output()
            .expect("run Lean cross-check");
        (
            output.status.success(),
            String::from_utf8_lossy(&output.stdout).into_owned(),
            String::from_utf8_lossy(&output.stderr).into_owned(),
        )
    };

    let (ok, stdout, stderr) = check("CompactShare.lean", &source);
    assert!(
        ok,
        "Lean rejected the compact-share module ({})\nstdout:\n{stdout}\nstderr:\n{stderr}\n\
         source:\n{source}",
        lean.display()
    );
    assert!(
        stdout.contains("axeyum_compact_share_crosscheck"),
        "missing #print axioms output: {stdout}"
    );
    assert!(!stdout.contains("sorryAx"), "{stdout}");

    // Negative control: reintroduce EXACTLY the defect — hoist the one-argument
    // prefix of the recursor spine into its own `def` and reference it bare. The
    // same binary must now reject the same proof, so the pass above is evidence
    // about our writer rather than a module Lean would accept however written.
    let argument = first_or_rec_argument(&source);
    let spine = format!("@Or.rec {argument} ");
    let theorem_at = source
        .find("\ntheorem ")
        .expect("the module must declare its theorem");
    let mut tampered = source.clone();
    tampered.insert_str(
        theorem_at,
        &format!("\ndef axeyum_share_control :=\n  @Or.rec {argument}\n"),
    );
    let tampered = tampered.replace(&spine, "axeyum_share_control ");
    assert_ne!(
        tampered, source,
        "the negative control must change the module"
    );
    let (control_ok, control_stdout, _) = check("TamperedCompactShare.lean", &tampered);
    assert!(
        !control_ok,
        "Lean accepted a hoisted recursor-spine prefix; the saturation rule is unverified\n\
         stdout:\n{control_stdout}"
    );

    let _ = std::fs::remove_dir_all(directory);
    lean_probe::report_checked("compact-share", 2);
}
