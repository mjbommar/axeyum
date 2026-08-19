//! Official-Lean cross-check that the string prelude's `append` is **defined,
//! not assumed** — and that a proof using its monoid laws exports to a module a
//! real `lean` binary accepts with an axiom list that no longer mentions it.
//!
//! # Why an external check, when the in-tree kernel already admitted the proofs
//!
//! `string_prelude::monoid` declares `append` as a `Declaration::Definition` and
//! its four laws as `Declaration::Theorem`s, so the in-tree kernel type-checked
//! every one of them on admission. That is the *construction* claim. This suite
//! is the *portability* claim, and they are different: until 2026-08-17 `append`
//! was a `Declaration::Axiom`, and an axiom is exactly the thing an external
//! checker accepts **vacuously**. A prelude can therefore go green in two kernels
//! while assuming its operation exists.
//!
//! So the assertion here is not "Lean says ok" — it is what Lean's own
//! `#print axioms` reports about the exported theorem. The generated module ends
//! in `#print axioms axeyum_string_monoid_crosscheck`, and the check is that the
//! reported dependency set contains the three problem hypotheses (the opaque
//! words `x`, `y`, `z` a word-level refutation would introduce) and **nothing
//! from the string prelude**. Before this change the same module would have
//! listed `axeyum.string._2.append` there.
//!
//! Following `lean_probe`'s rule, a missing toolchain prints the skip marker and
//! is a hard failure under `AXEYUM_REQUIRE_LEAN=1`; it never reads as a pass.

use std::process::Command;

use axeyum_lean_kernel::{
    Declaration, ExprId, Kernel, StringPrelude, build_logic_prelude, build_string_prelude,
};

#[path = "support/lean_probe.rs"]
mod lean_probe;

/// The opaque-word names a word-level refutation introduces. These are the only
/// assumptions the exported theorem is allowed to depend on.
const WORDS: [&str; 3] = ["axeyum.word.x", "axeyum.word.y", "axeyum.word.z"];

/// Declare three opaque `Str` constants and return them.
fn opaque_words(kernel: &mut Kernel, sp: &StringPrelude) -> Vec<ExprId> {
    let anon = kernel.anon();
    WORDS
        .iter()
        .map(|label| {
            let name = label
                .split('.')
                .fold(anon, |parent, part| kernel.name_str(parent, part));
            let ty = sp.str_const(kernel);
            kernel
                .add_declaration(Declaration::Axiom {
                    name,
                    uparams: vec![],
                    ty,
                })
                .expect("opaque word admits");
            kernel.const_(name, vec![])
        })
        .collect()
}

/// `Eq.{1} Str a b`.
fn eq_str(kernel: &mut Kernel, sp: &StringPrelude, a: ExprId, b: ExprId) -> ExprId {
    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);
    let str_ty = sp.str_const(kernel);
    let eq = kernel.const_(sp.logic.eq, vec![one]);
    let e = kernel.app(eq, str_ty);
    let e = kernel.app(e, a);
    kernel.app(e, b)
}

/// The module: `((x ++ y) ++ z) ++ nil = x ++ (y ++ z)`, proved by `append_nil`
/// composed with `append_assoc` through `Eq.rec`. It exercises **both**
/// inductive laws, and the right identity is the one that is not definitional.
fn string_monoid_module() -> String {
    let mut kernel = Kernel::new();
    let logic = build_logic_prelude(&mut kernel).expect("logic prelude must build");
    let sp = build_string_prelude(&mut kernel, logic, 2).expect("string prelude must build");
    let words = opaque_words(&mut kernel, &sp);
    let (x, y, z) = (words[0], words[1], words[2]);

    let nil = sp.nil(&mut kernel);
    let xy = sp.append_app(&mut kernel, x, y);
    let xy_z = sp.append_app(&mut kernel, xy, z); // (x ++ y) ++ z
    let yz = sp.append_app(&mut kernel, y, z);
    let x_yz = sp.append_app(&mut kernel, x, yz); // x ++ (y ++ z)
    let lhs = sp.append_app(&mut kernel, xy_z, nil); // ((x ++ y) ++ z) ++ nil

    // assoc : (x ++ y) ++ z = x ++ (y ++ z)
    let assoc = {
        let lemma = kernel.const_(sp.append_assoc, vec![]);
        let e = kernel.app(lemma, x);
        let e = kernel.app(e, y);
        kernel.app(e, z)
    };
    // identity : ((x ++ y) ++ z) ++ nil = (x ++ y) ++ z
    let identity = {
        let lemma = kernel.const_(sp.append_nil, vec![]);
        kernel.app(lemma, xy_z)
    };

    // Chain them: transport `identity` along `assoc` to land on `x ++ (y ++ z)`.
    let goal = eq_str(&mut kernel, &sp, lhs, x_yz);
    let proof = {
        let anon = kernel.anon();
        let str_ty = sp.str_const(&mut kernel);
        let zero = kernel.level_zero();
        let one = kernel.level_succ(zero);
        // motive := λ (w : Str) (_ : Eq Str ((x++y)++z) w), Eq Str lhs w
        let motive = {
            let w = kernel.bvar(1);
            let conclusion = eq_str(&mut kernel, &sp, lhs, w);
            let w0 = kernel.bvar(0);
            let hypothesis = eq_str(&mut kernel, &sp, xy_z, w0);
            let inner = kernel.lam(
                anon,
                hypothesis,
                conclusion,
                axeyum_lean_kernel::BinderInfo::Default,
            );
            kernel.lam(anon, str_ty, inner, axeyum_lean_kernel::BinderInfo::Default)
        };
        let rec = kernel.const_(sp.logic.eq_rec, vec![zero, one]);
        let e = kernel.app(rec, str_ty);
        let e = kernel.app(e, xy_z);
        let e = kernel.app(e, motive);
        let e = kernel.app(e, identity);
        let e = kernel.app(e, x_yz);
        kernel.app(e, assoc)
    };

    // The in-tree kernel accepts the term before Lean is ever asked.
    let inferred = kernel.infer(proof).expect("monoid chain must infer");
    assert!(
        kernel.def_eq(inferred, goal),
        "the in-tree kernel must accept the term before Lean is asked"
    );

    kernel.render_lean_module("axeyum_string_monoid_crosscheck", goal, proof)
}

#[test]
fn append_is_exported_as_a_definition_not_an_axiom() {
    let source = string_monoid_module();
    assert!(
        source.contains("def axeyum.string._2.append"),
        "append must export as a `def`, not an assumption:\n{source}"
    );
    assert!(
        !source.contains("axiom axeyum.string._2.append"),
        "append must not export as an `axiom`:\n{source}"
    );
    // The laws travel with it as theorems carrying their proof terms.
    for law in [
        "theorem axeyum.string._2.append_nil",
        "theorem axeyum.string._2.append_assoc",
    ] {
        assert!(source.contains(law), "missing {law}:\n{source}");
    }
    assert!(!source.contains("sorry"), "{source}");
}

#[test]
fn string_monoid_module_checks_in_real_lean_with_no_prelude_axioms() {
    let source = string_monoid_module();
    let Some(lean) = lean_probe::lean_bin_or_skip("string-monoid", 1) else {
        return;
    };

    let directory = std::env::temp_dir().join(format!(
        "axeyum_string_monoid_crosscheck_{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&directory).expect("create Lean cross-check directory");
    let file = directory.join("StringMonoid.lean");
    std::fs::write(&file, &source).expect("write Lean module");

    let output = Command::new(&lean)
        .arg(&file)
        .output()
        .expect("run Lean cross-check");
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    assert!(
        output.status.success(),
        "Lean rejected the string-monoid module ({})\nstdout:\n{stdout}\nstderr:\n{stderr}\n\
         module:\n{source}",
        lean.display()
    );

    // The payload of this suite: Lean's OWN axiom report. Every opaque word must
    // be there (they are the problem's hypotheses)…
    let report = stdout.replace('\n', " ");
    for word in WORDS {
        assert!(
            report.contains(word),
            "Lean's `#print axioms` must list the hypothesis {word}:\n{stdout}"
        );
    }
    // …and nothing from the string prelude may be, which is exactly what changed
    // when `append` stopped being a `Declaration::Axiom`.
    assert!(
        !report.contains("axeyum.string."),
        "Lean reports a string-prelude assumption; `append` (or another prelude \
         declaration) is being trusted rather than checked:\n{stdout}"
    );
    let _ = std::fs::remove_dir_all(&directory);
    // `report_checked`, not a hand-written marker line. This suite printed
    // `AXEYUM-LEAN-CHECKED|string-monoid|1|...` -- pipe-separated -- and
    // `scripts/check-lean-gate.sh` parses `AXEYUM-LEAN-CHECKED <tag> checked=<n>`,
    // so the count was unreadable to the only thing that reads it. Combined with
    // the suite's absence from that gate's table, one real-Lean check ran on
    // every push, uncounted, and reached no floor.
    lean_probe::report_checked("string-monoid", 1);
}
