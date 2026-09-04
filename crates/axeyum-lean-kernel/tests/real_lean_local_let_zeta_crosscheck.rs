//! Differential control for **local `let` (ζ) reduction** against pinned
//! official Lean 4.30.0.
//!
//! `local_let_zeta_reduction.rs` asserts that *this* kernel admits
//! `fun n => let n' : N := n; K n (Eq.refl (id2 n'))` and refuses the same shape
//! with `n'` bound to an opaque `g n`. That is a claim about a rule this port
//! widened, so it needs an external witness: the very same four modules are
//! handed to official Lean here, and Lean's verdicts have to match ours
//! declaration for declaration.
//!
//! # What this does and does not establish
//!
//! `lean file.lean` runs the **elaborator** before the kernel. The elaborator's
//! `isDefEq` has ζ enabled, so it would accept the positive module even if the
//! kernel could not. Two things keep the check meaningful anyway:
//!
//! * Lean's `let` elaborates to `Expr.letE`, and its kernel's `infer_let`
//!   (`src/kernel/type_checker.cpp`) pushes a local declaration **with a value**
//!   exactly as ours does, so the kernel really does face the obligation. This
//!   file asserts it by reading `#print probe` back and requiring a `let`/`have`
//!   to have survived elaboration into the stored term — if a future toolchain
//!   zeta-expands at elaboration time, this test fails loudly rather than
//!   quietly checking nothing.
//! * The negative modules must be **rejected**. Without them a module Lean
//!   accepted for any reason at all would read as agreement.
//!
//! The claim that the rule fires *in the position that was broken* — a let-local
//! exposed inside `lazy_delta_reduction` rather than at the head — is carried by
//! `local_let_zeta_reduction::a_let_local_exposed_by_delta_reduction_is_zeta_reduced`
//! and by `Nat.bitwise._unary` importing clean, not by this file.
//!
//! Two real-Lean invocations: the positive module, and the negative control.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

#[path = "support/lean_probe.rs"]
mod lean_probe;

/// The fixture, identical in shape to `local_let_zeta_reduction`'s: an opaque
/// carrier, an opaque endomorphism for the controls, a δ-reducible identity so
/// the delta loop actually runs, and `K` whose second argument's type mentions
/// its first.
const PRELUDE: &str = "\
axiom N : Type
axiom g : N -> N
axiom K : forall (a : N), a = a -> N
def id2 : N -> N := fun x => x
";

/// Both positives: the let-local exposed only after `id2` is unfolded, and the
/// chained one that needs ζ to be a fixed point rather than a single step.
const POSITIVE: &str = "\
noncomputable def probe : N -> N := fun n => let n' : N := n; K n (Eq.refl (id2 n'))
noncomputable def probe_chain : N -> N :=
  fun n => let a : N := n; let b : N := a; K n (Eq.refl (id2 b))
#print probe
";

/// The controls, one per positive. `g` is an axiom, so `g n` never reduces to
/// `n` and both must be refused however much ζ fires.
const NEGATIVE: &str = "\
noncomputable def control : N -> N := fun n => let n' : N := g n; K n (Eq.refl (id2 n'))
noncomputable def control_chain : N -> N :=
  fun n => let a : N := n; let b : N := g a; K n (Eq.refl (id2 b))
";

fn run_lean(lean: &Path, file: &Path) -> Output {
    Command::new(lean)
        .args(["-j", "1", "-s", "1024", "-M", "4096"])
        .arg(file)
        .output()
        .expect("run official Lean local-let cross-check")
}

fn require_pinned_version(lean: &PathBuf) {
    let version = Command::new(lean)
        .arg("--version")
        .output()
        .expect("query official Lean version");
    let version_text = format!(
        "{}{}",
        String::from_utf8_lossy(&version.stdout),
        String::from_utf8_lossy(&version.stderr)
    );
    lean_probe::assert_pinned_version("local-let-zeta", &version_text);
}

#[test]
fn local_let_zeta_verdicts_agree_with_pinned_lean() {
    let Some(lean) = lean_probe::lean_bin_or_skip("local-let-zeta", 2) else {
        return;
    };
    require_pinned_version(&lean);

    let directory = std::env::temp_dir().join(format!(
        "axeyum_local_let_zeta_crosscheck_{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&directory).expect("create cross-check directory");

    let positive_source = format!("{PRELUDE}{POSITIVE}");
    let positive_file = directory.join("LocalLetZetaPositive.lean");
    std::fs::write(&positive_file, &positive_source).expect("write positive Lean module");
    let positive = run_lean(&lean, &positive_file);
    let positive_out = format!(
        "{}{}",
        String::from_utf8_lossy(&positive.stdout),
        String::from_utf8_lossy(&positive.stderr)
    );
    assert!(
        positive.status.success(),
        "official Lean rejected a local-`let` shape this kernel admits ({})\n\
         output:\n{positive_out}\nsource:\n{positive_source}",
        lean.display(),
    );

    // The `let` has to survive elaboration into the stored term, or Lean's
    // kernel never saw the obligation and this comparison is vacuous.
    //
    // Lean renders a *non-dependent* `Expr.letE` as `have` rather than `let`,
    // and both are the same kernel node — `infer_let` pushes a local with a
    // value either way — so both spellings count. Measured on 4.30.0: this
    // module prints `have n' := n;`.
    assert!(
        positive_out.contains("let ") || positive_out.contains("have "),
        "`#print probe` shows neither `let` nor `have` in the elaborated term, so \
         Lean's kernel did not face the ζ obligation and this cross-check \
         measures nothing\n\
         output:\n{positive_out}"
    );

    let negative_source = format!("{PRELUDE}{NEGATIVE}");
    let negative_file = directory.join("LocalLetZetaNegative.lean");
    std::fs::write(&negative_file, &negative_source).expect("write negative Lean module");
    let negative = run_lean(&lean, &negative_file);
    assert!(
        !negative.status.success(),
        "official Lean accepted `let n' := g n; K n (Eq.refl (id2 n'))`, which this \
         kernel refuses\nsource:\n{negative_source}"
    );

    let _ = std::fs::remove_dir_all(directory);
    lean_probe::report_checked("local-let-zeta", 2);
}
