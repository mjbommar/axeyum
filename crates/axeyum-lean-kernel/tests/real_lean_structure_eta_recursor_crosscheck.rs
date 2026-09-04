//! Differential control for **structure-eta reduction of a stuck recursor major
//! premise** against pinned official Lean 4.30.0.
//!
//! `structure_eta_recursor_major.rs` asserts that *this* kernel now reduces
//! `Pair.rec (fun _ => A) (fun x _ => x) p` to `p.1` for an opaque `p : Pair`,
//! and that it still refuses the same shape when the family has two
//! constructors or a recursive field. That is a rule this port **widened**, so
//! it needs an external witness rather than an argument: the same declarations
//! are handed to official Lean here, and Lean's verdicts have to match ours,
//! module for module.
//!
//! # Why there are four invocations rather than two
//!
//! The three refusals are in **separate** modules on purpose. Lean stops
//! elaborating a declaration at its first error but keeps going through the
//! file, so three failures in one module would be indistinguishable from one
//! failure and two vacuous successes unless the assertion parsed Lean's
//! diagnostic text — which is exactly the kind of message-reading this
//! repository has been burned by. One module per claim; a non-zero exit is then
//! attributable.
//!
//! # What this does and does not establish
//!
//! `lean file.lean` runs the **elaborator** before the kernel, and the
//! elaborator's `whnf` performs this same eta expansion. So the positive module
//! could in principle be accepted by elaboration alone. Two things keep it
//! meaningful:
//!
//! * The proof term Lean stores for `theorem pairFirst : pairViaRec = p.1 :=
//!   rfl` is `@rfl A p.1`, whose type is `p.1 = p.1`. The kernel type-checks
//!   every stored declaration (`Lean.addDecl`), so it must itself show
//!   `pairViaRec ≡ p.1` — δ through the definition and then ι through
//!   `Pair.rec` on a major that is an opaque constant. There is no elaborator
//!   left at that point.
//! * `#print axioms pairFirst` is read back and required to name our three
//!   axioms and **not** `sorryAx`, so a module that "succeeded" by admitting the
//!   goal fails this suite instead of quietly agreeing with us.
//! * The three negative modules must be **rejected**. Without them a module Lean
//!   accepted for any reason at all would read as agreement.
//!
//! The claim that this port's rule fires in the position the corpus needs is
//! carried by `structure_eta_recursor_major::open_major_under_a_binder_reduces_at_the_gate`
//! and by `Nat.Linear.Poly.denote_reverse` importing clean, not by this file.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

#[path = "support/lean_probe.rs"]
mod lean_probe;

/// Four real-Lean invocations: one positive module and three refusals.
const CHECKS: usize = 4;

/// The shared fixture: an opaque carrier with two inhabitants, a two-field
/// structure, a two-constructor family, and a recursive one-constructor family
/// — each with an opaque inhabitant so every major premise is stuck.
const PRELUDE: &str = "\
axiom A : Type
axiom a0 : A
axiom a1 : A

structure Pair : Type where
  fst : A
  snd : A
axiom p : Pair

inductive Sum2 : Type where
  | inl (x : A) : Sum2
  | inr (y : A) : Sum2
axiom s : Sum2

inductive RecBox : Type where
  | mk (head : A) (tail : RecBox) : RecBox
axiom b : RecBox

inductive Solo : Type where
  | mk : Solo
axiom u : Solo
";

/// Both positives: the two-field structure whose stuck major must eta-expand,
/// and the unit-like `Solo`, whose constructor has no fields at all — the case
/// that flipped an over-strong assertion in `k_like_reduction.rs`.
const POSITIVE: &str = "\
noncomputable def pairViaRec : A := Pair.rec (motive := fun _ => A) (fun x _ => x) p
theorem pairFirst : pairViaRec = p.1 := rfl

noncomputable def soloViaRec : A := Solo.rec (motive := fun _ => A) a0 u
theorem soloConst : soloViaRec = a0 := rfl

#print axioms pairFirst
#print axioms soloConst
";

/// The recursor application is the FIRST field, not the second. A rule that
/// stopped discriminating would accept this.
const NEGATIVE_WRONG_FIELD: &str = "\
noncomputable def pairViaRec : A := Pair.rec (motive := fun _ => A) (fun x _ => x) p
theorem pairSecond : pairViaRec = p.2 := rfl
";

/// Two constructors: eta would have to *choose* one, and choosing `inl` makes
/// this equation provable — and false.
const NEGATIVE_TWO_CONSTRUCTORS: &str = "\
noncomputable def sumViaRec : A := Sum2.rec (motive := fun _ => A) (fun _ => a0) (fun _ => a1) s
theorem sumConst : sumViaRec = a0 := rfl
";

/// A recursive field: `is_non_rec_structure` is false, so there is no eta rule
/// and the recursor stays stuck on `b`.
const NEGATIVE_RECURSIVE: &str = "\
noncomputable def boxViaRec : A := RecBox.rec (motive := fun _ => A) (fun _ _ _ => a0) b
theorem boxConst : boxViaRec = a0 := rfl
";

fn run_lean(lean: &Path, file: &Path) -> Output {
    Command::new(lean)
        .args(["-j", "1", "-s", "1024", "-M", "4096"])
        .arg(file)
        .output()
        .expect("run official Lean structure-eta cross-check")
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
    lean_probe::assert_pinned_version("structure-eta-recursor", &version_text);
}

/// Write `<name>.lean` under `directory` and run Lean on it, returning the
/// merged stdout/stderr and whether Lean exited successfully.
fn check_module(lean: &Path, directory: &Path, name: &str, body: &str) -> (bool, String, String) {
    let source = format!("{PRELUDE}{body}");
    let file = directory.join(format!("{name}.lean"));
    std::fs::write(&file, &source).expect("write Lean module");
    let output = run_lean(lean, &file);
    let text = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    (output.status.success(), text, source)
}

#[test]
fn structure_eta_recursor_verdicts_agree_with_pinned_lean() {
    let Some(lean) = lean_probe::lean_bin_or_skip("structure-eta-recursor", CHECKS) else {
        return;
    };
    require_pinned_version(&lean);

    let directory = std::env::temp_dir().join(format!(
        "axeyum_structure_eta_recursor_crosscheck_{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&directory).expect("create cross-check directory");

    let (ok, text, source) = check_module(&lean, &directory, "StructEtaPositive", POSITIVE);
    assert!(
        ok,
        "official Lean rejected a stuck-major structure-eta reduction this kernel \
         admits ({})\noutput:\n{text}\nsource:\n{source}",
        lean.display(),
    );
    assert!(
        !text.contains("sorryAx"),
        "`#print axioms` shows `sorryAx`, so Lean admitted the goal rather than \
         checking it and this cross-check measures nothing\noutput:\n{text}"
    );
    assert!(
        text.contains("'pairFirst' depends on axioms") && text.contains("'soloConst' depends on"),
        "`#print axioms` did not report on both theorems, so the module did not \
         elaborate the way this test assumes\noutput:\n{text}"
    );

    for (name, body, why) in [
        (
            "StructEtaWrongField",
            NEGATIVE_WRONG_FIELD,
            "`Pair.rec (fun x _ => x) p = p.2` — the recursor selects the FIRST field",
        ),
        (
            "StructEtaTwoConstructors",
            NEGATIVE_TWO_CONSTRUCTORS,
            "`Sum2.rec … s = a0` — with two constructors there is no eta rule, and \
             `s` may be an `inr`",
        ),
        (
            "StructEtaRecursive",
            NEGATIVE_RECURSIVE,
            "`RecBox.rec … b = a0` — a recursive field excludes structure eta",
        ),
    ] {
        let (ok, _text, source) = check_module(&lean, &directory, name, body);
        assert!(
            !ok,
            "official Lean ACCEPTED {why}, which this kernel refuses\nsource:\n{source}"
        );
    }

    let _ = std::fs::remove_dir_all(directory);
    lean_probe::report_checked("structure-eta-recursor", CHECKS);
}
