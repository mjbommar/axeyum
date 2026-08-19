//! `Kernel::set_render_proofs_as_def` moves the keyword that opens an
//! environment theorem, and nothing else (ADR-0489).
//!
//! Lean has two checkers and they disagree about a proof's opacity (ADR-0488):
//! its kernel unfolds anything carrying a value, its elaborator will not unfold
//! a `theorem` while reducing. The render option exists so the second one can be
//! given a module it accepts. What makes the option safe is that it is a
//! *spelling*: no term, type, binder, share name or banner byte depends on it.
//!
//! These guards pin exactly that, plus the two ways a one-token switch goes
//! wrong in this renderer — catching `Opaque`, which shares the `Theorem` arm,
//! and catching the module's ROOT theorem, which is written by a different code
//! path and is deliberately left alone.

use axeyum_lean_kernel::{BinderInfo, Declaration, Kernel, ReducibilityHint, build_nat_prelude};

/// The root theorem name the module renderer states.
const THEOREM: &str = "axeyum_probe";

/// A kernel carrying the ℕ prelude — 100+ declarations, most of them theorems,
/// which is enough for the module-level comparisons to be about a real
/// development rather than a fixture.
fn nat_kernel() -> Kernel {
    let mut kernel = Kernel::new();
    build_nat_prelude(&mut kernel).expect("the Nat prelude must build");
    kernel
}

/// The default rendering with every ENVIRONMENT theorem's keyword replaced.
fn theorems_as_defs(source: &str) -> String {
    let root = format!("theorem {THEOREM} ");
    source
        .lines()
        .map(|line| match line.strip_prefix("theorem ") {
            Some(rest) if !line.starts_with(&root) => format!("def {rest}\n"),
            _ => format!("{line}\n"),
        })
        .collect()
}

#[test]
fn the_option_is_off_by_default() {
    let kernel = Kernel::new();
    assert!(
        !kernel.render_proofs_as_def(),
        "the default rendering must be the one that ships"
    );
}

#[test]
fn a_theorem_declaration_renders_as_def_only_under_the_option() {
    let mut kernel = Kernel::new();
    let anonymous = kernel.anon();
    let name = kernel.name_str(anonymous, "t");
    let prop = kernel.sort_zero();
    let decl = Declaration::Theorem {
        name,
        uparams: Vec::new(),
        ty: prop,
        value: prop,
    };

    assert_eq!(
        kernel.render_lean_decl(&decl),
        "theorem t : Prop :=\n  Prop"
    );
    kernel.set_render_proofs_as_def(true);
    assert_eq!(kernel.render_lean_decl(&decl), "def t : Prop :=\n  Prop");
    kernel.set_render_proofs_as_def(false);
    assert_eq!(
        kernel.render_lean_decl(&decl),
        "theorem t : Prop :=\n  Prop",
        "the option is a switch, not a one-way door"
    );
}

/// `Opaque` shares the `Theorem` arm of the module writer's `match`, so the
/// obvious implementation of this switch re-spells it too. An `opaque` is not a
/// proof and has no value to unfold; re-spelling it would change what Lean
/// checks, not merely how the artefact reads.
#[test]
fn an_opaque_declaration_is_not_re_spelled() {
    let mut kernel = Kernel::new();
    let anonymous = kernel.anon();
    let name = kernel.name_str(anonymous, "o");
    let prop = kernel.sort_zero();
    let decl = Declaration::Opaque {
        name,
        uparams: Vec::new(),
        ty: prop,
        value: prop,
    };
    let before = kernel.render_lean_decl(&decl);
    kernel.set_render_proofs_as_def(true);
    assert_eq!(
        kernel.render_lean_decl(&decl),
        before,
        "an `opaque` must stay `opaque` under the option"
    );
    assert!(before.starts_with("opaque "), "{before}");
}

/// A `def` renders identically either way — the switch reads the declaration's
/// kind, not the keyword it is about to write.
#[test]
fn a_definition_is_unchanged_by_the_option() {
    let mut kernel = Kernel::new();
    let anonymous = kernel.anon();
    let name = kernel.name_str(anonymous, "d");
    let prop = kernel.sort_zero();
    let decl = Declaration::Definition {
        name,
        uparams: Vec::new(),
        ty: prop,
        value: prop,
        hint: ReducibilityHint::Regular(0),
    };
    let before = kernel.render_lean_decl(&decl);
    kernel.set_render_proofs_as_def(true);
    assert_eq!(kernel.render_lean_decl(&decl), before);
}

/// The whole-development guard: over a real prelude module, the two renderings
/// differ EXACTLY by the leading keyword of the lines that open a theorem.
#[test]
fn a_prelude_module_differs_only_by_the_keyword() {
    let mut kernel = nat_kernel();
    let roots: Vec<_> = kernel.environment().iter().map(|(n, _)| *n).collect();
    let default = kernel
        .render_lean_prelude_module("AxeyumProbe", &roots)
        .source()
        .to_owned();
    kernel.set_render_proofs_as_def(true);
    let switched = kernel
        .render_lean_prelude_module("AxeyumProbe", &roots)
        .source()
        .to_owned();

    let theorem_lines = default
        .lines()
        .filter(|line| line.starts_with("theorem "))
        .count();
    assert!(
        theorem_lines > 20,
        "this fixture must contain real theorems, found {theorem_lines}"
    );
    assert_ne!(default, switched, "the option must change bytes");
    assert_eq!(
        theorems_as_defs(&default),
        switched,
        "the option moved something other than the keyword"
    );
    assert_eq!(
        switched
            .lines()
            .filter(|l| l.starts_with("theorem "))
            .count(),
        0,
        "no environment theorem may keep the keyword under the option"
    );
    // `def` is four bytes shorter than `theorem`, once per theorem line.
    assert_eq!(
        default.len() - switched.len(),
        4 * theorem_lines,
        "the size difference must be exactly the keyword's"
    );
}

/// The module's ROOT theorem keeps its keyword. Nothing reduces through a
/// module's root, so re-spelling it would cost the artefact's central claim and
/// buy nothing — and it is written by a different code path, so it has to be
/// pinned separately.
#[test]
fn the_root_theorem_keeps_its_keyword() {
    let mut kernel = nat_kernel();
    let anonymous = kernel.anon();
    let prop = kernel.sort_zero();
    let body = kernel.bvar(0);
    let goal = kernel.pi(anonymous, prop, body, BinderInfo::Default);
    let proof = kernel.lam(anonymous, prop, body, BinderInfo::Default);

    let default = kernel.render_lean_module(THEOREM, goal, proof);
    kernel.set_render_proofs_as_def(true);
    let switched = kernel.render_lean_module(THEOREM, goal, proof);

    let root = format!("theorem {THEOREM} : ");
    assert!(default.contains(&root), "{}", &default[..200]);
    assert!(
        switched.contains(&root),
        "the root must still be spelled `theorem` under the option"
    );
    assert!(
        !switched.contains(&format!("def {THEOREM} : ")),
        "the root must not be re-spelled"
    );
    assert!(
        switched.contains(&format!("#print axioms {THEOREM}")),
        "the audit command must survive"
    );
}

/// A prelude template restore assigns a whole-kernel snapshot over the caller's
/// kernel. The rendering preference is not kernel content and must survive it —
/// otherwise a measurement run silently renders the default bytes while
/// believing it rendered the other.
#[test]
fn the_option_survives_a_prelude_build() {
    let mut kernel = Kernel::new();
    kernel.set_render_proofs_as_def(true);
    build_nat_prelude(&mut kernel).expect("the Nat prelude must build");
    assert!(
        kernel.render_proofs_as_def(),
        "building a prelude cleared the render option"
    );
    // A second build takes the process-wide template's fast path when it is
    // enabled, which is the route that assigns over the kernel.
    let mut second = Kernel::new();
    second.set_render_proofs_as_def(true);
    build_nat_prelude(&mut second).expect("the Nat prelude must build");
    assert!(second.render_proofs_as_def(), "a cache hit cleared it");
    assert!(
        second
            .render_lean_prelude_module(
                "AxeyumProbe",
                &second
                    .environment()
                    .iter()
                    .map(|(n, _)| *n)
                    .collect::<Vec<_>>()
            )
            .source()
            .lines()
            .all(|line| !line.starts_with("theorem ")),
        "the restored kernel rendered the default spelling"
    );
}
