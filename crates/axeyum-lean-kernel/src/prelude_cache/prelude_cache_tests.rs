//! The soundness gate for process-wide prelude reuse (ADR-0464).
//!
//! Reuse hands a caller a kernel it did not build. The claim that makes this
//! sound is narrow and testable: **a restored template is bit-exactly the kernel
//! a fresh build would have produced**. These tests are that claim, exercised
//! rather than asserted.
//!
//! The comparison is deliberately whole-environment rather than spot-checked.
//! `render_lean4export_ndjson` serialises every admitted declaration — names,
//! universes, types and proof bodies — in a deterministic order, so two kernels
//! agreeing on those bytes agree on everything the kernel can be asked about.
//! The per-declaration and axiom-footprint checks below are redundant against
//! it *by design*: they fail with a readable diff, whereas an NDJSON mismatch
//! only says "somewhere".

use super::{enabled, stats, try_restore};
use crate::{
    Declaration, Kernel, Lean4ExportMetadata, PreludeKey, arith_prelude, creal, int_prelude,
    nat_prelude, prelude,
};

/// A whole-environment fingerprint: every declaration this kernel has admitted.
fn export_fingerprint(kernel: &Kernel) -> String {
    kernel
        .render_lean4export_ndjson(&Lean4ExportMetadata::axeyum("test"))
        .expect("a prelude environment must export")
}

/// Declaration name, kind and rendered type, in the environment's own order.
fn declaration_inventory(kernel: &Kernel) -> Vec<(String, &'static str, String)> {
    kernel
        .environment()
        .iter()
        .map(|(_, declaration)| {
            let (kind, name, ty) = match declaration {
                Declaration::Axiom { name, ty, .. } => ("axiom", name, ty),
                Declaration::Opaque { name, ty, .. } => ("opaque", name, ty),
                Declaration::Quotient { name, ty, .. } => ("quotient", name, ty),
                Declaration::Definition { name, ty, .. } => ("definition", name, ty),
                Declaration::Theorem { name, ty, .. } => ("theorem", name, ty),
                Declaration::Inductive { name, ty, .. } => ("inductive", name, ty),
                Declaration::Constructor { name, ty, .. } => ("constructor", name, ty),
                Declaration::Recursor { name, ty, .. } => ("recursor", name, ty),
            };
            (
                kernel.display_name(*name).to_string(),
                kind,
                kernel.render_lean(*ty),
            )
        })
        .collect()
}

/// The trusted surface (every declaration admitted without a checked body),
/// which is the number the project's axiom-freedom claim is made of.
fn trusted_surface(kernel: &Kernel) -> Vec<String> {
    let mut names: Vec<String> = kernel
        .environment()
        .iter()
        .filter_map(|(_, declaration)| match declaration {
            Declaration::Axiom { name, .. }
            | Declaration::Opaque { name, .. }
            | Declaration::Quotient { name, .. } => Some(kernel.display_name(*name).to_string()),
            _ => None,
        })
        .collect();
    names.sort();
    names
}

/// Builds `key` twice — once through the uncached trusted gate, once through the
/// process-wide template — and requires the two kernels to be indistinguishable.
/// Runs the comparison on an explicit deep stack.
///
/// Measured 2026-08-26: `CReal.integral` and its convergence bridges grew the
/// shared prelude past the default 2 MiB a `#[test]` thread gets, and this was
/// the THIRD module to cross that line in one session (after `creal_tests` and
/// `creal_model_tests`). Per `artifacts/kernel-stack-envelope.tsv` the `creal`
/// prelude needed **exactly** the default in debug, so there was never any
/// margin and each new declaration spends into a deficit.
///
/// Wrapped at the shared HELPER rather than at any one test, because the
/// failing test name is arbitrary when a shared builder blows the stack —
/// whichever caller runs first pays the whole cost, so protecting one just
/// elects a new victim. Confirmed a resource limit, not runaway recursion, by
/// `--release` passing.
fn assert_reuse_matches_fresh_build(key: PreludeKey, label: &'static str) {
    crate::on_a_deep_stack(move || assert_reuse_matches_fresh_build_body(key, label));
}

fn assert_reuse_matches_fresh_build_body(key: PreludeKey, label: &'static str) {
    let mut fresh = Kernel::new();
    match key {
        PreludeKey::Logic => {
            prelude::build_logic_prelude_uncached(&mut fresh).expect("logic must build");
        }
        PreludeKey::Nat => {
            nat_prelude::build_nat_prelude_uncached(&mut fresh).expect("nat must build");
        }
        PreludeKey::Int => {
            int_prelude::build_int_prelude_uncached(&mut fresh).expect("int must build");
        }
        PreludeKey::Real => {
            arith_prelude::build_arith_prelude_uncached(&mut fresh).expect("real must build");
        }
        PreludeKey::CReal => {
            creal::build_creal_prelude_uncached(&mut fresh).expect("creal must build");
        }
        PreludeKey::List => unreachable!("list preludes have no template yet"),
        PreludeKey::String(_) => unreachable!("string preludes have no template"),
    }

    let mut restored = Kernel::new();
    let value = try_restore(&mut restored, key)
        .unwrap_or_else(|| panic!("{label}: template restore must succeed when the cache is on"));

    // The registered package must be the same value the fresh build registered.
    let fresh_value = fresh
        .cached_prelude(key)
        .expect("fresh package must validate")
        .expect("fresh build must register its package");
    assert_eq!(value, fresh_value, "{label}: registered package differs");

    assert_eq!(
        fresh.environment().len(),
        restored.environment().len(),
        "{label}: declaration count differs"
    );
    assert_eq!(
        declaration_inventory(&fresh),
        declaration_inventory(&restored),
        "{label}: declaration inventory differs"
    );
    assert_eq!(
        trusted_surface(&fresh),
        trusted_surface(&restored),
        "{label}: trusted surface differs"
    );
    assert_eq!(
        export_fingerprint(&fresh),
        export_fingerprint(&restored),
        "{label}: exported environment differs"
    );
}

#[test]
fn logic_reuse_matches_fresh_build() {
    assert_reuse_matches_fresh_build(PreludeKey::Logic, "logic");
}

#[test]
fn nat_reuse_matches_fresh_build() {
    assert_reuse_matches_fresh_build(PreludeKey::Nat, "nat");
}

#[test]
fn int_reuse_matches_fresh_build() {
    assert_reuse_matches_fresh_build(PreludeKey::Int, "integer");
}

#[test]
fn real_reuse_matches_fresh_build() {
    assert_reuse_matches_fresh_build(PreludeKey::Real, "real");
}

/// The constructed reals: the most expensive template and the one whose reuse
/// the shipped LRA/SOS carrier depends on, so its bit-exactness is checked by
/// the same whole-environment comparison as the rest.
///
/// This test builds `CReal` twice through the trusted gate and is therefore the
/// slowest in the crate (~90 s in a debug build). That is the price of checking
/// the claim rather than assuming it; the whole point of the template is that
/// nothing *else* pays it.
#[test]
fn creal_reuse_matches_fresh_build() {
    assert_reuse_matches_fresh_build(PreludeKey::CReal, "creal");
}

/// The `CReal` slot restores the **constructed** reals and not some *other*
/// prelude — the failure this test exists for is silent and catastrophic.
///
/// A template slot wired to the wrong builder hands back the axiomatized `Real`
/// package under the name `CReal`. Everything still builds, every test that only
/// checks "a prelude came back" still passes, and the project's headline claim —
/// that the constructed carrier assumes nothing — is quietly false. So the
/// identity of the restored package is asserted three independent ways:
///
/// 1. the trusted surface is **empty** (the `Real` package would show 30);
/// 2. `CReal` and its setoid equality are **present** — a declaration the `Real`
///    package does not have;
/// 3. `Real`, the axiomatized carrier, is **absent** — a declaration the
///    constructed development does not have.
///
/// Checks 2 and 3 are not redundant with 1: a mis-wire to any other axiom-free
/// prelude (`Nat`, `Int`, `Rat`) passes 1 and fails 2.
#[test]
fn the_creal_slot_restores_the_constructed_reals_and_nothing_else() {
    let mut kernel = Kernel::new();
    let value =
        try_restore(&mut kernel, PreludeKey::CReal).expect("the CReal template must restore");
    // The registered package's own variant. A slot serving another prelude's
    // template fails `cached_prelude(CReal)` and never gets here, so this is the
    // direct form of the identity claim; the environment checks below are the
    // independent one.
    assert!(
        matches!(value, crate::PreludeValue::CReal(_)),
        "the CReal slot registered a package of another prelude: {value:?}"
    );

    let surface = trusted_surface(&kernel);
    assert!(
        surface.is_empty(),
        "the constructed reals must stay axiom-free through reuse; found: {surface:?}"
    );

    let names: std::collections::BTreeSet<String> = declaration_inventory(&kernel)
        .into_iter()
        .map(|(name, _, _)| name)
        .collect();
    for required in ["CReal", "CReal.Equiv", "CReal.add", "CReal.le"] {
        assert!(
            names.contains(required),
            "the CReal slot restored a kernel without `{required}`, so it is not \
             the constructed real development"
        );
    }
    assert!(
        !names.contains("AxReal"),
        "the CReal slot restored a kernel carrying the AXIOMATIZED `AxReal` \
         carrier -- the slot is wired to the wrong builder"
    );

    // Negative control: an empty environment would satisfy the surface
    // assertion vacuously. The construction is ~200 declarations.
    assert!(
        kernel.environment().len() > 100,
        "the restored CReal kernel is suspiciously small: {}",
        kernel.environment().len()
    );
}

/// The standing invariants. A change in any of these numbers is a failure, not
/// a new baseline: `nat` axiom-freedom is this kernel's headline claim, and the
/// `integer`/`real` counts are asserted-by-design surfaces whose growth would
/// mean something previously proved is now assumed.
#[test]
fn reuse_preserves_the_trusted_surface_invariants() {
    let mut nat = Kernel::new();
    nat_prelude::build_nat_prelude(&mut nat).expect("nat must build");
    assert_eq!(trusted_surface(&nat).len(), 0, "nat must be axiom-free");

    let mut logic = Kernel::new();
    prelude::build_logic_prelude(&mut logic).expect("logic must build");
    assert_eq!(trusted_surface(&logic).len(), 0, "logic must be axiom-free");

    let mut int = Kernel::new();
    int_prelude::build_int_prelude(&mut int).expect("int must build");
    assert_eq!(
        trusted_surface(&int).len(),
        0,
        "integer must be axiom-free: Int.euclidean_decomposition, its last \
         assumption, became a theorem on 2026-08-16"
    );
}

/// **The negative test.** Reuse must not share mutable state: mutating a kernel
/// obtained from a template must be invisible to every later restore.
///
/// Written against the observable API rather than the template internals,
/// because that is the surface a future caller could actually reach.
#[test]
fn mutating_a_restored_kernel_cannot_affect_a_later_restore() {
    let mut first = Kernel::new();
    try_restore(&mut first, PreludeKey::Nat).expect("first restore");
    let baseline = export_fingerprint(&first);
    let baseline_len = first.environment().len();

    // Mutate the restored kernel: admit a fresh declaration through the trusted
    // gate, and intern names/levels/expressions along the way.
    let anon = first.anon();
    let marker = first.name_str(anon, "PreludeCacheMutationMarker");
    let prop = first.sort_zero();
    first
        .add_inductive(marker, &[], 0, prop, &[])
        .expect("marker inductive must be admitted");
    assert!(
        first.environment().len() > baseline_len,
        "the mutation must actually have changed the kernel"
    );
    assert!(
        first.environment().contains(marker),
        "the marker must be present in the mutated kernel"
    );

    // A later restore must see none of it.
    let mut second = Kernel::new();
    try_restore(&mut second, PreludeKey::Nat).expect("second restore");
    assert!(
        !second.environment().contains(marker),
        "a later restore observed a mutation made to an earlier one: \
         the template is being shared mutably"
    );
    assert_eq!(
        second.environment().len(),
        baseline_len,
        "a later restore differs in size from the first"
    );
    assert_eq!(
        export_fingerprint(&second),
        baseline,
        "a later restore differs from the first"
    );

    // And the mutated kernel keeps its own mutation — the copies are independent
    // in both directions, not merely defensively re-cloned.
    assert!(
        first.environment().contains(marker),
        "the earlier kernel lost its own mutation"
    );
}

/// Restoration replaces the whole kernel, so it must decline any kernel that
/// already carries content a caller could observe.
#[test]
fn a_used_kernel_is_never_overwritten() {
    let mut kernel = Kernel::new();
    let anon = kernel.anon();
    let name = kernel.name_str(anon, "AlreadyUsed");
    assert!(
        !kernel.is_pristine(),
        "interning a name must make a kernel non-pristine"
    );

    let before = kernel.environment().len();
    assert!(
        try_restore(&mut kernel, PreludeKey::Nat).is_none(),
        "a used kernel must not be restored into"
    );
    assert_eq!(
        kernel.environment().len(),
        before,
        "a declined restore must leave the kernel untouched"
    );
    // The caller's interned handle is still theirs.
    assert_eq!(kernel.display_name(name).to_string(), "AlreadyUsed");
}

/// An environment emptied by rollback is *empty* but not *pristine*: its
/// revision has moved and its insertion log is non-empty. Restoring over it
/// would silently discard that history, so it must be declined.
#[test]
fn a_rolled_back_kernel_is_not_pristine() {
    let mut kernel = Kernel::new();
    let checkpoint = kernel.prelude_checkpoint();
    let anon = kernel.anon();
    let marker = kernel.name_str(anon, "RolledBack");
    let prop = kernel.sort_zero();
    kernel
        .add_inductive(marker, &[], 0, prop, &[])
        .expect("marker inductive must be admitted");
    kernel.rollback_prelude(checkpoint);

    assert!(
        kernel.environment().is_empty(),
        "rollback must empty the environment"
    );
    assert!(
        !kernel.is_pristine(),
        "a rolled-back kernel must not be treated as fresh"
    );
    assert!(
        try_restore(&mut kernel, PreludeKey::Nat).is_none(),
        "a rolled-back kernel must not be restored into"
    );
}

/// String preludes need a caller-held `LogicPrelude`, so they never start from a
/// pristine kernel and deliberately have no template.
#[test]
fn string_preludes_have_no_template() {
    let mut kernel = Kernel::new();
    assert!(try_restore(&mut kernel, PreludeKey::String(2)).is_none());
    assert!(
        kernel.is_pristine(),
        "a declined restore must leave the kernel pristine"
    );
}

/// Defeats the inert-gate trap: an equivalence test that never exercised the
/// cache would pass identically. This proves restores actually happened.
#[test]
fn the_cache_is_actually_exercised() {
    assert!(
        enabled(),
        "the crate's own test suite must run with prelude reuse ON; \
         AXEYUM_PRELUDE_CACHE=0 is for the differential gate only"
    );
    let before = stats();
    let mut kernel = Kernel::new();
    try_restore(&mut kernel, PreludeKey::Logic).expect("restore must succeed");
    let after = stats();
    assert!(
        after.hits > before.hits,
        "a successful restore must be counted as a hit ({before:?} -> {after:?})"
    );
    assert!(
        after.templates_built >= 1,
        "at least one template must have been built ({after:?})"
    );
}
