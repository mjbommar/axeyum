//! Cross-prelude declaration-name collision gate.
//!
//! # The incident this exists for
//!
//! A lane once added `Nat.inverseIndex` for a new bijection on `[0,n)`. That
//! name was already taken -- by
//! `crates/axeyum-lean-kernel/src/int_prelude/wilson.rs`, which declares
//! `Nat.inverseIndex` (and eight lemmas about it) into the `Nat` namespace
//! from the *Int* prelude module, for the modular-inverse index Wilson's
//! theorem needs. Nothing about that collision was visible where it mattered:
//!
//! - `nat_prelude/` (the whole directory) never mentions the name, because
//!   the clash was with a DIFFERENT prelude's file.
//! - `cargo test --lib nat_prelude::` was green: the `nat` prelude builds
//!   fine alone. The collision only fires once `int` (which builds `nat`
//!   first, then adds `wilson.rs`'s declarations on top) shares a kernel with
//!   whatever else declared the name.
//! - The failure that finally surfaced it named neither string nor either
//!   declaring site: `the Int model must build: DeclarationExists { name:
//!   NameId(457) }`, 230 failures deep in `arith_model`/`characterization`.
//!
//! This module turns that into a same-sweep, named-string, named-preludes
//! failure, run BEFORE any of those 230 tests get a chance to hit it.
//!
//! # "Declared under `Nat.`" vs. "declared by the `nat` prelude"
//!
//! These are different questions and this module answers the second one.
//! [`own_declarations`] attributes a name to the prelude MODULE whose build
//! call actually put it in the environment -- computed by diffing each
//! prelude's full declaration set against the one immediately below it in the
//! dependency chain ([`DEPENDS_ON`]), never by looking at the name's own
//! namespace prefix. `Nat.inverseIndex` and its siblings are attributed to
//! `integer` (the module that calls `wilson::declare_wilson`), even though
//! every one of those names lives under the `Nat.` namespace string, because
//! `integer` is what put them in the environment; they are not attributed to
//! `nat` just because their name starts with `Nat.`.
//!
//! # Why a diff, not an actual combined build
//!
//! Two prelude trees only collide for real once both are built into ONE
//! kernel (e.g. [`crate::build_int_model_of_arith`], which builds `axreal`
//! then `integer` in the same kernel). We don't need to enumerate every
//! combiner to catch this: if prelude A and prelude B each introduce (i.e.
//! are the first to declare) the same name, combining ANY two trees that
//! include both A's and B's own contribution will hit
//! [`crate::KernelError::DeclarationExists`] on whichever is added second.
//! So the real invariant is simpler than "every combiner still builds": no
//! two preludes may *introduce* the same name in the first place. That is
//! what [`cross_prelude_collisions`] checks, over every prelude this crate
//! ships.

use std::collections::{BTreeMap, BTreeSet};

use crate::{
    Declaration, Kernel, build_arith_prelude, build_complex_prelude, build_cpoint_prelude,
    build_creal_prelude, build_int_prelude, build_logic_prelude, build_nat_prelude,
    build_rat_prelude, build_string_prelude,
};

/// Every declaration name currently in `kernel`'s environment, in canonical
/// dotted form (`kernel.display_name`, the RAW interned name -- not the
/// `lean_pp` export rename, which is a distinct, non-shadowing rendering used
/// only for Lean text output; see the `AxNat` gotcha in `CLAUDE.md`).
fn declared_names(kernel: &Kernel) -> BTreeSet<String> {
    kernel
        .environment()
        .iter()
        .map(|(name, _)| kernel.display_name(*name).to_string())
        .collect()
}

/// One prelude group: its label and its full (transitive) declaration set.
struct Group {
    label: &'static str,
    all: BTreeSet<String>,
}

/// Build every prelude this crate ships, each in its own fresh kernel, and
/// collect the full (transitive) declaration set each one ends up with.
///
/// Mirrors `examples/prelude_theorem_inventory.rs`'s `build_groups`: same
/// prelude list, same dependency order, same "always include `--include
/// -constructed`'s groups" choice -- `creal`/`complex`/`cpoint` cost real
/// kernel type-checking, but this gate exists precisely to catch a collision
/// wherever one can occur, and skipping the constructed carriers would leave
/// exactly the kind of blind spot this file is about.
fn build_groups() -> Vec<Group> {
    let mut groups = Vec::new();

    let mut logic = Kernel::new();
    build_logic_prelude(&mut logic).expect("logic prelude must build");
    groups.push(Group {
        label: "logic",
        all: declared_names(&logic),
    });

    let mut nat = Kernel::new();
    build_nat_prelude(&mut nat).expect("Nat prelude must build");
    groups.push(Group {
        label: "nat",
        all: declared_names(&nat),
    });

    let mut axreal = Kernel::new();
    build_arith_prelude(&mut axreal).expect("AxReal prelude must build");
    groups.push(Group {
        label: "axreal",
        all: declared_names(&axreal),
    });

    let mut integer = Kernel::new();
    build_int_prelude(&mut integer).expect("Int prelude must build");
    groups.push(Group {
        label: "integer",
        all: declared_names(&integer),
    });

    let mut rat = Kernel::new();
    build_rat_prelude(&mut rat).expect("Rat prelude must build");
    groups.push(Group {
        label: "rat",
        all: declared_names(&rat),
    });

    let mut string = Kernel::new();
    let logic_handle = build_logic_prelude(&mut string).expect("logic prelude must build");
    build_string_prelude(&mut string, logic_handle, 2).expect("string prelude must build");
    groups.push(Group {
        label: "string",
        all: declared_names(&string),
    });

    let mut creal = Kernel::new();
    build_creal_prelude(&mut creal).expect("CReal prelude must build");
    groups.push(Group {
        label: "creal",
        all: declared_names(&creal),
    });

    let mut complex = Kernel::new();
    build_complex_prelude(&mut complex).expect("Complex prelude must build");
    groups.push(Group {
        label: "complex",
        all: declared_names(&complex),
    });

    let mut cpoint = Kernel::new();
    build_cpoint_prelude(&mut cpoint).expect("CPoint prelude must build");
    groups.push(Group {
        label: "cpoint",
        all: declared_names(&cpoint),
    });

    groups
}

/// Each prelude's immediate dependency, matching the internal `build_…`
/// calls each module makes on itself (`nat_prelude.rs` calls
/// `build_logic_prelude`, `int_prelude.rs` calls `build_nat_prelude`, …).
/// `None` for `logic`, the base of the chain. This is what lets
/// [`own_declarations`] tell "introduced by this module" apart from
/// "inherited from the dependency this module builds on top of".
const DEPENDS_ON: &[(&str, Option<&str>)] = &[
    ("logic", None),
    ("nat", Some("logic")),
    ("axreal", Some("logic")),
    ("integer", Some("nat")),
    ("rat", Some("integer")),
    ("string", Some("logic")),
    ("creal", Some("rat")),
    ("complex", Some("creal")),
    ("cpoint", Some("creal")),
];

/// For each prelude PRESENT in `groups`, the names it introduces ITSELF:
/// present in its own full declaration set but absent from the dependency it
/// builds on top of. See the module doc for why this -- not the name's
/// namespace prefix -- is what "declared by prelude X" means here.
///
/// A label in [`DEPENDS_ON`] with no matching entry in `groups` is skipped
/// rather than an error: [`cross_prelude_declaration_names_are_disjoint`]
/// always passes the full [`build_groups`] output (every label present), but
/// the negative control below deliberately runs this over a partial `groups`
/// (only `logic`/`nat`/`axreal`) to keep the injected-collision test cheap,
/// and that must not be treated as `build_groups` missing a prelude.
///
/// # Panics
///
/// Panics if a label present in `groups` names a dependency (via
/// [`DEPENDS_ON`]) that is absent from `groups` -- an inconsistent `groups`
/// value, never a data condition.
fn own_declarations(groups: &[Group]) -> BTreeMap<&'static str, BTreeSet<String>> {
    let by_label: BTreeMap<&str, &BTreeSet<String>> =
        groups.iter().map(|g| (g.label, &g.all)).collect();
    let mut own = BTreeMap::new();
    for &(label, dep) in DEPENDS_ON {
        let Some(&all) = by_label.get(label) else {
            continue;
        };
        let names = match dep {
            None => all.clone(),
            Some(dep_label) => {
                let dep_all = *by_label.get(dep_label).unwrap_or_else(|| {
                    panic!("{label:?} is present but its dependency {dep_label:?} is not")
                });
                all.difference(dep_all).cloned().collect()
            }
        };
        own.insert(label, names);
    }
    own
}

/// Every name introduced by more than one prelude, each paired with the full
/// list of preludes that introduce it (deterministic order: alphabetical by
/// label, from the `BTreeSet` this is built over -- NOT a claim about which
/// declaration is chronologically newer; see [`collision_report`] for why
/// this function does not attempt to guess that).
fn cross_prelude_collisions(
    own: &BTreeMap<&'static str, BTreeSet<String>>,
) -> Vec<(String, Vec<&'static str>)> {
    let mut owners: BTreeMap<String, Vec<&'static str>> = BTreeMap::new();
    for (&label, names) in own {
        for name in names {
            owners.entry(name.clone()).or_default().push(label);
        }
    }
    owners
        .into_iter()
        .filter(|(_, labels)| labels.len() > 1)
        .collect()
}

/// Render [`cross_prelude_collisions`]'s findings as the failure message a
/// lane can act on: the exact string, and every prelude that declares it.
fn collision_report(collisions: &[(String, Vec<&'static str>)]) -> String {
    let mut lines: Vec<String> = collisions
        .iter()
        .map(|(name, owners)| format!("  {name}  <- declared by: {}", owners.join(", ")))
        .collect();
    lines.sort();
    format!(
        "cross-prelude declaration-name collision(s): the name(s) below are each \
         introduced by MORE THAN ONE prelude module. Building both preludes into \
         one kernel (e.g. `build_int_model_of_arith`, or any future combiner) hits \
         `KernelError::DeclarationExists` on whichever is admitted second -- often \
         far from either declaring site, and reported only as an opaque interned \
         id with no string and no owning prelude attached. \
         Rename whichever of the two conflicting declarations is the more recent \
         addition (check `git log -p` on each declaring site) -- the older one may \
         already be load-bearing elsewhere, which is exactly what made the \
         `Nat.inverseIndex` collision this gate is named for expensive to diagnose:\n{}",
        lines.join("\n")
    )
}

/// **The gate.** Every prelude this crate ships must introduce a disjoint set
/// of declaration names. See the module doc for the incident this replaces
/// and why "introduces" is computed by diffing against each prelude's
/// dependency rather than by namespace prefix.
#[test]
fn cross_prelude_declaration_names_are_disjoint() {
    // `build_groups` builds `complex` and `cpoint`, and both overflow the
    // default 2 MiB test-thread stack in a DEBUG build (same reason
    // `complex_tests.rs`/`creal_point_tests.rs` run on a deep-stack thread: the
    // recursion is in the kernel's own type checker over a genuinely large
    // term, not a bug). Without this, `cargo test -p axeyum-lean-kernel --lib`
    // (the ordinary, debug-mode sweep every lane runs) aborts the whole test
    // binary with SIGABRT before any assertion here -- or anywhere else in the
    // same binary -- runs.
    let groups = on_a_deep_stack(build_groups);
    let own = own_declarations(&groups);
    let collisions = cross_prelude_collisions(&own);
    assert!(collisions.is_empty(), "{}", collision_report(&collisions));
}

/// Run `f` on a thread with a **64 MiB stack**. Verbatim copy of
/// `complex_tests.rs`'s helper of the same name; see its doc for why this is
/// not solved with `RUST_MIN_STACK` instead.
fn on_a_deep_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(f)
        .expect("spawning a deep-stack thread must succeed")
        .join()
        .expect("the deep-stack thread must not panic")
}

#[cfg(test)]
mod negative_control {
    use super::{
        Declaration, Group, Kernel, build_arith_prelude, build_nat_prelude,
        cross_prelude_collisions, own_declarations,
    };

    /// Declare one throwaway `AxReal.__collision_probe : True` axiom into
    /// `kernel`, reusing whatever `True` that kernel's own logic prelude
    /// declared. A real declaration through the real trusted gate
    /// (`Kernel::add_declaration`), not a string fixture -- this is genuinely
    /// indistinguishable, from the gate's point of view, from two prelude
    /// modules that happen to pick the same name for two different things.
    fn inject_collision_probe(kernel: &mut Kernel, true_: crate::NameId) {
        let anon = kernel.anon();
        let ns = kernel.name_str(anon, "AxReal");
        let probe = kernel.name_str(ns, "__collision_probe");
        let true_ty = kernel.const_(true_, vec![]);
        kernel
            .add_declaration(Declaration::Axiom {
                name: probe,
                uparams: vec![],
                ty: true_ty,
            })
            .expect(
                "injecting the probe axiom must itself succeed (fresh name, no real clash yet)",
            );
    }

    /// **The negative control.** Build `nat` and `axreal` for real, then
    /// inject the SAME name into both independently -- through the real
    /// trusted gate, not a synthetic map -- and confirm
    /// [`cross_prelude_collisions`] catches it. Also confirms directly that
    /// combining the two mutated kernels for real hits
    /// `KernelError::DeclarationExists`, and NOT the message this gate emits
    /// -- i.e. that the gate's job is to pre-empt exactly that failure mode
    /// with something a lane can act on.
    #[test]
    fn cross_prelude_collision_is_detected_and_named() {
        let mut nat = Kernel::new();
        let nat_prelude = build_nat_prelude(&mut nat).expect("Nat prelude must build");
        inject_collision_probe(&mut nat, nat_prelude.logic.true_);

        let mut axreal = Kernel::new();
        let axreal_prelude = build_arith_prelude(&mut axreal).expect("AxReal prelude must build");
        inject_collision_probe(&mut axreal, axreal_prelude.logic.true_);

        // Run the real pipeline (`build_groups` + diff), with these two
        // mutated kernels swapped in for the pristine ones.
        let groups = vec![
            Group {
                label: "logic",
                all: super::declared_names(&{
                    let mut logic = Kernel::new();
                    crate::build_logic_prelude(&mut logic).expect("logic prelude must build");
                    logic
                }),
            },
            Group {
                label: "nat",
                all: super::declared_names(&nat),
            },
            Group {
                label: "axreal",
                all: super::declared_names(&axreal),
            },
        ];
        let own = own_declarations(&groups);
        let collisions = cross_prelude_collisions(&own);

        assert_eq!(
            collisions.len(),
            1,
            "expected exactly one injected collision, found {collisions:?}"
        );
        let (name, owners) = &collisions[0];
        assert_eq!(name, "AxReal.__collision_probe");
        assert_eq!(owners, &vec!["axreal", "nat"]);

        let report = super::collision_report(&collisions);
        assert!(
            report.contains("AxReal.__collision_probe"),
            "gate message must name the colliding string:\n{report}"
        );
        assert!(
            report.contains("nat") && report.contains("axreal"),
            "gate message must name both declaring preludes:\n{report}"
        );
        // The report is allowed to MENTION `KernelError::DeclarationExists`
        // (it does, explaining what this gate pre-empts) -- what it must never
        // do is degrade to the raw, unreadable form the incident actually hit:
        // an opaque interned id with no string and no owning prelude attached.
        assert!(
            !report.contains("NameId("),
            "the gate's OWN failure message must never regress to the raw \
             `NameId(<n>)` form it exists to replace:\n{report}"
        );

        // And: confirm the failure mode this gate replaces really does occur.
        // Combine the two mutated trees into ONE kernel for real (`nat` first,
        // then `axreal`'s declarations replayed on top) and check the SECOND
        // admission of the probe is rejected as `DeclarationExists` -- the raw,
        // unnamed failure the incident this module documents actually hit.
        let mut combined = Kernel::new();
        let combined_nat = build_nat_prelude(&mut combined).expect("Nat prelude must build");
        inject_collision_probe(&mut combined, combined_nat.logic.true_);
        let anon = combined.anon();
        let ns = combined.name_str(anon, "AxReal");
        let probe = combined.name_str(ns, "__collision_probe");
        let true_ty = combined.const_(combined_nat.logic.true_, vec![]);
        let second_admission = combined.add_declaration(Declaration::Axiom {
            name: probe,
            uparams: vec![],
            ty: true_ty,
        });
        assert!(
            matches!(
                second_admission,
                Err(crate::KernelError::DeclarationExists { .. })
            ),
            "expected the raw kernel error this gate pre-empts, got {second_admission:?}"
        );
    }
}
