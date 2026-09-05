//! **The replay census over every carrier the kernel builds** (ADR-1661).
//!
//! # What this adds that `real_lean_replay_census` does not
//!
//! That suite (ADR-0760) grades independent replay per declaration, by name,
//! over **one** carrier: the constructed reals. It is the right discipline and
//! this suite reuses it verbatim — `tests/support/replay_census.rs` holds the
//! classifier, the exporter call and the grading function, so the two suites
//! cannot drift. What it did not do is say anything about ℕ, ℤ, ℚ, the
//! intuitionistic-logic package, `List`, `String`, the axiomatized reals, ℂ,
//! the plane, the metric layer, the integration space or ℝⁿ.
//!
//! So the chair's headline — *N axiom-free results* — could not be paired with
//! *and pinned Lean's kernel accepts M of them*, because M existed for one
//! carrier. This suite measures the rest.
//!
//! # The population is derived, and the derivation is gated
//!
//! A test named "every X" that iterates its own list measures the maintainer's
//! memory. So [`every_public_prelude_builder_is_accounted_for`] reads the
//! crate's own `pub use` re-export block out of `src/lib.rs` — the authority
//! for what this kernel offers to build — extracts every `build_*` name in it,
//! and requires each to appear in [`BUILDERS`] with a disposition: it is what a
//! census carrier runs, it is run transitively by one that is, or it is
//! explicitly not a carrier with a stated reason. Adding a prelude to the crate
//! without adding it to the census fails that test.
//!
//! # One test per carrier, deliberately
//!
//! Each carrier is its own `#[test]` so it can be run — or honestly reported as
//! *did not run* — on its own. The constructive carriers are supersets of the
//! constructed reals and cost minutes each; a single test over all of them
//! would make "the census is green" mean "whichever carriers fit in the
//! budget", which is exactly the shape of claim this repository keeps having to
//! retract. Run them one at a time:
//!
//! ```sh
//! scripts/cargo-serialized.sh test --release -p axeyum-lean-kernel \
//!   --test real_lean_replay_census_all -- --test-threads=1 --nocapture nat
//! ```
//!
//! Concurrency is bounded by a lock inside the suite
//! ([`ONE_CARRIER_AT_A_TIME`]) rather than by that flag, because
//! `scripts/check-lean-gate.sh` runs this suite with the default thread count
//! and a rule written only in a comment is enforced only on whoever read it.

use std::collections::BTreeSet;
use std::path::Path;
use std::sync::{Mutex, PoisonError};

use axeyum_lean_kernel::{
    Kernel, build_arith_prelude, build_characterization, build_complex_prelude,
    build_cpoint_prelude, build_creal_model_of_arith, build_int_model_of_arith, build_int_prelude,
    build_intspace_prelude, build_ipc_eval_prelude, build_ipc_soundness_prelude,
    build_list_nat_bridge, build_list_perm, build_logic_prelude, build_metric_prelude,
    build_nat_prelude, build_rat_model_of_arith, build_rat_prelude, build_rn_prelude,
    build_string_length_append, build_string_prelude, build_string_substr_arithmetic,
    on_a_deep_stack,
};

#[path = "support/lean_probe.rs"]
mod lean_probe;
#[path = "support/replay_census.rs"]
mod replay_census;

use replay_census::{CarrierCensus, Representability, census_carrier, classify, is_a_proposition};

const TAG: &str = "replay-census-all";

/// The carrier that builds every other carrier into ONE kernel.
///
/// The per-carrier rows nest, so they cannot be added up: `rn` ⊇ `metric` ⊇
/// `cpoint` ⊇ `creal` ⊇ `rat` ⊇ `int` ⊇ `nat` ⊇ `logic`. A headline like "of N
/// proved declarations Lean accepts M" must be read from this row and from no
/// other.
const UNION_CARRIER: &str = "everything";

// ---------------------------------------------------------------------------
// The carriers.
// ---------------------------------------------------------------------------

/// One census carrier: a label, the construction that fills a fresh kernel with
/// it, and the monotone floor on how many of its declarations pinned Lean's
/// kernel must admit **by name**.
struct Carrier {
    name: &'static str,
    build: fn(&mut Kernel),
    /// Set below the measured value with headroom, so ordinary churn does not
    /// trip it. It may only RISE; LOWERING one needs a reason in the commit
    /// message. It is a ratchet against silent shrinkage, never a target — the
    /// check that cannot be satisfied by admitting fewer things is
    /// `missing == 0`, which `census_carrier` enforces separately.
    floor: usize,
}

/// Every census carrier, with the floors measured 2026-09-05 on pinned Lean
/// 4.34.0-rc1 (see `artifacts/measurements/lean-replay-census-2026-09-05.md`).
///
/// `creal` is deliberately absent: it is the subject of
/// `real_lean_replay_census`, which carries its own floor and its own mutation
/// controls, and duplicating it here would double a two-minute run and give one
/// ratchet two homes. The two suites together are the census.
static CARRIERS: &[Carrier] = &[
    Carrier {
        name: "logic",
        build: |k| {
            build_logic_prelude(k).expect("the logic prelude must build");
        },
        floor: 90,
    },
    Carrier {
        name: "nat",
        build: |k| {
            build_nat_prelude(k).expect("the Nat prelude must build");
        },
        floor: 1_900,
    },
    Carrier {
        name: "axreal",
        build: |k| {
            build_arith_prelude(k).expect("the AxReal prelude must build");
        },
        floor: 120,
    },
    Carrier {
        name: "int",
        build: |k| {
            build_int_prelude(k).expect("the Int prelude must build");
        },
        floor: 2_250,
    },
    Carrier {
        name: "characterization",
        build: |k| {
            build_characterization(k).expect("the Nat/Int characterization must build");
        },
        floor: 2_300,
    },
    Carrier {
        name: "ipc",
        build: |k| {
            build_ipc_soundness_prelude(k).expect("the IPC soundness prelude must build");
        },
        floor: 1_900,
    },
    Carrier {
        name: "ipc_eval",
        build: |k| {
            build_ipc_eval_prelude(k).expect("the IPC evaluation prelude must build");
        },
        floor: 1_900,
    },
    Carrier {
        name: "list",
        build: |k| {
            let (list, nat, bridge) =
                build_list_nat_bridge(k).expect("the List/Nat bridge must build");
            build_list_perm(k, &list, &nat, &bridge).expect("List.Perm must build");
        },
        floor: 1_900,
    },
    Carrier {
        name: "rat",
        build: |k| {
            build_rat_prelude(k).expect("the Rat prelude must build");
        },
        floor: 2_850,
    },
    Carrier {
        name: "string",
        build: |k| {
            // On `nat` rather than on `logic` alone: `build_string_length_append`
            // and `build_string_substr_arithmetic` are the arithmetic half of
            // the string surface and both take a `NatPrelude`. A `string`
            // carrier without them would silently omit the two theorems that
            // are the reason the carrier is interesting.
            let nat = build_nat_prelude(k).expect("the Nat prelude must build");
            let sp = build_string_prelude(k, nat.logic, 2).expect("the String prelude must build");
            build_string_length_append(k, &sp, &nat).expect("String.length_append must build");
            build_string_substr_arithmetic(k, &sp, &nat)
                .expect("String.substr_append_split must build");
        },
        floor: 2_000,
    },
    Carrier {
        name: "arith_models",
        build: |k| {
            // The three interpretations of the axiomatized reals. Each builds
            // `AxReal` plus its model carrier, so this one kernel carries the
            // whole model-of-arith surface — including the `CReal` model, which
            // is why it is priced with the constructive carriers below.
            build_int_model_of_arith(k).expect("the Int model of AxReal must build");
            build_rat_model_of_arith(k).expect("the Rat model of AxReal must build");
            build_creal_model_of_arith(k).expect("the CReal model of AxReal must build");
        },
        floor: 3_450,
    },
    Carrier {
        name: "complex",
        build: |k| {
            build_complex_prelude(k).expect("the Complex prelude must build");
        },
        floor: 3_500,
    },
    Carrier {
        name: "cpoint",
        build: |k| {
            build_cpoint_prelude(k).expect("the CPoint prelude must build");
        },
        floor: 3_500,
    },
    Carrier {
        name: "metric",
        build: |k| {
            build_metric_prelude(k).expect("the Metric prelude must build");
        },
        floor: 3_600,
    },
    Carrier {
        name: "intspace",
        build: |k| {
            build_intspace_prelude(k).expect("the IntSpace prelude must build");
        },
        floor: 3_700,
    },
    Carrier {
        name: "rn",
        build: |k| {
            build_rn_prelude(k).expect("the RN prelude must build");
        },
        floor: 3_650,
    },
    Carrier {
        name: "everything",
        build: |k| {
            // ONE kernel carrying every carrier above, so the headline number is
            // a UNION and not a sum. The per-carrier rows nest -- `rn` contains
            // `metric` contains `cpoint` contains `creal` contains `rat`
            // contains `int` contains `nat` contains `logic` -- so adding them
            // up counts most declarations several times over. This row is the
            // only one a reader may quote as "of N proved declarations, pinned
            // Lean's kernel accepts M".
            //
            // Dependency order, deepest first. Every builder here is idempotent
            // (each checks whether its own carrier is already present and
            // returns), so the shared layers are built once.
            build_rn_prelude(k).expect("the RN prelude must build");
            build_intspace_prelude(k).expect("the IntSpace prelude must build");
            build_complex_prelude(k).expect("the Complex prelude must build");
            build_characterization(k).expect("the Nat/Int characterization must build");
            // `build_ipc_soundness_prelude` calls `ipc_eval::declare_eval`
            // itself, so `build_ipc_eval_prelude` is NOT idempotent after it --
            // it re-declares `Ipc.eval` and the kernel refuses the duplicate
            // (`DeclarationExists`). The `ipc_eval` carrier row above measures
            // that prelude on its own; here it is already inside `ipc`.
            build_ipc_soundness_prelude(k).expect("the IPC soundness prelude must build");
            let (list, nat, bridge) =
                build_list_nat_bridge(k).expect("the List/Nat bridge must build");
            build_list_perm(k, &list, &nat, &bridge).expect("List.Perm must build");
            let sp = build_string_prelude(k, nat.logic, 2).expect("the String prelude must build");
            build_string_length_append(k, &sp, &nat).expect("String.length_append must build");
            build_string_substr_arithmetic(k, &sp, &nat)
                .expect("String.substr_append_split must build");
            build_int_model_of_arith(k).expect("the Int model of AxReal must build");
            build_rat_model_of_arith(k).expect("the Rat model of AxReal must build");
            build_creal_model_of_arith(k).expect("the CReal model of AxReal must build");
        },
        floor: 4_000,
    },
];

/// Where a public builder sits relative to the census.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Disposition {
    /// A census carrier runs this builder directly.
    Carrier(&'static str),
    /// A census carrier's build runs it transitively.
    CoveredBy(&'static str),
    /// Not a carrier, with the reason.
    NotACarrier(&'static str),
}

/// Every `build_*` this crate re-exports, and what the census does with it.
///
/// The KEYS are checked against `src/lib.rs`'s re-export block by
/// [`every_public_prelude_builder_is_accounted_for`], in both directions: a
/// builder the crate exports and this table omits is a gap in the census, and a
/// name here that the crate no longer exports is a stale row.
static BUILDERS: &[(&str, Disposition)] = &[
    ("build_logic_prelude", Disposition::Carrier("logic")),
    ("build_nat_prelude", Disposition::Carrier("nat")),
    ("build_arith_prelude", Disposition::Carrier("axreal")),
    ("build_int_prelude", Disposition::Carrier("int")),
    (
        "build_characterization",
        Disposition::Carrier("characterization"),
    ),
    (
        "build_characterization_with",
        Disposition::NotACarrier(
            "the deliberate-defect injector: it takes a `Weakening` and exists to \
             build a characterization that is WRONG on purpose. \
             `build_characterization` is `_with(Weakening::None)`, and that is the \
             carrier",
        ),
    ),
    ("build_ipc_soundness_prelude", Disposition::Carrier("ipc")),
    ("build_ipc_provable_prelude", Disposition::CoveredBy("ipc")),
    ("build_ipc_heyting_prelude", Disposition::CoveredBy("ipc")),
    ("build_ipc_eval_prelude", Disposition::Carrier("ipc_eval")),
    ("build_list_prelude", Disposition::CoveredBy("list")),
    ("build_list_nat_bridge", Disposition::Carrier("list")),
    ("build_list_perm", Disposition::Carrier("list")),
    ("build_rat_prelude", Disposition::Carrier("rat")),
    ("build_string_prelude", Disposition::Carrier("string")),
    ("build_string_length_append", Disposition::Carrier("string")),
    (
        "build_string_substr_arithmetic",
        Disposition::Carrier("string"),
    ),
    (
        "build_creal_prelude",
        Disposition::NotACarrier(
            "the `creal` carrier is the subject of `real_lean_replay_census` \
             (ADR-0760), which carries its own floor of 1,900 and its own \
             mutation controls. Duplicating it here would double a four-minute \
             run and give the ratchet two homes",
        ),
    ),
    ("build_complex_prelude", Disposition::Carrier("complex")),
    ("build_cpoint_prelude", Disposition::Carrier("cpoint")),
    ("build_metric_prelude", Disposition::Carrier("metric")),
    ("build_intspace_prelude", Disposition::Carrier("intspace")),
    ("build_rn_prelude", Disposition::Carrier("rn")),
    (
        "build_int_model_of_arith",
        Disposition::Carrier("arith_models"),
    ),
    (
        "build_rat_model_of_arith",
        Disposition::Carrier("arith_models"),
    ),
    (
        "build_creal_model_of_arith",
        Disposition::Carrier("arith_models"),
    ),
];

// ---------------------------------------------------------------------------
// The coverage guard: the carrier list is derived from the crate, not recalled.
// ---------------------------------------------------------------------------

/// Every `build_*` name in `src/lib.rs`'s `pub use` re-export block.
///
/// Read from the file rather than from a list, because the point of this guard
/// is to notice a builder nobody told it about. Only `pub use` statements are
/// scanned: a `build_*` mentioned in a doc comment is not a public surface.
fn exported_builders() -> BTreeSet<String> {
    let lib = Path::new(env!("CARGO_MANIFEST_DIR")).join("src/lib.rs");
    let text = std::fs::read_to_string(&lib).expect("src/lib.rs must be readable");
    let mut names = BTreeSet::new();
    let mut in_use = false;
    for line in text.lines() {
        let trimmed = line.trim_start();
        if trimmed.starts_with("pub use ") {
            in_use = true;
        }
        if in_use {
            let mut rest = trimmed;
            while let Some(at) = rest.find("build_") {
                let tail = &rest[at..];
                let end = tail
                    .find(|c: char| !c.is_ascii_alphanumeric() && c != '_')
                    .unwrap_or(tail.len());
                names.insert(tail[..end].to_owned());
                rest = &tail[end..];
            }
            if trimmed.ends_with(';') {
                in_use = false;
            }
        }
    }
    names
}

#[test]
fn every_public_prelude_builder_is_accounted_for() {
    let exported = exported_builders();

    // Positive control: an empty result from a scanner that never found its
    // subject is indistinguishable from "the crate exports no builders". Two
    // builders that have existed for the whole life of this crate must be here,
    // or the parse is wrong rather than the crate.
    assert!(
        exported.contains("build_nat_prelude") && exported.contains("build_creal_prelude"),
        "the `pub use` scan did not find builders that are certainly exported, so \
         it is measuring its own parse and not the crate: {exported:?}"
    );

    let tabled: BTreeSet<String> = BUILDERS
        .iter()
        .map(|(name, _)| (*name).to_owned())
        .collect();

    let unaccounted: Vec<&String> = exported.difference(&tabled).collect();
    assert!(
        unaccounted.is_empty(),
        "these builders are public surface of `axeyum-lean-kernel` and the replay \
         census says nothing about them. Add each to `BUILDERS` as a carrier, as \
         covered by one, or as explicitly not a carrier WITH A REASON: \
         {unaccounted:?}"
    );

    let stale: Vec<&String> = tabled.difference(&exported).collect();
    assert!(
        stale.is_empty(),
        "`BUILDERS` names builders the crate no longer exports, so the census is \
         accounted against a surface that moved: {stale:?}"
    );

    // Every `Carrier`/`CoveredBy` target must be a real carrier, or a row could
    // discharge a builder onto a carrier nothing runs.
    let carriers: BTreeSet<&str> = CARRIERS.iter().map(|c| c.name).collect();
    for (builder, disposition) in BUILDERS {
        match disposition {
            Disposition::Carrier(target) | Disposition::CoveredBy(target) => assert!(
                carriers.contains(target),
                "`{builder}` is accounted to carrier `{target}`, which no `Carrier` \
                 entry defines"
            ),
            Disposition::NotACarrier(reason) => assert!(
                reason.len() > 40,
                "`{builder}` is excluded from the census without a stated reason"
            ),
        }
    }

    // Every carrier must be named by at least one builder row, or a carrier
    // could exist that no public surface produces. `everything` is the one
    // exception and it is named here rather than skipped by a wildcard: it runs
    // no builder of its own, it runs ALL of them into one kernel so the headline
    // is a union rather than a sum of overlapping rows.
    for carrier in &carriers {
        if *carrier == UNION_CARRIER {
            continue;
        }
        assert!(
            BUILDERS
                .iter()
                .any(|(_, d)| *d == Disposition::Carrier(carrier)),
            "carrier `{carrier}` is run by no builder in `BUILDERS`"
        );
    }
    assert!(
        carriers.contains(UNION_CARRIER),
        "the union carrier `{UNION_CARRIER}` is gone, so nothing measures the \
         combined population and the per-carrier rows -- which NEST -- would have \
         to be added up to get a headline, which double-counts"
    );

    println!(
        "{} carriers={} builders={}",
        replay_census::CENSUS_MARKER,
        carriers.len(),
        exported.len()
    );
}

// ---------------------------------------------------------------------------
// The classifier's own controls, which need no Lean.
// ---------------------------------------------------------------------------

/// `is_a_proposition` must DISCRIMINATE.
///
/// Without both halves a classifier that had started saying "yes" — or "no" —
/// to everything would leave every census in this file green: an all-yes
/// classifier exports `Type`-valued theorems Lean then rejects (loudly), but an
/// all-no classifier exports nothing and every `missing == 0` passes over an
/// empty set. `census_carrier` guards the empty case; this guards the reason.
#[test]
fn the_representability_classifier_separates_prop_from_type() {
    on_a_deep_stack(|| {
        let mut kernel = Kernel::new();
        let nat = build_nat_prelude(&mut kernel).expect("the Nat prelude must build");

        let true_ = kernel.const_(nat.logic.true_, vec![]);
        assert!(
            is_a_proposition(&mut kernel, true_),
            "`True : Prop`, so the classifier must call it a proposition; if it \
             does not, every census here is exporting an empty slice"
        );

        let nat_ty = kernel.const_(nat.nat, vec![]);
        assert!(
            !is_a_proposition(&mut kernel, nat_ty),
            "`Nat : Type`, so the classifier must NOT call it a proposition; if it \
             does, the `theorem_type_not_prop` class is empty by construction and \
             the census is understating what Lean refuses"
        );
    });
}

/// A carrier with no `Type`-valued theorem must report an EMPTY blocked class,
/// and one with them must report a non-empty one — the two halves of the
/// dependency pass, checked on a carrier cheap enough to build in seconds.
#[test]
fn the_blocked_class_is_empty_exactly_when_the_not_prop_class_is() {
    on_a_deep_stack(|| {
        let mut kernel = Kernel::new();
        build_nat_prelude(&mut kernel).expect("the Nat prelude must build");
        let verdicts = classify(&mut kernel);

        let not_prop = verdicts
            .values()
            .filter(|v| **v == Representability::TheoremTypeNotProp)
            .count();
        let blocked = verdicts
            .values()
            .filter(|v| matches!(v, Representability::BlockedBy(_)))
            .count();
        assert!(
            not_prop > 0 || blocked == 0,
            "`nat` reports {blocked} declarations blocked behind {not_prop} \
             non-representable ones, which cannot happen: a blocker must itself be \
             in the census"
        );

        // Positive half: the classifier produced verdicts at all.
        let representable = verdicts
            .values()
            .filter(|v| **v == Representability::Representable)
            .count();
        assert!(
            representable > 0,
            "`nat` classified nothing as representable, so the census over it \
             would export an empty slice and pass"
        );
        println!(
            "{} carrier=nat classifier-control representable={representable} \
             theorem_type_not_prop={not_prop} blocked_by_dependency={blocked}",
            replay_census::CENSUS_MARKER
        );
    });
}

// ---------------------------------------------------------------------------
// One census per carrier.
// ---------------------------------------------------------------------------

/// Only one carrier is built and censused at a time, whatever the harness's
/// thread count is.
///
/// The seven constructive carriers each hold a full `CReal` kernel, and this
/// suite is registered in `scripts/check-lean-gate.sh`, which runs
/// `cargo test -q -p … --test …` with the DEFAULT thread count. Documenting
/// `--test-threads=1` in the module header would then be a rule enforced only
/// on whoever read it; the gate would run a dozen kernel builds at once and
/// the failure would look like the host's, not this suite's. So the constraint
/// is a lock rather than a sentence.
///
/// It bounds memory, not wall time: the totals are the serial sum either way,
/// because the Lean replays are separate processes and were never the parallel
/// part.
static ONE_CARRIER_AT_A_TIME: Mutex<()> = Mutex::new(());

/// Resolve the carrier, resolve Lean, build, census.
///
/// Lean is resolved BEFORE the build: several of these carriers cost minutes to
/// construct and a skip after that work is a skip nobody waits for.
fn census(name: &'static str) -> Option<CarrierCensus> {
    let carrier = CARRIERS
        .iter()
        .find(|c| c.name == name)
        .unwrap_or_else(|| panic!("no carrier named `{name}`"));
    let lean = lean_probe::lean_bin_or_skip(TAG, 1)?;
    // `into_inner` on a poisoned lock: one carrier failing must let the rest
    // report their OWN verdicts. A poison error here would replace fifteen real
    // findings with one message about a mutex.
    let _serialized = ONE_CARRIER_AT_A_TIME
        .lock()
        .unwrap_or_else(PoisonError::into_inner);
    let census = on_a_deep_stack(move || {
        let mut kernel = Kernel::new();
        (carrier.build)(&mut kernel);
        census_carrier(carrier.name, &mut kernel, &lean, carrier.floor)
    });
    lean_probe::report_checked(TAG, 1);
    Some(census)
}

#[ignore = "nested inside `everything`, which the gate runs; re-derive the per-carrier rows with `-- --ignored` (coordinator, 2026-09-05: seventeen debug-mode Lean replays were unmeasured and the gate is in the push hook)"]
#[test]
fn pinned_lean_admits_the_logic_carrier() {
    census("logic");
}

#[ignore = "nested inside `everything`, which the gate runs; re-derive the per-carrier rows with `-- --ignored` (coordinator, 2026-09-05: seventeen debug-mode Lean replays were unmeasured and the gate is in the push hook)"]
#[test]
fn pinned_lean_admits_the_nat_carrier() {
    census("nat");
}

#[ignore = "nested inside `everything`, which the gate runs; re-derive the per-carrier rows with `-- --ignored` (coordinator, 2026-09-05: seventeen debug-mode Lean replays were unmeasured and the gate is in the push hook)"]
#[test]
fn pinned_lean_admits_the_axreal_carrier() {
    census("axreal");
}

#[ignore = "nested inside `everything`, which the gate runs; re-derive the per-carrier rows with `-- --ignored` (coordinator, 2026-09-05: seventeen debug-mode Lean replays were unmeasured and the gate is in the push hook)"]
#[test]
fn pinned_lean_admits_the_int_carrier() {
    census("int");
}

#[ignore = "nested inside `everything`, which the gate runs; re-derive the per-carrier rows with `-- --ignored` (coordinator, 2026-09-05: seventeen debug-mode Lean replays were unmeasured and the gate is in the push hook)"]
#[test]
fn pinned_lean_admits_the_characterization_carrier() {
    census("characterization");
}

#[ignore = "nested inside `everything`, which the gate runs; re-derive the per-carrier rows with `-- --ignored` (coordinator, 2026-09-05: seventeen debug-mode Lean replays were unmeasured and the gate is in the push hook)"]
#[test]
fn pinned_lean_admits_the_ipc_carrier() {
    census("ipc");
}

#[ignore = "nested inside `everything`, which the gate runs; re-derive the per-carrier rows with `-- --ignored` (coordinator, 2026-09-05: seventeen debug-mode Lean replays were unmeasured and the gate is in the push hook)"]
#[test]
fn pinned_lean_admits_the_ipc_eval_carrier() {
    census("ipc_eval");
}

#[ignore = "nested inside `everything`, which the gate runs; re-derive the per-carrier rows with `-- --ignored` (coordinator, 2026-09-05: seventeen debug-mode Lean replays were unmeasured and the gate is in the push hook)"]
#[test]
fn pinned_lean_admits_the_list_carrier() {
    census("list");
}

#[ignore = "nested inside `everything`, which the gate runs; re-derive the per-carrier rows with `-- --ignored` (coordinator, 2026-09-05: seventeen debug-mode Lean replays were unmeasured and the gate is in the push hook)"]
#[test]
fn pinned_lean_admits_the_rat_carrier() {
    census("rat");
}

#[ignore = "nested inside `everything`, which the gate runs; re-derive the per-carrier rows with `-- --ignored` (coordinator, 2026-09-05: seventeen debug-mode Lean replays were unmeasured and the gate is in the push hook)"]
#[test]
fn pinned_lean_admits_the_string_carrier() {
    census("string");
}

#[ignore = "nested inside `everything`, which the gate runs; re-derive the per-carrier rows with `-- --ignored` (coordinator, 2026-09-05: seventeen debug-mode Lean replays were unmeasured and the gate is in the push hook)"]
#[test]
fn pinned_lean_admits_the_arith_models_carrier() {
    census("arith_models");
}

#[ignore = "nested inside `everything`, which the gate runs; re-derive the per-carrier rows with `-- --ignored` (coordinator, 2026-09-05: seventeen debug-mode Lean replays were unmeasured and the gate is in the push hook)"]
#[test]
fn pinned_lean_admits_the_complex_carrier() {
    census("complex");
}

#[ignore = "nested inside `everything`, which the gate runs; re-derive the per-carrier rows with `-- --ignored` (coordinator, 2026-09-05: seventeen debug-mode Lean replays were unmeasured and the gate is in the push hook)"]
#[test]
fn pinned_lean_admits_the_cpoint_carrier() {
    census("cpoint");
}

#[ignore = "nested inside `everything`, which the gate runs; re-derive the per-carrier rows with `-- --ignored` (coordinator, 2026-09-05: seventeen debug-mode Lean replays were unmeasured and the gate is in the push hook)"]
#[test]
fn pinned_lean_admits_the_metric_carrier() {
    census("metric");
}

#[ignore = "nested inside `everything`, which the gate runs; re-derive the per-carrier rows with `-- --ignored` (coordinator, 2026-09-05: seventeen debug-mode Lean replays were unmeasured and the gate is in the push hook)"]
#[test]
fn pinned_lean_admits_the_intspace_carrier() {
    census("intspace");
}

#[ignore = "nested inside `everything`, which the gate runs; re-derive the per-carrier rows with `-- --ignored` (coordinator, 2026-09-05: seventeen debug-mode Lean replays were unmeasured and the gate is in the push hook)"]
#[test]
fn pinned_lean_admits_the_rn_carrier() {
    census("rn");
}

/// The union of every carrier in one kernel -- the row a headline sentence is
/// read from, because the per-carrier rows nest and so cannot be added up.
#[test]
fn pinned_lean_admits_every_carrier_at_once() {
    census("everything");
}
