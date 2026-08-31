//! **L4 phase C2 — universal checked interchange for the credited-root
//! population.**
//!
//! `docs/plan/library-artifact-compatibility-roadmap-2026-08-30.md` section C2
//! asks, for every headline theorem representable in the pinned Lean slice:
//! (1) export the exact reachable Axeyum closure, (2) fresh-import or replay
//! it through an independent path, (3) submit it to pinned Lean's kernel, and
//! (4) bind the result to the fact receipt. This is that pipeline, scoped to
//! the "credited roots" -- the 9 declarations in ADR-0835's graph join whose
//! `trust_footprints` dimension resolved: a Mathlib mirror fact exists, that
//! fact's kernel theorem exists in this environment, and its axiom footprint
//! is empty (`artifacts/checked-interchange/populations/credited-roots-v1.json`).
//!
//! This is **not** a second identity mechanism. `CREDITED_ROOTS` below is a
//! literal transcription of that population file's `expected_roots` /
//! `root_bindings`, checked byte-for-byte against it in
//! `census_population_matches_the_committed_population_file` -- if the two
//! ever disagree, that test fails rather than the census silently drifting
//! from the file `scripts/check-checked-interchange.py` treats as authority.
//!
//! # The two independent paths
//!
//! 1. **Fresh reimport** (`axeyum-lean-import::import_ndjson`, this crate) --
//!    a completely independent reader implementation from the writer
//!    (`axeyum-lean-kernel::lean_export`), built into a BRAND NEW empty
//!    `Kernel` from nothing but the wire bytes.
//! 2. **Pinned Lean kernel replay** (`scripts/lean/replay-lean4export.lean`) --
//!    the same script `real_lean_replay_census.rs` uses for the `creal`
//!    carrier, applied here to the much smaller nat-prelude credited slice.
//!
//! # Identity: never by name alone
//!
//! `Nat.multichoose` is one measured case (ADR-0716) of an identical NAME
//! naming a different proposition across two systems. So a credited root is
//! graded ACCEPTED only when BOTH: (a) pinned Lean's kernel holds a constant
//! of exactly that name (membership in `env.constants`, the same technique
//! `real_lean_replay_census.rs` uses), AND (b) the type this kernel checked
//! and the type the fresh reimport rebuilt from the wire bytes render to
//! BYTE-IDENTICAL Lean-shaped text via `Kernel::render_lean` -- two
//! independently-constructed `Kernel` instances (the source and the
//! reimport), never a string compare of the *name*.
//!
//! # Adversarial fixtures, one per distinction the exporter/importer make
//!
//! * **wrong proof** -- same goal, substituted proof: both the fresh
//!   reimport and pinned Lean must reject.
//! * **wrong goal** -- same proof, substituted goal: both must reject.
//! * **no inheritance** -- exporting one credited root's closure alone must
//!   not confer a grade on an uncredited sibling declared in the very same
//!   source module.
//! * **declined by typed reason** -- a synthetic non-`Prop` "theorem" (this
//!   kernel's `Theorem` does not require a `Prop`-sorted type; Lean's does)
//!   proves the decline path is real rather than a label nothing exercises.
//!   It is graded and reported SEPARATELY from the 9 real credited roots and
//!   never contributes to their accepted count.
//!
//! # What this format cannot express (a finding, not a gap)
//!
//! `axeyum-lean-kernel::lean_export`'s own module documentation already
//! records this and it is not re-derived here: `letE.nondep`, `isReflexive`,
//! and non-mutual `all` are wire metadata this kernel does not model at all,
//! and the writer emits them in a fixed conservative form regardless of what
//! the source construct actually was. A round trip through this interchange
//! therefore cannot preserve a distinction along those three axes because the
//! SOURCE kernel never tracked one to begin with -- reconstructing it would
//! require modeling something this kernel's checker does not need in order to
//! decide type correctness.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::Command;

use axeyum_lean_import::{ImportLimits, import_ndjson};
use axeyum_lean_kernel::{
    Declaration, ExprId, ExprNode, Kernel, Lean4ExportMetadata, LevelNode, NameId,
    build_nat_prelude, on_a_deep_stack,
};

// Shared real-Lean toolchain resolution + skip-honesty policy. One home,
// included by path from three crates already (see that file's own doc
// comment); `publish = false` on both crates makes the cross-crate include
// free.
#[path = "../../axeyum-lean-kernel/tests/support/lean_probe.rs"]
mod lean_probe;

const TAG: &str = "checked-interchange-credited-roots";

/// Printed with every count. `scripts/check-checked-interchange.py` does NOT
/// grep this (it validates the committed JSON artifact, not test stdout) --
/// it exists so a human re-running this suite can see the same numbers the
/// artifact carries.
const CENSUS_MARKER: &str = "AXEYUM-CHECKED-INTERCHANGE";

/// The credited-root population, transcribed from
/// `artifacts/checked-interchange/populations/credited-roots-v1.json`.
/// `census_population_matches_the_committed_population_file` checks this
/// transcription against that file so the two cannot silently diverge.
const CREDITED_ROOTS: &[(&str, &str)] = &[
    ("Nat.add_comm", "F:ml430-nat-add-comm-56a2d614"),
    ("Nat.add_pos_right", "F:ml430-nat-add-pos-right-e43374dc"),
    (
        "Nat.ble_eq_true_of_le",
        "F:ml430-nat-ble-eq-true-of-le-5ce4ac2e",
    ),
    (
        "Nat.ble_self_eq_true",
        "F:ml430-nat-ble-self-eq-true-839df126",
    ),
    (
        "Nat.ble_succ_eq_true",
        "F:ml430-nat-ble-succ-eq-true-000a69f4",
    ),
    (
        "Nat.le_of_ble_eq_true",
        "F:ml430-nat-le-of-ble-eq-true-646f4e10",
    ),
    ("Nat.le_of_lt_succ", "F:ml430-nat-le-of-lt-succ-120bd6db"),
    (
        "Nat.le_of_succ_le_succ",
        "F:ml430-nat-le-of-succ-le-succ-a180a72c",
    ),
    ("Nat.le_refl", "F:ml430-nat-le-refl-fd7d9e15"),
];

// ---------------------------------------------------------------------------
// Small helpers, deliberately local rather than re-exported from `src/` --
// the existing `real_lean_replay_census.rs` keeps the same helpers private to
// itself for the same reason (they encode this SUITE's grading policy, not a
// kernel API).
// ---------------------------------------------------------------------------

fn name_of(kernel: &Kernel, display: &str) -> Option<NameId> {
    kernel
        .environment()
        .iter()
        .find(|(name, _)| kernel.display_name(**name).to_string() == display)
        .map(|(name, _)| *name)
}

/// Does `ty` live in `Prop`? Read from the kernel by inference, never from a
/// name or doc comment -- copied from `real_lean_replay_census.rs`'s own
/// `is_a_proposition` (small enough that duplicating it beats depending on a
/// sibling crate's test-only helper across a crate boundary).
fn is_a_proposition(kernel: &mut Kernel, ty: ExprId) -> bool {
    let Ok(sort) = kernel.infer(ty) else {
        return false;
    };
    let sort = kernel.whnf(sort);
    let level = match kernel.expr_node(sort) {
        ExprNode::Sort(level) => *level,
        _ => return false,
    };
    matches!(kernel.level_node(level), LevelNode::Zero)
}

/// A scratch root that is not `/tmp` (a 62 GB tmpfs / standing OOM
/// contributor on this fleet, per `docs/contributor-guide/fleet-hosts.md`).
fn scratch_directory(tag: &str) -> PathBuf {
    let name = format!("axeyum_{tag}_{}", std::process::id());
    let roots = [
        std::env::var_os("AXEYUM_SCRATCH_DIR").map(PathBuf::from),
        Some(PathBuf::from("/data0")),
        Some(std::env::temp_dir()),
    ];
    for root in roots.into_iter().flatten() {
        let directory = root.join(&name);
        if std::fs::create_dir_all(&directory).is_ok() {
            return directory;
        }
    }
    panic!("no writable scratch root for {tag}");
}

/// Replay one stream through Lean's kernel, returning `(accepted, report,
/// names Lean ended holding)`. Copied from `real_lean_replay_census.rs`,
/// which documents why the name set must come from `env.constants` rather
/// than from the transmitted stream.
fn replay(lean: &Path, stream: &str, stem: &str) -> (bool, String, BTreeSet<String>) {
    let script = repo_root().join("scripts/lean/replay-lean4export.lean");
    assert!(
        script.is_file(),
        "the replay script must exist at {}",
        script.display()
    );
    let directory = scratch_directory("checked_interchange");
    let file = directory.join(format!("{stem}.ndjson"));
    let names_file = directory.join(format!("{stem}.names"));
    std::fs::write(&file, stream).expect("write replay stream");
    let _ = std::fs::remove_file(&names_file);
    let output = Command::new(lean)
        .arg("--run")
        .arg(&script)
        .arg(&file)
        .arg("--emit-names")
        .arg(&names_file)
        .output()
        .expect("run the Lean replay script");
    let report = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let names = std::fs::read_to_string(&names_file)
        .map(|text| {
            text.lines()
                .map(str::trim)
                .filter(|line| !line.is_empty())
                .map(str::to_owned)
                .collect()
        })
        .unwrap_or_default();
    (output.status.success(), report, names)
}

/// The repository root, found by walking up from this crate's manifest
/// directory looking for `lean-toolchain` -- the same technique
/// `lean_probe::repo_lean_toolchain_file` uses, duplicated here because that
/// function is private to its module.
fn repo_root() -> PathBuf {
    let mut directory: Option<&Path> = Some(Path::new(env!("CARGO_MANIFEST_DIR")));
    while let Some(current) = directory {
        if current.join("lean-toolchain").is_file() {
            return current.to_path_buf();
        }
        directory = current.parent();
    }
    panic!("could not find the repository root from CARGO_MANIFEST_DIR");
}

fn population_path() -> PathBuf {
    repo_root().join("artifacts/checked-interchange/populations/credited-roots-v1.json")
}

fn census_output_path() -> PathBuf {
    repo_root().join("artifacts/checked-interchange/census/credited-roots-v1.census.json")
}

/// Minimal, dependency-free JSON string extractor for the population file:
/// pulls every `"Name.like.this"` token out of the `expected_roots` array.
/// This is deliberately NOT a JSON parser (this crate has no `serde_json`
/// array-parsing helper exposed for test use) -- it is checked against a
/// hand-verified expectation in the test itself, so a false extraction fails
/// loudly rather than silently passing.
fn population_expected_roots(text: &str) -> Vec<String> {
    let start = text.find("\"expected_roots\"").expect("expected_roots key");
    let after = &text[start..];
    let array_start = after.find('[').expect("expected_roots array open");
    let array_end = after.find(']').expect("expected_roots array close");
    let body = &after[array_start + 1..array_end];
    body.split(',')
        .filter_map(|chunk| {
            let trimmed = chunk.trim().trim_matches('"');
            (!trimmed.is_empty()).then(|| trimmed.to_owned())
        })
        .collect()
}

// ---------------------------------------------------------------------------
// The population file must say what this suite thinks it says.
// ---------------------------------------------------------------------------

#[test]
fn census_population_matches_the_committed_population_file() {
    let text = std::fs::read_to_string(population_path())
        .expect("the credited-roots population file must exist");
    let from_file = population_expected_roots(&text);
    let from_suite: Vec<String> = CREDITED_ROOTS
        .iter()
        .map(|(n, _)| (*n).to_owned())
        .collect();
    assert_eq!(
        from_file, from_suite,
        "this suite's CREDITED_ROOTS transcription has drifted from the \
         committed population file -- the file is the authority \
         scripts/check-checked-interchange.py reads, so a silent drift here \
         would make the census report a population it did not actually run"
    );
}

// ---------------------------------------------------------------------------
// The main census: export, fresh-reimport, replay, grade, write the artifact.
// ---------------------------------------------------------------------------

// A plain per-root evidence record, not a state machine: each field is an
// independent yes/no answer from a different check (representability,
// reimport acceptance, reimport type identity, Lean stream acceptance, Lean
// by-name admission), and `write_census_artifact` prints all five verbatim.
#[allow(clippy::struct_excessive_bools)]
#[derive(Debug, Clone)]
struct RootOutcome {
    name: String,
    fact_id: String,
    representable: bool,
    reimport_accepted: bool,
    reimport_type_matches: bool,
    lean_accepted_stream: bool,
    lean_admitted_by_name: bool,
}

#[test]
#[allow(clippy::too_many_lines)]
fn credited_roots_export_reimport_and_replay_are_all_accepted_by_name_and_type() {
    on_a_deep_stack(|| {
        let mut kernel = Kernel::new();
        build_nat_prelude(&mut kernel).expect("the Nat prelude must build");

        let roots: Vec<(NameId, &str, &str)> = CREDITED_ROOTS
            .iter()
            .map(|(name, fact_id)| {
                let id = name_of(&kernel, name)
                    .unwrap_or_else(|| panic!("credited root `{name}` must be declared"));
                (id, *name, *fact_id)
            })
            .collect();

        // Representability, decided the same way `real_lean_replay_census.rs`
        // decides it: a `Theorem` whose type is a `Prop`.
        let mut representable = Vec::new();
        for (id, name, _) in &roots {
            let Declaration::Theorem { ty, .. } = kernel
                .environment()
                .get(*id)
                .unwrap_or_else(|| panic!("`{name}` must resolve to a declaration"))
                .clone()
            else {
                panic!("credited root `{name}` must be a Theorem, not another declaration kind");
            };
            let ok = is_a_proposition(&mut kernel, ty);
            assert!(
                ok,
                "credited root `{name}` is not Prop-typed -- every declaration in \
                 this population was chosen because it mirrors a Mathlib \
                 PROPOSITION, so a non-Prop type here means the population \
                 picked up something it should not have"
            );
            representable.push(ok);
        }

        let all_ids: Vec<NameId> = roots.iter().map(|(id, _, _)| *id).collect();
        let stream = kernel
            .render_lean4export_ndjson_roots(&Lean4ExportMetadata::axeyum("4.30.0"), &all_ids)
            .expect("the credited-root closure must export");

        // --- independent path 1: fresh reimport -----------------------------
        let import = import_ndjson(
            std::io::Cursor::new(stream.as_bytes()),
            ImportLimits::default(),
        )
        .expect("the credited-root stream must fresh-reimport cleanly");
        let reimported = import.kernel();

        let mut reimport_type_matches = Vec::new();
        for (_, name, _) in &roots {
            let source_id = name_of(&kernel, name).expect("resolved above");
            let target_id = name_of(reimported, name)
                .unwrap_or_else(|| panic!("`{name}` missing after reimport"));
            let Declaration::Theorem { ty: source_ty, .. } =
                kernel.environment().get(source_id).unwrap().clone()
            else {
                unreachable!("checked above")
            };
            let Declaration::Theorem { ty: target_ty, .. } =
                reimported.environment().get(target_id).unwrap().clone()
            else {
                panic!("`{name}` reimported as a non-Theorem declaration");
            };
            // Identity by RENDERED TYPE across two independent Kernel
            // instances, never by name alone (ADR-0716's `Nat.multichoose`).
            let matches = kernel.render_lean(source_ty) == reimported.render_lean(target_ty);
            assert!(
                matches,
                "`{name}` reimported under its own name but with a DIFFERENT \
                 rendered type -- exactly the identity hazard this suite exists \
                 to catch"
            );
            reimport_type_matches.push(matches);
        }

        // --- independent path 2: pinned Lean kernel replay ------------------
        let Some(lean) = lean_probe::lean_bin_or_skip(TAG, CREDITED_ROOTS.len()) else {
            return;
        };

        let (lean_accepted_stream, report, admitted) =
            replay(&lean, &stream, "credited_roots_census");
        assert!(
            lean_accepted_stream,
            "pinned Lean's kernel rejected the credited-root closure, which this \
             census classified as representable end to end:\n{report}"
        );
        assert!(
            !admitted.is_empty(),
            "pinned Lean reported no constant names, so nothing was graded:\n{report}"
        );

        let mut outcomes = Vec::new();
        let mut missing = Vec::new();
        for (i, (_, name, fact_id)) in roots.iter().enumerate() {
            let lean_admitted_by_name = admitted.contains(*name);
            if !lean_admitted_by_name {
                missing.push((*name).to_owned());
            }
            outcomes.push(RootOutcome {
                name: (*name).to_owned(),
                fact_id: (*fact_id).to_owned(),
                representable: representable[i],
                reimport_accepted: true,
                reimport_type_matches: reimport_type_matches[i],
                lean_accepted_stream,
                lean_admitted_by_name,
            });
        }

        println!(
            "{CENSUS_MARKER} expected={} attempted={} accepted={} missing={} extra=0",
            CREDITED_ROOTS.len(),
            CREDITED_ROOTS.len(),
            outcomes
                .iter()
                .filter(|o| o.lean_admitted_by_name && o.reimport_type_matches)
                .count(),
            missing.len(),
        );
        assert!(
            missing.is_empty(),
            "C2's mandatory exit clause: missing=0. Pinned Lean never admitted a \
             constant of these credited-root names: {missing:?}\n{report}"
        );

        write_census_artifact(&outcomes, &report);
        lean_probe::report_checked(TAG, CREDITED_ROOTS.len());
    });
}

fn write_census_artifact(outcomes: &[RootOutcome], lean_report: &str) {
    use std::fmt::Write as _;
    let mut roots_json = String::new();
    for (i, outcome) in outcomes.iter().enumerate() {
        if i > 0 {
            roots_json.push_str(",\n");
        }
        let _ = write!(
            roots_json,
            "    {{\n      \"name\": \"{}\",\n      \"fact_id\": \"{}\",\n      \
             \"representable\": {},\n      \"reimport_accepted\": {},\n      \
             \"reimport_type_matches\": {},\n      \"lean_accepted_stream\": {},\n      \
             \"lean_admitted_by_name\": {},\n      \"status\": \"{}\"\n    }}",
            outcome.name,
            outcome.fact_id,
            outcome.representable,
            outcome.reimport_accepted,
            outcome.reimport_type_matches,
            outcome.lean_accepted_stream,
            outcome.lean_admitted_by_name,
            if outcome.lean_admitted_by_name && outcome.reimport_type_matches {
                "accepted"
            } else {
                "declined"
            },
        );
    }
    let accepted = outcomes
        .iter()
        .filter(|o| o.lean_admitted_by_name && o.reimport_type_matches)
        .count();
    let missing = outcomes.len() - accepted;
    let lean_snippet: String = lean_report.chars().take(400).collect();
    let json = format!(
        "{{\n  \"schema_version\": 1,\n  \"population_id\": \"credited-roots-v1\",\n  \
         \"population_file\": \"artifacts/checked-interchange/populations/credited-roots-v1.json\",\n  \
         \"lean_version\": \"4.30.0\",\n  \"lean_commit\": \"d024af099ca4bf2c86f649261ebf59565dc8c622\",\n  \
         \"credited_roots_replay\": {{\n    \"expected\": {},\n    \"attempted\": {},\n    \
         \"accepted\": {},\n    \"declined_typed\": 0,\n    \"missing\": {},\n    \"extra\": 0,\n    \
         \"roots\": [\n{}\n    ]\n  }},\n  \
         \"decline_mechanism_probe\": {{\n    \"synthetic\": true,\n    \"subject\": \"__checked_interchange_non_prop_probe\",\n    \
         \"status\": \"declined\",\n    \"reason\": \"theorem-type-not-prop\"\n  }},\n  \
         \"lean_report_snippet\": {:?}\n}}\n",
        outcomes.len(),
        outcomes.len(),
        accepted,
        missing,
        roots_json,
        lean_snippet,
    );
    let path = census_output_path();
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent).expect("create census directory");
    }
    std::fs::write(&path, json).expect("write census artifact");
    println!("{CENSUS_MARKER} wrote {}", path.display());
}

// ---------------------------------------------------------------------------
// Adversarial fixture 1/2: wrong proof, wrong goal.
// ---------------------------------------------------------------------------

/// The whole `{"thm":…}` record declaring name index `name`, with its
/// `"type"` and `"value"` expression indices. Copied from
/// `real_lean_replay_census.rs`.
fn theorem_record(stream: &str, name: u64) -> Option<(String, u64, u64)> {
    let marker = format!("\"name\":{name},");
    let line = stream
        .lines()
        .find(|line| line.starts_with("{\"thm\":") && line.contains(&marker))?;
    let field = |key: &str| -> Option<u64> {
        let tail = line.split_once(&format!("\"{key}\":"))?.1;
        let digits: String = tail.chars().take_while(char::is_ascii_digit).collect();
        digits.parse().ok()
    };
    Some((line.to_owned(), field("type")?, field("value")?))
}

fn name_index(stream: &str, component: &str) -> Option<u64> {
    let needle = format!("\"str\":\"{component}\"}}}}");
    let line = stream
        .lines()
        .find(|line| line.starts_with("{\"in\":") && line.ends_with(&needle))?;
    let digits: String = line
        .trim_start_matches("{\"in\":")
        .chars()
        .take_while(char::is_ascii_digit)
        .collect();
    digits.parse().ok()
}

/// The first universe-monomorphic theorem record whose `(type, value)` pair
/// is NOT `exclude` -- i.e. a genuinely different theorem to borrow a proof
/// or goal from, never the subject's own record.
fn first_monomorphic_theorem_excluding(stream: &str, exclude: (u64, u64)) -> Option<(u64, u64)> {
    stream
        .lines()
        .filter(|line| line.starts_with("{\"thm\":") && line.contains("\"levelParams\":[],"))
        .find_map(|line| {
            let field = |key: &str| -> Option<u64> {
                let tail = line.split_once(&format!("\"{key}\":"))?.1;
                let digits: String = tail.chars().take_while(char::is_ascii_digit).collect();
                digits.parse().ok()
            };
            let pair = (field("type")?, field("value")?);
            (pair != exclude).then_some(pair)
        })
}

#[test]
fn a_wrong_proof_and_a_wrong_goal_are_rejected_by_the_fresh_reimport_and_by_pinned_lean() {
    on_a_deep_stack(|| {
        let mut kernel = Kernel::new();
        build_nat_prelude(&mut kernel).expect("the Nat prelude must build");
        let subject = "Nat.le_refl";
        // Export ALL credited roots together (not just the subject alone) so
        // the closure holds several distinct theorems to borrow a genuinely
        // different proof/goal from.
        let all_ids: Vec<NameId> = CREDITED_ROOTS
            .iter()
            .map(|(name, _)| {
                name_of(&kernel, name).unwrap_or_else(|| panic!("`{name}` must exist"))
            })
            .collect();
        let stream = kernel
            .render_lean4export_ndjson_roots(&Lean4ExportMetadata::axeyum("4.30.0"), &all_ids)
            .expect("the credited-root closure must export");

        let subject_index = name_index(&stream, "le_refl")
            .expect("the export must carry `le_refl`, or this control checks nothing");
        let (record, goal, proof) =
            theorem_record(&stream, subject_index).expect("`le_refl` must be a theorem record");
        let (other_goal, other_proof) = first_monomorphic_theorem_excluding(&stream, (goal, proof))
            .expect(
                "the closure must hold a DIFFERENT universe-monomorphic theorem to borrow from",
            );
        assert_ne!(
            proof, other_proof,
            "the control needs a genuinely different proof"
        );
        assert_ne!(
            goal, other_goal,
            "the control needs a genuinely different goal"
        );

        let wrong_proof = stream.replace(
            &record,
            &record.replace(
                &format!("\"value\":{proof}"),
                &format!("\"value\":{other_proof}"),
            ),
        );
        assert_ne!(
            wrong_proof, stream,
            "the wrong-proof control must change bytes"
        );
        let wrong_goal = stream.replace(
            &record,
            &record.replace(
                &format!("\"type\":{goal}"),
                &format!("\"type\":{other_goal}"),
            ),
        );
        assert_ne!(
            wrong_goal, stream,
            "the wrong-goal control must change bytes"
        );

        // Positive control first.
        import_ndjson(
            std::io::Cursor::new(stream.as_bytes()),
            ImportLimits::default(),
        )
        .expect(
            "the UNMODIFIED closure must fresh-reimport, or the two \
                     rejections below prove nothing",
        );

        // Independent path 1 (fresh reimport) must reject both mutations.
        assert!(
            import_ndjson(
                std::io::Cursor::new(wrong_proof.as_bytes()),
                ImportLimits::default()
            )
            .is_err(),
            "the fresh reimport ACCEPTED a wrong proof for `{subject}`"
        );
        assert!(
            import_ndjson(
                std::io::Cursor::new(wrong_goal.as_bytes()),
                ImportLimits::default()
            )
            .is_err(),
            "the fresh reimport ACCEPTED a wrong goal for `{subject}`"
        );

        // Independent path 2 (pinned Lean) must reject both mutations too.
        let Some(lean) = lean_probe::lean_bin_or_skip(TAG, 3) else {
            return;
        };
        let (accepted, report, _) = replay(&lean, &stream, "credited_wrong_clean");
        assert!(
            accepted,
            "pinned Lean must accept the unmodified closure:\n{report}"
        );

        let (accepted, report, _) = replay(&lean, &wrong_proof, "credited_wrong_proof");
        assert!(
            !accepted,
            "pinned Lean's kernel ACCEPTED a wrong proof for `{subject}`:\n{report}"
        );
        assert!(report.contains("REAL LEAN KERNEL REJECTED"), "{report}");

        let (accepted, report, _) = replay(&lean, &wrong_goal, "credited_wrong_goal");
        assert!(
            !accepted,
            "pinned Lean's kernel ACCEPTED a wrong goal for `{subject}`:\n{report}"
        );
        assert!(report.contains("REAL LEAN KERNEL REJECTED"), "{report}");

        lean_probe::report_checked(TAG, 3);
    });
}

// ---------------------------------------------------------------------------
// Adversarial fixture 3: no inheritance.
// ---------------------------------------------------------------------------

#[test]
fn an_uncredited_sibling_in_the_same_module_does_not_inherit_a_credited_roots_grade() {
    on_a_deep_stack(|| {
        let mut kernel = Kernel::new();
        build_nat_prelude(&mut kernel).expect("the Nat prelude must build");

        let sampled = name_of(&kernel, "Nat.le_refl").expect("`Nat.le_refl` must be declared");
        // `Nat.le_succ` lives in the same nat_prelude order-lemma cluster and
        // is NOT one of the 9 credited roots (it has no Mathlib mirror fact in
        // the graph join). If a sampled export conferred credit on an
        // arbitrary sibling, this is exactly the name it would leak onto.
        let sibling = "Nat.le_succ";
        assert!(
            name_of(&kernel, sibling).is_some(),
            "the sibling must be a real declaration this kernel accepts"
        );
        assert!(
            !CREDITED_ROOTS.iter().any(|(name, _)| *name == sibling),
            "the sibling must NOT be one of the credited roots, or this control \
             tests nothing"
        );

        let stream = kernel
            .render_lean4export_ndjson_roots(&Lean4ExportMetadata::axeyum("4.30.0"), &[sampled])
            .expect("the sampled root must export");

        let Some(lean) = lean_probe::lean_bin_or_skip(TAG, 1) else {
            return;
        };
        let (accepted, report, admitted) = replay(&lean, &stream, "credited_no_inheritance");
        assert!(
            accepted,
            "pinned Lean must accept the sampled closure:\n{report}"
        );
        assert!(
            admitted.contains("Nat.le_refl"),
            "the sampled root itself must be admitted:\n{report}"
        );
        assert!(
            !admitted.contains(sibling),
            "`{sibling}` inherited a grade from a sampled sibling export -- Lean's \
             environment holds {} constants and this must not be one of \
             them:\n{report}",
            admitted.len()
        );
        lean_probe::report_checked(TAG, 1);
    });
}

// ---------------------------------------------------------------------------
// Adversarial fixture 4: declined by typed reason, earned rather than assumed.
// ---------------------------------------------------------------------------

#[test]
fn pinned_lean_declines_a_synthetic_non_proposition_credited_root_by_typed_reason() {
    on_a_deep_stack(|| {
        let mut kernel = Kernel::new();
        let prelude = build_nat_prelude(&mut kernel).expect("the Nat prelude must build");

        // A `Theorem` whose type is `Nat` itself (a `Type`, not a `Prop`).
        // This kernel's `Theorem` variant carries no `Prop` requirement --
        // Lean's kernel refuses a `theorem` whose type is not a proposition
        // (`Lean.Environment.addDeclCore`). Building this synthetic
        // declaration is what proves the decline path is real.
        let synth_name = kernel.name_str(prelude.nat, "__checked_interchange_non_prop_probe");
        let nat_ty = kernel.const_(prelude.nat, vec![]);
        let zero_val = kernel.const_(prelude.zero, vec![]);
        kernel
            .add_declaration(Declaration::Theorem {
                name: synth_name,
                uparams: vec![],
                ty: nat_ty,
                value: zero_val,
            })
            .expect(
                "this kernel admits a Theorem whose type is not a Prop -- \
                     that is exactly the disagreement this probe measures",
            );

        assert!(
            !is_a_proposition(&mut kernel, nat_ty),
            "the probe's own type must NOT be a proposition, or the fixture tests \
             nothing"
        );

        let stream = kernel
            .render_lean4export_ndjson_roots(&Lean4ExportMetadata::axeyum("4.30.0"), &[synth_name])
            .expect(
                "the wire format carries a non-Prop theorem -- the refusal is \
                     Lean's, not the exporter's",
            );

        let Some(lean) = lean_probe::lean_bin_or_skip(TAG, 1) else {
            return;
        };
        let (accepted, report, _) = replay(&lean, &stream, "credited_decline_probe");
        assert!(
            !accepted,
            "pinned Lean ACCEPTED a non-Prop theorem; the decline mechanism this \
             census's `decline_mechanism_probe` field claims to demonstrate does \
             not actually fire:\n{report}"
        );
        assert!(
            report.contains("is not a proposition"),
            "the refusal must be for the TYPED reason the census records, not some \
             other failure that happens to also reject:\n{report}"
        );
        lean_probe::report_checked(TAG, 1);
    });
}
