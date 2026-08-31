//! **L4 phase C3 — the thin Lean adapter's preregistered goal pack.**
//!
//! `docs/plan/library-artifact-compatibility-roadmap-2026-08-30.md` section C3
//! asks for "a small Lean command/tactic adapter that receives an already
//! elaborated goal plus environment identity, calls Axeyum as a
//! sidecar/library, and returns a proof/certificate that Lean itself checks.
//! It must not trust Axeyum's verdict or add an axiom", with an exit
//! criterion covering eight representative outcomes: success, unknown,
//! timeout, unsupported, malformed response, wrong goal, wrong environment,
//! and mutated proof.
//!
//! This suite drives `axeyum_lean_import::thin_adapter`'s grading logic
//! against ONE real goal (`Nat.add_comm`, drawn from C2's own credited-root
//! population -- reused, not reinvented) and eight synthetic sidecar
//! responses, one per required category. Every category that needs a Lean
//! verdict gets one: the "success" and "wrong-goal" and "mutated-proof"
//! fixtures are all replayed through the SAME
//! `scripts/lean/replay-lean4export.lean` and independent `import_ndjson`
//! path C2 already validated. Nothing here re-implements export, reimport,
//! or replay -- `thin_adapter`'s own module doc says as much, and this suite
//! is where that claim is checked.
//!
//! Writes `artifacts/lean-adapter/results/thin-adapter-v1.result.json`,
//! validated by `scripts/check-lean-adapter.py`.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::Command;

use axeyum_lean_import::thin_adapter::{
    AdapterVerdict, GoalDescriptor, PreLeanStage, decide_after_lean, pre_lean_verdict,
};
use axeyum_lean_import::{ImportLimits, import_ndjson};
use axeyum_lean_kernel::{
    Declaration, Kernel, Lean4ExportMetadata, NameId, build_nat_prelude, on_a_deep_stack,
};

#[path = "../../axeyum-lean-kernel/tests/support/lean_probe.rs"]
mod lean_probe;

const TAG: &str = "thin-lean-adapter-goal-pack";
const RESULT_MARKER: &str = "AXEYUM-LEAN-ADAPTER";
const LEAN_VERSION: &str = "4.30.0";
const LEAN_COMMIT: &str = "d024af099ca4bf2c86f649261ebf59565dc8c622";
const GOAL_PACK_ID: &str = "thin-adapter-v1";

/// The goal: `Nat.add_comm`, one of C2's own 9 credited roots
/// (`artifacts/checked-interchange/populations/credited-roots-v1.json`).
/// Reusing a credited root means this suite needs no new claim about what
/// this kernel can prove -- C2 already established the identity story for
/// this exact name.
const SUBJECT: &str = "Nat.add_comm";
/// A second credited root, borrowed only to build a genuinely different,
/// separately-valid proof/goal for the wrong-goal and mutated-proof
/// fixtures -- never presented as the answer to a request for `SUBJECT`.
const BORROWED: &str = "Nat.le_refl";

fn environment_id() -> String {
    format!("lean-{LEAN_VERSION}@{LEAN_COMMIT}:{GOAL_PACK_ID}")
}

fn name_of(kernel: &Kernel, display: &str) -> Option<NameId> {
    kernel
        .environment()
        .iter()
        .find(|(name, _)| kernel.display_name(**name).to_string() == display)
        .map(|(name, _)| *name)
}

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

fn scratch_directory() -> PathBuf {
    let name = format!("axeyum_{TAG}_{}", std::process::id());
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
    panic!("no writable scratch root for {TAG}");
}

/// Replay one stream through pinned Lean's kernel via
/// `scripts/lean/replay-lean4export.lean` -- the SAME script and the SAME
/// invocation shape `checked_interchange_credited_roots.rs` uses. Returns
/// `(accepted, report, names Lean ended holding)`.
fn replay(lean: &Path, stream: &str, stem: &str) -> (bool, String, BTreeSet<String>) {
    let script = repo_root().join("scripts/lean/replay-lean4export.lean");
    assert!(
        script.is_file(),
        "the replay script must exist at {}",
        script.display()
    );
    let directory = scratch_directory();
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

/// The whole `{"thm":…}` record declaring name index `name`, with its
/// `"type"` and `"value"` expression indices. Copied from
/// `checked_interchange_credited_roots.rs` (itself copied from
/// `real_lean_replay_census.rs`) -- this is exactly the mutation technique
/// ADR-0915's adversarial fixtures use, reused rather than reinvented.
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

/// The outcome of grading one fixture, in the shape written to the committed
/// result artifact.
struct Outcome {
    category: &'static str,
    expected_verdict: &'static str,
    observed_verdict: String,
    reason: Option<String>,
    lean_invoked: bool,
}

fn grade(
    goal: &GoalDescriptor,
    raw_response: &[u8],
    lean: Option<&Path>,
) -> (AdapterVerdict, bool) {
    match pre_lean_verdict(goal, raw_response) {
        PreLeanStage::Final(verdict) => (verdict, false),
        PreLeanStage::NeedsLeanCheck { stream_path } => {
            let stream = std::fs::read_to_string(&stream_path).expect("read staged stream");
            let lean = lean.expect("this fixture needs a real Lean binary");
            let stem = Path::new(&stream_path)
                .file_stem()
                .and_then(|s| s.to_str())
                .unwrap_or("stream")
                .to_owned();
            let (lean_accepted_stream, _report, admitted) = replay(lean, &stream, &stem);
            let reimported_type_matches = import_ndjson(
                std::io::Cursor::new(stream.as_bytes()),
                ImportLimits::default(),
            )
            .ok()
            .and_then(|import| {
                let reimported = import.kernel();
                let target_id = name_of(reimported, &goal.name)?;
                let Declaration::Theorem { ty: target_ty, .. } =
                    reimported.environment().get(target_id)?.clone()
                else {
                    return Some(false);
                };
                Some(reimported.render_lean(target_ty) == goal.expected_type)
            });
            let verdict = decide_after_lean(
                goal,
                lean_accepted_stream,
                &admitted,
                reimported_type_matches,
            );
            (verdict, true)
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)]
fn the_eight_required_categories_are_each_graded_correctly_by_real_pinned_lean() {
    on_a_deep_stack(|| {
        let mut kernel = Kernel::new();
        build_nat_prelude(&mut kernel).expect("the Nat prelude must build");

        let subject_id =
            name_of(&kernel, SUBJECT).unwrap_or_else(|| panic!("`{SUBJECT}` must be declared"));
        let borrowed_id =
            name_of(&kernel, BORROWED).unwrap_or_else(|| panic!("`{BORROWED}` must be declared"));

        let Declaration::Theorem { ty: subject_ty, .. } = kernel
            .environment()
            .get(subject_id)
            .expect("subject resolves")
            .clone()
        else {
            panic!("`{SUBJECT}` must be a Theorem");
        };
        let goal = GoalDescriptor {
            name: SUBJECT.to_owned(),
            expected_type: kernel.render_lean(subject_ty),
            environment_id: environment_id(),
        };

        // The real, honest closure for the subject alone -- what a correctly
        // functioning sidecar would actually send back for "success".
        let success_stream = kernel
            .render_lean4export_ndjson_roots(
                &Lean4ExportMetadata::axeyum(LEAN_VERSION),
                &[subject_id],
            )
            .expect("the subject must export");

        // The borrowed root's OWN closure, which never mentions `SUBJECT` at
        // all -- a real, Lean-acceptable proof of a DIFFERENT goal, used for
        // "wrong goal".
        let wrong_goal_stream = kernel
            .render_lean4export_ndjson_roots(
                &Lean4ExportMetadata::axeyum(LEAN_VERSION),
                &[borrowed_id],
            )
            .expect("the borrowed root must export");
        assert!(
            name_index(&wrong_goal_stream, "add_comm").is_none()
                || !wrong_goal_stream.contains(SUBJECT),
            "the wrong-goal control must not happen to also name the subject"
        );

        // A combined closure holding BOTH roots, so a genuinely different
        // theorem's proof value exists to swap in for "mutated proof".
        let combined_stream = kernel
            .render_lean4export_ndjson_roots(
                &Lean4ExportMetadata::axeyum(LEAN_VERSION),
                &[subject_id, borrowed_id],
            )
            .expect("the combined closure must export");
        let subject_index = name_index(&combined_stream, "add_comm")
            .expect("the combined export must carry `add_comm`");
        let (record, subject_type_idx, subject_value_idx) =
            theorem_record(&combined_stream, subject_index)
                .expect("`add_comm` must be a theorem record");
        let (_other_goal, other_value) = first_monomorphic_theorem_excluding(
            &combined_stream,
            (subject_type_idx, subject_value_idx),
        )
        .expect("the combined closure must hold a different theorem to borrow a proof from");
        let mutated_proof_stream = combined_stream.replace(
            &record,
            &record.replace(
                &format!("\"value\":{subject_value_idx}"),
                &format!("\"value\":{other_value}"),
            ),
        );
        assert_ne!(
            mutated_proof_stream, combined_stream,
            "the mutated-proof control must change bytes"
        );

        let directory = scratch_directory();
        let write = |name: &str, content: &str| -> String {
            let path = directory.join(name);
            std::fs::write(&path, content).expect("write fixture stream");
            path.to_string_lossy().into_owned()
        };
        let success_path = write("success.ndjson", &success_stream);
        let wrong_goal_path = write("wrong_goal.ndjson", &wrong_goal_stream);
        let mutated_proof_path = write("mutated_proof.ndjson", &mutated_proof_stream);

        let env_id = environment_id();
        let response = |json: String| -> Vec<u8> { json.into_bytes() };

        let Some(lean) = lean_probe::lean_bin_or_skip(TAG, 8) else {
            return;
        };

        let mut outcomes = Vec::new();

        // 1. success
        let raw = response(format!(
            "{{\"status\":\"accepted\",\"environment_id\":{env_id:?},\"stream_path\":{success_path:?}}}"
        ));
        let (verdict, invoked) = grade(&goal, &raw, Some(&lean));
        outcomes.push(Outcome {
            category: "success",
            expected_verdict: "accepted",
            observed_verdict: verdict.tag().to_owned(),
            reason: verdict.reason().map(str::to_owned),
            lean_invoked: invoked,
        });

        // 2-4. typed declines: unknown, timeout, unsupported
        for reason in ["unknown", "timeout", "unsupported"] {
            let raw = response(format!("{{\"status\":\"declined\",\"reason\":{reason:?}}}"));
            let (verdict, invoked) = grade(&goal, &raw, Some(&lean));
            outcomes.push(Outcome {
                category: match reason {
                    "unknown" => "unknown",
                    "timeout" => "timeout",
                    _ => "unsupported",
                },
                expected_verdict: "declined",
                observed_verdict: verdict.tag().to_owned(),
                reason: verdict.reason().map(str::to_owned),
                lean_invoked: invoked,
            });
        }

        // 5. malformed response -- bytes that are not even JSON.
        let raw: Vec<u8> = b"{not-json".to_vec();
        let (verdict, invoked) = grade(&goal, &raw, Some(&lean));
        outcomes.push(Outcome {
            category: "malformed_response",
            expected_verdict: "declined",
            observed_verdict: verdict.tag().to_owned(),
            reason: verdict.reason().map(str::to_owned),
            lean_invoked: invoked,
        });

        // 6. wrong goal -- a real, Lean-acceptable proof of a DIFFERENT goal.
        let raw = response(format!(
            "{{\"status\":\"accepted\",\"environment_id\":{env_id:?},\"stream_path\":{wrong_goal_path:?}}}"
        ));
        let (verdict, invoked) = grade(&goal, &raw, Some(&lean));
        outcomes.push(Outcome {
            category: "wrong_goal",
            expected_verdict: "rejected",
            observed_verdict: verdict.tag().to_owned(),
            reason: verdict.reason().map(str::to_owned),
            lean_invoked: invoked,
        });

        // 7. wrong environment -- correct goal and stream, wrong identity.
        let raw = response(format!(
            "{{\"status\":\"accepted\",\"environment_id\":\"wrong-environment-id\",\"stream_path\":{success_path:?}}}"
        ));
        let (verdict, invoked) = grade(&goal, &raw, Some(&lean));
        outcomes.push(Outcome {
            category: "wrong_environment",
            expected_verdict: "rejected",
            observed_verdict: verdict.tag().to_owned(),
            reason: verdict.reason().map(str::to_owned),
            lean_invoked: invoked,
        });

        // 8. mutated proof -- Lean's own kernel must reject the stream.
        let raw = response(format!(
            "{{\"status\":\"accepted\",\"environment_id\":{env_id:?},\"stream_path\":{mutated_proof_path:?}}}"
        ));
        let (verdict, invoked) = grade(&goal, &raw, Some(&lean));
        outcomes.push(Outcome {
            category: "mutated_proof",
            expected_verdict: "rejected",
            observed_verdict: verdict.tag().to_owned(),
            reason: verdict.reason().map(str::to_owned),
            lean_invoked: invoked,
        });

        for outcome in &outcomes {
            assert_eq!(
                outcome.observed_verdict,
                outcome.expected_verdict,
                "category `{}` graded `{}`, expected `{}` (reason={:?})",
                outcome.category,
                outcome.observed_verdict,
                outcome.expected_verdict,
                outcome.reason
            );
        }
        // Categories that MUST invoke real Lean (the ones that need a stream
        // check at all) -- proves this suite is not grading everything from
        // the envelope alone.
        for must_invoke in ["success", "wrong_goal", "mutated_proof"] {
            let invoked = outcomes
                .iter()
                .find(|o| o.category == must_invoke)
                .expect("category present")
                .lean_invoked;
            assert!(invoked, "`{must_invoke}` must actually invoke pinned Lean");
        }

        println!(
            "{RESULT_MARKER} categories={} accepted={} declined={} rejected={}",
            outcomes.len(),
            outcomes
                .iter()
                .filter(|o| o.observed_verdict == "accepted")
                .count(),
            outcomes
                .iter()
                .filter(|o| o.observed_verdict == "declined")
                .count(),
            outcomes
                .iter()
                .filter(|o| o.observed_verdict == "rejected")
                .count(),
        );

        write_result_artifact(&outcomes);
        lean_probe::report_checked(TAG, 8);
    });
}

fn write_result_artifact(outcomes: &[Outcome]) {
    use std::fmt::Write as _;
    let mut body = String::new();
    for (i, outcome) in outcomes.iter().enumerate() {
        if i > 0 {
            body.push_str(",\n");
        }
        let reason_json = match &outcome.reason {
            Some(r) => format!("{r:?}"),
            None => "null".to_owned(),
        };
        let _ = write!(
            body,
            "    {{\n      \"category\": \"{}\",\n      \"expected_verdict\": \"{}\",\n      \
             \"observed_verdict\": \"{}\",\n      \"reason\": {},\n      \"lean_invoked\": {}\n    }}",
            outcome.category,
            outcome.expected_verdict,
            outcome.observed_verdict,
            reason_json,
            outcome.lean_invoked,
        );
    }
    let json = format!(
        "{{\n  \"schema_version\": 1,\n  \"goal_pack_id\": \"{GOAL_PACK_ID}\",\n  \
         \"goal_pack_file\": \"artifacts/lean-adapter/goal-pack/thin-adapter-v1.json\",\n  \
         \"lean_version\": \"{LEAN_VERSION}\",\n  \"lean_commit\": \"{LEAN_COMMIT}\",\n  \
         \"environment_id\": \"{}\",\n  \"subject\": \"{SUBJECT}\",\n  \"borrowed\": \"{BORROWED}\",\n  \
         \"outcomes\": [\n{body}\n  ]\n}}\n",
        environment_id(),
    );
    let path = repo_root().join("artifacts/lean-adapter/results/thin-adapter-v1.result.json");
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent).expect("create results directory");
    }
    std::fs::write(&path, json).expect("write result artifact");
    println!("{RESULT_MARKER} wrote {}", path.display());
}
