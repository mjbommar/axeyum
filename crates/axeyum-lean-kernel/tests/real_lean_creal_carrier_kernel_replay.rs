//! **The whole constructed-real carrier**, every declaration of it, handed to
//! the real Lean kernel.
//!
//! # The coverage hole this closes
//!
//! Every other real-Lean cross-check in this repository is *reachability
//! driven*: it renders the closure of one refutation and hands Lean that. So
//! Lean only ever saw the declarations some query happened to cite. Measured on
//! 2026-08-18 by the lane that split the module (ADR-0511), a refutation over
//! the constructed reals reached 343 of the carrier's 465 declarations —
//! **122 had never been handed to any Lean**, and the first time anything
//! pointed Lean at them two of them were refused. The carrier is 470 today; the
//! count this suite asserts is read out of the kernel at run time, never
//! transcribed.
//!
//! A cross-check that only ever sees the reachable slice cannot find that
//! class. This suite removes the reachability filter: the export is over the
//! **complete checked environment**, and the count Lean reports back is compared
//! against the count read out of the kernel, so "Lean accepted it" cannot mean
//! "Lean accepted a subset".
//!
//! # Why the kernel route and not a `.lean` module
//!
//! The two routes are not equivalent, and that is the finding ADR-0517 records:
//! `lean Module.lean` runs Lean's **elaborator**, whose reducer treats a
//! `theorem` as opaque, so it cannot check any declaration whose type-checking
//! must reduce one — which includes `Nat.gcd`'s recursive step (justified by
//! the theorem `Nat.mod_lt`), hence every closed `Rat` normalization, hence
//! `CReal.Equiv.not_zero_one` and `CReal.not_le_one_zero`. Measured on the
//! whole carrier on 2026-08-18: 4 of 470 refused by the elaborator in 14.1 s,
//! 0 of 470 refused by the kernel in 1.4 s.
//! `scripts/lean/replay-lean4export.lean` drives
//! `Lean.Environment.addDeclCore` from our official `lean4export` NDJSON, which
//! is Lean's **kernel**, and the kernel does unfold it.
//!
//! So the kernel route is the one that can carry the whole carrier, and it is
//! also the stronger claim: no elaborator, no implicit-argument insertion, no
//! coercion, no code generator, starting from `mkEmptyEnvironment` so nothing
//! can be satisfied by Lean's own `Init`.
//! `real_lean_wellfounded_elaborator_divergence` pins the residue in the other
//! direction.
//!
//! # What the exit status depends on
//!
//! 1. Lean's kernel accepts the stream, and reports a final constant count
//!    **equal to** the number of declarations this kernel holds;
//! 2. the stream carries the two declarations the source route cannot — by
//!    name, because a suite that silently stopped covering them would look
//!    exactly like a suite that passed;
//! 3. the same Lean **rejects** the same stream with `CReal.Equiv.not_zero_one`'s
//!    proof swapped for another closed proof, and names that theorem's own type
//!    when it does. Without (3), (1) is consistent with a replay that checked
//!    nothing.
//!
//! # Cost
//!
//! `build_creal_prelude` is the expensive prelude (~45 s in a debug test
//! binary; `prelude_cache` makes it once per process). The Lean half is
//! ~1.4 s for 470 declarations, which is why the whole carrier is affordable
//! here and a 7 MB elaborated module is not.

use std::path::{Path, PathBuf};
use std::process::Command;

use axeyum_lean_kernel::{Kernel, Lean4ExportMetadata, build_creal_prelude, on_a_deep_stack};

#[path = "support/lean_probe.rs"]
mod lean_probe;

const TAG: &str = "creal-carrier-kernel-replay";

/// Printed with both counts, so a fact can pin the carrier size by value
/// instead of a document transcribing it.
const CARRIER_MARKER: &str = "AXEYUM-CREAL-CARRIER";

/// The two theorems Lean's elaborator refuses and its kernel accepts. Named
/// here so the suite fails if the export stops carrying them.
const ELABORATOR_RESIDUE: [&str; 2] = ["not_zero_one", "not_le_one_zero"];

/// A scratch directory for the artefacts this suite hands to `lean`.
///
/// **Not** `std::env::temp_dir()`. `/tmp` on the development host is a 62 GB
/// **tmpfs** — RAM — which CLAUDE.md records as a standing contributor to the
/// OOM kills that have ended sessions on this box. A suite that exports the
/// whole checked environment is precisely the one that grows, so it writes
/// where the rest of the repository's scratch goes (`/data0`, as
/// `scripts/lane-snapshot.sh` does). `AXEYUM_SCRATCH_DIR` overrides it, and a
/// host without `/data0` falls back to the temporary directory rather than
/// failing — the fallback is the old behaviour, not a new hazard.
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

/// Replay one NDJSON stream through Lean's own kernel.
fn replay(lean: &Path, stream: &str, stem: &str) -> (bool, String) {
    let script = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../scripts/lean/replay-lean4export.lean")
        .canonicalize()
        .expect("the replay script must exist");
    let directory = scratch_directory("creal_replay");
    let file = directory.join(format!("{stem}.ndjson"));
    std::fs::write(&file, stream).expect("write replay stream");
    let output = Command::new(lean)
        .arg("--run")
        .arg(&script)
        .arg(&file)
        .output()
        .expect("run the Lean replay script");
    let combined = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    (output.status.success(), combined)
}

/// The `"in":<n>` index of the name record whose final component is
/// `component`. Names are interned as `(prefix, component)` pairs, so this is
/// how a suite refers to a declaration in the wire format without
/// re-implementing the interner.
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

/// The `"value":<n>` of the theorem record declaring name index `name`.
fn theorem_record(stream: &str, name: u64) -> Option<(String, u64)> {
    let marker = format!("\"name\":{name},");
    let line = stream
        .lines()
        .find(|line| line.starts_with("{\"thm\":") && line.contains(&marker))?;
    let tail = line.split_once("\"value\":")?.1;
    let digits: String = tail.chars().take_while(char::is_ascii_digit).collect();
    Some((line.to_owned(), digits.parse().ok()?))
}

/// The `"value":<n>` of the first universe-monomorphic theorem in the stream —
/// a closed proof of *something else*, early enough in the expression index to
/// be in scope wherever it is substituted.
fn first_monomorphic_theorem_value(stream: &str) -> Option<u64> {
    let line = stream
        .lines()
        .find(|line| line.starts_with("{\"thm\":") && line.contains("\"levelParams\":[],"))?;
    let tail = line.split_once("\"value\":")?.1;
    let digits: String = tail.chars().take_while(char::is_ascii_digit).collect();
    digits.parse().ok()
}

/// The constant count the replay script reports it ended with.
fn reported_constants(report: &str) -> Option<usize> {
    let tail = report.split_once("environment now holds ")?.1;
    let digits: String = tail.chars().take_while(char::is_ascii_digit).collect();
    digits.parse().ok()
}

#[test]
fn the_real_lean_kernel_accepts_every_declaration_of_the_constructed_real_carrier() {
    // `creal` needs 16 MiB of stack in debug (`artifacts/kernel-stack-envelope.tsv`
    // row `debug creal 16777216`) and a `#[test]` thread has 2 MiB, so
    // `build_creal_prelude` aborted here with a SIGABRT before a single Lean
    // ran. Measured 2026-08-30 in a shell with `RUST_MIN_STACK` unset: this
    // suite is registered in `scripts/check-lean-gate.sh` and was failing on
    // the stack, not on any verdict. Carried explicitly rather than inherited
    // from an ambient variable, which is a gate on one shell.
    on_a_deep_stack(|| {
        let mut kernel = Kernel::new();
        build_creal_prelude(&mut kernel).expect("the CReal development must build");
        let declared = kernel.environment().iter().count();
        assert!(
            declared > 400,
            "the constructed-real carrier must be the whole development, not a slice: {declared}"
        );

        let stream = kernel
            .render_lean4export_ndjson(&Lean4ExportMetadata::axeyum("4.30.0"))
            .expect("the checked carrier must export");

        // Coverage, asserted before any Lean runs: an empty answer from a tool that
        // was never pointed at the subject is indistinguishable from a strong
        // negative result.
        let residue: Vec<(&str, u64)> = ELABORATOR_RESIDUE
            .iter()
            .map(|component| {
                let index = name_index(&stream, component).unwrap_or_else(|| {
                    panic!(
                        "the export no longer carries `{component}`, so this suite covers \
                         neither declaration the source route cannot take"
                    )
                });
                (*component, index)
            })
            .collect();

        let Some(lean) = lean_probe::lean_bin_or_skip(TAG, 2) else {
            return;
        };

        let (accepted, report) = replay(&lean, &stream, "creal_carrier");
        assert!(
            accepted,
            "the REAL LEAN KERNEL rejected the constructed-real carrier this kernel \
             admitted:\n{report}"
        );
        let held = reported_constants(&report).unwrap_or_else(|| {
            panic!("the replay must report its final constant count:\n{report}")
        });
        assert_eq!(
            held, declared,
            "Lean's kernel ended with {held} constants where this kernel holds {declared}. \
             A replay that admits a SUBSET is exactly the reachability hole this suite \
             exists to close:\n{report}"
        );
        // Printed so the number is READ OUT of the run rather than transcribed into
        // a document: `artifacts/facts/` pins this line by value.
        println!("{CARRIER_MARKER} declared={declared} lean_kernel_constants={held}");

        // The negative control, aimed at the declaration the source route refuses.
        // Anything weaker would leave "Lean accepted the carrier" consistent with
        // Lean having checked nothing in particular about THAT theorem.
        let (component, name) = residue[0];
        let (record, value) =
            theorem_record(&stream, name).expect("`not_zero_one` must be a theorem record");
        let substitute = first_monomorphic_theorem_value(&stream)
            .expect("the carrier must hold a universe-monomorphic theorem");
        assert_ne!(
            value, substitute,
            "the negative control must substitute a DIFFERENT proof"
        );
        let tampered = stream.replace(
            &record,
            &record.replace(
                &format!("\"value\":{value}"),
                &format!("\"value\":{substitute}"),
            ),
        );
        assert_ne!(tampered, stream, "the negative control must change bytes");

        let (accepted, report) = replay(&lean, &tampered, "creal_carrier_tampered");
        assert!(
            !accepted,
            "the real Lean kernel accepted a mismatched proof for `{component}`; the \
             positive result above is worthless:\n{report}"
        );
        assert!(
            report.contains("REAL LEAN KERNEL REJECTED"),
            "the rejection must come from the kernel: {report}"
        );
        assert!(
            report.contains("CReal.Equiv"),
            "the rejection must name the TYPE it was checking, or it could be any \
             unrelated failure downstream:\n{report}"
        );

        lean_probe::report_checked(TAG, 2);
    });
}
