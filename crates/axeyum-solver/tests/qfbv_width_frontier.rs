//! Capability ratchet (roadmap item 3.9): how wide a satisfiable `QF_BV`
//! instance our bit-blasting path still decides.
//!
//! # Why this is a frontier and not a pass/fail list
//!
//! The instances this gates are ones we currently **lose**. A test asserting
//! `sat` on them would be red today, and a test that merely records "we do not
//! decide these" cannot fail. So the pinned quantity is the shape the
//! `synthetic/QF_NRA` and `synthetic/QF_NIA` corpora already use: a
//! **DECIDE-FRONTIER**, the largest knob decided in a graduated family. It can
//! only move one way, an improvement raises it, and a regression drops it below
//! the floor and fails.
//!
//! # Why not `corpus/regression/`
//!
//! That sweep is a soundness gate by construction. Read
//! `corpus_regression.rs`: its only hard assertion is that `disagreements` is
//! empty, plus a global `agree >= 6` floor. `Eval::Unknown` is *counted* and
//! never fails. Dropping these files there would look like coverage and gate
//! nothing — a file regressing from `sat` to `unknown` would be tallied as a
//! coverage gap and the suite would stay green.
//!
//! # The measured frame these floors come from
//!
//! **A frontier is a function of THREE things — the budget, the build profile,
//! and the entry point — and quoting one without the other two is how a floor
//! gets set to a number the gate can never reach.** Two frames were measured
//! 2026-09-10 on the shared dev box (load average 1.2-5.9), one file per
//! process, both at a 10 s budget:
//!
//! | frame                             | `addcmp` frontier | `mul` frontier |
//! |-----------------------------------|------------------:|---------------:|
//! | RELEASE, cold `SatBvBackend`      |            8,192  |         1,024  |
//! | DEBUG, front door (`solve_smtlib`)|            1,024  |         1,024  |
//!
//! **The floors below are calibrated to the second row**, because that is the
//! frame this suite runs in: `cargo test` builds debug, and the push hook runs
//! these integration suites in debug too. Calibrating to the release number
//! would have set a floor of 4,096 that the gate fails on a healthy tree — which
//! is exactly what the first draft of this file did.
//!
//! In the release frame the cost split at each frontier is the finding this
//! whole item turns on: `addcmp` spends **56 ms of 5,385 ms (1.0%)** on lowering
//! plus CNF construction, so it is search-bound; `mul` spends **2,813 ms of
//! 5,935 ms (47%)**, so it is encoding-bound. The two families are here to keep
//! those apart.
//!
//! Floors sit one ladder rung below the measured frontier. Slack is deliberate:
//! a ratchet that fails under load teaches lanes to ignore it. Raise a floor only
//! from a measurement, and say which of the three frame axes you measured in.
//!
//! Full measurement:
//! `docs/research/03-measurements/why-43-satisfiable-qfbv-miss-2026-09-10.md`.
#![cfg(feature = "full")]

use std::path::{Path, PathBuf};
use std::thread;
use std::time::{Duration, Instant};

use axeyum_solver::{CheckResult, SolverConfig, solve_smtlib};

/// The generated width ladder. Regenerate with
/// `python3 scripts/gen-graduated-qfbv-width.py`.
fn graduated_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../corpus/public-curated/synthetic/QF_BV/width-graduated")
}

/// The real SMT-LIB family the ladder is derived from: `QF_BV/pspace/ndist.b.*`,
/// widths 20,000-29,980, every one `:status sat` and every one currently missed.
fn pspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../corpus/public-curated/non-incremental/QF_BV/smtlib-pspace-ndist")
}

/// Per-file solve budget, held at the 10 s the frontiers above were measured at
/// so the floors and the frame agree. The walk stops at its first miss, so a
/// family costs its decided prefix plus this budget exactly once (~25 s for
/// `addcmp`, ~10 s for `mul`).
///
/// Do not raise this to "make the test more robust": the frontier is a function
/// of the budget, and a larger budget silently moves it (at 30 s `addcmp`
/// reaches width 16,384-20,000). Robustness comes from the floors sitting a
/// ladder rung below the measurement, not from a longer clock.
const BUDGET: Duration = Duration::from_secs(10);

/// Wide bit-blasting builds deep recursive structures; the same stack
/// `corpus_regression` gives its solves.
const STACK: usize = 256 * 1024 * 1024;

/// Floors, one ladder rung below the DEBUG front-door frontier of 1,024 measured
/// for both families (see the module docs — not the release number).
const ADDCMP_FLOOR: u32 = 512;
const MUL_FLOOR: u32 = 512;

/// What the generator emits. A mismatch means the corpus and the generator have
/// drifted apart, which would silently change every number below.
const ADDCMP_FILES: usize = 15;
const MUL_FILES: usize = 14;
const PSPACE_FILES: usize = 21;

fn is_smt2(path: &Path) -> bool {
    path.extension()
        .is_some_and(|ext| ext.eq_ignore_ascii_case("smt2"))
}

/// One ladder member: its width knob and its text.
struct Rung {
    width: u32,
    name: String,
    text: String,
}

/// Reads a family's ladder, ordered by its width knob.
///
/// The width comes from the file NAME and is cross-checked against the
/// `(_ BitVec N)` declarations inside, so a file renamed without being
/// regenerated (or regenerated without being renamed) fails here rather than
/// silently re-ordering the ladder and moving the frontier.
fn read_ladder(prefix: &str) -> Vec<Rung> {
    let root = graduated_root();
    let entries =
        std::fs::read_dir(&root).unwrap_or_else(|error| panic!("read {}: {error}", root.display()));
    let mut rungs = Vec::new();
    for entry in entries {
        let path = entry.expect("dir entry").path();
        let Some(name) = path.file_name().and_then(|n| n.to_str()) else {
            continue;
        };
        if !name.starts_with(prefix) || !is_smt2(&path) {
            continue;
        }
        let width: u32 = name
            .rsplit_once("-w")
            .and_then(|(_, tail)| tail.strip_suffix(".smt2"))
            .and_then(|digits| digits.parse().ok())
            .unwrap_or_else(|| panic!("{name} does not carry a -wNNNNN width knob"));
        let text = std::fs::read_to_string(&path).expect("read ladder file");
        assert!(
            text.contains(&format!("(_ BitVec {width})")),
            "{name} is named for width {width} but declares no `(_ BitVec {width})` — \
             the file name and its contents have drifted; regenerate with \
             scripts/gen-graduated-qfbv-width.py"
        );
        rungs.push(Rung {
            width,
            name: name.to_owned(),
            text,
        });
    }
    rungs.sort_by_key(|rung| rung.width);
    rungs
}

/// Every `.smt2` under the vendored `pspace` slice.
fn read_pspace() -> Vec<(String, String)> {
    let root = pspace_root();
    let mut files = Vec::new();
    for entry in std::fs::read_dir(&root).expect("read pspace slice") {
        let path = entry.expect("dir entry").path();
        let Some(name) = path.file_name().and_then(|n| n.to_str()) else {
            continue;
        };
        if !is_smt2(&path) {
            continue;
        }
        files.push((
            name.to_owned(),
            std::fs::read_to_string(&path).expect("read pspace file"),
        ));
    }
    files.sort();
    files
}

enum Verdict {
    Sat,
    Unsat,
    Undecided(String),
}

/// Runs one instance through the **front door** — the path we ship — on a worker
/// with the solve stack, and reports its verdict alongside the `:status` the
/// front door read back out of the file.
fn solve(text: &str) -> (Verdict, Option<String>, Duration) {
    let owned = text.to_owned();
    let start = Instant::now();
    let outcome = thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || solve_smtlib(&owned, &SolverConfig::default().with_timeout(BUDGET)))
        .expect("spawn solver worker")
        .join()
        .expect("solver worker did not panic")
        .expect("front door runs");
    let elapsed = start.elapsed();
    let verdict = match &outcome.result {
        CheckResult::Sat(_) => Verdict::Sat,
        CheckResult::Unsat => Verdict::Unsat,
        CheckResult::Unknown(reason) => Verdict::Undecided(reason.detail.clone()),
    };
    (verdict, outcome.expected_status.clone(), elapsed)
}

/// Walks a family upward and returns `(frontier, examined)`.
///
/// Stops at the first width that is not decided, so the run costs the decided
/// prefix plus exactly one budget rather than one budget per missed rung.
fn decide_frontier(prefix: &str, expected_files: usize) -> (u32, usize) {
    let ladder = read_ladder(prefix);
    assert_eq!(
        ladder.len(),
        expected_files,
        "the `{prefix}` ladder has {} files, expected {expected_files}. If the \
         generator's width list changed, re-measure the frontier and update BOTH \
         the count and the floor — do not just bump the count.",
        ladder.len()
    );

    let mut frontier = 0;
    let mut examined = 0;
    for rung in &ladder {
        let (verdict, status, elapsed) = solve(&rung.text);
        examined += 1;

        // Ground truth from the benchmark's own `:status`, read back through the
        // front door — never a literal here. Editing a vendored file cannot leave
        // this pinned to a status it no longer carries.
        assert_eq!(
            status.as_deref(),
            Some("sat"),
            "{} lost the `:status sat` annotation this ratchet is anchored to",
            rung.name
        );

        match verdict {
            Verdict::Sat => {
                frontier = rung.width;
                println!("  {} decided sat in {elapsed:.2?}", rung.name);
            }
            // A satisfiable instance answered `unsat` is a wrong verdict, and the
            // frontier walk is the only thing that runs these files. This is the
            // assertion that makes the slice a soundness gate as well as a
            // capability one.
            Verdict::Unsat => panic!(
                "SOUNDNESS FAILURE: {} is satisfiable by construction (witness in \
                 the file header, checked by scripts/gen-graduated-qfbv-width.py) \
                 and the front door answered `unsat`",
                rung.name
            ),
            Verdict::Undecided(detail) => {
                println!("  {} undecided in {elapsed:.2?}: {detail}", rung.name);
                break;
            }
        }
    }
    (frontier, examined)
}

#[test]
fn the_addcmp_width_frontier_does_not_regress() {
    let (frontier, examined) = decide_frontier("bvwide-addcmp-", ADDCMP_FILES);
    assert!(
        examined > 1,
        "the frontier walk examined {examined} instance(s); it cannot report a \
         frontier without deciding at least one and then reaching a rung it does not"
    );
    assert!(
        frontier >= ADDCMP_FLOOR,
        "addcmp decide-frontier fell to width {frontier}, below the floor \
         {ADDCMP_FLOOR}. Lowering and CNF construction are ~1% of the budget on \
         this family (measured), so a drop here is a SEARCH regression in the CDCL \
         core, not an encoding one. See \
         docs/research/03-measurements/why-43-satisfiable-qfbv-miss-2026-09-10.md"
    );
    println!("addcmp decide-frontier: width {frontier} (floor {ADDCMP_FLOOR})");
}

#[test]
fn the_mul_width_frontier_does_not_regress() {
    let (frontier, examined) = decide_frontier("bvwide-mul-", MUL_FILES);
    assert!(
        examined > 1,
        "the frontier walk examined {examined} instance(s); it cannot report a \
         frontier without deciding at least one and then reaching a rung it does not"
    );
    assert!(
        frontier >= MUL_FLOOR,
        "mul decide-frontier fell to width {frontier}, below the floor {MUL_FLOOR}. \
         Unlike addcmp this family IS encoding-bound: ~47% of the budget is \
         lowering + CNF at its frontier (release frame). A drop here is most \
         likely an encoding-size or admission change, not a search one. Note the \
         two frames differ ABOVE the frontier as well as at it — the cold \
         `SatBvBackend` refuses width 2,048 outright on \
         `ABSOLUTE_CLAUSE_CEILING` (projected 100,681,731 clauses vs the \
         64,000,000 cap, while the real encoding is 35,609,626), whereas the \
         front door measured here reaches it and times out instead."
    );
    println!("mul decide-frontier: width {frontier} (floor {MUL_FLOOR})");
}

/// The vendored real SMT-LIB family is the ratchet's upper anchor. It is not
/// solved here — every member is far past both frontiers and would cost a full
/// budget each — but its ground truth is checked, so a slice that drifted away
/// from the class it exists to represent fails loudly and cheaply.
#[test]
fn the_vendored_pspace_slice_is_entirely_satisfiable_and_far_past_the_frontier() {
    let files = read_pspace();
    assert_eq!(
        files.len(),
        PSPACE_FILES,
        "the vendored pspace slice has {} files, expected {PSPACE_FILES}",
        files.len()
    );
    let mut widths = Vec::new();
    for (name, text) in &files {
        assert!(
            text.contains("(set-info :status sat)"),
            "{name} does not declare `:status sat`; the whole point of this slice \
             is that it is a SATISFIABLE class we miss"
        );
        let width: u32 = text
            .split("(_ BitVec ")
            .nth(1)
            .and_then(|tail| tail.split(')').next())
            .and_then(|digits| digits.parse().ok())
            .unwrap_or_else(|| panic!("{name} declares no `(_ BitVec N)`"));
        widths.push(width);
    }
    let narrowest = *widths.iter().min().expect("non-empty slice");
    // If this ever fails it is GOOD NEWS and this whole file needs re-basing: it
    // would mean the frontier has climbed into the real SMT-LIB family's range.
    assert!(
        narrowest > ADDCMP_FLOOR,
        "the narrowest vendored pspace instance is {narrowest} bits, which is no \
         longer past the addcmp floor {ADDCMP_FLOOR}. Re-measure the frontier and \
         re-base this suite."
    );
    println!(
        "vendored pspace slice: {} files, widths {}..={}, all `:status sat`",
        files.len(),
        narrowest,
        widths.iter().max().expect("non-empty slice")
    );
}
