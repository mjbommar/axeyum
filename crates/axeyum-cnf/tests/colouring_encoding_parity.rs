//! Differential gate: the Rust colouring encoder against the generator of
//! record, byte for byte.
//!
//! `scripts/gen-rado-instance.py` is named by `formal.generator` in every claim
//! under `artifacts/claims/rado/`. It **defines what those claims mean**: a
//! stored DRAT refutation only refutes the intended instance if the CNF
//! regenerates exactly, and the ledger's own re-checker
//! (`scripts/check-claim-certificates.py`) enforces that with a second Python
//! encoder. Two Python implementations by the same hand are not independent in
//! the way that matters, so this file adds a third derivation in another
//! language and requires **byte-identical** output.
//!
//! Three layers, weakest dependency first:
//!
//! 1. [`stored_ledger_cnf_artifacts_regenerate_byte_identically`] — pure Rust,
//!    no interpreter: every `F_*.cnf` committed under `artifacts/claims/rado/`
//!    must come back out of the Rust encoder unchanged. This is the layer that
//!    speaks directly to the shipped evidence, and it can never be skipped.
//! 2. [`python_generator_of_record_matches_on_a_wide_sweep`] — the generator of
//!    record, *imported* (not reimplemented), over a broad parameter sweep that
//!    includes every instance the ledger cites and their satisfiable/borderline
//!    neighbours.
//! 3. [`python_cli_matches_on_the_headline_instances`] — the script's actual
//!    command line, on the instances behind the headline claims
//!    `R_4(2(x−y)=3z) = 226` and `R_4(4(x−y)=3z) = 313`, so layer 2's `import`
//!    shortcut cannot hide a difference between `generate()` and `main()`.
//!
//! Layers 2 and 3 **fail closed** when `python3` or the script is missing. A
//! differential gate that quietly turns into a no-op is the failure mode this
//! repository has been bitten by most; there is no skip path here.

use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, Instant};

use axeyum_cnf::colouring::{ColouringProblem, Rado};

/// Parameters of one instance: `a(x−y) = bz`, `k` colours, points `1..=n`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Instance {
    a: usize,
    b: usize,
    k: usize,
    n: usize,
}

impl Instance {
    fn new(a: usize, b: usize, k: usize, n: usize) -> Self {
        Self { a, b, k, n }
    }

    /// The Rust encoder's DIMACS for this instance.
    fn encode(self) -> String {
        let family = Rado::new(self.a, self.b).expect("a, b >= 1");
        ColouringProblem::from_family(&family, self.n, self.k)
            .expect("the family only emits sets inside 1..=n")
            .to_dimacs()
            .expect("n * k fits a CNF variable index")
    }
}

/// Repository root, from this crate's manifest directory.
fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .canonicalize()
        .expect("the crate lives two levels below the repository root")
}

/// Reports the first line at which two DIMACS texts differ.
///
/// A byte-identity failure has to name the divergence, or the next reader has
/// to re-derive it by hand.
fn describe_difference(instance: Instance, expected: &str, actual: &str) -> String {
    if expected == actual {
        return String::new();
    }
    let mut report = format!(
        "instance a={} b={} k={} n={}: expected {} bytes, produced {} bytes",
        instance.a,
        instance.b,
        instance.k,
        instance.n,
        expected.len(),
        actual.len()
    );
    for (number, (want, got)) in expected.lines().zip(actual.lines()).enumerate() {
        if want != got {
            let line = number + 1;
            write!(
                report,
                "\n  first difference at line {line}:\n    reference: {want}\n    rust:      {got}"
            )
            .expect("writing to a String cannot fail");
            return report;
        }
    }
    let (want_lines, got_lines) = (expected.lines().count(), actual.lines().count());
    write!(
        report,
        "\n  common prefix agrees; reference has {want_lines} lines, rust has {got_lines}"
    )
    .expect("writing to a String cannot fail");
    report
}

// ---------------------------------------------------------------- layer 1

/// Parses `rado-r{k}-a{a}-b{b}` into `(k, a, b)`.
fn parse_claim_id(id: &str) -> Option<(usize, usize, usize)> {
    let rest = id.strip_prefix("rado-r")?;
    let (k, rest) = rest.split_once("-a")?;
    let (a, b) = rest.split_once("-b")?;
    Some((k.parse().ok()?, a.parse().ok()?, b.parse().ok()?))
}

/// Parses `F_{n}.cnf` into `n`.
fn parse_instance_file(name: &str) -> Option<usize> {
    name.strip_prefix("F_")?.strip_suffix(".cnf")?.parse().ok()
}

/// Every committed `F_*.cnf` in the claim ledger must come back out of the Rust
/// encoder byte for byte.
///
/// These are the files the stored DRAT certificates refute. If the Rust encoder
/// and the artifact disagree, either the artifact does not say what the claim
/// says it says, or this encoder is wrong; both are reportable, neither is
/// papered over.
///
/// A claim directory whose name does not parse is a **failure**, not a skip: a
/// renamed family that silently drops out of the sweep is exactly how a gate
/// stops gating.
#[test]
fn stored_ledger_cnf_artifacts_regenerate_byte_identically() {
    let ledger = repo_root().join("artifacts").join("claims").join("rado");
    let mut claim_dirs: Vec<PathBuf> = fs::read_dir(&ledger)
        .unwrap_or_else(|error| panic!("cannot read {}: {error}", ledger.display()))
        .map(|entry| entry.expect("directory entry").path())
        .filter(|path| path.is_dir())
        .collect();
    claim_dirs.sort();
    assert!(
        !claim_dirs.is_empty(),
        "no claim directories under {}; the ledger gate would check nothing",
        ledger.display()
    );

    let mut checked = Vec::new();
    let mut failures = Vec::new();
    for dir in &claim_dirs {
        let id = dir
            .file_name()
            .expect("directory has a name")
            .to_str()
            .expect("claim ids are UTF-8");
        let mut files: Vec<PathBuf> = fs::read_dir(dir)
            .unwrap_or_else(|error| panic!("cannot read {}: {error}", dir.display()))
            .map(|entry| entry.expect("directory entry").path())
            .filter(|path| {
                path.extension().is_some_and(|extension| extension == "cnf")
                    && path
                        .file_name()
                        .and_then(|name| name.to_str())
                        .is_some_and(|name| name.starts_with("F_"))
            })
            .collect();
        if files.is_empty() {
            continue;
        }
        files.sort();
        let Some((k, a, b)) = parse_claim_id(id) else {
            failures.push(format!(
                "claim id {id:?} carries {} CNF artifact(s) but does not parse as \
                 rado-r<k>-a<a>-b<b>, so its instances were never checked",
                files.len()
            ));
            continue;
        };
        for file in files {
            let name = file
                .file_name()
                .expect("file has a name")
                .to_str()
                .expect("artifact names are UTF-8");
            let Some(n) = parse_instance_file(name) else {
                failures.push(format!("{id}/{name} does not parse as F_<n>.cnf"));
                continue;
            };
            let instance = Instance::new(a, b, k, n);
            let stored = fs::read_to_string(&file)
                .unwrap_or_else(|error| panic!("cannot read {}: {error}", file.display()));
            let produced = instance.encode();
            if stored != produced {
                failures.push(format!(
                    "{id}/{name}: {}",
                    describe_difference(instance, &stored, &produced)
                ));
            }
            checked.push(instance);
        }
    }

    assert!(
        failures.is_empty(),
        "{} of {} stored ledger CNF artifacts did not regenerate:\n{}",
        failures.len(),
        checked.len(),
        failures.join("\n")
    );
    // The ledger had 35 stored formulas when this gate was written. Requiring a
    // floor turns "the glob stopped matching" from a silent pass into a failure.
    assert!(
        checked.len() >= 35,
        "only {} stored CNF artifacts were checked; expected at least the 35 the \
         ledger carried when this gate was written",
        checked.len()
    );
    println!(
        "layer 1: {} stored ledger CNF artifacts regenerated byte-identically",
        checked.len()
    );
}

// ---------------------------------------------------------------- layer 2

/// Instances the claim ledger cites, as `(a, b, k, n)` where `n = R_k`.
///
/// Kept as data rather than read from `claim.json` so this crate needs no JSON
/// dependency.
///
/// CORRECTION 2026-08-13: this comment used to claim layer 1 "would fail if the
/// ledger grew a formula this list does not mention". It would not. Layer 1
/// walks the artifacts on disk and never consults this list, so the two can
/// drift apart silently; today they happen to coincide at 36. The stated
/// safety property did not exist, and it guarded exactly the drift the paper's
/// macro note warns about.
const LEDGER_INSTANCES: &[(usize, usize, usize, usize)] = &[
    (1, 1, 3, 14),
    (1, 2, 3, 43),
    (1, 3, 3, 94),
    (1, 4, 3, 173),
    (1, 5, 3, 286),
    (2, 1, 3, 14),
    (2, 2, 3, 14),
    (2, 3, 3, 61),
    (2, 4, 3, 43),
    (2, 5, 3, 181),
    (3, 1, 3, 27),
    (3, 2, 3, 31),
    (3, 3, 3, 14),
    (3, 4, 3, 109),
    (3, 5, 3, 186),
    (4, 1, 3, 64),
    (4, 2, 3, 14),
    (4, 3, 3, 73),
    (4, 4, 3, 14),
    (4, 5, 3, 180),
    (5, 1, 3, 125),
    (5, 2, 3, 125),
    (5, 3, 3, 125),
    (5, 4, 3, 141),
    (5, 5, 3, 14),
    (1, 1, 4, 45),
    (1, 2, 4, 171),
    (2, 1, 4, 56),
    (2, 2, 4, 45),
    // The headline: R_4(2(x−y)=3z) = 226.
    (2, 3, 4, 226),
    (3, 1, 4, 81),
    (3, 2, 4, 103),
    (3, 3, 4, 45),
    (4, 1, 4, 256),
    (4, 2, 4, 56),
    // The headline: R_4(4(x−y)=3z) = 313.
    (4, 3, 4, 313),
];

/// The parameter sweep both sides encode.
///
/// Three bands: a dense small grid that hits every `gcd(a,b)` shape and the
/// degenerate ends of the loops; every ledger instance together with `n − 1`
/// (the satisfiable side of the same claim) and `n + 1`; and the `k = 5`
/// frontier instance `R_5(3(x−y)=2z) > 350`.
fn sweep() -> Vec<Instance> {
    let mut cases = Vec::new();
    for a in 1..=6 {
        for b in 1..=6 {
            for k in 1..=4 {
                // Small `n` covers the loop's degenerate ends: `n` below `a'`
                // or `b'` (no solutions at all), and `n <= k` (where symmetry
                // breaking degenerates to unit clauses).
                for n in [1, 2, 3, 4, 5, 7, 9, 12, 17, 25] {
                    cases.push(Instance::new(a, b, k, n));
                }
            }
        }
    }
    for &(a, b, k, n) in LEDGER_INSTANCES {
        cases.push(Instance::new(a, b, k, n - 1));
        cases.push(Instance::new(a, b, k, n));
        cases.push(Instance::new(a, b, k, n + 1));
    }
    // rado-r5-a3-b2-frontier: R_5(3(x−y)=2z) > 350, the only k = 5 claim.
    for n in [349, 350, 351] {
        cases.push(Instance::new(3, 2, 5, n));
    }
    // Coefficients well past the ledger's 1..=5 box, including a large common
    // factor (gcd 6) and coefficients larger than n.
    for &(a, b) in &[(12, 18), (18, 12), (7, 11), (11, 7), (40, 40), (97, 3)] {
        for k in [2, 3] {
            for n in [1, 6, 30, 90] {
                cases.push(Instance::new(a, b, k, n));
            }
        }
    }
    cases.sort();
    cases.dedup();
    cases
}

/// Imports `generate()` from the generator of record and writes one CNF per
/// manifest line. It does **not** re-derive the encoding — importing is the
/// point.
const DRIVER: &str = r#"
import importlib.util
import pathlib
import sys

script, manifest, outdir = sys.argv[1], sys.argv[2], sys.argv[3]
spec = importlib.util.spec_from_file_location("gen_rado_instance", script)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

out = pathlib.Path(outdir)
out.mkdir(parents=True, exist_ok=True)
written = 0
for index, line in enumerate(pathlib.Path(manifest).read_text().splitlines()):
    a, b, k, n = (int(token) for token in line.split())
    (out / f"{index}.cnf").write_text(module.generate(a, b, k, n))
    written += 1
print(written)
"#;

/// Fails with the reason `python3` could not be used, rather than skipping.
fn require_python(root: &Path) -> PathBuf {
    let script = root.join("scripts").join("gen-rado-instance.py");
    assert!(
        script.is_file(),
        "the generator of record is missing at {}; this differential gate has \
         nothing to compare against and must not pass",
        script.display()
    );
    let probe = Command::new("python3").arg("--version").output();
    match probe {
        Ok(output) if output.status.success() => {}
        Ok(output) => panic!(
            "python3 --version exited {}; the generator of record cannot be run, \
             and a skipped differential gate is not a passing one",
            output.status
        ),
        Err(error) => panic!(
            "cannot run python3 ({error}); the generator of record cannot be run, \
             and a skipped differential gate is not a passing one"
        ),
    }
    script
}

/// The whole sweep, byte for byte, against the imported generator of record.
#[test]
fn python_generator_of_record_matches_on_a_wide_sweep() {
    let root = repo_root();
    let script = require_python(&root);
    let cases = sweep();
    assert!(
        cases.len() >= 1_500,
        "sweep collapsed to {} instances; a differential gate over almost nothing \
         is the failure this assertion exists to catch",
        cases.len()
    );

    let work = Path::new(env!("CARGO_TARGET_TMPDIR")).join("colouring-parity");
    let _ = fs::remove_dir_all(&work);
    fs::create_dir_all(&work).expect("create the work directory");
    let manifest = work.join("manifest.txt");
    let mut manifest_text = String::new();
    for case in &cases {
        writeln!(manifest_text, "{} {} {} {}", case.a, case.b, case.k, case.n)
            .expect("writing to a String cannot fail");
    }
    fs::write(&manifest, &manifest_text).expect("write the manifest");
    let outdir = work.join("reference");

    let python_started = Instant::now();
    let output = Command::new("python3")
        .arg("-c")
        .arg(DRIVER)
        .arg(&script)
        .arg(&manifest)
        .arg(&outdir)
        .output()
        .expect("run the generator of record");
    let python_elapsed = python_started.elapsed();
    assert!(
        output.status.success(),
        "the generator of record failed ({}):\n{}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
    let written: usize = String::from_utf8_lossy(&output.stdout)
        .trim()
        .parse()
        .expect("the driver prints the number of instances it wrote");
    assert_eq!(
        written,
        cases.len(),
        "the generator of record wrote {written} instances for {} manifest lines",
        cases.len()
    );

    let mut rust_elapsed = Duration::ZERO;
    let mut failures = Vec::new();
    for (index, case) in cases.iter().enumerate() {
        let started = Instant::now();
        let produced = case.encode();
        rust_elapsed += started.elapsed();
        let reference_path = outdir.join(format!("{index}.cnf"));
        let reference = fs::read_to_string(&reference_path)
            .unwrap_or_else(|error| panic!("cannot read {}: {error}", reference_path.display()));
        if reference != produced {
            failures.push(describe_difference(*case, &reference, &produced));
        }
    }

    assert!(
        failures.is_empty(),
        "{} of {} instances differ from the generator of record:\n{}",
        failures.len(),
        cases.len(),
        failures
            .iter()
            .take(8)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    );
    let total_bytes: usize = cases.iter().map(|case| case.n * case.k).sum();
    println!(
        "layer 2: {} instances byte-identical to the generator of record \
         ({} CNF variables total); python {:?} (interpreter start + generate + \
         write), rust {:?} (generate only)",
        cases.len(),
        total_bytes,
        python_elapsed,
        rust_elapsed
    );
    let _ = fs::remove_dir_all(&work);
}

// ---------------------------------------------------------------- layer 3

/// The script's own command line, on the instances behind the headline claims.
///
/// Layer 2 imports `generate()`; this runs `gen-rado-instance.py a b k n` the
/// way the ledger's provenance says the artifacts were produced, so a
/// difference between the function and the entry point cannot hide.
#[test]
fn python_cli_matches_on_the_headline_instances() {
    let root = repo_root();
    let script = require_python(&root);
    let headline = [
        // R_4(2(x−y)=3z) = 226: both sides of the boundary.
        Instance::new(2, 3, 4, 225),
        Instance::new(2, 3, 4, 226),
        // R_4(4(x−y)=3z) = 313: both sides of the boundary.
        Instance::new(4, 3, 4, 312),
        Instance::new(4, 3, 4, 313),
        // R_5(3(x−y)=2z) > 350.
        Instance::new(3, 2, 5, 350),
        // The smallest interesting instance, where every loop bound bites.
        Instance::new(1, 1, 3, 14),
    ];
    for case in headline {
        let output = Command::new("python3")
            .arg(&script)
            .arg(case.a.to_string())
            .arg(case.b.to_string())
            .arg(case.k.to_string())
            .arg(case.n.to_string())
            .output()
            .expect("run the generator of record");
        assert!(
            output.status.success(),
            "generator exited {} on {case:?}:\n{}",
            output.status,
            String::from_utf8_lossy(&output.stderr)
        );
        let reference = String::from_utf8(output.stdout).expect("DIMACS is ASCII");
        let produced = case.encode();
        assert!(
            reference == produced,
            "{}",
            describe_difference(case, &reference, &produced)
        );
    }
    println!(
        "layer 3: {} headline instances byte-identical through the script's own CLI",
        headline.len()
    );
}
