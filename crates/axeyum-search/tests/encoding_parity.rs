//! Differential gate: this crate's colouring encoder against the generator of
//! record, byte for byte.
//!
//! `crates/axeyum-search/src/colouring.rs` has claimed since it was written that
//! "`tests/encoding_parity.rs` compares them directly". **It did not exist.** It
//! was the last of the four prose-only guards found on 2026-08-14 — a comment
//! describing a check that was never written — and this file is that check.
//!
//! ## Why this crate needs its own gate
//!
//! `axeyum-cnf` already has one (`tests/colouring_encoding_parity.rs`, three
//! layers, no skip path). But **this** encoder is the one the search actually
//! runs: cube covers, local search and the frontier driver all encode through
//! `axeyum_search::colouring::ColouringProblem`. A cover computed here against a
//! formula that differs from the ledger's stored CNF would be a valid proof of
//! the wrong statement — the exact failure the campaign flagged when an unsound
//! symmetry break manufactured a wrong `unsat`.
//!
//! `examples/recertify_rado.rs` does byte-compare a regenerated CNF against the
//! stored artifacts, but it **reimplements the generator by hand** rather than
//! calling this encoder, and it runs in no gate.
//!
//! ## Two layers
//!
//! 1. [`search_encoder_agrees_with_the_cnf_encoder`] — pure Rust, no
//!    interpreter. Ties this encoder to `axeyum-cnf`'s, which is already checked
//!    against the generator of record and every stored ledger instance.
//! 2. [`python_generator_of_record_matches_directly`] — the script itself, so
//!    layer 1 cannot pass by both Rust encoders drifting together.
//!
//! Layer 2 **fails closed** when `python3` or the script is missing. A
//! differential gate that quietly becomes a no-op is the failure mode this
//! repository has been bitten by most.

use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::Command;

use axeyum_search::colouring::ColouringProblem as SearchProblem;
use axeyum_search::family::{ColouringFamily, Rado as SearchRado};

use axeyum_cnf::colouring::{ColouringProblem as CnfProblem, Rado as CnfRado};

/// `a(x − y) = b z` with `k` colours over the points `1..=n`.
#[derive(Clone, Copy, Debug)]
struct Instance {
    a: usize,
    b: usize,
    k: usize,
    n: usize,
}

/// The instances the ledger's headline claims rest on, plus their satisfiable
/// neighbours and a few small shapes that exercise `gcd(a, b) > 1`.
const SWEEP: &[Instance] = &[
    Instance {
        a: 1,
        b: 1,
        k: 3,
        n: 13,
    },
    Instance {
        a: 1,
        b: 1,
        k: 3,
        n: 14,
    },
    Instance {
        a: 2,
        b: 3,
        k: 3,
        n: 20,
    },
    Instance {
        a: 3,
        b: 2,
        k: 3,
        n: 31,
    },
    Instance {
        a: 4,
        b: 2,
        k: 3,
        n: 14,
    },
    Instance {
        a: 5,
        b: 4,
        k: 3,
        n: 141,
    },
    Instance {
        a: 2,
        b: 3,
        k: 4,
        n: 226,
    },
    Instance {
        a: 4,
        b: 3,
        k: 4,
        n: 60,
    },
    Instance {
        a: 6,
        b: 4,
        k: 2,
        n: 25,
    },
];

fn search_dimacs(instance: Instance) -> String {
    let family = SearchRado::new(instance.a, instance.b, instance.k)
        .expect("search Rado family is well-formed");
    let problem: SearchProblem = family
        .problem(instance.n)
        .expect("search colouring problem is well-formed");
    problem
        .encode()
        .expect("search encoder produces a formula")
        .to_dimacs()
}

fn cnf_dimacs(instance: Instance) -> String {
    let family = CnfRado::new(instance.a, instance.b).expect("cnf Rado family is well-formed");
    let problem = CnfProblem::from_family(&family, instance.n, instance.k)
        .expect("cnf colouring problem is well-formed");
    problem
        .encode()
        .expect("cnf encoder produces a formula")
        .to_dimacs()
}

/// The first line and the first differing line, which is what actually
/// localises a divergence in a million-literal instance.
fn describe(instance: Instance, expected: &str, actual: &str) -> String {
    let Instance { a, b, k, n } = instance;
    let mut report = format!("instance a={a} b={b} k={k} n={n}\n");
    for (index, (left, right)) in expected.lines().zip(actual.lines()).enumerate() {
        if left != right {
            let _ = writeln!(
                report,
                "first difference at line {}:\n  expected: {left}\n  actual:   {right}",
                index + 1
            );
            return report;
        }
    }
    let _ = writeln!(
        report,
        "no differing line; lengths {} vs {}",
        expected.lines().count(),
        actual.lines().count()
    );
    report
}

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("repository root resolves")
}

/// Layer 1: the two Rust encoders agree byte for byte.
///
/// `axeyum-cnf`'s side is already gated against the generator of record and
/// against every stored ledger instance, so agreement here carries this
/// encoder into that gate.
#[test]
fn search_encoder_agrees_with_the_cnf_encoder() {
    for &instance in SWEEP {
        let expected = cnf_dimacs(instance);
        let actual = search_dimacs(instance);
        assert!(
            expected == actual,
            "search and cnf encoders disagree\n{}",
            describe(instance, &expected, &actual)
        );
    }
}

/// Layer 2: the generator of record itself, so layer 1 cannot pass by both Rust
/// encoders drifting together.
///
/// Fails closed: a missing interpreter or script is a failure, not a skip.
#[test]
fn python_generator_of_record_matches_directly() {
    let root = repo_root();
    let script = root.join("scripts/gen-rado-instance.py");
    assert!(
        script.is_file(),
        "the generator of record is missing at {}; this gate cannot be skipped",
        script.display()
    );

    // A small sweep: the interpreter costs more than the encoder does, and
    // layer 1 already covers breadth.
    for &instance in &SWEEP[..5] {
        let Instance { a, b, k, n } = instance;
        let output = Command::new("python3")
            .arg(&script)
            .args([a.to_string(), b.to_string(), k.to_string(), n.to_string()])
            .output()
            .unwrap_or_else(|error| {
                panic!("python3 must be available to run the generator of record: {error}")
            });
        assert!(
            output.status.success(),
            "generator of record failed on a={a} b={b} k={k} n={n}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        let expected = String::from_utf8(output.stdout).expect("generator emits UTF-8");
        let actual = search_dimacs(instance);
        assert!(
            expected == actual,
            "search encoder differs from the generator of record\n{}",
            describe(instance, &expected, &actual)
        );
    }
}
