//! Micro-benchmarks for SMT-LIB ingest — the s-expression reader
//! ([`read_all`]) and the full typed parser ([`parse_script`]).
//!
//! # What real workload this is a proxy for
//!
//! **This one is not a proxy: the inputs ARE the real workload.** Every case
//! below reads a file committed under `corpus/` and hands the parser exactly
//! the bytes the shipped front door (`solve_smtlib`) would hand it. Ingest is
//! not an instant but a *phase* — [`crate::SmtError::DeadlineExceeded`]'s own
//! doc records a 58 MB benchmark taking ~54 s to read, and a 24 s solve budget
//! producing measured runs of 39.9 s / 49.4 s / 66 s because the parser had no
//! deadline. So parse time is charged against the same wall clock as the
//! search, on every single query.
//!
//! # The two-stage split is the point
//!
//! `parse_script` runs two passes over the source: [`read_all`] builds an
//! [`SExpr`] tree (lexing + paren matching + `String` allocation per atom),
//! and the typed parser then walks that tree doing sort checking and
//! [`TermArena`](axeyum_ir::TermArena) construction. Both are benched on the
//! same file so the pair reads as a decomposition rather than two unrelated
//! numbers: `read_all` is a lower bound on `parse_script`, and the difference
//! is what semantic analysis costs.
//!
//! # Where the committed corpus does NOT represent the real workload
//!
//! Measured 2026-09-07, `corpus/**/*.smt2` is 1,101 files with this size
//! distribution:
//!
//! | bytes | files |
//! |---|---|
//! | < 1 K | 965 |
//! | 1 K – 10 K | 107 |
//! | 10 K – 100 K | 18 |
//! | 100 K – 1 M | 8 |
//! | > 1 M | 3 |
//!
//! 88% of it is under a kilobyte. The multi-megabyte SMT-LIB benchmarks that
//! motivated the ingest deadline are **not in the tree** (they are fetched),
//! so the largest committed file is a 10 MB `QF_ABV` outlier rather than a
//! representative of the tail. The three sizes benched here (~2.7 K, ~50 K,
//! ~1.1 M) are chosen to span the committed range and to make the *shape* of
//! the cost curve visible; a reader wanting the tail must run the fetched
//! corpus, not this bench.
//!
//! Each case is a fixed committed file — no RNG, no seed to pin.

#![allow(missing_docs)] // criterion_group!/criterion_main! expand to undocumented items; see module doc.

use std::hint::black_box;
use std::path::{Path, PathBuf};

use axeyum_smtlib::{parse_script, read_all};
use criterion::{Criterion, criterion_group, criterion_main};

/// Committed inputs, smallest first. Each is `(bench label, repo-relative path)`.
///
/// - `bit_counting` (~2.7 K) — the largest file in `corpus/qfbv-curated`, i.e.
///   the regime 88% of the committed corpus lives in, where fixed per-call
///   overhead is still visible against real work.
/// - `array_subst7` (~50 K) — a `QF_ABV` bitwuzla regression, the middle of the
///   committed range.
/// - `array_random3` (~1.1 M) — a real megabyte-scale benchmark, the only
///   committed size class where ingest time is plausibly comparable to solve
///   time.
const CASES: &[(&str, &str)] = &[
    (
        "bit_counting_2k",
        "corpus/qfbv-curated/crafted__bit-counting.smt2",
    ),
    (
        "array_subst7_50k",
        "corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/preprocess__array__nondestr_subst7.smt2",
    ),
    (
        "array_random3_1m",
        "corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__random3.btor.smt2",
    ),
];

/// Resolves a repo-relative corpus path from `CARGO_MANIFEST_DIR`.
///
/// `cargo bench` sets the cwd to the *workspace* root, but a bench binary run
/// directly does not, so deriving the path from the manifest directory is the
/// only form that works in both.
fn corpus_path(relative: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join(relative)
}

fn load(relative: &str) -> String {
    let path = corpus_path(relative);
    std::fs::read_to_string(&path).unwrap_or_else(|e| {
        panic!(
            "committed corpus file {} must be readable: {e}",
            path.display()
        )
    })
}

fn bench_read_all(c: &mut Criterion) {
    let mut group = c.benchmark_group("smtlib_read_all");
    for (label, relative) in CASES {
        let source = load(relative);
        // A megabyte file needs a smaller sample count to stay inside the
        // lane's five-minute-per-bench budget; criterion's default 100 samples
        // times a ~10 ms iteration is fine, but the ceiling is set explicitly
        // rather than left to luck.
        group.sample_size(if source.len() > 500_000 { 20 } else { 100 });
        group.bench_function(*label, |b| {
            b.iter(|| {
                let exprs = read_all(&source).expect("committed corpus files read cleanly");
                assert!(
                    !exprs.is_empty(),
                    "a committed SMT-LIB file must yield at least one top-level \
                     s-expression; an empty result means the fixture stopped \
                     exercising the reader"
                );
                black_box(exprs);
            });
        });
    }
    group.finish();
}

fn bench_parse_script(c: &mut Criterion) {
    let mut group = c.benchmark_group("smtlib_parse_script");
    for (label, relative) in CASES {
        let source = load(relative);
        group.sample_size(if source.len() > 500_000 { 20 } else { 100 });
        group.bench_function(*label, |b| {
            b.iter(|| {
                let script = parse_script(&source).expect("committed corpus files parse cleanly");
                assert!(
                    !script.assertions.is_empty(),
                    "a committed benchmark must produce at least one assertion; \
                     zero means the fixture stopped exercising the typed parser"
                );
                black_box(script);
            });
        });
    }
    group.finish();
}

criterion_group!(benches, bench_read_all, bench_parse_script);
criterion_main!(benches);
