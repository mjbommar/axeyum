//! The denominator for the `!features.has_real` array gate (ADR-1960).
//!
//! [ADR-1955] measured that 19,620 AUFLIRA/AUFNIRA files fail a **flat** array
//! obligation at `scalar_alia_auflia_arrays_supported`
//! (`crates/axeyum-solver/src/auto.rs`), whose first clause is
//! `!features.has_real`. That is a *blocked* count taken behind the nested-array
//! parse refusal, and [ADR-1945] is explicit that a blocked count is an upper
//! bound on a reachable count — measured instances in this repository ran
//! 143→6, 51→2, 173→10, 84→49.
//!
//! This is the instrument that says what lifting that one clause reaches **on
//! its own**, with the parse refusal still in place. It reports, per division,
//! the population split that the dispatcher itself would see:
//!
//! * `parse_err` — never reaches any gate (the nested-array refusal lives here).
//! * `no_array` — no array-sorted term, so the gate is not consulted.
//! * `bv_array` — `has_array` but not `has_non_bv_array`: the pure-`QF_ABV`
//!   route, untouched by this clause.
//! * `pass_today` — a non-BV array query the predicate already admits.
//! * `real_gate_only` — a non-BV array query refused by **`has_real` alone**:
//!   every other clause of the predicate passes. *This is the population the
//!   change reaches directly.*
//! * `blocked_other` — a non-BV array query refused by a clause this lane does
//!   not touch, broken out by which one (sorts/datatype/BV can co-occur, so the
//!   sub-buckets are reported as independent counts, not a partition).
//!
//! The `q` / `nq` split on every array bucket is load-bearing: the array fast
//! paths sit in the quantifier-free ladder, so a quantified file does not reach
//! the gate even when its features admit it. Counting without that split is how
//! a blocked count becomes an overstated reachable one.
//!
//! The feature scan here MIRRORS `Features::scan_within` / `Features::note_sort`
//! (`crates/axeyum-solver/src/auto.rs`), which are private to the solver crate.
//! A mirror is a second implementation and can drift, so treat its output as a
//! denominator to be confirmed by the A/B, never as the finding itself. It is
//! deliberately written against the same public IR surface the original uses
//! (`arena.sort_of`, `arena.node`, `Sort`, `ArraySortKey`, `Op`) so that the two
//! agree by construction on everything but a future feature flag.
//!
//! Usage:
//! ```sh
//! cargo run --release -p axeyum-smtlib --example array_real_gate_census -- <list-file|->
//! ```
//! One benchmark path per line. Per-file lines go to stdout as
//! `<class> <sub> <q|nq> <path>`; the summary goes to stderr.
//!
//! [ADR-1955]: ../../docs/research/09-decisions/adr-1955-the-nested-array-sort-is-the-first-of-three-gates-and-the-only-one-the-ir-owns.md
//! [ADR-1945]: ../../docs/research/09-decisions/adr-1945-a-blocked-count-is-not-a-reachable-count-and-two-sequential-caps-are-not-two-caps.md

use std::collections::{BTreeMap, BTreeSet};
use std::io::Read as _;
use std::process::ExitCode;

use axeyum_ir::{Op, Sort, TermArena, TermId, TermNode};
use axeyum_smtlib::parse_script;

/// The subset of `Features` this gate consults, scanned the same way.
///
/// `struct_excessive_bools` is allowed because this type MIRRORS
/// `auto::Features`, which is a bag of theory flags. Collapsing them into an
/// enum or a bitflag set here would make the mirror harder to diff against the
/// original, and a mirror that does not read like its subject is how it drifts.
#[derive(Default, Clone, Copy)]
#[allow(clippy::struct_excessive_bools)]
struct GateFeatures {
    has_real: bool,
    has_bv_or_float: bool,
    has_datatype: bool,
    has_function: bool,
    has_uninterpreted_sort: bool,
    has_array: bool,
    has_non_bv_array: bool,
    has_quantifier: bool,
}

impl GateFeatures {
    fn note_sort(&mut self, sort: Sort) {
        match sort {
            Sort::Real => self.has_real = true,
            Sort::BitVec(_) | Sort::RoundingMode | Sort::Float { .. } => {
                self.has_bv_or_float = true;
            }
            Sort::Array { index, element } => {
                self.has_array = true;
                if sort.array_widths().is_none() {
                    self.has_non_bv_array = true;
                }
                self.note_sort(index.to_sort());
                self.note_sort(element.to_sort());
            }
            Sort::Datatype(_) => self.has_datatype = true,
            Sort::Uninterpreted(_) => self.has_uninterpreted_sort = true,
            Sort::Bool | Sort::Int | Sort::Seq(_) => {}
        }
    }

    fn scan(arena: &TermArena, assertions: &[TermId]) -> Self {
        let mut features = GateFeatures::default();
        let mut seen = BTreeSet::new();
        let mut stack = assertions.to_vec();
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            features.note_sort(arena.sort_of(term));
            if let TermNode::App { op, args } = arena.node(term) {
                if matches!(op, Op::Apply(_)) {
                    features.has_function = true;
                }
                if matches!(op, Op::Forall(_) | Op::Exists(_)) {
                    features.has_quantifier = true;
                }
                if matches!(
                    op,
                    Op::DtConstruct { .. } | Op::DtSelect { .. } | Op::DtTest(_)
                ) {
                    features.has_datatype = true;
                }
                for &arg in &**args {
                    stack.push(arg);
                }
            }
        }
        features
    }

    /// `scalar_alia_auflia_arrays_supported` verbatim.
    fn passes_today(self) -> bool {
        !self.has_real
            && !self.has_bv_or_float
            && !self.has_uninterpreted_sort
            && !self.has_datatype
    }

    /// The same predicate with the `has_real` clause dropped.
    fn passes_without_real_clause(self) -> bool {
        !self.has_bv_or_float && !self.has_uninterpreted_sort && !self.has_datatype
    }
}

/// `(class, sub-class)` for one file.
fn classify(features: GateFeatures) -> (&'static str, &'static str) {
    if !features.has_array {
        return ("no_array", "-");
    }
    if !features.has_non_bv_array {
        return ("bv_array", "-");
    }
    if features.passes_today() {
        return (
            "pass_today",
            if features.has_function {
                "auflia"
            } else {
                "alia"
            },
        );
    }
    if features.has_real && features.passes_without_real_clause() {
        return (
            "real_gate_only",
            if features.has_function {
                "auflia"
            } else {
                "alia"
            },
        );
    }
    let sub = if features.has_uninterpreted_sort {
        "uninterp_sort"
    } else if features.has_datatype {
        "datatype"
    } else if features.has_bv_or_float {
        "bv_or_float"
    } else {
        "other"
    };
    ("blocked_other", sub)
}

fn main() -> ExitCode {
    let Some(list_path) = std::env::args().nth(1) else {
        eprintln!("usage: array_real_gate_census <list-file|->");
        return ExitCode::from(2);
    };
    let list = if list_path == "-" {
        let mut buf = String::new();
        if let Err(e) = std::io::stdin().read_to_string(&mut buf) {
            eprintln!("read error on stdin: {e}");
            return ExitCode::from(2);
        }
        buf
    } else {
        match std::fs::read_to_string(&list_path) {
            Ok(text) => text,
            Err(e) => {
                eprintln!("read error on {list_path}: {e}");
                return ExitCode::from(2);
            }
        }
    };

    let paths: Vec<&str> = list
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .collect();
    if paths.is_empty() {
        eprintln!("ABORT: the list is empty, so every count below would be a vacuous zero");
        return ExitCode::from(2);
    }

    // `(class, sub, quantified)` -> count.
    let mut tally: BTreeMap<(&'static str, &'static str, bool), usize> = BTreeMap::new();
    for path in &paths {
        let text = match std::fs::read_to_string(path) {
            Ok(text) => text,
            Err(e) => {
                println!("read_err {e} nq {path}");
                *tally.entry(("read_err", "-", false)).or_default() += 1;
                continue;
            }
        };
        let (class, sub, quantified) = match parse_script(&text) {
            // A corpus reader over arbitrary text must HANDLE the word-first
            // fallback rather than assert it away: its flat view is empty, so
            // scanning it would report `no_array` for a file nobody looked at.
            Ok(script) => match script.solvable_flat_view() {
                Some(assertions) => {
                    let features = GateFeatures::scan(&script.arena, assertions);
                    let (class, sub) = classify(features);
                    (class, sub, features.has_quantifier)
                }
                None => ("word_fallback", "-", false),
            },
            Err(_) => ("parse_err", "-", false),
        };
        println!(
            "{class} {sub} {} {path}",
            if quantified { "q" } else { "nq" }
        );
        *tally.entry((class, sub, quantified)).or_default() += 1;
    }

    eprintln!("files: {}", paths.len());
    for ((class, sub, quantified), count) in &tally {
        eprintln!(
            "{class}\t{sub}\t{}\t{count}",
            if *quantified { "q" } else { "nq" }
        );
    }
    let reachable_now: usize = tally
        .iter()
        .filter(|((class, _, quantified), _)| *class == "real_gate_only" && !*quantified)
        .map(|(_, count)| *count)
        .sum();
    let reachable_if_quantifiers: usize = tally
        .iter()
        .filter(|((class, _, _), _)| *class == "real_gate_only")
        .map(|(_, count)| *count)
        .sum();
    eprintln!("real_gate_only, quantifier-free (reaches the gate today): {reachable_now}");
    eprintln!("real_gate_only, all (needs a quantifier route too): {reachable_if_quantifiers}");
    ExitCode::SUCCESS
}
