//! Dumps the **exact DRAT text** the native proof-producing CDCL core
//! ([`solve_with_drat_proof_streaming`]) emits for a fixed, reproducible corpus,
//! so two builds of the tree can be compared with `cmp`/`diff` rather than by
//! eye.
//!
//! This is the instrument for the S6 requirement "the emitted proof for any CNF
//! must be byte-identical before and after". A verdict comparison is far too
//! weak for a change to the reason representation: `analyze` and `lit_redundant`
//! decide *which* literals survive minimization, so a defect there changes the
//! learned clauses -- and therefore the proof -- while leaving every verdict
//! intact. The proof text is the finest-grained observable the core has.
//!
//! The corpus is two halves, both fixed:
//!
//! 1. every DIMACS path given on the command line (e.g. `corpus/micro-cnf/*.cnf`);
//! 2. a **seeded random 3-SAT family** generated in-process from a splitmix64
//!    stream, so it needs no committed files and is identical in any checkout of
//!    any commit. Sizes straddle the satisfiability threshold (ratio 4.26), which
//!    is where conflict analysis and clause minimization do the most work.
//!
//! ```sh
//! cargo run --release -p axeyum-cnf --example drat_stream_dump -- \
//!     corpus/micro-cnf/*.cnf > /tmp/after.drat
//! ```
//!
//! Output is one `=== <name> <verdict> ===` header per instance followed by the
//! literal proof text, so a diff points at the instance and the step.
//!
//! Not part of the solve path -- a measurement tool.

use std::path::Path;

use axeyum_cnf::{
    CnfClause, CnfFormula, CnfLit, CnfVar, DEFAULT_PROOF_SAT_CONFLICT_LIMIT, StreamingProofOutcome,
    TextProofSink, parse_dimacs, solve_with_drat_proof_streaming,
};

/// splitmix64: a fixed, dependency-free, fully specified PRNG. Chosen so the
/// generated corpus is a function of the seed alone and cannot drift with a
/// crate version.
struct SplitMix64(u64);

impl SplitMix64 {
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn below(&mut self, bound: u64) -> u64 {
        self.next_u64() % bound
    }
}

/// One random 3-SAT instance: `vars` variables, `clauses` clauses, no repeated
/// variable within a clause.
fn random_3sat(vars: usize, clauses: usize, rng: &mut SplitMix64) -> CnfFormula {
    let mut formula = CnfFormula::new(vars);
    let bound = u64::try_from(vars).expect("variable count fits u64");
    for _ in 0..clauses {
        let mut picked: Vec<usize> = Vec::with_capacity(3);
        while picked.len() < 3 {
            let candidate = usize::try_from(rng.below(bound)).expect("index fits usize");
            if !picked.contains(&candidate) {
                picked.push(candidate);
            }
        }
        let lits: Vec<CnfLit> = picked
            .iter()
            .map(|&v| {
                let lit = CnfLit::positive(CnfVar::new(v).expect("variable index in range"));
                if rng.next_u64() & 1 == 0 {
                    lit
                } else {
                    lit.negated()
                }
            })
            .collect();
        formula
            .add_clause(CnfClause::new(lits))
            .expect("clause is over the declared variables");
    }
    formula
}

/// Solves one formula and prints its header plus the raw proof text.
fn dump(name: &str, formula: &CnfFormula) {
    let mut text: Vec<u8> = Vec::new();
    let mut sink = TextProofSink::new(&mut text);
    let outcome =
        solve_with_drat_proof_streaming(formula, None, DEFAULT_PROOF_SAT_CONFLICT_LIMIT, &mut sink);
    sink.finish().expect("writing to a Vec cannot fail");
    let verdict = match outcome {
        StreamingProofOutcome::Sat(_) => "sat",
        StreamingProofOutcome::Unsat => "unsat",
        StreamingProofOutcome::ResourceOut => "resource-out",
        StreamingProofOutcome::Interrupted => "interrupted",
        StreamingProofOutcome::SinkFailed(_) => "sink-failed",
    };
    println!(
        "=== {name} {verdict} vars={} clauses={} bytes={} ===",
        formula.variable_count(),
        formula.clauses().len(),
        text.len()
    );
    print!("{}", String::from_utf8_lossy(&text));
}

fn main() {
    // Half 1: the DIMACS files named on the command line, in the order given.
    for path in std::env::args().skip(1) {
        let path = Path::new(&path);
        let name = path.file_name().map_or_else(
            || path.display().to_string(),
            |n| n.to_string_lossy().into(),
        );
        let text = std::fs::read_to_string(path)
            .unwrap_or_else(|error| panic!("reading {}: {error}", path.display()));
        let formula = parse_dimacs(&text)
            .unwrap_or_else(|error| panic!("parsing {}: {error:?}", path.display()));
        dump(&name, &formula);
    }

    // Half 2: the seeded random 3-SAT family. One RNG for the whole family, so
    // the instances are a fixed function of the single seed below.
    let mut rng = SplitMix64(0x2026_0906_0000_0056u64);
    for vars in [20usize, 30, 40, 50, 60] {
        for repeat in 0..6usize {
            // 4.26 is the 3-SAT threshold ratio: half the instances land on
            // each side, so both the sat and the unsat proof paths are covered.
            let clauses = (vars * 426) / 100;
            let formula = random_3sat(vars, clauses, &mut rng);
            dump(&format!("random3sat-v{vars}-r{repeat}"), &formula);
        }
    }
}
