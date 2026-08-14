//! Measures the peak resident size of each DRAT checking route on a real
//! certificate (ADR-0426).
//!
//! The in-process `DratMemoryReport` measures the checker's own allocations;
//! this measures what the *operating system* saw, from `/proc/self/status`
//! `VmHWM`, which is the number a scheduler actually has to fit. The two are
//! reconciled in the module docs of `drat_resource`.
//!
//! ```text
//! cargo run --release -p axeyum-cnf --example drat_memory_probe -- \
//!     <formula.cnf> <proof.drat> [mode]
//! ```
//!
//! Modes: `backward` (default, the in-memory route), `file-backed`,
//! `file-backed-within` (with a system budget and a printed report), `parse`
//! (the step vector alone), `forward-stream` (the reference forward checker).
//!
//! Linux only: `VmHWM` comes from `/proc`. Prints one JSON line on stdout and
//! human-readable detail on stderr.

use std::fs;
use std::io::BufReader;

/// Peak resident bytes per proof byte, as a diagnostic ratio.
#[allow(clippy::cast_precision_loss)]
fn ratio(peak: u64, drat_bytes: u64) -> f64 {
    peak as f64 / drat_bytes.max(1) as f64
}

fn vm_hwm() -> u64 {
    let status = fs::read_to_string("/proc/self/status").unwrap_or_default();
    for line in status.lines() {
        if let Some(rest) = line.strip_prefix("VmHWM:") {
            let kb: u64 = rest
                .split_whitespace()
                .next()
                .and_then(|t| t.parse().ok())
                .unwrap_or(0);
            return kb * 1024;
        }
    }
    0
}

fn vm_rss() -> u64 {
    let status = fs::read_to_string("/proc/self/status").unwrap_or_default();
    for line in status.lines() {
        if let Some(rest) = line.strip_prefix("VmRSS:") {
            let kb: u64 = rest
                .split_whitespace()
                .next()
                .and_then(|t| t.parse().ok())
                .unwrap_or(0);
            return kb * 1024;
        }
    }
    0
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let cnf_path = &args[1];
    let drat_path = &args[2];
    let mode = args.get(3).map_or("backward", |s| s.as_str());

    let drat_bytes = fs::metadata(drat_path).unwrap().len();
    let cnf_text = fs::read_to_string(cnf_path).unwrap();
    let formula = axeyum_cnf::parse_dimacs(&cnf_text).unwrap();
    drop(cnf_text);
    let base = vm_hwm();
    let literals: usize = formula.clauses().iter().map(|c| c.lits().len()).sum();
    eprintln!(
        "formula: {} vars {} clauses {} literals; baseline VmHWM {} B",
        formula.variable_count(),
        formula.clauses().len(),
        literals,
        base
    );

    let start = std::time::Instant::now();
    match mode {
        "file-backed" => {
            let file = fs::File::open(drat_path).unwrap();
            let verdict = axeyum_cnf::check_drat_backward_reader(
                &formula,
                BufReader::with_capacity(1 << 20, file),
            )
            .unwrap();
            eprintln!("file-backed verdict: {verdict}");
        }
        "file-backed-within" => {
            let file = fs::File::open(drat_path).unwrap();
            let shape = axeyum_cnf::DratProofShape::from_proof_bytes(drat_bytes);
            let estimate =
                axeyum_cnf::DratMemoryModel::new(axeyum_cnf::DratCheckRoute::FileBackedBackward)
                    .estimate(shape, axeyum_cnf::FormulaShape::of(&formula));
            let budget = axeyum_cnf::MemoryBudget::from_system().unwrap();
            let outcome = axeyum_cnf::check_drat_backward_reader_within(
                &formula,
                BufReader::with_capacity(1 << 20, file),
                estimate,
                budget,
            )
            .unwrap();
            match &outcome {
                axeyum_cnf::BackwardCheckOutcome::Refuted(report) => {
                    eprintln!("REFUTED  {report}");
                }
                axeyum_cnf::BackwardCheckOutcome::NoRefutation(report) => {
                    eprintln!("NO-REFUTATION  {report}");
                }
                axeyum_cnf::BackwardCheckOutcome::Declined(decline) => {
                    eprintln!("DECLINED  {decline}");
                }
            }
        }
        "forward-stream" => {
            let file = fs::File::open(drat_path).unwrap();
            let reader = axeyum_cnf::DratTextReader::new(BufReader::with_capacity(1 << 20, file));
            let verdict = axeyum_cnf::check_drat_streaming(&formula, reader).unwrap();
            eprintln!("forward-stream verdict: {verdict}");
        }
        "parse" => {
            let text = fs::read_to_string(drat_path).unwrap();
            let steps = axeyum_cnf::parse_drat(&text).unwrap();
            eprintln!(
                "parsed {} steps; rss after parse {} B (text still held: {} B)",
                steps.len(),
                vm_rss(),
                text.len()
            );
            drop(text);
            eprintln!("rss after dropping text: {} B", vm_rss());
            std::hint::black_box(&steps);
        }
        _ => {
            let text = fs::read_to_string(drat_path).unwrap();
            let steps = axeyum_cnf::parse_drat(&text).unwrap();
            drop(text);
            let rss_steps = vm_rss();
            eprintln!(
                "parsed {} steps; rss holding steps only {} B",
                steps.len(),
                rss_steps
            );
            let verdict = axeyum_cnf::check_drat_backward(&formula, &steps).unwrap();
            eprintln!("backward verdict: {verdict}");
        }
    }
    let peak = vm_hwm();
    println!(
        "{{\"mode\":\"{mode}\",\"drat_bytes\":{drat_bytes},\"peak_rss_bytes\":{peak},\"baseline_rss_bytes\":{base},\"ratio\":{:.3},\"seconds\":{:.3}}}",
        ratio(peak, drat_bytes),
        start.elapsed().as_secs_f64()
    );
}
