//! Compare byte-identical DIMACS inputs across fresh SAT cores.
//!
//! This is a mechanism diagnostic, not an end-to-end SMT benchmark. Every
//! repetition imports the same standalone CNF into a fresh core. External
//! solver time includes process startup and is therefore reported separately.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::Instant;

use axeyum_cnf::{
    CnfFormula, ProofSolveOutcome, SatResult, check_drat, parse_dimacs, solve_with_drat_proof,
    solve_with_rustsat_batsat,
};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

#[cfg(feature = "z3")]
use z3::{Params, SatResult as Z3SatResult, Solver, ast::Bool};

fn outcome_batsat(formula: &CnfFormula) -> Result<&'static str, String> {
    match solve_with_rustsat_batsat(formula).map_err(|error| error.to_string())? {
        SatResult::Sat(_) => Ok("sat"),
        SatResult::Unsat(_) => Ok("unsat"),
        SatResult::Unknown(_) => Ok("unknown"),
    }
}

fn sha256_hex(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let digest = Sha256::digest(bytes);
    let mut encoded = String::with_capacity(64);
    for byte in digest {
        encoded.push(char::from(HEX[usize::from(byte >> 4)]));
        encoded.push(char::from(HEX[usize::from(byte & 0x0f)]));
    }
    encoded
}

fn outcome_proof(formula: &CnfFormula) -> &'static str {
    match solve_with_drat_proof(formula) {
        ProofSolveOutcome::Sat(_) => "sat",
        ProofSolveOutcome::Unsat(_) => "unsat",
        ProofSolveOutcome::ResourceOut => "resource-out",
        ProofSolveOutcome::Interrupted => "interrupted",
    }
}

fn outcome_proof_rechecked(formula: &CnfFormula) -> Result<&'static str, String> {
    match solve_with_drat_proof(formula) {
        ProofSolveOutcome::Sat(_) => Ok("sat"),
        ProofSolveOutcome::Unsat(proof) => match check_drat(formula, &proof) {
            Ok(true) => Ok("unsat"),
            Ok(false) => Err("proof core emitted a DRAT proof that did not refute the CNF".into()),
            Err(error) => Err(format!("DRAT recheck failed: {error}")),
        },
        ProofSolveOutcome::ResourceOut => Ok("resource-out"),
        ProofSolveOutcome::Interrupted => Ok("interrupted"),
    }
}

#[cfg(feature = "z3")]
fn outcome_z3(formula: &CnfFormula) -> &'static str {
    let vars = (0..formula.variable_count())
        .map(|index| Bool::new_const(format!("v{index}")))
        .collect::<Vec<_>>();
    let solver = Solver::new();
    let mut params = Params::new();
    params.set_u32("random_seed", 0);
    solver.set_params(&params);
    for clause in formula.clauses() {
        let lits = clause
            .lits()
            .iter()
            .map(|lit| {
                let atom = vars[lit.var().index()].clone();
                if lit.is_negated() { atom.not() } else { atom }
            })
            .collect::<Vec<_>>();
        solver.assert(Bool::or(&lits));
    }
    match solver.check() {
        Z3SatResult::Sat => "sat",
        Z3SatResult::Unsat => "unsat",
        Z3SatResult::Unknown => "unknown",
    }
}

fn outcome_external(binary: &Path, cnf: &Path) -> Result<&'static str, String> {
    let status = Command::new(binary)
        .arg(cnf)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .map_err(|error| format!("run {}: {error}", binary.display()))?;
    match status.code() {
        Some(10) => Ok("sat"),
        Some(20) => Ok("unsat"),
        Some(code) => Err(format!("{} returned exit code {code}", binary.display())),
        None => Err(format!("{} terminated by signal", binary.display())),
    }
}

fn timed<F>(mut solve: F, repetitions: usize) -> Result<(String, Vec<u64>), String>
where
    F: FnMut() -> Result<&'static str, String>,
{
    let mut expected = None;
    let mut nanos = Vec::with_capacity(repetitions);
    for _ in 0..repetitions {
        let started = Instant::now();
        let outcome = solve()?;
        nanos.push(u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX));
        if expected
            .replace(outcome)
            .is_some_and(|prior| prior != outcome)
        {
            return Err("one core changed verdict across repetitions".to_string());
        }
    }
    Ok((expected.unwrap_or("not-run").to_string(), nanos))
}

fn main() -> Result<(), String> {
    let mut args = std::env::args_os().skip(1);
    let input = PathBuf::from(
        args.next()
            .ok_or("usage: cnf_core_bench DIR OUT.json [N] [KISSAT]")?,
    );
    let output = PathBuf::from(
        args.next()
            .ok_or("usage: cnf_core_bench DIR OUT.json [N] [KISSAT]")?,
    );
    let repetitions = args
        .next()
        .map(|value| value.to_string_lossy().parse::<usize>())
        .transpose()
        .map_err(|error| format!("invalid repetitions: {error}"))?
        .unwrap_or(5);
    if repetitions == 0 {
        return Err("repetitions must be nonzero".to_string());
    }
    let external = args.next().map(PathBuf::from);
    if args.next().is_some() {
        return Err("too many arguments".to_string());
    }

    let mut paths = fs::read_dir(&input)
        .map_err(|error| format!("read {}: {error}", input.display()))?
        .map(|entry| entry.map(|entry| entry.path()))
        .collect::<Result<Vec<_>, _>>()
        .map_err(|error| format!("read {}: {error}", input.display()))?;
    paths.retain(|path| path.extension().is_some_and(|extension| extension == "cnf"));
    paths.sort();
    if paths.is_empty() {
        return Err(format!("no CNF files in {}", input.display()));
    }

    let mut rows = Vec::with_capacity(paths.len());
    for path in paths {
        let bytes = fs::read(&path).map_err(|error| format!("read {}: {error}", path.display()))?;
        let text = std::str::from_utf8(&bytes)
            .map_err(|error| format!("{} is not UTF-8: {error}", path.display()))?;
        let formula = parse_dimacs(text).map_err(|error| format!("{}: {error}", path.display()))?;
        let (batsat_outcome, batsat_nanos) = timed(|| outcome_batsat(&formula), repetitions)?;
        let (proof_outcome, proof_nanos) =
            timed(|| Ok::<_, String>(outcome_proof(&formula)), repetitions)?;
        let (proof_rechecked_outcome, proof_rechecked_nanos) =
            timed(|| outcome_proof_rechecked(&formula), repetitions)?;
        #[cfg(feature = "z3")]
        let (z3_outcome, z3_nanos) = timed(|| Ok::<_, String>(outcome_z3(&formula)), repetitions)?;
        let external_result = external
            .as_ref()
            .map(|binary| timed(|| outcome_external(binary, &path), repetitions))
            .transpose()?;
        let mut row = json!({
            "path": path,
            "sha256": sha256_hex(&bytes),
            "variables": formula.variable_count(),
            "clauses": formula.clauses().len(),
            "batsat": {"outcome": batsat_outcome, "nanos": batsat_nanos},
            "proof_core": {"outcome": proof_outcome, "nanos": proof_nanos},
            "proof_core_rechecked": {
                "outcome": proof_rechecked_outcome,
                "nanos": proof_rechecked_nanos
            },
        });
        #[cfg(feature = "z3")]
        {
            row["z3"] = json!({"outcome": z3_outcome, "nanos": z3_nanos});
        }
        if let Some((outcome, nanos)) = external_result {
            row["external"] = json!({"outcome": outcome, "nanos": nanos});
        }
        rows.push(row);
    }

    let report: Value = json!({
        "schema": "axeyum-identical-cnf-core-benchmark-v1",
        "input": input,
        "repetitions": repetitions,
        "external_binary": external,
        "z3_enabled": cfg!(feature = "z3"),
        "instances": rows,
    });
    fs::write(
        &output,
        serde_json::to_vec_pretty(&report).map_err(|error| error.to_string())?,
    )
    .map_err(|error| format!("write {}: {error}", output.display()))
}
