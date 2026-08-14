//! agent-h H3: emit an externally checkable Lean certificate of a **refutation**.
//!
//! DIMACS -> DRAT -> LRAT -> Alethe -> `reconstruct_resolution_proof_compact`
//! -> `Kernel::render_lean_module`, written to a file that a real `lean` binary
//! can check. Also prints the hypothesis-axiom footprint audit, so the claim
//! "`False` from exactly these clauses of this CNF" is checkable and not merely
//! asserted.

use std::collections::BTreeSet;
use std::time::Instant;

use axeyum_cnf::{
    CnfFormula, DratStep, ProofSolveOutcome, elaborate_drat_to_lrat_backward, lrat_to_alethe,
    parse_dimacs, solve_with_drat_proof,
};
use axeyum_solver::{
    ReconstructCtx, declared_assumption_clauses, reconstruct_resolution_proof_compact,
};

fn vm_hwm_kb() -> u64 {
    std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|s| {
            s.lines()
                .find(|l| l.starts_with("VmHWM:"))
                .and_then(|l| l.split_whitespace().nth(1).and_then(|v| v.parse().ok()))
        })
        .unwrap_or(0)
}

fn formula_clause_keys(formula: &CnfFormula) -> BTreeSet<String> {
    formula
        .clauses()
        .iter()
        .map(|clause| {
            let mut lits: Vec<String> = clause
                .lits()
                .iter()
                .map(|lit| {
                    format!(
                        "{}v{}",
                        if lit.is_negated() { '-' } else { '+' },
                        lit.var().index()
                    )
                })
                .collect();
            lits.sort();
            lits.dedup();
            lits.join(",")
        })
        .collect()
}

fn main() {
    let mut args = std::env::args().skip(1);
    let path = args
        .next()
        .expect("usage: reconstruct_lean_certificate <cnf> <out.lean>");
    let out = args
        .next()
        .expect("usage: reconstruct_lean_certificate <cnf> <out.lean>");

    let text = std::fs::read_to_string(&path).expect("read cnf");
    let formula = parse_dimacs(&text).expect("parse dimacs");
    let source_clauses = formula_clause_keys(&formula);

    let drat: Vec<DratStep> = match solve_with_drat_proof(&formula) {
        ProofSolveOutcome::Unsat(p) => p,
        other => {
            println!("{path}\tsolve\tNOT-UNSAT\t{other:?}");
            return;
        }
    };
    let drat_steps = drat.len();
    let lrat = elaborate_drat_to_lrat_backward(&formula, &drat).expect("lrat elaboration");
    let hint_total: usize = lrat
        .iter()
        .map(|s| match s {
            axeyum_cnf::LratStep::Add { hints, .. } => hints.len(),
            axeyum_cnf::LratStep::Delete { .. } => 0,
        })
        .sum();
    let commands = lrat_to_alethe(&formula, &lrat);
    drop(drat);
    drop(lrat);

    let mut ctx = ReconstructCtx::new();
    let start = Instant::now();
    let proof = match reconstruct_resolution_proof_compact(&mut ctx, &commands) {
        Ok(p) => p,
        Err(e) => {
            println!("{path}\treconstruct\tERROR\t{e}");
            return;
        }
    };
    let recon_s = start.elapsed().as_secs_f64();

    let footprint: BTreeSet<String> = declared_assumption_clauses(&ctx).into_iter().collect();
    let alien = footprint
        .iter()
        .filter(|k| !source_clauses.contains(*k))
        .count();

    let false_ = {
        let n = ctx.prelude().false_;
        ctx.kernel_mut().const_(n, vec![])
    };
    // Render `False` and `Or` as real Lean `inductive` commands, so official
    // Lean regenerates their constructors and recursors *with* the iota rules,
    // instead of being handed `False.rec`/`Or.rec` as axioms. This is the
    // difference between Lean checking the elimination and Lean being told it.
    let inductives = vec![ctx.prelude().false_, ctx.prelude().or];
    let render_start = Instant::now();
    // Stream to disk: the module is never materialised as one `String`.
    let file = std::fs::File::create(&out).expect("create lean module");
    let mut writer = std::io::BufWriter::new(file);
    ctx.kernel()
        .write_lean_module_compact_with_inductives(
            &mut writer,
            "axeyum_refutation",
            false_,
            proof,
            &inductives,
        )
        .expect("stream lean module");
    std::io::Write::flush(&mut writer).expect("flush lean module");
    drop(writer);
    let render_s = render_start.elapsed().as_secs_f64();
    let bytes = std::fs::metadata(&out).map_or(0, |m| m.len());

    println!("{path}\tdrat_steps\t{drat_steps}\thints\t{hint_total}");
    println!(
        "{path}\treconstruct\tok\ts\t{recon_s:.3}\trender_s\t{render_s:.3}\tlean_bytes\t{bytes}\thwm_kb\t{}",
        vm_hwm_kb()
    );
    println!(
        "{path}\taudit\tassumption_axioms\t{}\tsource_clauses\t{}\talien\t{alien}",
        footprint.len(),
        source_clauses.len()
    );
    let mut role_counts: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();
    for role in ctx.declared_axiom_roles() {
        *role_counts.entry(role).or_default() += 1;
    }
    println!("{path}\taxiom_roles\t{role_counts:?}");
    println!("{path}\tout\t{out}");
}
