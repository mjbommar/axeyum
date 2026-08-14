//! How far a certified-infeasibility explanation travels toward an independent
//! kernel: extract the minimized core of an LRA planning model, produce its
//! **Farkas certificate**, and try to reconstruct that certificate as a Lean
//! kernel proof term of `False`.
//!
//! WHY THE CORE FIRST. The Farkas multipliers over the whole 60-row model would
//! be 60 numbers, 55 of them zero, and the reader would have to find the
//! explanation inside the certificate. Reconstructing the CORE means the proof
//! term and the explanation are the same object: five rows, five multipliers,
//! one contradiction.
//!
//! WHAT THIS MEASURES, and why it prints two different Lean results. The top
//! level `prove_unsat_to_lean_module` and the arithmetic reconstructor
//! `reconstruct_lra_proof` do NOT produce the same thing for this query, and the
//! difference is the entire honesty of the claim:
//!
//! - `prove_unsat_to_lean_module` routes a pure-Real conjunctive `unsat`
//!   through `ProofFragment::LraDpll`, whose Lean module is a **structural
//!   shim**: `axiom A : P`, `axiom B : ¬P`, `theorem _ : False := B A`. It
//!   kernel-checks, it is `sorry`-free, and it contains none of the arithmetic
//!   — the refutation is *asserted* in `B`. Reporting that as "the Farkas proof
//!   reached the kernel" would be false.
//! - `reconstruct_lra_proof` builds the real thing: one hypothesis axiom per
//!   core row, the scaled sum assembled with the prelude's ordered-field laws,
//!   and `lt_irrefl` closing it. That is the term whose type-check is worth
//!   something.
//!
//! So this prints the fragment the facade chose, the shim-detection verdict,
//! and the direct reconstruction separately. It also counts the axioms the
//! resulting module actually rests on, because the `Real` prelude is 30 asserted
//! ordered-field laws plus one hypothesis axiom per row — this route is not, and
//! cannot presently be, axiom-free.
//!
//! ```sh
//! cargo run --release -q -p axeyum-solver --features full --example infeasibility_farkas_lean -- \
//!     artifacts/instances/infeasibility/schedule-deadline.smt2 --require-kernel
//! ```

use std::process::ExitCode;
use std::time::Duration;

use axeyum_ir::TermId;
use axeyum_smtlib::parse_script;
use axeyum_solver::{
    LraReconstructCtx, SolverConfig, lra_farkas_certificate, prove_unsat_to_lean_module,
    reconstruct_lra_proof, unsat_core,
};

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(message) => {
            eprintln!("infeasibility_farkas_lean: {message}");
            ExitCode::FAILURE
        }
    }
}

/// A reported stop is a result, not a failure — unless the caller pinned the
/// route with `--require-kernel`, which is how a fact's checker command asserts
/// that a route it already measured is still there.
fn stop(require_kernel: bool, detail: &str) -> Result<(), String> {
    if require_kernel {
        Err(format!(
            "--require-kernel was given but the route stopped: {detail}"
        ))
    } else {
        Ok(())
    }
}

// One function on purpose: this is a single measurement walked end to end --
// core, certificate, facade module, direct reconstruction -- and each stage
// consumes the last stage's output.
#[allow(clippy::too_many_lines)]
fn run() -> Result<(), String> {
    let mut path = None;
    let mut require_kernel = false;
    let mut dump = false;
    for arg in std::env::args().skip(1) {
        match arg.as_str() {
            "--require-kernel" => require_kernel = true,
            "--dump-modules" => dump = true,
            other if other.starts_with("--") => return Err(format!("unknown flag `{other}`")),
            other => path = Some(other.to_owned()),
        }
    }
    let path = path.ok_or(
        "usage: infeasibility_farkas_lean <file.smt2> [--require-kernel] [--dump-modules]",
    )?;
    let text =
        std::fs::read_to_string(&path).map_err(|error| format!("cannot read `{path}`: {error}"))?;
    let config = SolverConfig::new().with_timeout(Duration::from_secs(120));
    let mut script = parse_script(&text).map_err(|error| format!("parse: {error}"))?;
    let assertions: Vec<TermId> = script.assertions.clone();
    println!("instance            {path}");
    println!("rows                {}", assertions.len());

    let core = unsat_core(&mut script.arena, &assertions, &config)
        .map_err(|error| format!("unsat_core: {error}"))?
        .ok_or("no core: the instance is not unsat")?;
    let row_name = |index: usize| -> String {
        script.assertion_names[index]
            .clone()
            .unwrap_or_else(|| format!("assertion #{index}"))
    };
    let core_terms: Vec<TermId> = core.iter().map(|&index| assertions[index]).collect();
    println!("core                {} rows", core.len());

    // --- the Farkas certificate for the core -------------------------------
    //
    // This is where the two integer instances stop, and the stop is reported
    // rather than raised: `lra_farkas_certificate` decides linear REAL
    // arithmetic, so a roster or a load plan -- integer decision variables,
    // conjunctive-linear only by accident of shape -- is outside it by
    // construction, not by a missing case. The core is still an irreducible,
    // measured explanation there; it just has no Farkas route to a kernel.
    let certificate = match lra_farkas_certificate(&script.arena, &core_terms) {
        Ok(Some(certificate)) => certificate,
        Ok(None) => {
            println!("farkas route        STOPPED: no certificate (unsat is not LRA-refutable)");
            return stop(require_kernel, "no Farkas certificate for the core");
        }
        Err(error) => {
            println!("farkas route        STOPPED: {error}");
            return stop(require_kernel, &format!("lra_farkas_certificate: {error}"));
        }
    };
    println!("farkas atoms        {}", certificate.atoms.len());
    for (atom_index, &origin) in certificate.origins.iter().enumerate() {
        // `origins` indexes the slice we passed in, i.e. the CORE, so map back
        // through `core` to the original row.
        let name = row_name(core[origin]);
        let multiplier = certificate.multipliers[atom_index];
        println!("  lambda {multiplier:>8}  x  {name}");
    }
    // `verify()` re-derives the refutation from scratch in exact rationals:
    // nonnegative multipliers, at least one positive, every variable cancels,
    // and the surviving constant relation is unsatisfiable. It shares no code
    // with the Fourier-Motzkin elimination that found the multipliers.
    let verified = certificate.verify();
    println!("farkas verify()     {verified}");
    if !verified {
        return Err("the Farkas certificate failed its own from-scratch check".to_owned());
    }

    // --- what the top-level facade produces --------------------------------
    let (fragment, module) = prove_unsat_to_lean_module(&mut script.arena, &core_terms)
        .map_err(|error| format!("prove_unsat_to_lean_module: {error}"))?;
    // The structural shim is recognizable by what it does NOT contain: no
    // ordered-field relation applied to anything. Detected on the declared
    // `axiom`/`theorem` types rather than a substring of the whole module,
    // because the prelude's own declarations mention `le` no matter what.
    let arith_content = module.lines().any(|line| {
        let line = line.trim_start();
        (line.starts_with("axiom hyp") || line.starts_with("theorem "))
            && (line.contains(" le ") || line.contains(" lt "))
    });
    println!("facade fragment     {fragment:?}");
    println!("facade module       {} line(s)", module.lines().count());
    println!(
        "facade content      {}",
        if arith_content {
            "carries ordered-field content"
        } else {
            "STRUCTURAL SHIM -- the arithmetic is asserted, not reconstructed"
        }
    );
    if dump {
        println!("--- facade module ---\n{module}\n--- end ---");
    }

    // --- the direct arithmetic reconstruction ------------------------------
    let mut ctx = LraReconstructCtx::new();
    let direct = reconstruct_lra_proof(&mut ctx, &script.arena, &core_terms);
    match direct {
        Ok(proof) => {
            let inferred = ctx
                .kernel_mut()
                .infer(proof)
                .map_err(|error| format!("kernel infer rejected the term: {error:?}"))?;
            let false_ = {
                let name = ctx.arith().logic.false_;
                ctx.kernel_mut().const_(name, vec![])
            };
            if !ctx.kernel_mut().def_eq(inferred, false_) {
                return Err("the reconstructed LRA term did not infer to False".to_owned());
            }
            let rendered = ctx.kernel().render_lean_module("infeasible", false_, proof);
            // Classify on the DECLARED NAME -- the token after `axiom ` -- and
            // never on the line. A hypothesis axiom's *type* mentions every
            // variable it constrains, so a substring test over the whole line
            // counts each hypothesis again as a variable (it reported 9
            // variables for a 4-variable chain before this was fixed).
            let axiom_names: Vec<&str> = rendered
                .lines()
                .map(str::trim_start)
                .filter_map(|line| line.strip_prefix("axiom "))
                .filter_map(|rest| rest.split_whitespace().next())
                .collect();
            // The reconstructor mints one `…lra.hyp._N` axiom per constraint it
            // uses and one `…lra.x._N` per variable; everything else asserted is
            // the ordered-field prelude.
            let hypotheses = axiom_names
                .iter()
                .filter(|name| name.contains(".lra.hyp._"))
                .count();
            let variables = axiom_names
                .iter()
                .filter(|name| name.contains(".lra.x._"))
                .count();
            let prelude = axiom_names.len() - hypotheses - variables;
            // The `theorem … := <term>` body, which is where the size lives: the
            // prelude has no numerals, so an integer constant `k` reconstructs as
            // a `k`-fold `Real.add Real.one …` chain and every cancellation is an
            // explicit `Eq`-rewrite.
            let term_bytes = rendered
                .lines()
                .map(|line| {
                    if line.trim_start().starts_with("Real.") {
                        line.len()
                    } else {
                        0
                    }
                })
                .max()
                .unwrap_or(0);
            println!("kernel-lean route   REACHED (term infers to False)");
            println!(
                "kernel module       {} line(s), {} bytes",
                rendered.lines().count(),
                rendered.len()
            );
            println!("kernel proof term   {term_bytes} bytes");
            println!(
                "kernel axioms       {} = {prelude} prelude + {variables} variable + {hypotheses} hypothesis",
                axiom_names.len()
            );
            println!("axiom-free          no -- the ordered field and every core row are asserted");
            if hypotheses != core.len() {
                return Err(format!(
                    "the reconstructed term rests on {hypotheses} hypothesis axiom(s) but the \
                     core has {} rows; the proof is not about the reported explanation",
                    core.len()
                ));
            }
            if dump {
                println!("--- kernel module ---\n{rendered}\n--- end ---");
            }
        }
        Err(error) => {
            println!("kernel-lean route   STOPPED: {error:?}");
            if require_kernel {
                return Err(format!(
                    "--require-kernel was given but reconstruct_lra_proof declined: {error:?}"
                ));
            }
        }
    }
    Ok(())
}
