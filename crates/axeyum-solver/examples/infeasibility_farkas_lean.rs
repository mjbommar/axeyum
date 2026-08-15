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
//! WHAT THIS MEASURES, and why it still prints two Lean results even though
//! they now agree. The top-level `prove_unsat_to_lean_module` and the
//! arithmetic reconstructor `reconstruct_lra_proof` used NOT to produce the same
//! thing for this query, and the difference was the entire honesty of the claim:
//!
//! - **Until 2026-08-15** `prove_unsat_to_lean_module` routed a pure-Real
//!   conjunctive `unsat` through `ProofFragment::LraDpll`, whose Lean module is a
//!   **structural attestation**: `axiom A : P`, `axiom B : ¬P`,
//!   `theorem _ : False := B A`. It kernel-checks, it is `sorry`-free, and it
//!   contains none of the arithmetic — the refutation is *asserted* in `B`.
//!   Reporting that as "the Farkas proof reached the kernel" would have been
//!   false, and this example is what made it visible.
//! - `reconstruct_lra_proof` builds the real thing: one hypothesis axiom per
//!   core row, the scaled sum assembled with the prelude's ordered-field laws,
//!   and `lt_irrefl` closing it. That is the term whose type-check is worth
//!   something.
//!
//! The `lra-dispatch` lane reordered the classifier so a conjunctive real system
//! whose Farkas reconstruction actually builds reaches `ProofFragment::Lra`
//! first. So the facade line below should now read `Lra` and
//! `carries ordered-field content` for this instance — and the shim detection is
//! KEPT, and kept as TWO independent instruments (a structural scan of the
//! declared axiom names and types, and the module's own self-label), because a
//! detector that is only exercised while it reports the bad case is a detector
//! nobody notices going blind. That is not a hypothetical: the structural scan
//! **was** broken, matched nothing on a real arithmetic module, and the
//! self-label caught it on the first run after the dispatch was fixed.
//! Disagreement between the two is an error in the direction that is impossible
//! by construction, and an error in the other direction whenever the facade
//! routed to `ProofFragment::Lra`.
//!
//! It also counts the axioms the resulting module actually rests on, because the
//! `Real` prelude is 30 asserted ordered-field laws plus one hypothesis axiom
//! per row — this route is not, and cannot presently be, axiom-free.
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
    LeanModuleContent, LraReconstructCtx, ProofFragment, SolverConfig, lra_farkas_certificate,
    prove_unsat_to_lean_module, prove_unsat_to_lean_theory_module, reconstruct_lra_proof,
    unsat_core,
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
    let mut dump_axioms = false;
    // `--expect-axioms N` exists because the fact ledger's whole promise is that
    // a status is worth what its checker returns, and this checker returned 0 no
    // matter what the footprint said. `F:schedule-critical-chain-infeasible`
    // recorded 30 axioms while the code produced 26 -- four prelude laws had
    // since become PROVED rather than asserted, which is a real shrink of the
    // trusted surface and exactly the kind of change a ledger exists to notice.
    // It went unnoticed because nothing compared the two. Drift in the safe
    // direction is still drift: the same silence would hide a footprint that
    // GREW.
    let mut expect_axioms: Option<usize> = None;
    let mut axioms_checked = false;
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--require-kernel" => require_kernel = true,
            "--dump-modules" => dump = true,
            "--dump-axioms" => dump_axioms = true,
            "--expect-axioms" => {
                let raw = args
                    .next()
                    .ok_or("`--expect-axioms` needs a count, e.g. `--expect-axioms 26`")?;
                expect_axioms = Some(
                    raw.parse()
                        .map_err(|_| format!("`--expect-axioms` wants a number, got `{raw}`"))?,
                );
            }
            other if other.starts_with("--") => return Err(format!("unknown flag `{other}`")),
            other => path = Some(other.to_owned()),
        }
    }
    let path = path.ok_or(
        "usage: infeasibility_farkas_lean <file.smt2> [--require-kernel] [--dump-modules] \
         [--dump-axioms] [--expect-axioms N]",
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
    // The structural attestation is recognizable by what it does NOT contain:
    // no HYPOTHESIS axiom whose declared type is an ordered-field relation.
    // Classify on the declared NAME and its declared TYPE, never on a substring
    // of the whole module, because the prelude's own declarations mention `le`
    // no matter what.
    //
    // This predicate was WRONG until 2026-08-15 and nothing could tell: it
    // looked for a line starting `axiom hyp`, but the reconstructor mints
    // `axeyum.reconstruct.lra.hyp._N`, so it returned `false` for a genuine
    // arithmetic module too. It gave the right answer for exactly as long as the
    // facade emitted an attestation, and the moment the dispatch was fixed it
    // reported `STRUCTURAL ATTESTATION` for a module full of `Real.le`. The
    // second instrument below caught it on its first run. A detector exercised
    // only while it reports the bad case is one nobody notices going blind.
    let arith_content = module.lines().any(|line| {
        let Some(rest) = line.trim_start().strip_prefix("axiom ") else {
            return false;
        };
        let Some((name, ty)) = rest.split_once(" : ") else {
            return false;
        };
        name.contains(".lra.hyp._") && (ty.contains("Real.le") || ty.contains("Real.lt"))
    });
    // Second, independent instrument: the module's own self-label. A structural
    // attestation carries `STRUCTURAL_ATTESTATION_MARKER` in its header, which
    // is what a caller holding only the source can read.
    let labelled = LeanModuleContent::of_module_source(&module);
    println!("facade fragment     {fragment:?}");
    println!("facade module       {} line(s)", module.lines().count());
    println!(
        "facade content      {}",
        if arith_content {
            "carries ordered-field content"
        } else {
            "STRUCTURAL ATTESTATION -- the arithmetic is asserted, not reconstructed"
        }
    );
    println!("facade self-label   {labelled}");
    // Two instruments, one subject. ONE direction is impossible by
    // construction: a structural attestation's only axioms are an opaque `Prop`
    // and its negation, so it can never carry an `…lra.hyp._N : Real.le …`.
    // That disagreement is always an error.
    if arith_content && labelled == LeanModuleContent::StructuralAttestation {
        return Err(
            "a module self-labelled as a structural attestation declares an LRA \
             hypothesis axiom; one of the two detectors is lying"
                .to_owned(),
        );
    }
    // The other direction is weaker: the structural scan only knows the LRA
    // reconstructor's naming, so a theory reconstruction of some OTHER fragment
    // reads as "no arithmetic" here, and that is the scan's coverage limit
    // rather than a defect. It IS an error when the facade routed to `Lra`,
    // which is exactly the case this example exists to pin.
    if !arith_content && labelled == LeanModuleContent::TheoryReconstruction {
        if fragment == ProofFragment::Lra {
            return Err(
                "the facade routed to ProofFragment::Lra but the module declares no \
                 `lra.hyp._N` ordered-field hypothesis axiom"
                    .to_owned(),
            );
        }
        println!(
            "facade note         the structural scan only recognizes the LRA reconstructor's \
             axiom names; {fragment:?} is outside it"
        );
    }
    // The strict front door: it returns a module only when there is reasoning in
    // it, and a typed `NoTheoryContent` decline otherwise.
    match prove_unsat_to_lean_theory_module(&mut script.arena, &core_terms) {
        Ok((strict_fragment, _)) => {
            println!("strict facade       ACCEPTED as {strict_fragment:?}");
        }
        Err(error) => {
            println!("strict facade       DECLINED: {error}");
            if require_kernel {
                return Err(format!(
                    "--require-kernel was given but the strict facade declined: {error}"
                ));
            }
        }
    }
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
            if dump_axioms {
                // The fact ledger records this footprint by NAME, and until this
                // flag existed nothing printed the names -- so the only way to
                // fill in `axiom_footprint` was to read the module by eye, and
                // the only way to check it was to trust that reading. Sorted, so
                // a diff against the ledger is a diff.
                let mut sorted = axiom_names.clone();
                sorted.sort_unstable();
                println!("--- axiom footprint ({}) ---", sorted.len());
                for name in &sorted {
                    println!("{name}");
                }
                println!("--- end ---");
            }
            if let Some(want) = expect_axioms
                && axiom_names.len() != want
            {
                return Err(format!(
                    "axiom footprint drifted: the module asserts {} axiom(s) \
                     ({prelude} prelude + {variables} variable + {hypotheses} hypothesis) \
                     but --expect-axioms said {want}. If this shrank, the trusted surface \
                     got smaller and the ledger should be updated to match \
                     (`--dump-axioms` prints the names). If it GREW, something is now \
                     asserted that was proved before, and that is a regression.",
                    axiom_names.len()
                ));
            }
            axioms_checked = true;
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
    // A check that never ran is not a check that passed. If the kernel route
    // stops early, every line above it still prints and the process still exits
    // 0 -- which is precisely the "green-looking gate that examined nothing"
    // failure this repository has shipped more than once. So `--expect-axioms`
    // fails when it was never reached, rather than being satisfied by absence.
    if expect_axioms.is_some() && !axioms_checked {
        return Err(
            "--expect-axioms was given but the kernel-lean route never produced a module, \
             so the footprint was never compared. Treating an unreached check as a pass is \
             how a gate ends up asserting nothing."
                .to_owned(),
        );
    }
    Ok(())
}
