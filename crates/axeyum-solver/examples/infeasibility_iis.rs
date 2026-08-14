//! Certified infeasibility for an operations-research model: decide `unsat`,
//! extract the minimized unsat core, and **measure** that the core is
//! irreducible by re-solving every leave-one-out subset.
//!
//! WHY THIS EXISTS. `get-unsat-core` at the SMT-LIB front door is documented as
//! deletion-minimized, and deletion minimization is *supposed* to yield an
//! irreducible subset. It does not always: `axeyum_solver::unsat_core`
//! conservatively KEEPS an assertion whose removal leaves the remainder
//! `unknown` rather than definitively `sat`, because an undecided remainder
//! cannot justify a drop. That is the right call for soundness and it means the
//! returned subset is a core whose minimality is a *hope*, not a result. In
//! scheduling and rostering the minimality is the entire product -- "these 5 of
//! your 102 rows contradict" is an explanation, "these 102 rows contradict" is
//! the input restated -- so this example refuses to report a ratio it has not
//! established.
//!
//! What it runs, per instance, all against the same solver the front door uses:
//!
//! 1. the whole model must decide `unsat`;
//! 2. the front-door `(get-unsat-core)` names must all be real `:named` rows;
//! 3. the core ALONE must re-decide `unsat` (it is genuinely an explanation of
//!    infeasibility, not a superset that happens to contain one);
//! 4. for every member `m` of the core, `core \ {m}` must decide **`sat`** --
//!    the irreducibility measurement. `unknown` here is a FAILURE, not a pass:
//!    an undecided leave-one-out subset leaves open that a smaller core exists,
//!    which is exactly the claim being made;
//! 5. the instance MINUS the core must decide `sat` -- the "buried" property.
//!    Without it a core can be small only because the model is small, and the
//!    demonstration would be empty.
//!
//! `--expect-rows` / `--expect-core` pin the measured numbers so that a
//! regression in core minimization fails this rather than silently printing a
//! worse ratio. A checker that reports whatever it found pins nothing.
//!
//! ```sh
//! cargo run --release -q -p axeyum-solver --features full --example infeasibility_iis -- \
//!     artifacts/instances/infeasibility/roster-icu-night.smt2 --expect-rows 102 --expect-core 5
//! ```

use std::collections::BTreeMap;
use std::process::ExitCode;
use std::time::Duration;

use axeyum_ir::TermId;
use axeyum_smtlib::parse_script;
use axeyum_solver::{
    CheckResult, SolverConfig, check_model, produce_evidence, solve, solve_smtlib_unsat_core,
    unsat_core,
};

/// One decided subset, reduced to the verdict word the checks compare on.
fn verdict(result: &CheckResult) -> &'static str {
    match result {
        CheckResult::Sat(_) => "sat",
        CheckResult::Unsat => "unsat",
        CheckResult::Unknown(_) => "unknown",
    }
}

struct Args {
    path: String,
    expect_rows: Option<usize>,
    expect_core: Option<usize>,
    timeout_secs: u64,
}

fn parse_args() -> Result<Args, String> {
    let mut path = None;
    let mut expect_rows = None;
    let mut expect_core = None;
    let mut timeout_secs = 120;
    let mut argv = std::env::args().skip(1);
    while let Some(arg) = argv.next() {
        match arg.as_str() {
            "--expect-rows" => {
                expect_rows = Some(next_usize(&mut argv, "--expect-rows")?);
            }
            "--expect-core" => {
                expect_core = Some(next_usize(&mut argv, "--expect-core")?);
            }
            "--timeout" => {
                timeout_secs = next_usize(&mut argv, "--timeout")? as u64;
            }
            other if other.starts_with("--") => {
                return Err(format!("unknown flag `{other}`"));
            }
            other => path = Some(other.to_owned()),
        }
    }
    Ok(Args {
        path: path.ok_or("usage: infeasibility_iis <file.smt2> [--expect-rows N] [--expect-core N] [--timeout S]")?,
        expect_rows,
        expect_core,
        timeout_secs,
    })
}

fn next_usize(argv: &mut impl Iterator<Item = String>, flag: &str) -> Result<usize, String> {
    argv.next()
        .ok_or_else(|| format!("{flag} needs a value"))?
        .parse()
        .map_err(|_| format!("{flag} needs a non-negative integer"))
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(message) => {
            eprintln!("infeasibility_iis: {message}");
            ExitCode::FAILURE
        }
    }
}

// Kept as one function on purpose: the five checks are a single argument read
// top to bottom, and each one's precondition is the previous one's result.
// Splitting them would hand every step the whole state anyway.
#[allow(clippy::too_many_lines)]
fn run() -> Result<(), String> {
    let args = parse_args()?;
    let text = std::fs::read_to_string(&args.path)
        .map_err(|error| format!("cannot read `{}`: {error}", args.path))?;
    let config = SolverConfig::new().with_timeout(Duration::from_secs(args.timeout_secs));

    // The parsed script is the authority on what a "row" is: the `:named` labels
    // parallel to the assertion list. Counting `:named` in the text would count
    // whatever the text happens to contain, including a commented-out row.
    let mut script = parse_script(&text).map_err(|error| format!("parse: {error}"))?;
    let rows = script.assertions.len();
    let named: BTreeMap<String, usize> = script
        .assertion_names
        .iter()
        .enumerate()
        .filter_map(|(index, name)| name.clone().map(|name| (name, index)))
        .collect();
    if named.len() != rows {
        return Err(format!(
            "{rows} assertion(s) but only {} are `:named`; every row must be \
             labelled or a core cannot name it",
            named.len()
        ));
    }
    println!("instance            {}", args.path);
    println!("rows                {rows}");

    // 1. The whole model is infeasible.
    let assertions: Vec<TermId> = script.assertions.clone();
    let whole = solve(&mut script.arena, &assertions, &config)
        .map_err(|error| format!("deciding the whole model: {error}"))?;
    println!("whole model         {}", verdict(&whole));
    if !matches!(whole, CheckResult::Unsat) {
        return Err(format!(
            "expected the instance to be unsat, got {}",
            verdict(&whole)
        ));
    }

    // 2. The front door's core, by name. This is the artifact a consumer of
    //    `(get-unsat-core)` receives, so it is what gets audited -- not a core
    //    re-derived internally for the occasion.
    let core_names = solve_smtlib_unsat_core(&text, &config)
        .map_err(|error| format!("get-unsat-core: {error}"))?
        .ok_or("get-unsat-core returned no core for an unsat instance")?;
    let mut core_indices = Vec::with_capacity(core_names.len());
    for name in &core_names {
        let index = *named
            .get(name)
            .ok_or_else(|| format!("core names `{name}`, which is not a `:named` row"))?;
        core_indices.push(index);
    }
    core_indices.sort_unstable();
    core_indices.dedup();
    if core_indices.len() != core_names.len() {
        return Err("the core repeats a row".to_owned());
    }
    let core_size = core_indices.len();
    // Row counts are in the hundreds; the cast is exact far beyond any model
    // an O(n)-solve deletion loop can reach.
    #[allow(clippy::cast_precision_loss)]
    let ratio = 100.0 * core_size as f64 / rows as f64;
    println!("core                {core_size} of {rows} rows ({ratio:.1}%)");
    let mut sorted_names: Vec<&String> = core_names.iter().collect();
    sorted_names.sort();
    for name in &sorted_names {
        println!("  core row          {name}");
    }

    // Cross-check the front door against the term-level minimizer: the same
    // instance through `axeyum_solver::unsat_core` on parsed terms must produce
    // the same row set. These share the deletion loop, so this is ONE check of
    // the plumbing between them, not an independent re-derivation of the core.
    let direct = unsat_core(&mut script.arena, &assertions, &config)
        .map_err(|error| format!("term-level unsat_core: {error}"))?
        .ok_or("term-level unsat_core returned no core")?;
    let mut direct_sorted = direct.clone();
    direct_sorted.sort_unstable();
    if direct_sorted != core_indices {
        return Err(format!(
            "front-door core {core_indices:?} disagrees with term-level core {direct_sorted:?}"
        ));
    }

    let subset = |indices: &[usize]| -> Vec<TermId> {
        indices.iter().map(|&index| assertions[index]).collect()
    };

    // 3. The core alone is unsatisfiable.
    let core_terms = subset(&core_indices);
    let core_alone = solve(&mut script.arena, &core_terms, &config)
        .map_err(|error| format!("re-deciding the core: {error}"))?;
    println!("core alone          {}", verdict(&core_alone));
    if !matches!(core_alone, CheckResult::Unsat) {
        return Err(format!(
            "the core alone decided {}, so it does not explain the infeasibility",
            verdict(&core_alone)
        ));
    }

    // What the core's `unsat` actually rests on, MEASURED rather than named in
    // prose: the evidence variant the dispatcher produced, whether this run
    // re-derived it, and the trust ledger for the reductions it used. A fact's
    // `axiom_footprint` is only honest if it comes from here.
    let report = produce_evidence(&mut script.arena, &core_terms, &config)
        .map_err(|error| format!("produce_evidence for the core: {error}"))?;
    let variant = format!("{:?}", report.evidence);
    let variant = variant
        .split(['(', ' ', '{'])
        .next()
        .unwrap_or("?")
        .to_owned();
    let outcome = report
        .evidence
        .check_outcome(&script.arena, &core_terms)
        .map_err(|error| format!("re-checking the core's evidence: {error}"))?;
    println!(
        "core evidence       {variant} (re-check: {})",
        outcome.label()
    );
    if report.trusted_steps.is_empty() {
        println!("core trust steps    none recorded");
    } else {
        for step in &report.trusted_steps {
            println!(
                "  trust step        {} ({})",
                step.id.label(),
                if step.certified {
                    "certified this run"
                } else {
                    "TRUSTED, not certified"
                }
            );
        }
    }

    // 4. IRREDUCIBILITY, measured. Every leave-one-out subset must be `sat`,
    //    and -- because a bare `sat` is the solver's word for it -- every model
    //    is REPLAYED against the very terms it claims to satisfy, by the IR
    //    evaluator. That replay shares nothing with the decision procedure, so
    //    the satisfiable half of "irreducible" does not rest on the solver at
    //    all: it rests on 5 (or 14) concrete rosters/load plans/schedules an
    //    evaluator confirms.
    let mut irreducible = true;
    for (position, &dropped) in core_indices.iter().enumerate() {
        let remainder: Vec<usize> = core_indices
            .iter()
            .copied()
            .filter(|&index| index != dropped)
            .collect();
        let name = script.assertion_names[dropped]
            .clone()
            .unwrap_or_else(|| format!("assertion #{dropped}"));
        // A one-row core leaves an empty remainder, which is vacuously
        // satisfiable; no solver call is needed or meaningful.
        let word = if remainder.is_empty() {
            "sat (empty remainder, vacuous)".to_owned()
        } else {
            let terms = subset(&remainder);
            let result = solve(&mut script.arena, &terms, &config)
                .map_err(|error| format!("leave-one-out on `{name}`: {error}"))?;
            match &result {
                CheckResult::Sat(model) => {
                    let replayed = check_model(&script.arena, &terms, model)
                        .map_err(|error| format!("replaying the model for `{name}`: {error}"))?;
                    if replayed {
                        "sat (model replayed)".to_owned()
                    } else {
                        // The solver said `sat` and the evaluator disagreed.
                        // That is a soundness alarm, not a weaker pass.
                        return Err(format!(
                            "the model for `core \\ {{{name}}}` failed evaluator replay"
                        ));
                    }
                }
                other => verdict(other).to_owned(),
            }
        };
        println!(
            "  drop {name:<26} -> {word}   [{}/{core_size}]",
            position + 1
        );
        if !word.starts_with("sat") {
            irreducible = false;
        }
    }
    println!(
        "irreducible         {}",
        if irreducible { "yes" } else { "NO" }
    );
    if !irreducible {
        return Err(
            "a leave-one-out subset did not decide `sat`, so the core is not \
             measured-irreducible: a smaller explanation may exist"
                .to_owned(),
        );
    }

    // 5. The "buried" property: everything OUTSIDE the core is jointly
    //    satisfiable, so the core is the whole of the infeasibility and not one
    //    contradiction among several.
    let outside: Vec<usize> = (0..rows)
        .filter(|index| !core_indices.contains(index))
        .collect();
    let outside_terms = subset(&outside);
    let rest = solve(&mut script.arena, &outside_terms, &config)
        .map_err(|error| format!("deciding the instance minus the core: {error}"))?;
    let CheckResult::Sat(rest_model) = &rest else {
        return Err(format!(
            "the instance minus its core decided {}; the contradiction is not \
             confined to the reported core",
            verdict(&rest)
        ));
    };
    if !check_model(&script.arena, &outside_terms, rest_model)
        .map_err(|error| format!("replaying the instance-minus-core model: {error}"))?
    {
        return Err("the instance-minus-core model failed evaluator replay".to_owned());
    }
    println!("instance minus core sat (model replayed)");

    // Pinned expectations, so a regression in minimization fails the gate rather
    // than quietly reporting a worse ratio.
    if let Some(expected) = args.expect_rows
        && expected != rows
    {
        return Err(format!("expected {expected} rows, measured {rows}"));
    }
    if let Some(expected) = args.expect_core
        && expected != core_size
    {
        return Err(format!(
            "expected a core of {expected} rows, measured {core_size}"
        ));
    }

    println!("VERIFIED            irreducible core of {core_size} in {rows} rows ({ratio:.1}%)");
    Ok(())
}
