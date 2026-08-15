//! Certified **conjunctive-query containment**: `Q₁ ⊆ Q₂` decided three ways,
//! and reported only with a certificate that has already been replayed.
//!
//! Query containment is the reasoning behind view reuse, redundant-join
//! elimination and answering queries using views: if the optimiser can prove
//! `Q₁ ⊆ Q₂` it may answer `Q₁` from a materialisation of `Q₂`, and if it can
//! prove `Q₁ ≡ Q₂` it may swap one plan for the other outright. Chandra and
//! Merlin (STOC 1977) showed the problem is NP-complete and that its
//! certificate is a **homomorphism** from the containing query into the
//! *frozen* body of the contained one. Finding it is the hard half; checking
//! it is a nested loop.
//!
//! # The three routes, and why three
//!
//! 1. **Backtracking search** over the frozen domain — fast, heuristic,
//!    untrusted. Whatever it returns goes to `check_homomorphism` before it is
//!    believed.
//! 2. **The solver**, on a one-hot Boolean encoding of "a homomorphism
//!    exists". `sat` decodes to a map that goes through the *same* checker;
//!    the model is additionally replayed against the encoding by the IR
//!    evaluator. `unsat` is the containment failing.
//! 3. **Complete evaluation** of both queries over the frozen database, by
//!    enumerating every variable assignment with no pruning at all. This is
//!    what makes a *negative* answer a result rather than a report about a
//!    search that gave up: the frozen database is exhibited as a concrete
//!    counterexample on which the two queries disagree.
//!
//! Routes 1 and 2 must agree with each other and with route 3. A run in which
//! they disagree is a failure, not a tie-break.
//!
//! ```sh
//! cargo run --release -q -p axeyum-bench --example cq_containment_certify -- \
//!     artifacts/instances/dbdesign/reachability-views.cq --expect-checks 6
//! ```

use std::process::ExitCode;
use std::time::Duration;

use axeyum_ir::{TermArena, Value};
use axeyum_scenarios::dbdesign::cq::{
    ContainmentVerdict, Cq, CqProgram, FrozenQuery, check_homomorphism, decide_containment,
    evaluate, freeze, render_frozen,
};
use axeyum_scenarios::dbdesign::encode::{homomorphism_from_model, homomorphism_query};
use axeyum_scenarios::dbdesign::{Expectation, Instance};
use axeyum_smtlib::parse_script;
use axeyum_solver::{CheckResult, SolverConfig, check_model, solve};

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(message) => {
            eprintln!("cq_containment_certify: {message}");
            ExitCode::FAILURE
        }
    }
}

struct Args {
    path: String,
    expect_checks: Option<usize>,
    verify_formal: Option<String>,
    timeout_secs: u64,
    show: bool,
}

fn parse_args() -> Result<Args, String> {
    let mut path = None;
    let mut expect_checks = None;
    let mut verify_formal = None;
    let mut timeout_secs = 120;
    let mut show = false;
    let mut argv = std::env::args().skip(1);
    while let Some(arg) = argv.next() {
        match arg.as_str() {
            "--expect-checks" => expect_checks = Some(next_usize(&mut argv, "--expect-checks")?),
            "--verify-formal" => {
                verify_formal = Some(
                    argv.next()
                        .ok_or("--verify-formal needs a path to an SMT-LIB script")?,
                );
            }
            "--timeout" => timeout_secs = next_usize(&mut argv, "--timeout")? as u64,
            "--show-certificates" => show = true,
            other if other.starts_with("--") => return Err(format!("unknown flag `{other}`")),
            other => path = Some(other.to_owned()),
        }
    }
    Ok(Args {
        path: path.ok_or(
            "usage: cq_containment_certify <file.cq> [--expect-checks N] \
             [--show-certificates] [--verify-formal <file.smt2>] [--timeout SECONDS]",
        )?,
        expect_checks,
        verify_formal,
        timeout_secs,
        show,
    })
}

fn next_usize(argv: &mut impl Iterator<Item = String>, flag: &str) -> Result<usize, String> {
    argv.next()
        .ok_or_else(|| format!("{flag} needs a value"))?
        .parse()
        .map_err(|_| format!("{flag} needs a non-negative integer"))
}

/// Decide "a homomorphism from `source` into `target` exists" through the
/// solver, and — on `sat` — hand the decoded map straight to the independent
/// checker.
fn solver_route(
    source: &Cq,
    target: &FrozenQuery,
    tag: &str,
    config: &SolverConfig,
) -> Result<bool, String> {
    let mut arena = TermArena::new();
    let query = homomorphism_query(&mut arena, source, target, &format!("{tag}_"))
        .map_err(|error| format!("encoding {tag}: {error}"))?;
    let result = solve(&mut arena, &query.assertions, config)
        .map_err(|error| format!("solving {tag}: {error}"))?;
    match result {
        CheckResult::Unsat => Ok(false),
        CheckResult::Unknown(reason) => Err(format!(
            "the solver returned `unknown` ({reason:?}) on {tag}; an undecided route cannot back \
             a containment decision"
        )),
        CheckResult::Sat(model) => {
            if !check_model(&arena, &query.assertions, &model)
                .map_err(|error| format!("replaying the model for {tag}: {error}"))?
            {
                return Err(format!("the model for {tag} failed evaluator replay"));
            }
            let hom = homomorphism_from_model(&query, |symbol| match model.get(symbol) {
                Some(Value::Bool(value)) => Some(value),
                _ => None,
            })
            .ok_or_else(|| format!("the model for {tag} leaves a variable unmapped"))?;
            check_homomorphism(source, target, &hom)
                .map_err(|error| format!("the solver's map is not a homomorphism: {error}"))?;
            Ok(true)
        }
    }
}

/// Verify that the fact ledger's `formal.statement` for this instance really
/// is valid, by dispatching the committed script that asserts its **negation**
/// and requiring `unsat`.
///
/// This closes a loop the ledger otherwise leaves open. A fact's
/// `formal.statement` is prose-adjacent unless something runs it; a checker
/// that certifies an instance but never touches the statement recorded about
/// that instance is checking the tool, not the fact. Here the recorded
/// proposition is a propositional formula, so its validity is decidable by the
/// same solver the rest of the run uses, and its refutation is one call.
fn verify_formal(path: &str, config: &SolverConfig) -> Result<usize, String> {
    let text =
        std::fs::read_to_string(path).map_err(|error| format!("cannot read `{path}`: {error}"))?;
    let mut script = parse_script(&text).map_err(|error| format!("parsing `{path}`: {error}"))?;
    if script.assertions.is_empty() {
        return Err(format!(
            "`{path}` asserts nothing, so requiring `unsat` of it would be vacuous"
        ));
    }
    let assertions = script.assertions.clone();
    match solve(&mut script.arena, &assertions, config)
        .map_err(|error| format!("solving `{path}`: {error}"))?
    {
        CheckResult::Unsat => Ok(assertions.len()),
        CheckResult::Sat(_) => Err(format!(
            "`{path}` is SATISFIABLE: the negation of the recorded formal statement has a \
             model, so the recorded statement is NOT valid"
        )),
        CheckResult::Unknown(reason) => Err(format!(
            "`{path}` decided `unknown` ({reason:?}); an undecided formal statement is not a              checked one"
        )),
    }
}

fn named<'a>(program: &'a CqProgram, name: &str) -> Result<&'a Cq, String> {
    program
        .query(name)
        .ok_or_else(|| format!("no query named `{name}`"))
}

// The four verdict/expectation combinations are one argument read top to
// bottom -- two of them pass and two of them are the diagnostics for the
// mismatch. Splitting them would hand each arm the same five values back.
#[allow(clippy::too_many_lines)]
fn run() -> Result<(), String> {
    let args = parse_args()?;
    let text = std::fs::read_to_string(&args.path)
        .map_err(|error| format!("cannot read `{}`: {error}", args.path))?;
    let instance = Instance::parse(&text).map_err(|error| format!("parse: {error}"))?;
    let program = &instance.program;
    let config = SolverConfig::new().with_timeout(Duration::from_secs(args.timeout_secs));

    println!("instance            {}", args.path);
    println!(
        "predicates          {}",
        program
            .predicates
            .iter()
            .zip(program.arities.iter())
            .map(|(name, arity)| format!("{name}/{arity}"))
            .collect::<Vec<_>>()
            .join(" ")
    );
    println!("queries             {}", program.queries.len());
    for query in &program.queries {
        println!(
            "  query {:<12} {} variable(s), {} atom(s), head arity {}",
            query.name,
            query.variables.len(),
            query.body.len(),
            query.head.len()
        );
    }
    println!("expectations        {}", instance.expectations.len());

    let mut executed = 0usize;
    let mut failures = Vec::new();

    for (index, expectation) in instance.expectations.iter().enumerate() {
        let (left_name, right_name, want_contained) = match expectation {
            Expectation::Subset { left, right } => (left, right, true),
            Expectation::NotSubset { left, right } => (left, right, false),
            other => {
                return Err(format!(
                    "expectation {index} is `{}`, which is a schema question; run \
                     `db_design_certify` on this file instead",
                    other.kind()
                ));
            }
        };
        let left = named(program, left_name)?;
        let right = named(program, right_name)?;
        let tag = format!("c{index}");

        let frozen = freeze(program, left).map_err(|error| format!("freezing: {error}"))?;
        let solver_says = solver_route(right, &frozen, &tag, &config)?;
        let verdict = decide_containment(program, left, right)
            .map_err(|error| format!("deciding {left_name} in {right_name}: {error}"))?;

        executed += 1;
        let shown = format!("{left_name} subseteq {right_name}");
        match (&verdict, want_contained) {
            (
                ContainmentVerdict::Contained {
                    frozen: canonical,
                    homomorphism,
                },
                true,
            ) => {
                check_homomorphism(right, canonical, homomorphism)
                    .map_err(|error| format!("replaying the homomorphism: {error}"))?;
                if !solver_says {
                    failures.push(format!(
                        "{shown}: the search found a homomorphism and the solver refuted its \
                         existence"
                    ));
                    println!("  FAIL  {shown}: search and solver disagree");
                    continue;
                }
                let image: Vec<String> = homomorphism
                    .image
                    .iter()
                    .enumerate()
                    .map(|(variable, &element)| {
                        format!(
                            "{}->{}",
                            right.variables[variable],
                            canonical
                                .element_names
                                .get(element)
                                .map_or("?", String::as_str)
                        )
                    })
                    .collect();
                println!(
                    "  PASS  subset {shown}   [homomorphism {} over a {}-fact frozen database, \
                     replayed; solver agrees]",
                    image.join(" "),
                    canonical.facts.len()
                );
                if args.show {
                    print!("{}", render_frozen(program, canonical));
                }
            }
            (
                ContainmentVerdict::NotContained {
                    frozen: canonical,
                    assignments_enumerated,
                },
                false,
            ) => {
                if solver_says {
                    failures.push(format!(
                        "{shown}: the solver found a homomorphism the search did not"
                    ));
                    println!("  FAIL  {shown}: search and solver disagree");
                    continue;
                }
                // The counterexample database, re-derived here rather than
                // taken on the decision routine's word.
                let left_answers = evaluate(left, canonical)
                    .map_err(|error| format!("evaluating {left_name}: {error}"))?;
                let right_answers = evaluate(right, canonical)
                    .map_err(|error| format!("evaluating {right_name}: {error}"))?;
                if !left_answers.contains(&canonical.head)
                    || right_answers.contains(&canonical.head)
                {
                    failures.push(format!(
                        "{shown}: the frozen database does not separate the two queries"
                    ));
                    println!("  FAIL  {shown}: the counterexample database does not separate them");
                    continue;
                }
                println!(
                    "  PASS  notsubset {shown}   [{}-fact counterexample database: {left_name} \
                     returns the frozen head, {right_name} returns {} tuple(s) and not that one; \
                     {assignments_enumerated} assignments enumerated; solver unsat]",
                    canonical.facts.len(),
                    right_answers.len()
                );
                if args.show {
                    print!("{}", render_frozen(program, canonical));
                }
            }
            (ContainmentVerdict::Contained { .. }, false) => {
                failures.push(format!("notsubset {shown}: the containment holds"));
                println!("  FAIL  notsubset {shown}: a homomorphism exists");
            }
            (ContainmentVerdict::NotContained { .. }, true) => {
                failures.push(format!("subset {shown}: the containment fails"));
                println!("  FAIL  subset {shown}: no homomorphism exists");
            }
        }
    }

    println!(
        "executed            {executed} of {}",
        instance.expectations.len()
    );
    if executed != instance.expectations.len() {
        return Err("some expectation never ran".to_owned());
    }
    if let Some(expected) = args.expect_checks
        && expected != executed
    {
        return Err(format!("expected {expected} checks, executed {executed}"));
    }
    if !failures.is_empty() {
        return Err(format!(
            "{} of {} expectations failed",
            failures.len(),
            instance.expectations.len()
        ));
    }
    if let Some(formal) = &args.verify_formal {
        let asserted = verify_formal(formal, &config)?;
        println!(
            "formal statement    {formal}: {asserted} assertion(s), negation UNSAT -> the \
             recorded proposition is valid"
        );
    }

    println!("VERIFIED            {executed} containment obligations, every certificate replayed");
    Ok(())
}
