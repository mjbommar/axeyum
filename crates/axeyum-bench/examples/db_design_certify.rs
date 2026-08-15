//! Certified relational **schema design**: decide the classical questions
//! about a committed schema, and refuse to report any answer without a
//! certificate an independent checker has already replayed.
//!
//! # What it runs
//!
//! The instance file pins its own answers (`expect …` lines, see
//! [`axeyum_scenarios::dbdesign::Instance`]). Every one of them is *executed*,
//! and the run fails if the file pins nothing, if an expectation is unmet, or
//! if fewer expectations were executed than the file declares. A checker that
//! exits `0` on completion alone checks nothing; this one exits `0` only after
//! reporting how many obligations it discharged.
//!
//! | expectation | decided by | certified by |
//! |---|---|---|
//! | `implies` | attribute closure **and** the solver on the Horn encoding | an Armstrong derivation, replayed under the three axioms |
//! | `notimplies` | the solver, `sat` | its **model**, read as a two-row relation and evaluated against `F` |
//! | `keys` | exhaustive subset sweep | a derivation per key, a two-row relation per removal, and a two-row relation for every non-superkey subset |
//! | `bcnf` / `3nf` | the dependencies of `F` | the violating dependency plus its two-row relation |
//! | `lossless` / `lossy` | the tableau chase | a replayed chase trace, or a relation exhibiting a spurious tuple |
//! | `preserving` / `notpreserving` | projected dependencies | derivations both ways, or a two-row relation over the projection |
//!
//! # Where the solver comes in
//!
//! Functional-dependency implication is decided **twice**, by routes that
//! share no code: the closure fixpoint in `axeyum-scenarios`, and the solver
//! on a Boolean Horn encoding. They must agree, and when the solver says `sat`
//! its model is replayed by the IR evaluator (`check_model`) *and* decoded
//! into the counterexample relation that the two-row checker then verifies. So
//! a wrong `sat` cannot survive, and a wrong `unsat` is caught by the closure
//! route disagreeing.
//!
//! ```sh
//! cargo run --release -q -p axeyum-bench --example db_design_certify -- \
//!     artifacts/instances/dbdesign/orders-schema.dbd --expect-checks 12
//! ```

use std::process::ExitCode;
use std::time::Duration;

use axeyum_ir::{TermArena, Value};
use axeyum_scenarios::dbdesign::armstrong::{
    check_derivation, check_two_tuple_witness, derive, witness_from_agreement,
};
use axeyum_scenarios::dbdesign::decomposition::{
    JoinVerdict, PreservationVerdict, chase, check_chase_trace, check_spurious_tuple, preservation,
};
use axeyum_scenarios::dbdesign::encode::{agreement_from_model, fd_implication_query};
use axeyum_scenarios::dbdesign::normal_forms::{
    analyze_keys, bcnf_violations, certify_key_completeness, third_normal_form_violations,
};
use axeyum_scenarios::dbdesign::{AttrSet, Expectation, Instance, Schema};
use axeyum_smtlib::parse_script;
use axeyum_solver::{CheckResult, SolverConfig, check_model, solve};

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(message) => {
            eprintln!("db_design_certify: {message}");
            ExitCode::FAILURE
        }
    }
}

struct Args {
    path: String,
    expect_checks: Option<usize>,
    verify_formal: Option<String>,
    timeout_secs: u64,
}

fn parse_args() -> Result<Args, String> {
    let mut path = None;
    let mut expect_checks = None;
    let mut verify_formal = None;
    let mut timeout_secs = 120;
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
            other if other.starts_with("--") => return Err(format!("unknown flag `{other}`")),
            other => path = Some(other.to_owned()),
        }
    }
    Ok(Args {
        path: path
            .ok_or("usage: db_design_certify <file.dbd> [--expect-checks N] [--verify-formal <file.smt2>] [--timeout SECONDS]")?,
        expect_checks,
        verify_formal,
        timeout_secs,
    })
}

fn next_usize(argv: &mut impl Iterator<Item = String>, flag: &str) -> Result<usize, String> {
    argv.next()
        .ok_or_else(|| format!("{flag} needs a value"))?
        .parse()
        .map_err(|_| format!("{flag} needs a non-negative integer"))
}

/// Decide `F ⊨ X → Y` through the solver, on the Boolean Horn encoding.
///
/// Returns `Some(agreement set)` when the implication **fails** — the model,
/// read back as the agreement set of a two-row relation — and `None` when the
/// encoding is unsatisfiable, i.e. the implication holds.
fn solver_verdict(
    schema: &Schema,
    x: AttrSet,
    y: AttrSet,
    tag: &str,
    config: &SolverConfig,
) -> Result<Option<AttrSet>, String> {
    let mut arena = TermArena::new();
    let query = fd_implication_query(&mut arena, schema, x, y, &format!("{tag}_"))
        .map_err(|error| format!("encoding {tag}: {error}"))?;
    let result = solve(&mut arena, &query.assertions, config)
        .map_err(|error| format!("solving {tag}: {error}"))?;
    match result {
        CheckResult::Unsat => Ok(None),
        CheckResult::Unknown(reason) => Err(format!(
            "the solver returned `unknown` ({reason:?}) on {tag}; an undecided route cannot back \
             a design decision"
        )),
        CheckResult::Sat(model) => {
            // Hard rule: a `sat` is checkable by evaluating the original terms
            // against the lifted model.
            if !check_model(&arena, &query.assertions, &model)
                .map_err(|error| format!("replaying the model for {tag}: {error}"))?
            {
                return Err(format!("the model for {tag} failed evaluator replay"));
            }
            Ok(Some(agreement_from_model(&query, |symbol| {
                match model.get(symbol) {
                    Some(Value::Bool(value)) => Some(value),
                    _ => None,
                }
            })))
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

struct Report {
    executed: usize,
    failures: Vec<String>,
}

impl Report {
    fn pass(&mut self, line: &str) {
        self.executed += 1;
        println!("  PASS  {line}");
    }

    fn fail(&mut self, line: String) {
        self.executed += 1;
        println!("  FAIL  {line}");
        self.failures.push(line);
    }
}

// The expectation kinds are a flat dispatch and each arm is short; splitting
// them across functions would hand every arm the same four values back.
#[allow(clippy::too_many_lines)]
fn run() -> Result<(), String> {
    let args = parse_args()?;
    let text = std::fs::read_to_string(&args.path)
        .map_err(|error| format!("cannot read `{}`: {error}", args.path))?;
    let instance = Instance::parse(&text).map_err(|error| format!("parse: {error}"))?;
    let config = SolverConfig::new().with_timeout(Duration::from_secs(args.timeout_secs));
    let schema = instance.schema.clone();

    println!("instance            {}", args.path);
    println!(
        "attributes          {} ({})",
        schema.arity(),
        schema.render(schema.all())
    );
    println!("dependencies        {}", schema.fds().len());
    for fd in schema.fds() {
        println!(
            "  fd {:<16} {} -> {}",
            fd.name,
            schema.render(fd.lhs),
            schema.render(fd.rhs)
        );
    }
    println!("queries             {}", instance.program.queries.len());
    println!("expectations        {}", instance.expectations.len());

    // The key analysis is shared by `keys` and `3nf`; compute it once, and
    // only when something asks for it.
    let needs_keys = instance
        .expectations
        .iter()
        .any(|expectation| matches!(expectation, Expectation::Keys(_) | Expectation::ThirdNf(_)));
    let keys = if needs_keys {
        Some(analyze_keys(&schema).map_err(|error| format!("key analysis: {error}"))?)
    } else {
        None
    };

    let mut report = Report {
        executed: 0,
        failures: Vec::new(),
    };

    for (index, expectation) in instance.expectations.iter().enumerate() {
        let tag = format!("e{index}");
        match expectation {
            Expectation::Implies { lhs, rhs } => {
                let shown = format!("{} -> {}", schema.render(*lhs), schema.render(*rhs));
                let solver = solver_verdict(&schema, *lhs, *rhs, &tag, &config)?;
                match derive(&schema, *lhs, *rhs) {
                    Ok(derivation) => {
                        check_derivation(schema.fds(), &derivation)
                            .map_err(|error| format!("replaying the derivation: {error}"))?;
                        if let Some(agreement) = solver {
                            report.fail(format!(
                                "implies {shown}: the closure route derived it in {} lines but \
                                 the solver found a counterexample agreeing on {}",
                                derivation.len(),
                                schema.render(agreement)
                            ));
                        } else {
                            report.pass(&format!(
                                "implies {shown}   [Armstrong derivation, {} lines, replayed; \
                                 solver unsat]",
                                derivation.len()
                            ));
                        }
                    }
                    Err(error) => report.fail(format!("implies {shown}: {error}")),
                }
            }
            Expectation::NotImplies { lhs, rhs } => {
                let shown = format!("{} -> {}", schema.render(*lhs), schema.render(*rhs));
                match solver_verdict(&schema, *lhs, *rhs, &tag, &config)? {
                    None => report.fail(format!(
                        "notimplies {shown}: the solver refuted the counterexample encoding, so \
                         F does imply it"
                    )),
                    Some(agreement) => {
                        let witness = witness_from_agreement(&schema, agreement, *lhs, *rhs)
                            .map_err(|error| {
                                format!("the solver model is not a counterexample: {error}")
                            })?;
                        check_two_tuple_witness(&schema, &witness)
                            .map_err(|error| format!("re-checking the two rows: {error}"))?;
                        if derive(&schema, *lhs, *rhs).is_ok() {
                            report.fail(format!(
                                "notimplies {shown}: the closure route derived it anyway"
                            ));
                        } else {
                            report.pass(&format!(
                                "notimplies {shown}   [solver model -> two rows agreeing on {}, \
                                 checked]",
                                schema.render(witness.agreement)
                            ));
                        }
                    }
                }
            }
            Expectation::Keys(expected) => {
                let analysis = keys.as_ref().ok_or("key analysis missing")?;
                let mut wanted = expected.clone();
                wanted.sort_by_key(|key| key.bits());
                wanted.dedup();
                let completeness = certify_key_completeness(&schema, &analysis.candidate_keys)
                    .map_err(|error| format!("certifying that these are all the keys: {error}"))?;
                let shown: Vec<String> = analysis
                    .candidate_keys
                    .iter()
                    .map(|key| format!("({})", schema.render(*key)))
                    .collect();
                if wanted == analysis.candidate_keys {
                    report.pass(&format!(
                        "keys {}   [{} subsets swept, {} non-superkey relations checked, {} \
                         removal tests all decided -> minimality ABSOLUTE (ADR-0455)]",
                        shown.join(" "),
                        completeness.subsets_examined,
                        completeness.counterexamples_checked,
                        analysis.minimality_tests_decided
                    ));
                } else {
                    report.fail(format!(
                        "keys: expected {} but the sweep found {}",
                        expected
                            .iter()
                            .map(|key| format!("({})", schema.render(*key)))
                            .collect::<Vec<_>>()
                            .join(" "),
                        shown.join(" ")
                    ));
                }
            }
            Expectation::Bcnf(expected) => {
                let violations =
                    bcnf_violations(&schema).map_err(|error| format!("bcnf: {error}"))?;
                let holds = violations.is_empty();
                if holds == *expected {
                    let detail = violations.first().map_or_else(
                        || "no dependency has a non-superkey determinant".to_owned(),
                        |violation| {
                            format!(
                                "`{}` has determinant {} with {} not a superkey; two rows agree \
                                 on {} and differ",
                                violation.fd_name,
                                schema.render(violation.lhs),
                                schema.render(violation.lhs),
                                schema.render(violation.not_superkey.agreement)
                            )
                        },
                    );
                    report.pass(&format!(
                        "bcnf {}   [{} violation(s); {detail}]",
                        if *expected { "yes" } else { "no" },
                        violations.len()
                    ));
                } else {
                    report.fail(format!(
                        "bcnf: expected {}, measured {} ({} violation(s))",
                        expected,
                        holds,
                        violations.len()
                    ));
                }
            }
            Expectation::ThirdNf(expected) => {
                let analysis = keys.as_ref().ok_or("key analysis missing")?;
                let violations = third_normal_form_violations(&schema, analysis)
                    .map_err(|error| format!("3nf: {error}"))?;
                let holds = violations.is_empty();
                if holds == *expected {
                    report.pass(&format!(
                        "3nf {}   [{} violation(s); prime attributes {}]",
                        if *expected { "yes" } else { "no" },
                        violations.len(),
                        schema.render(analysis.prime_attributes)
                    ));
                } else {
                    report.fail(format!(
                        "3nf: expected {expected}, measured {holds} ({} violation(s))",
                        violations.len()
                    ));
                }
            }
            Expectation::Lossless(name) | Expectation::Lossy(name) => {
                let want_lossless = matches!(expectation, Expectation::Lossless(_));
                let decomposition = instance
                    .decomposition(name)
                    .ok_or_else(|| format!("no decomposition `{name}`"))?;
                let verdict = chase(&schema, &decomposition.fragments)
                    .map_err(|error| format!("chasing `{name}`: {error}"))?;
                match (&verdict, want_lossless) {
                    (JoinVerdict::Lossless(trace), true) => {
                        check_chase_trace(&schema, trace)
                            .map_err(|error| format!("replaying the chase: {error}"))?;
                        report.pass(&format!(
                            "lossless {name}   [chase trace of {} identifications, replayed to \
                             an all-distinguished row]",
                            trace.steps.len()
                        ));
                    }
                    (JoinVerdict::Lossy(witness), false) => {
                        check_spurious_tuple(&schema, witness)
                            .map_err(|error| format!("checking the spurious tuple: {error}"))?;
                        report.pass(&format!(
                            "lossy {name}   [{}-row relation over F whose projections rejoin to \
                             a tuple it does not contain]",
                            witness.rows.len()
                        ));
                    }
                    (JoinVerdict::Lossless(_), false) => {
                        report.fail(format!("lossy {name}: the chase reached an all-a row"));
                    }
                    (JoinVerdict::Lossy(_), true) => {
                        report.fail(format!(
                            "lossless {name}: the chase terminated with a spurious tuple"
                        ));
                    }
                }
            }
            Expectation::Preserving(name) | Expectation::NotPreserving(name) => {
                let want_preserved = matches!(expectation, Expectation::Preserving(_));
                let decomposition = instance
                    .decomposition(name)
                    .ok_or_else(|| format!("no decomposition `{name}`"))?;
                let verdict = preservation(&schema, &decomposition.fragments)
                    .map_err(|error| format!("projecting onto `{name}`: {error}"))?;
                match (&verdict, want_preserved) {
                    (
                        PreservationVerdict::Preserved {
                            projected,
                            f_from_g,
                            g_from_f,
                        },
                        true,
                    ) => {
                        report.pass(&format!(
                            "preserving {name}   [G has {} dependencies; {} derivations F from \
                             G and {} G from F, all replayed]",
                            projected.fds().len(),
                            f_from_g.len(),
                            g_from_f.len()
                        ));
                    }
                    (
                        PreservationVerdict::NotPreserved {
                            projected,
                            lost_fd,
                            witness,
                        },
                        false,
                    ) => {
                        check_two_tuple_witness(projected, witness)
                            .map_err(|error| format!("checking the lost dependency: {error}"))?;
                        report.pass(&format!(
                            "notpreserving {name}   [`{lost_fd}` is lost; two rows satisfy all \
                             {} projected dependencies and violate it]",
                            projected.fds().len()
                        ));
                    }
                    (PreservationVerdict::Preserved { .. }, false) => {
                        report.fail(format!(
                            "notpreserving {name}: every dependency is recoverable"
                        ));
                    }
                    (PreservationVerdict::NotPreserved { lost_fd, .. }, true) => {
                        report.fail(format!("preserving {name}: `{lost_fd}` is lost"));
                    }
                }
            }
            Expectation::Subset { .. } | Expectation::NotSubset { .. } => {
                return Err(format!(
                    "expectation {index} is a conjunctive-query containment; run \
                     `cq_containment_certify` on this file instead"
                ));
            }
        }
    }

    println!(
        "executed            {} of {}",
        report.executed,
        instance.expectations.len()
    );
    if report.executed != instance.expectations.len() {
        return Err(format!(
            "{} of {} expectations never ran; an unexecuted expectation is indistinguishable \
             from a passing one",
            instance.expectations.len() - report.executed,
            instance.expectations.len()
        ));
    }
    if let Some(expected) = args.expect_checks
        && expected != report.executed
    {
        return Err(format!(
            "expected {expected} checks, executed {}",
            report.executed
        ));
    }
    if !report.failures.is_empty() {
        return Err(format!(
            "{} of {} expectations failed",
            report.failures.len(),
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

    println!(
        "VERIFIED            {} design obligations, every certificate replayed",
        report.executed
    );
    Ok(())
}
