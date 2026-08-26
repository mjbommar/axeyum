//! Run the generic multiplicative-complexity encoder on PRIMATEs inverse.

use std::fmt::Write as _;
use std::fs::File;
use std::io::BufReader;
use std::path::PathBuf;
use std::time::{Duration, Instant};

use axeyum_cnf::{
    CnfAssignment, ProofSolveOutcome, VivifyOptions, check_drat_backward,
    check_drat_backward_reader, vivify_within,
};
use axeyum_search::boolean_anf_cnf::{BooleanAnfCnfLimits, encode_boolean_anf_cnf};
use axeyum_search::harness::parse_sat_competition_model;
use axeyum_search::multiplicative_circuit::{
    MultiplicativeBasisTerm, MultiplicativeEncodingOptions, MultiplicativeSelectorOwner,
    MultiplicativeSynthesisLimits, MultiplicativeSynthesisOutcome, MultiplicativeSynthesisProblem,
    encode_multiplicative_anf_system, encode_multiplicative_circuit_anf,
    encode_multiplicative_circuit_with_options,
};

const TABLE: [u64; 32] = [
    1, 0, 14, 19, 10, 9, 18, 21, 17, 25, 27, 30, 29, 20, 12, 16, 23, 4, 13, 31, 8, 6, 28, 11, 22,
    2, 3, 7, 15, 5, 24, 26,
];

struct Arguments {
    budget: usize,
    seconds: u64,
    encoding: String,
    dimacs_path: Option<PathBuf>,
    anf_path: Option<PathBuf>,
    drat_path: Option<PathBuf>,
    eliminate_internal_constants: bool,
    operand_order: String,
    checked_lower_budget: Option<usize>,
    selector_map: Option<PathBuf>,
    model_path: Option<PathBuf>,
    circuit_out: Option<PathBuf>,
}

fn positional_arguments(args: &[String]) -> (usize, u64) {
    let budget = args
        .first()
        .and_then(|text| text.parse::<usize>().ok())
        .unwrap_or(8);
    let seconds = args
        .get(1)
        .and_then(|text| text.parse::<u64>().ok())
        .unwrap_or(30);
    (budget, seconds)
}

fn arguments() -> Arguments {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (budget, seconds) = positional_arguments(&args);
    let mut encoding = "anf".to_string();
    let mut dimacs_path: Option<PathBuf> = None;
    let mut anf_path: Option<PathBuf> = None;
    let mut drat_path: Option<PathBuf> = None;
    let mut eliminate_internal_constants = true;
    let mut operand_order = "lex".to_string();
    let mut checked_lower_budget = None;
    let mut selector_map = None;
    let mut model_path = None;
    let mut circuit_out = None;
    let mut index = 2;
    while index < args.len() {
        match args[index].as_str() {
            "--encoding" => {
                encoding.clone_from(
                    args.get(index + 1)
                        .expect("--encoding needs anf, system, or truth"),
                );
                assert!(matches!(encoding.as_str(), "anf" | "system" | "truth"));
                index += 2;
            }
            "--dimacs" => {
                dimacs_path = Some(PathBuf::from(
                    args.get(index + 1).expect("--dimacs needs a path"),
                ));
                index += 2;
            }
            "--anf-file" => {
                anf_path = Some(PathBuf::from(
                    args.get(index + 1).expect("--anf-file needs a path"),
                ));
                index += 2;
            }
            "--check-drat" => {
                drat_path = Some(PathBuf::from(
                    args.get(index + 1).expect("--check-drat needs a path"),
                ));
                index += 2;
            }
            "--retain-internal-constants" => {
                eliminate_internal_constants = false;
                index += 1;
            }
            "--operand-order" => {
                operand_order.clone_from(
                    args.get(index + 1)
                        .expect("--operand-order needs none, first, or lex"),
                );
                assert!(matches!(operand_order.as_str(), "none" | "first" | "lex"));
                index += 2;
            }
            "--exact-budget-after-checked-lower" => {
                let lower = args
                    .get(index + 1)
                    .expect("--exact-budget-after-checked-lower needs a budget")
                    .parse::<usize>()
                    .expect("checked lower budget must be an integer");
                assert_eq!(
                    lower.checked_add(1),
                    Some(budget),
                    "checked lower budget must be exactly one below the query"
                );
                checked_lower_budget = Some(lower);
                index += 2;
            }
            option @ ("--selector-map" | "--model" | "--circuit-out") => {
                let destination = match option {
                    "--selector-map" => &mut selector_map,
                    "--model" => &mut model_path,
                    "--circuit-out" => &mut circuit_out,
                    _ => unreachable!("matched path options"),
                };
                *destination = Some(PathBuf::from(
                    args.get(index + 1).expect("path option needs a value"),
                ));
                index += 2;
            }
            other => panic!("unknown argument: {other}"),
        }
    }
    Arguments {
        budget,
        seconds,
        encoding,
        dimacs_path,
        anf_path,
        drat_path,
        eliminate_internal_constants,
        operand_order,
        checked_lower_budget,
        selector_map,
        model_path,
        circuit_out,
    }
}

fn write_circuit(args: &Arguments, circuit: &axeyum_cas::boolean_circuit::BooleanCircuitArtifact) {
    let path = args
        .circuit_out
        .as_ref()
        .expect("model import has a paired circuit output");
    std::fs::write(
        path,
        serde_json::to_vec_pretty(circuit).expect("serialize circuit"),
    )
    .expect("write circuit");
    println!("model={}", args.model_path.as_ref().unwrap().display());
    println!("circuit-out={}", path.display());
    println!("verdict=sat-replayed");
}

fn write_selector_map(
    path: &PathBuf,
    selectors: &[axeyum_search::multiplicative_circuit::MultiplicativeSelector],
) {
    let mut text = String::from("schema=axeyum.multiplicative-selector-map.v1\n");
    text.push_str("dimacs\towner\towner-index\tbasis\tbasis-index\n");
    for selector in selectors {
        let (owner, owner_index) = match selector.owner {
            MultiplicativeSelectorOwner::GateLeft(gate) => ("gate-left", gate),
            MultiplicativeSelectorOwner::GateRight(gate) => ("gate-right", gate),
            MultiplicativeSelectorOwner::Output(output) => ("output", output),
        };
        let (basis, basis_index) = match selector.term {
            MultiplicativeBasisTerm::Constant => ("constant", "-".to_owned()),
            MultiplicativeBasisTerm::Input(input) => ("input", input.to_string()),
            MultiplicativeBasisTerm::EarlierAnd(gate) => ("earlier-and", gate.to_string()),
        };
        writeln!(
            text,
            "{}\t{owner}\t{owner_index}\t{basis}\t{basis_index}",
            selector.variable + 1
        )
        .expect("write selector-map row");
    }
    std::fs::write(path, text).expect("write selector map");
    println!("selector-map={}", path.display());
    println!("selector-count={}", selectors.len());
}

fn export_anf(
    problem: &MultiplicativeSynthesisProblem,
    limits: MultiplicativeSynthesisLimits,
    options: MultiplicativeEncodingOptions,
    path: &PathBuf,
    budget: usize,
) {
    let encoding =
        encode_multiplicative_anf_system(problem, limits, options).expect("ANF encoding must fit");
    std::fs::write(path, encoding.system().to_bosphorus_anf()).expect("write ANF");
    println!("schema=axeyum.mc-anf-system.v1");
    println!("problem=primates-inverse");
    println!("and-budget={budget}");
    println!("variables={}", encoding.system().variable_count());
    println!("equations={}", encoding.system().equations().len());
    println!(
        "monomials={}",
        encoding
            .system()
            .equations()
            .iter()
            .map(axeyum_cas::boolean_anf::BooleanAnfPolynomial::monomial_count)
            .sum::<usize>()
    );
    println!("anf={}", path.display());
    println!("verdict=encoded");
}

fn encoding_options(args: &Arguments) -> MultiplicativeEncodingOptions {
    MultiplicativeEncodingOptions {
        eliminate_internal_constants: args.eliminate_internal_constants,
        partial_operand_order: args.operand_order == "first",
        lexicographic_operand_order: args.operand_order == "lex",
    }
}

fn print_encoding_options(args: &Arguments) {
    println!(
        "internal-constants={}",
        if args.eliminate_internal_constants {
            "eliminated"
        } else {
            "retained"
        }
    );
    println!("operand-order={}", args.operand_order);
    if let Some(lower) = args.checked_lower_budget {
        println!("exact-budget-irredundancy=enabled");
        println!("checked-lower-budget-premise={lower}");
    } else {
        println!("exact-budget-irredundancy=disabled");
    }
}

fn print_problem_header(args: &Arguments) {
    println!("schema=axeyum.mc-synthesis-run.v1");
    println!("problem=primates-inverse");
    println!("and-budget={}", args.budget);
}

fn run_system_cnf(
    args: &Arguments,
    problem: &MultiplicativeSynthesisProblem,
    limits: MultiplicativeSynthesisLimits,
    options: MultiplicativeEncodingOptions,
) {
    let source =
        encode_multiplicative_anf_system(problem, limits, options).expect("ANF system must fit");
    if let Some(path) = &args.selector_map {
        write_selector_map(path, &source.selectors());
    }
    let encoding = encode_boolean_anf_cnf(source.system(), BooleanAnfCnfLimits::default())
        .expect("ANF-to-CNF lowering must fit");
    let formula = if args.checked_lower_budget.is_some() {
        encoding
            .formula_with_source_clauses(&source.exact_budget_irredundancy_source_clauses())
            .expect("exact-budget clauses must reference source selectors")
    } else {
        encoding.formula().clone()
    };
    print_problem_header(args);
    print_encoding_options(args);
    println!("semantics=system");
    println!("anf-variables={}", source.system().variable_count());
    println!("anf-equations={}", source.system().equations().len());
    println!("variables={}", formula.variable_count());
    println!("clauses={}", formula.clauses().len());
    if let Some(path) = &args.dimacs_path {
        std::fs::write(path, formula.to_dimacs()).expect("write DIMACS");
        println!("dimacs={}", path.display());
        println!("verdict=encoded");
        return;
    }
    if let Some(path) = &args.model_path {
        let output = std::fs::read_to_string(path).expect("read SAT Competition output");
        let values = parse_sat_competition_model(&output, formula.variable_count())
            .expect("strict SAT model import");
        assert_eq!(formula.evaluate(&values), Ok(true));
        let assignment = encoding
            .lift_source_assignment(source.system(), &CnfAssignment::new(values))
            .expect("project and replay source ANF model");
        let circuit = source
            .lift_assignment(&assignment)
            .expect("lift and replay circuit");
        write_circuit(args, &circuit);
        return;
    }
    if let Some(path) = &args.drat_path {
        let reader = BufReader::new(File::open(path).expect("open textual DRAT"));
        assert_eq!(check_drat_backward_reader(&formula, reader), Ok(true));
        println!("drat={}", path.display());
        println!("drat-mode=file-backed-backward");
        println!("verdict=unsat-checked");
        return;
    }
    let started = Instant::now();
    let outcome = axeyum_cnf::solve_with_drat_proof_with_limits(
        &formula,
        Some(started + Duration::from_secs(args.seconds)),
        limits.max_conflicts,
    );
    println!("elapsed-ms={}", started.elapsed().as_millis());
    match outcome {
        ProofSolveOutcome::Sat(model) => {
            let assignment = encoding
                .lift_source_assignment(source.system(), &model)
                .expect("project and replay source ANF model");
            source
                .lift_assignment(&assignment)
                .expect("lift and replay circuit");
            println!("verdict=sat-replayed");
        }
        ProofSolveOutcome::Unsat(proof) => {
            assert_eq!(check_drat_backward(&formula, &proof), Ok(true));
            println!("verdict=unsat-checked");
            println!("drat-steps={}", proof.len());
        }
        ProofSolveOutcome::ResourceOut => println!("verdict=resource-out"),
        ProofSolveOutcome::Interrupted => println!("verdict=interrupted"),
    }
}

fn run_direct_cnf(
    args: &Arguments,
    problem: &MultiplicativeSynthesisProblem,
    limits: MultiplicativeSynthesisLimits,
    options: MultiplicativeEncodingOptions,
) {
    let encoding = match args.encoding.as_str() {
        "anf" => encode_multiplicative_circuit_anf(problem, limits, options),
        "truth" => encode_multiplicative_circuit_with_options(problem, limits, options),
        _ => unreachable!("validated above"),
    }
    .expect("encoding must fit");
    if let Some(path) = &args.selector_map {
        write_selector_map(path, &encoding.selectors());
    }
    let formula = if args.checked_lower_budget.is_some() {
        encoding
            .formula_with_exact_budget_irredundancy()
            .expect("exact-budget clauses must reference selectors")
    } else {
        encoding.formula().clone()
    };
    print_problem_header(args);
    print_encoding_options(args);
    println!("semantics={}", args.encoding);
    println!("variables={}", formula.variable_count());
    println!("clauses={}", formula.clauses().len());
    if let Some(path) = &args.dimacs_path {
        std::fs::write(path, formula.to_dimacs()).expect("write DIMACS");
        println!("dimacs={}", path.display());
        println!("verdict=encoded");
        return;
    }
    if let Some(path) = &args.model_path {
        let output = std::fs::read_to_string(path).expect("read SAT Competition output");
        let values = parse_sat_competition_model(&output, formula.variable_count())
            .expect("strict SAT model import");
        assert_eq!(formula.evaluate(&values), Ok(true));
        let circuit = encoding
            .lift_model(&CnfAssignment::new(values))
            .expect("lift and replay circuit");
        write_circuit(args, &circuit);
        return;
    }
    if let Some(path) = &args.drat_path {
        let reader = BufReader::new(File::open(path).expect("open textual DRAT"));
        assert_eq!(check_drat_backward_reader(&formula, reader), Ok(true));
        println!("drat={}", path.display());
        println!("drat-mode=file-backed-backward");
        println!("verdict=unsat-checked");
        return;
    }
    let started = Instant::now();
    let deadline = started + Duration::from_secs(args.seconds);
    let vivified = vivify_within(
        &formula,
        VivifyOptions::default(),
        Some((started + Duration::from_secs(10)).min(deadline)),
    );
    println!("vivified-clauses={}", vivified.formula.clauses().len());
    println!(
        "vivified-literals-removed={}",
        vivified.stats.literals_removed
    );
    let outcome = match axeyum_cnf::solve_with_drat_proof_with_limits(
        &vivified.formula,
        Some(deadline),
        limits.max_conflicts,
    ) {
        ProofSolveOutcome::Sat(model) => MultiplicativeSynthesisOutcome::Sat(
            encoding.lift_model(&model).expect("lift and replay model"),
        ),
        ProofSolveOutcome::Unsat(proof) => {
            let mut combined = vivified.proof;
            combined.extend(proof);
            assert_eq!(check_drat_backward(&formula, &combined), Ok(true));
            MultiplicativeSynthesisOutcome::Unsat {
                formula: formula.clone(),
                proof: combined,
            }
        }
        ProofSolveOutcome::ResourceOut => MultiplicativeSynthesisOutcome::ResourceOut,
        ProofSolveOutcome::Interrupted => MultiplicativeSynthesisOutcome::Interrupted,
    };
    println!("elapsed-ms={}", started.elapsed().as_millis());
    match outcome {
        MultiplicativeSynthesisOutcome::Sat(artifact) => {
            let ands = artifact
                .gates
                .iter()
                .filter(|gate| gate.op == axeyum_cas::boolean_circuit::BooleanGateOp::And)
                .count();
            println!("verdict=sat-replayed");
            println!("lifted-and-gates={ands}");
        }
        MultiplicativeSynthesisOutcome::Unsat { proof, .. } => {
            println!("verdict=unsat-checked");
            println!("drat-steps={}", proof.len());
        }
        MultiplicativeSynthesisOutcome::ResourceOut => println!("verdict=resource-out"),
        MultiplicativeSynthesisOutcome::Interrupted => println!("verdict=interrupted"),
    }
}

fn main() {
    let args = arguments();
    assert_eq!(
        args.model_path.is_some(),
        args.circuit_out.is_some(),
        "--model and --circuit-out must be supplied together"
    );
    let budget = args.budget;
    let problem = MultiplicativeSynthesisProblem {
        input_bits: 5,
        output_bits: 5,
        truth_table: TABLE.to_vec(),
        and_gates: budget,
    };
    let limits = MultiplicativeSynthesisLimits {
        max_conflicts: 10_000_000,
        ..MultiplicativeSynthesisLimits::default()
    };
    let options = encoding_options(&args);
    if let Some(path) = &args.anf_path {
        assert!(
            args.checked_lower_budget.is_none(),
            "exact-budget irredundancy contains disjunctive clauses; export the checked system CNF"
        );
        export_anf(&problem, limits, options, path, budget);
        return;
    }
    if args.encoding == "system" {
        run_system_cnf(&args, &problem, limits, options);
        return;
    }
    run_direct_cnf(&args, &problem, limits, options);
}
