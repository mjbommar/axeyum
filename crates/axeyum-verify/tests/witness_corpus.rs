//! ADR-0339 deterministic, replay-checked witness-seed corpus.

use axeyum_ir::{Assignment, Sort, TermArena, Value, eval};
use axeyum_solver::{ProofOutcome, SolverConfig, prove};
use axeyum_verify::Witness;
use axeyum_verify::witness_corpus::{ReplayRecipe, WitnessSeed, WitnessSeedCorpus};

const EXPECTED_JSON: &str = include_str!("fixtures/witness-seed-corpus/corpus.json");
const EXPECTED_TESTS: &str = include_str!("fixtures/witness-seed-corpus/generated.rs");

#[axeyum_verify::verify(expect_bug)]
fn corpus_overflow(x: u8) -> u8 {
    x + 1
}

#[axeyum_verify::verify(expect_bug)]
#[axeyum_verify::requires(x < 255)]
#[axeyum_verify::ensures(|result| result == x)]
fn corpus_contract(x: u8) -> u8 {
    x + 1
}

fn corpus_reference(x: u8) -> u8 {
    x.wrapping_add(1)
}

fn corpus_mutated(x: u8) -> u8 {
    x.wrapping_add(2)
}

fn witness_u8(inputs: &[Witness], name: &str) -> u8 {
    inputs
        .iter()
        .find_map(|witness| match witness {
            Witness::Int {
                name: actual,
                width: 8,
                signed: false,
                bits,
            } if actual == name => u8::try_from(*bits).ok(),
            _ => None,
        })
        .expect("named u8 witness")
}

fn equivalence_countermodel() -> Witness {
    let mut arena = TermArena::new();
    let x_symbol = arena.declare("x", Sort::BitVec(8)).unwrap();
    let x = arena.var(x_symbol);
    let one = arena.bv_const(8, 1).unwrap();
    let two = arena.bv_const(8, 2).unwrap();
    let reference = arena.bv_add(x, one).unwrap();
    let mutated = arena.bv_add(x, two).unwrap();
    let equivalent = arena.eq(reference, mutated).unwrap();
    let outcome = prove(&mut arena, &[], equivalent, &SolverConfig::default())
        .expect("solver should not hard-error");
    let ProofOutcome::Disproved(model) = outcome else {
        panic!("wrong transform must be refuted, got {outcome:?}");
    };
    let Some(Value::Bv { width: 8, value }) = model.get(x_symbol) else {
        panic!("countermodel must carry the shared u8 input");
    };

    let mut assignment = Assignment::new();
    assignment.set(x_symbol, Value::Bv { width: 8, value });
    assert_ne!(
        eval(&arena, reference, &assignment).unwrap(),
        eval(&arena, mutated, &assignment).unwrap(),
        "solver countermodel must replay in the original term arena"
    );
    let x = u8::try_from(value).expect("width-8 model value");
    assert_ne!(
        corpus_reference(x),
        corpus_mutated(x),
        "solver countermodel must replay against the real Rust functions"
    );

    Witness::Int {
        name: "x".into(),
        width: 8,
        signed: false,
        bits: value,
    }
}

fn build_corpus() -> WitnessSeedCorpus {
    let overflow = corpus_overflow__axeyum_verdict();
    let overflow_seed = WitnessSeed::from_verdict(
        "overflow_panic_repro",
        &overflow,
        ReplayRecipe::panic_call("corpus_overflow", ["x"]),
        |inputs| {
            let x = witness_u8(inputs, "x");
            axeyum_verify::reproduce::panics_on(|| {
                let _ = corpus_overflow(x);
            })
        },
    )
    .expect("macro panic witness must replay");

    let contract = corpus_contract__axeyum_verdict();
    let postcondition_seed = WitnessSeed::from_verdict(
        "postcondition_violation_repro",
        &contract,
        ReplayRecipe::rust_body(
            "let result = corpus_contract(x);\nassert!(x < 255);\nassert_ne!(result, x, \"normally returned result must violate the postcondition\");",
        ),
        |inputs| {
            let x = witness_u8(inputs, "x");
            x < 255 && corpus_contract(x) != x
        },
    )
    .expect("postcondition witness must replay");

    let equivalence_seed = WitnessSeed::from_counterexample(
        "equivalence_refutation_repro",
        "equivalence mismatch",
        vec![equivalence_countermodel()],
        ReplayRecipe::rust_body(
            "assert_ne!(corpus_reference(x), corpus_mutated(x), \"wrong transform must remain distinguishable\");",
        ),
        |inputs| {
            let x = witness_u8(inputs, "x");
            corpus_reference(x) != corpus_mutated(x)
        },
    )
    .expect("raw equivalence countermodel must replay");

    let mut corpus = WitnessSeedCorpus::new("p5_4_2_countermodels").unwrap();
    // Deliberately add in non-lexical order; rendering owns canonical order.
    corpus.add(postcondition_seed).unwrap();
    corpus.add(overflow_seed).unwrap();
    corpus.add(equivalence_seed).unwrap();
    corpus
}

#[test]
fn preregistered_corpus_is_byte_stable_and_compiled() {
    let corpus = build_corpus();
    assert_eq!(
        corpus
            .seeds()
            .iter()
            .map(WitnessSeed::id)
            .collect::<Vec<_>>(),
        [
            "equivalence_refutation_repro",
            "overflow_panic_repro",
            "postcondition_violation_repro",
        ]
    );
    assert_eq!(corpus.render_json().unwrap(), EXPECTED_JSON);
    assert_eq!(corpus.render_tests().unwrap(), EXPECTED_TESTS);
    assert_eq!(build_corpus().render_json().unwrap(), EXPECTED_JSON);

    let mut reverse = WitnessSeedCorpus::new("p5_4_2_countermodels").unwrap();
    for seed in corpus.seeds().iter().rev().cloned() {
        reverse.add(seed).unwrap();
    }
    assert_eq!(reverse.render_json().unwrap(), EXPECTED_JSON);
    assert_eq!(reverse.render_tests().unwrap(), EXPECTED_TESTS);

    let mutated = WitnessSeed::from_counterexample(
        "equivalence_refutation_repro",
        "equivalence mismatch",
        vec![Witness::Int {
            name: "x".into(),
            width: 8,
            signed: false,
            bits: 1,
        }],
        ReplayRecipe::rust_body(
            "assert_ne!(corpus_reference(x), corpus_mutated(x), \"wrong transform must remain distinguishable\");",
        ),
        |inputs| {
            let x = witness_u8(inputs, "x");
            corpus_reference(x) != corpus_mutated(x)
        },
    )
    .unwrap();
    let mut mutated_corpus = WitnessSeedCorpus::new("p5_4_2_countermodels").unwrap();
    for seed in corpus
        .seeds()
        .iter()
        .filter(|seed| seed.id() != mutated.id())
        .cloned()
    {
        mutated_corpus.add(seed).unwrap();
    }
    mutated_corpus.add(mutated).unwrap();
    assert_ne!(mutated_corpus.render_json().unwrap(), EXPECTED_JSON);
    assert_ne!(mutated_corpus.render_tests().unwrap(), EXPECTED_TESTS);
}

// Compile and execute the exact committed generated artifact. This is the
// byte-for-byte reproduction gate, not merely a string-shape assertion.
include!("fixtures/witness-seed-corpus/generated.rs");
