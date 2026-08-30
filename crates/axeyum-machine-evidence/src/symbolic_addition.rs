//! Source-derived symbolic evidence for the A0 addition operation.

use std::{fs, path::Path};

use axeyum_ir::{Assignment, Sort, SymbolId, TermArena, TermId, Value, eval, render};
use axeyum_machine::a0::{
    AdditionDomain, Instruction, Memory, Program, State, Word, addition, encode, step,
};
use axeyum_solver::{UnsatProof, UnsatProofOutcome, export_qf_bv_unsat_proof};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::{EvidenceError, load_semantic_package};

const SCHEMA: &str = "axeyum.a0.symbolic-addition.v1";
const WIDTHS: [u8; 8] = [8, 16, 24, 32, 40, 48, 56, 64];

/// Saved clausal proof for one supported architectural word width.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SymbolicAdditionWidthProof {
    /// Fixed bit-vector width proved by this certificate.
    pub width: u8,
    /// SHA-256 of the exact source Boolean assertion rebuilt by the checker.
    pub assertion_sha256: String,
    /// DIMACS input bound to the assertion by deterministic bit blasting.
    pub dimacs: String,
    /// DRAT refutation checked by Axeyum and exportable to an external checker.
    pub drat: String,
    /// LRAT refutation with explicit hints, when elaboration succeeded.
    pub lrat: Option<String>,
}

/// Concrete replay of the satisfying inverted-carry mutation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SymbolicCounterexample {
    /// Width of the finite model and concrete A0 replay.
    pub width: u8,
    /// Model value for the left operand.
    pub lhs: u64,
    /// Model value for the right operand.
    pub rhs: u64,
    /// Carry produced by the unmodified concrete executor.
    pub concrete_carry: bool,
    /// Carry predicted by the deliberately inverted symbolic definition.
    pub mutated_carry: bool,
    /// Whether executing encoded A0 `add` reproduced the unmodified result.
    pub replayed_through_step: bool,
}

/// Source-bound symbolic A0 addition report and its saved certificates.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SymbolicAdditionReport {
    /// Report schema identifier.
    pub schema: String,
    /// SHA-256 of the canonical semantic-package JSON bytes.
    pub semantic_package_sha256: String,
    /// One certificate for every A0-supported word width.
    pub proofs: Vec<SymbolicAdditionWidthProof>,
    /// Satisfying mutation model replayed through concrete encoded execution.
    pub inverted_carry_counterexample: SymbolicCounterexample,
}

struct SymbolicDomain<'a> {
    arena: &'a mut TermArena,
    width: u32,
}

impl AdditionDomain for SymbolicDomain<'_> {
    type Word = TermId;
    type Bit = TermId;

    fn sum(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        self.arena
            .bv_add(lhs, rhs)
            .expect("symbolic A0 operands have one valid width")
    }

    fn is_zero(&mut self, word: TermId) -> TermId {
        let zero = self
            .arena
            .bv_const(self.width, 0)
            .expect("A0 width is a valid bit-vector width");
        self.arena
            .eq(word, zero)
            .expect("zero has the A0 word sort")
    }

    fn high_bit(&mut self, word: TermId) -> TermId {
        high_bit(self.arena, self.width, word)
    }

    fn carry(&mut self, lhs: TermId, _rhs: TermId, sum: TermId) -> TermId {
        self.arena
            .bv_ult(sum, lhs)
            .expect("sum and operand have the A0 word sort")
    }

    fn overflow(&mut self, lhs: TermId, rhs: TermId, sum: TermId) -> TermId {
        let lhs_sign = high_bit(self.arena, self.width, lhs);
        let rhs_sign = high_bit(self.arena, self.width, rhs);
        let sum_sign = high_bit(self.arena, self.width, sum);
        let same_inputs = self
            .arena
            .eq(lhs_sign, rhs_sign)
            .expect("sign terms are Boolean");
        let same_result = self
            .arena
            .eq(sum_sign, lhs_sign)
            .expect("sign terms are Boolean");
        let changed = self
            .arena
            .not(same_result)
            .expect("sign equality is Boolean");
        self.arena
            .and(same_inputs, changed)
            .expect("overflow components are Boolean")
    }
}

struct Query {
    arena: TermArena,
    assertion: TermId,
    lhs_symbol: SymbolId,
    rhs_symbol: SymbolId,
}

fn build_query(width: u8, inverted_carry: bool) -> Query {
    let width32 = u32::from(width);
    let mut arena = TermArena::new();
    let lhs_symbol = arena
        .declare("lhs", Sort::BitVec(width32))
        .expect("fresh A0 lhs symbol is valid");
    let rhs_symbol = arena
        .declare("rhs", Sort::BitVec(width32))
        .expect("fresh A0 rhs symbol is valid");
    let lhs = arena.var(lhs_symbol);
    let rhs = arena.var(rhs_symbol);
    let mut derived = addition(
        &mut SymbolicDomain {
            arena: &mut arena,
            width: width32,
        },
        lhs,
        rhs,
    );
    if inverted_carry {
        derived.carry = arena.not(derived.carry).expect("derived carry is Boolean");
    }

    // These standard overflow predicates are a second construction of the
    // architecture contract. The shared A0 orchestration above deliberately
    // uses explicit high-bit and unsigned-order formulae instead.
    let reference_sum = arena
        .bv_add(lhs, rhs)
        .expect("reference operands have one width");
    let reference_zero_word = arena
        .bv_const(width32, 0)
        .expect("A0 width is a valid bit-vector width");
    let reference_zero = arena
        .eq(reference_sum, reference_zero_word)
        .expect("reference zero operands have one sort");
    let reference_negative = high_bit(&mut arena, width32, reference_sum);
    let reference_carry = arena
        .bv_uaddo(lhs, rhs)
        .expect("reference operands have one width");
    let reference_overflow = arena
        .bv_saddo(lhs, rhs)
        .expect("reference operands have one width");

    let pairs = [
        (derived.result, reference_sum),
        (derived.zero, reference_zero),
        (derived.negative, reference_negative),
        (derived.carry, reference_carry),
        (derived.overflow, reference_overflow),
    ];
    let mut all_equal = arena.bool_const(true);
    for (actual, expected) in pairs {
        let equal = arena
            .eq(actual, expected)
            .expect("each architecture result pair has one sort");
        all_equal = arena
            .and(all_equal, equal)
            .expect("architecture equalities are Boolean");
    }
    let assertion = arena
        .not(all_equal)
        .expect("the architecture conjunction is Boolean");
    Query {
        arena,
        assertion,
        lhs_symbol,
        rhs_symbol,
    }
}

fn high_bit(arena: &mut TermArena, width: u32, word: TermId) -> TermId {
    let bit = arena
        .extract(width - 1, width - 1, word)
        .expect("A0 word has a most-significant bit");
    let one = arena.bv_const(1, 1).expect("one-bit constant is valid");
    arena.eq(bit, one).expect("extracted bit is one bit wide")
}

/// Produces certificates for all eight supported A0 widths.
///
/// # Errors
///
/// Returns a categorized error if the package is stale, a proof cannot be
/// produced and checked, or the required mutation model does not replay.
pub fn symbolic_addition_report(
    package_path: &Path,
) -> Result<SymbolicAdditionReport, EvidenceError> {
    load_semantic_package(package_path)?;
    let package_bytes = fs::read(package_path)?;
    let mut proofs = Vec::with_capacity(WIDTHS.len());
    for width in WIDTHS {
        let query = build_query(width, false);
        let proof = match export_qf_bv_unsat_proof(&query.arena, &[query.assertion])
            .map_err(|error| EvidenceError::SemanticMismatch(error.to_string()))?
        {
            UnsatProofOutcome::Proved(proof) => proof,
            UnsatProofOutcome::Satisfiable => {
                return Err(EvidenceError::SemanticMismatch(format!(
                    "symbolic addition contract has a width-{width} counterexample"
                )));
            }
            UnsatProofOutcome::Inconclusive => {
                return Err(EvidenceError::SemanticMismatch(format!(
                    "symbolic addition proof was inconclusive at width {width}"
                )));
            }
        };
        if !proof
            .recheck_for_bool_terms(&query.arena, &[query.assertion])
            .map_err(|error| EvidenceError::SemanticMismatch(error.to_string()))?
        {
            return Err(EvidenceError::SemanticMismatch(format!(
                "saved width-{width} certificate did not bind to its Boolean term"
            )));
        }
        proofs.push(saved_proof(width, &query.arena, query.assertion, &proof));
    }
    let inverted_carry_counterexample = mutation_counterexample()?;
    Ok(SymbolicAdditionReport {
        schema: SCHEMA.to_owned(),
        semantic_package_sha256: sha256_hex(&package_bytes),
        proofs,
        inverted_carry_counterexample,
    })
}

/// Rebuilds source terms and checks every saved certificate and counterexample.
///
/// # Errors
///
/// Returns a categorized error for stale metadata, malformed artifacts,
/// certificate failure, or a counterexample that does not concretely replay.
pub fn check_symbolic_addition(
    package_path: &Path,
    report_path: &Path,
) -> Result<SymbolicAdditionReport, EvidenceError> {
    load_semantic_package(package_path)?;
    let report: SymbolicAdditionReport = serde_json::from_slice(&fs::read(report_path)?)?;
    if report.schema != SCHEMA
        || report.semantic_package_sha256 != sha256_hex(&fs::read(package_path)?)
    {
        return Err(EvidenceError::SemanticMismatch(
            "symbolic addition metadata does not match the semantic package".to_owned(),
        ));
    }
    if report.proofs.len() != WIDTHS.len() {
        return Err(EvidenceError::SemanticMismatch(
            "symbolic addition report does not cover all A0 widths".to_owned(),
        ));
    }
    for (&width, saved) in WIDTHS.iter().zip(&report.proofs) {
        if saved.width != width {
            return Err(EvidenceError::SemanticMismatch(
                "symbolic addition widths are not canonical".to_owned(),
            ));
        }
        let query = build_query(width, false);
        if saved.assertion_sha256 != assertion_digest(&query.arena, query.assertion) {
            return Err(EvidenceError::SemanticMismatch(format!(
                "width-{width} assertion digest differs"
            )));
        }
        let proof = UnsatProof {
            dimacs: saved.dimacs.clone(),
            drat: saved.drat.clone(),
            lrat: saved.lrat.clone(),
        };
        if !proof
            .recheck_for_bool_terms(&query.arena, &[query.assertion])
            .map_err(|error| EvidenceError::SemanticMismatch(error.to_string()))?
        {
            return Err(EvidenceError::SemanticMismatch(format!(
                "width-{width} certificate failed source-term replay"
            )));
        }
        if proof
            .recheck_lrat()
            .map_err(|error| EvidenceError::SemanticMismatch(error.to_string()))?
            != Some(true)
        {
            return Err(EvidenceError::SemanticMismatch(format!(
                "width-{width} certificate lacks a valid LRAT replay"
            )));
        }
    }
    if report.inverted_carry_counterexample != mutation_counterexample()? {
        return Err(EvidenceError::SemanticMismatch(
            "inverted-carry counterexample did not replay".to_owned(),
        ));
    }
    Ok(report)
}

/// Requires an inverted symbolic carry to be satisfiable and concretely replayable.
///
/// # Errors
///
/// Returns `semantic-mismatch` when the intended mutation is detected and
/// `control-failure` if the faulty carry is unexpectedly accepted.
pub fn check_symbolic_addition_inverted_carry_control(
    package_path: &Path,
    report_path: &Path,
) -> Result<(), EvidenceError> {
    let report = check_symbolic_addition(package_path, report_path)?;
    if report.inverted_carry_counterexample.concrete_carry
        == report.inverted_carry_counterexample.mutated_carry
    {
        return Err(EvidenceError::ControlFailure(
            "inverted carry was accepted by concrete replay".to_owned(),
        ));
    }
    Err(EvidenceError::SemanticMismatch(
        "inverted symbolic carry has a replayed satisfying model".to_owned(),
    ))
}

fn mutation_counterexample() -> Result<SymbolicCounterexample, EvidenceError> {
    let query = build_query(8, true);
    match export_qf_bv_unsat_proof(&query.arena, &[query.assertion])
        .map_err(|error| EvidenceError::SemanticMismatch(error.to_string()))?
    {
        UnsatProofOutcome::Satisfiable => {}
        UnsatProofOutcome::Proved(_) => {
            return Err(EvidenceError::ControlFailure(
                "inverted carry mutation was unexpectedly unsatisfiable".to_owned(),
            ));
        }
        UnsatProofOutcome::Inconclusive => {
            return Err(EvidenceError::ControlFailure(
                "inverted carry mutation was inconclusive".to_owned(),
            ));
        }
    }
    let (lhs, rhs) = finite_mutation_model(&query)?;
    replay_counterexample(lhs, rhs)
}

fn finite_mutation_model(query: &Query) -> Result<(u64, u64), EvidenceError> {
    for lhs in 0_u64..=u64::from(u8::MAX) {
        for rhs in 0_u64..=u64::from(u8::MAX) {
            let mut assignment = Assignment::new();
            assignment.set(
                query.lhs_symbol,
                Value::Bv {
                    width: 8,
                    value: u128::from(lhs),
                },
            );
            assignment.set(
                query.rhs_symbol,
                Value::Bv {
                    width: 8,
                    value: u128::from(rhs),
                },
            );
            let value = eval(&query.arena, query.assertion, &assignment)
                .map_err(|error| EvidenceError::SemanticMismatch(error.to_string()))?;
            if value == Value::Bool(true) {
                return Ok((lhs, rhs));
            }
        }
    }
    Err(EvidenceError::ControlFailure(
        "SAT result had no witness in the complete width-eight domain".to_owned(),
    ))
}

fn replay_counterexample(lhs: u64, rhs: u64) -> Result<SymbolicCounterexample, EvidenceError> {
    let instruction = Instruction::Add {
        rd: 2,
        rs1: 0,
        rs2: 1,
    };
    let program = Program::new(
        8,
        word(0)?,
        encode(instruction).map_err(machine_error)?.to_vec(),
    )
    .map_err(machine_error)?;
    let mut state = State::new(8, Memory::zeroed(0), word(0)?).map_err(machine_error)?;
    state.registers[0] = word(lhs)?;
    state.registers[1] = word(rhs)?;
    let next = step(&program, &state);
    let concrete_carry = next.conditions.carry;
    let replayed_through_step = next.registers[2].unsigned() == lhs.wrapping_add(rhs) & 0xff;
    if !replayed_through_step {
        return Err(EvidenceError::ControlFailure(
            "symbolic mutation witness did not replay through encoded A0 add".to_owned(),
        ));
    }
    Ok(SymbolicCounterexample {
        width: 8,
        lhs,
        rhs,
        concrete_carry,
        mutated_carry: !concrete_carry,
        replayed_through_step,
    })
}

fn word(value: u64) -> Result<Word, EvidenceError> {
    Word::new(8, value).map_err(machine_error)
}

fn machine_error(error: impl core::fmt::Debug) -> EvidenceError {
    EvidenceError::SemanticMismatch(format!("{error:?}"))
}

fn saved_proof(
    width: u8,
    arena: &TermArena,
    assertion: TermId,
    proof: &UnsatProof,
) -> SymbolicAdditionWidthProof {
    SymbolicAdditionWidthProof {
        width,
        assertion_sha256: assertion_digest(arena, assertion),
        dimacs: proof.dimacs.clone(),
        drat: proof.drat.clone(),
        lrat: proof.lrat.clone(),
    }
}

fn assertion_digest(arena: &TermArena, assertion: TermId) -> String {
    sha256_hex(render(arena, assertion).as_bytes())
}

fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut output = String::with_capacity(64);
    for byte in digest {
        use core::fmt::Write as _;
        write!(&mut output, "{byte:02x}").expect("writing to String cannot fail");
    }
    output
}
