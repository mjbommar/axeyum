//! Deterministic proof-carrying synthesis for Boolean multiplicative complexity.
//!
//! A circuit of multiplicative complexity at most `k` has a complete normal
//! form: gate `g` ANDs two affine functions of the primary inputs and earlier
//! AND outputs, and every circuit output is an affine function of the inputs
//! and all `k` AND outputs. XOR, NOT, constants, and fanout are free in this
//! metric. This module encodes that normal form for every truth-table row.
//!
//! SAT models are lifted to the portable circuit format and exhaustively
//! replayed by `axeyum-cas`. UNSAT is returned only with a DRAT proof accepted
//! by Axeyum's independent checker.

use std::collections::BTreeMap;
use std::time::Instant;

use axeyum_cas::boolean_anf::{
    BooleanAnfError, BooleanAnfLimits, BooleanAnfPolynomial, BooleanAnfSystem,
};
use axeyum_cas::boolean_circuit::{
    BOOLEAN_CIRCUIT_SCHEMA, BooleanCircuitArtifact, BooleanCircuitCheck, BooleanCircuitLimits,
    BooleanGate, BooleanGateOp, check_boolean_circuit,
};
use axeyum_cnf::{
    CnfAssignment, CnfClause, CnfFormula, CnfLit, CnfVar, DratStep, ProofSolveOutcome,
    check_drat_backward, solve_with_drat_proof_with_limits,
};

/// A complete vector Boolean truth table and an AND-gate budget.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MultiplicativeSynthesisProblem {
    /// Primary inputs, interpreted most-significant bit first.
    pub input_bits: usize,
    /// Vector output width, interpreted most-significant bit first.
    pub output_bits: usize,
    /// Output integer for every ascending input integer.
    pub truth_table: Vec<u64>,
    /// Number of AND gates in the padded normal form (equivalently, at most this many).
    pub and_gates: usize,
}

/// Deterministic resource admission for synthesis encoding and search.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MultiplicativeSynthesisLimits {
    /// Largest admitted input width; the encoding has `2^n` semantic rows.
    pub max_input_bits: usize,
    /// Largest admitted output width.
    pub max_output_bits: usize,
    /// Largest admitted AND budget.
    pub max_and_gates: usize,
    /// Largest encoded variable count.
    pub max_variables: usize,
    /// Largest encoded clause count.
    pub max_clauses: usize,
    /// Deterministic CDCL conflict limit.
    pub max_conflicts: usize,
}

/// Completeness-preserving reductions for the multiplicative normal form.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct MultiplicativeEncodingOptions {
    /// Remove constants before AND gates and pin output constants to `S(0)`.
    ///
    /// This uses Zhang--Huang Proposition 1 after translating each coordinate
    /// by its constant term. It changes representation, not the gate budget.
    pub eliminate_internal_constants: bool,
    /// Break operand-swap symmetry by requiring the first input coefficient of
    /// the left affine form to be at least the corresponding right coefficient.
    pub partial_operand_order: bool,
}

impl Default for MultiplicativeSynthesisLimits {
    fn default() -> Self {
        Self {
            max_input_bits: 10,
            max_output_bits: 64,
            max_and_gates: 32,
            max_variables: 5_000_000,
            max_clauses: 25_000_000,
            max_conflicts: 10_000_000,
        }
    }
}

/// Malformed or inadmissible synthesis input, or a violated internal handoff.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MultiplicativeSynthesisError {
    /// This artifact format needs at least one primary input to spell constants.
    ZeroInputs,
    /// A stable resource ceiling was exceeded.
    LimitExceeded {
        /// Resource name.
        resource: &'static str,
        /// First observed value known to exceed the ceiling.
        observed: usize,
        /// Configured ceiling.
        limit: usize,
    },
    /// Truth-table row count differs from `2^input_bits`.
    TruthTableLength {
        /// Required row count.
        expected: usize,
        /// Supplied row count.
        observed: usize,
    },
    /// A truth-table value does not fit the output width.
    TruthTableValueOutOfRange {
        /// Offending row.
        row: usize,
        /// Offending value.
        value: u64,
    },
    /// A CNF model had the wrong length or failed replay.
    InvalidModel(String),
    /// A lifted portable circuit failed independent exhaustive replay.
    LiftedCircuit(String),
    /// The proof-producing solver claimed UNSAT but its proof did not check.
    InvalidUnsatProof,
    /// A portable circuit cannot be represented in the affine-between-ANDs normal form.
    NonMultiplicativeNormalForm(String),
    /// Boolean ANF construction exceeded its domain or resource policy.
    BooleanAnf(BooleanAnfError),
}

impl From<BooleanAnfError> for MultiplicativeSynthesisError {
    fn from(value: BooleanAnfError) -> Self {
        Self::BooleanAnf(value)
    }
}

/// One affine form over constants, primary inputs, and earlier AND outputs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AffineSelection {
    /// Constant coefficient.
    pub constant: bool,
    /// Primary-input coefficients in declared order.
    pub inputs: Vec<bool>,
    /// Earlier-AND coefficients in gate order.
    pub earlier_ands: Vec<bool>,
}

/// A positive multiplicative-complexity witness in the complete normal form.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MultiplicativeCircuitWitness {
    /// Left and right affine operands for each AND gate.
    pub gates: Vec<(AffineSelection, AffineSelection)>,
    /// Affine output forms.
    pub outputs: Vec<AffineSelection>,
}

/// Fully checked synthesis result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MultiplicativeSynthesisOutcome {
    /// A satisfying model lifted to and replayed as a portable circuit.
    Sat(BooleanCircuitArtifact),
    /// The exact deterministic encoding is UNSAT and the DRAT proof checked.
    Unsat {
        /// Formula refuted by `proof`.
        formula: CnfFormula,
        /// Independently checked DRAT refutation.
        proof: Vec<DratStep>,
    },
    /// Conflict policy was exhausted without a verdict.
    ResourceOut,
    /// Wall-clock policy was exhausted without a verdict.
    Interrupted,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct SelectorLayout {
    left: Vec<Vec<usize>>,
    right: Vec<Vec<usize>>,
    outputs: Vec<Vec<usize>>,
}

/// Deterministic CNF plus the private map needed to lift a satisfying model.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MultiplicativeEncoding {
    formula: CnfFormula,
    layout: SelectorLayout,
    problem: MultiplicativeSynthesisProblem,
}

/// Exact selector-level Boolean ANF system for multiplicative synthesis.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MultiplicativeAnfEncoding {
    system: BooleanAnfSystem,
    layout: SelectorLayout,
    problem: MultiplicativeSynthesisProblem,
}

impl MultiplicativeAnfEncoding {
    /// Algebraic equations over the selector coefficients.
    pub fn system(&self) -> &BooleanAnfSystem {
        &self.system
    }

    /// Lift a satisfying selector assignment and independently replay it.
    ///
    /// # Errors
    ///
    /// Refuses a wrong-size or non-satisfying assignment and any circuit that
    /// fails exhaustive truth-table replay.
    pub fn lift_assignment(
        &self,
        assignment: &[bool],
    ) -> Result<BooleanCircuitArtifact, MultiplicativeSynthesisError> {
        if !self.system.evaluate(assignment)? {
            return Err(MultiplicativeSynthesisError::InvalidModel(
                "assignment does not satisfy the ANF synthesis system".to_owned(),
            ));
        }
        lift_selector_assignment(&self.problem, &self.layout, assignment)
    }
}

impl MultiplicativeEncoding {
    /// Exact synthesis formula.
    pub fn formula(&self) -> &CnfFormula {
        &self.formula
    }

    /// Lift a satisfying CNF assignment to a portable circuit and replay it.
    ///
    /// # Errors
    ///
    /// Refuses a wrong-size or non-satisfying model and any lifted circuit that
    /// does not pass the independent complete truth-table checker.
    pub fn lift_model(
        &self,
        model: &CnfAssignment,
    ) -> Result<BooleanCircuitArtifact, MultiplicativeSynthesisError> {
        if model.values().len() != self.formula.variable_count() {
            return Err(MultiplicativeSynthesisError::InvalidModel(format!(
                "model has {} values for {} variables",
                model.values().len(),
                self.formula.variable_count()
            )));
        }
        if self.formula.evaluate(model.values()) != Ok(true) {
            return Err(MultiplicativeSynthesisError::InvalidModel(
                "model does not satisfy the synthesis formula".to_owned(),
            ));
        }

        lift_selector_assignment(&self.problem, &self.layout, model.values())
    }

    /// Add unit clauses pinning every selector to a positive witness.
    ///
    /// The returned formula retains all row-semantics constraints, so solving
    /// it checks that the witness inhabits this exact encoding.
    ///
    /// # Errors
    ///
    /// Refuses a witness whose gate, output, or affine-basis dimensions do not
    /// exactly match this encoding.
    pub fn formula_with_witness(
        &self,
        witness: &MultiplicativeCircuitWitness,
    ) -> Result<CnfFormula, MultiplicativeSynthesisError> {
        if witness.gates.len() != self.problem.and_gates
            || witness.outputs.len() != self.problem.output_bits
        {
            return Err(MultiplicativeSynthesisError::NonMultiplicativeNormalForm(
                "witness gate or output count disagrees with the problem".to_owned(),
            ));
        }
        let mut formula = self.formula.clone();
        for (gate, (left, right)) in witness.gates.iter().enumerate() {
            pin_affine(
                &mut formula,
                &self.layout.left[gate],
                left,
                self.problem.input_bits,
                gate,
            )?;
            pin_affine(
                &mut formula,
                &self.layout.right[gate],
                right,
                self.problem.input_bits,
                gate,
            )?;
        }
        for (output, affine) in witness.outputs.iter().enumerate() {
            pin_affine(
                &mut formula,
                &self.layout.outputs[output],
                affine,
                self.problem.input_bits,
                self.problem.and_gates,
            )?;
        }
        Ok(formula)
    }
}

fn lift_selector_assignment(
    problem: &MultiplicativeSynthesisProblem,
    layout: &SelectorLayout,
    values: &[bool],
) -> Result<BooleanCircuitArtifact, MultiplicativeSynthesisError> {
    let mut gates = Vec::new();
    let inputs: Vec<String> = (0..problem.input_bits)
        .map(|index| format!("x{index}"))
        .collect();
    let mut nonlinear = Vec::<String>::new();
    for gate_index in 0..problem.and_gates {
        let left = emit_affine(
            &format!("a{gate_index}_left"),
            &inputs,
            &nonlinear,
            &layout.left[gate_index],
            values,
            &mut gates,
        );
        let right = emit_affine(
            &format!("a{gate_index}_right"),
            &inputs,
            &nonlinear,
            &layout.right[gate_index],
            values,
            &mut gates,
        );
        let output = format!("a{gate_index}");
        gates.push(BooleanGate {
            output: output.clone(),
            op: BooleanGateOp::And,
            inputs: vec![left, right],
        });
        nonlinear.push(output);
    }
    let outputs = layout
        .outputs
        .iter()
        .enumerate()
        .map(|(index, coefficients)| {
            emit_affine(
                &format!("y{index}"),
                &inputs,
                &nonlinear,
                coefficients,
                values,
                &mut gates,
            )
        })
        .collect();
    let artifact = BooleanCircuitArtifact {
        schema: BOOLEAN_CIRCUIT_SCHEMA.to_owned(),
        inputs,
        gates,
        outputs,
        truth_table: problem.truth_table.clone(),
    };
    match check_boolean_circuit(&artifact, BooleanCircuitLimits::default()) {
        Ok(BooleanCircuitCheck::Verified { .. }) => Ok(artifact),
        other => Err(MultiplicativeSynthesisError::LiftedCircuit(format!(
            "{other:?}"
        ))),
    }
}

fn pin_affine(
    formula: &mut CnfFormula,
    selectors: &[usize],
    affine: &AffineSelection,
    input_bits: usize,
    earlier_ands: usize,
) -> Result<(), MultiplicativeSynthesisError> {
    if affine.inputs.len() != input_bits || affine.earlier_ands.len() != earlier_ands {
        return Err(MultiplicativeSynthesisError::NonMultiplicativeNormalForm(
            "affine coefficient width disagrees with its gate position".to_owned(),
        ));
    }
    let values = std::iter::once(affine.constant)
        .chain(affine.inputs.iter().copied())
        .chain(affine.earlier_ands.iter().copied());
    for (&selector, value) in selectors.iter().zip(values) {
        let variable = CnfVar::new(selector)
            .map_err(|error| MultiplicativeSynthesisError::InvalidModel(format!("{error:?}")))?;
        let literal = CnfLit::positive(variable);
        formula
            .add_clause(CnfClause::new(vec![if value {
                literal
            } else {
                literal.negated()
            }]))
            .map_err(|error| MultiplicativeSynthesisError::InvalidModel(format!("{error:?}")))?;
    }
    Ok(())
}

fn xor_forms(left: &[bool], right: &[bool], invert: bool) -> Vec<bool> {
    left.iter()
        .zip(right)
        .enumerate()
        .map(|(index, (&a, &b))| a ^ b ^ (invert && index == 0))
        .collect()
}

fn affine_from_bits(bits: &[bool], inputs: usize, earlier: usize) -> AffineSelection {
    AffineSelection {
        constant: bits[0],
        inputs: bits[1..=inputs].to_vec(),
        earlier_ands: bits[1 + inputs..1 + inputs + earlier].to_vec(),
    }
}

/// Normalize an already replayable XOR/NOT/AND circuit into the complete
/// multiplicative-complexity witness form.
///
/// # Errors
///
/// Refuses malformed circuits, unsupported OR/NAND/NOR gates, unexpected AND
/// count, or any missing wire. The source circuit is exhaustively replayed
/// before its algebraic normal form is returned.
pub fn normalize_multiplicative_witness(
    artifact: &BooleanCircuitArtifact,
    expected_and_gates: usize,
) -> Result<MultiplicativeCircuitWitness, MultiplicativeSynthesisError> {
    if !matches!(
        check_boolean_circuit(artifact, BooleanCircuitLimits::default()),
        Ok(BooleanCircuitCheck::Verified { .. })
    ) {
        return Err(MultiplicativeSynthesisError::NonMultiplicativeNormalForm(
            "source circuit does not replay".to_owned(),
        ));
    }
    let width = 1 + artifact.inputs.len() + expected_and_gates;
    let mut wires = BTreeMap::<&str, Vec<bool>>::new();
    for (index, input) in artifact.inputs.iter().enumerate() {
        let mut form = vec![false; width];
        form[1 + index] = true;
        wires.insert(input, form);
    }
    let mut gates = Vec::new();
    for gate in &artifact.gates {
        let operands = gate
            .inputs
            .iter()
            .map(|wire| {
                wires.get(wire.as_str()).cloned().ok_or_else(|| {
                    MultiplicativeSynthesisError::NonMultiplicativeNormalForm(format!(
                        "undefined wire {wire}"
                    ))
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let form = match gate.op {
            BooleanGateOp::Xor => xor_forms(&operands[0], &operands[1], false),
            BooleanGateOp::Xnor => xor_forms(&operands[0], &operands[1], true),
            BooleanGateOp::Not => {
                let mut form = operands[0].clone();
                form[0] ^= true;
                form
            }
            BooleanGateOp::And => {
                let index = gates.len();
                if index >= expected_and_gates {
                    return Err(MultiplicativeSynthesisError::NonMultiplicativeNormalForm(
                        "source has too many AND gates".to_owned(),
                    ));
                }
                gates.push((
                    affine_from_bits(&operands[0], artifact.inputs.len(), index),
                    affine_from_bits(&operands[1], artifact.inputs.len(), index),
                ));
                let mut form = vec![false; width];
                form[1 + artifact.inputs.len() + index] = true;
                form
            }
            BooleanGateOp::Or | BooleanGateOp::Nand | BooleanGateOp::Nor => {
                return Err(MultiplicativeSynthesisError::NonMultiplicativeNormalForm(
                    format!("gate {} uses {:?}", gate.output, gate.op),
                ));
            }
        };
        wires.insert(&gate.output, form);
    }
    if gates.len() != expected_and_gates {
        return Err(MultiplicativeSynthesisError::NonMultiplicativeNormalForm(
            format!(
                "source has {} AND gates, expected {expected_and_gates}",
                gates.len()
            ),
        ));
    }
    let outputs = artifact
        .outputs
        .iter()
        .map(|wire| {
            wires
                .get(wire.as_str())
                .map(|bits| affine_from_bits(bits, artifact.inputs.len(), expected_and_gates))
                .ok_or_else(|| {
                    MultiplicativeSynthesisError::NonMultiplicativeNormalForm(format!(
                        "undefined output {wire}"
                    ))
                })
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(MultiplicativeCircuitWitness { gates, outputs })
}

#[derive(Debug)]
struct RawBuilder {
    variables: usize,
    clauses: Vec<Vec<(usize, bool)>>,
    limits: MultiplicativeSynthesisLimits,
}

impl RawBuilder {
    fn new(limits: MultiplicativeSynthesisLimits) -> Self {
        Self {
            variables: 0,
            clauses: Vec::new(),
            limits,
        }
    }

    fn variable(&mut self) -> Result<usize, MultiplicativeSynthesisError> {
        self.variables = self.variables.saturating_add(1);
        if self.variables > self.limits.max_variables {
            return Err(MultiplicativeSynthesisError::LimitExceeded {
                resource: "variables",
                observed: self.variables,
                limit: self.limits.max_variables,
            });
        }
        Ok(self.variables - 1)
    }

    fn clause(&mut self, literals: &[(usize, bool)]) -> Result<(), MultiplicativeSynthesisError> {
        self.clauses.push(literals.to_vec());
        if self.clauses.len() > self.limits.max_clauses {
            return Err(MultiplicativeSynthesisError::LimitExceeded {
                resource: "clauses",
                observed: self.clauses.len(),
                limit: self.limits.max_clauses,
            });
        }
        Ok(())
    }

    fn and_equiv(
        &mut self,
        output: usize,
        left: usize,
        right: usize,
    ) -> Result<(), MultiplicativeSynthesisError> {
        self.clause(&[(left, true), (right, true), (output, false)])?;
        self.clause(&[(left, false), (output, true)])?;
        self.clause(&[(right, false), (output, true)])
    }

    fn xor_equiv(
        &mut self,
        output: usize,
        left: usize,
        right: usize,
    ) -> Result<(), MultiplicativeSynthesisError> {
        self.clause(&[(left, true), (right, true), (output, true)])?;
        self.clause(&[(left, false), (right, false), (output, true)])?;
        self.clause(&[(left, false), (right, true), (output, false)])?;
        self.clause(&[(left, true), (right, false), (output, false)])
    }

    fn parity_equals(
        &mut self,
        terms: &[usize],
        value: bool,
    ) -> Result<(), MultiplicativeSynthesisError> {
        let final_variable = match terms {
            [] => {
                if value {
                    self.clause(&[])?;
                }
                return Ok(());
            }
            [only] => *only,
            [first, second, rest @ ..] => {
                let mut accumulator = self.variable()?;
                self.xor_equiv(accumulator, *first, *second)?;
                for term in rest {
                    let next = self.variable()?;
                    self.xor_equiv(next, accumulator, *term)?;
                    accumulator = next;
                }
                accumulator
            }
        };
        self.clause(&[(final_variable, !value)])
    }

    fn finish(self) -> Result<CnfFormula, MultiplicativeSynthesisError> {
        let mut formula = CnfFormula::new(self.variables);
        for clause in self.clauses {
            let literals = clause
                .into_iter()
                .map(|(index, negated)| {
                    CnfVar::new(index)
                        .map(|variable| {
                            let literal = CnfLit::positive(variable);
                            if negated { literal.negated() } else { literal }
                        })
                        .map_err(|error| {
                            MultiplicativeSynthesisError::InvalidModel(format!("{error:?}"))
                        })
                })
                .collect::<Result<Vec<_>, _>>()?;
            formula
                .add_clause(CnfClause::new(literals))
                .map_err(|error| {
                    MultiplicativeSynthesisError::InvalidModel(format!("{error:?}"))
                })?;
        }
        Ok(formula)
    }
}

fn allocate_vector(
    builder: &mut RawBuilder,
    count: usize,
) -> Result<Vec<usize>, MultiplicativeSynthesisError> {
    (0..count).map(|_| builder.variable()).collect()
}

fn validate_problem(
    problem: &MultiplicativeSynthesisProblem,
    limits: MultiplicativeSynthesisLimits,
) -> Result<usize, MultiplicativeSynthesisError> {
    if problem.input_bits == 0 {
        return Err(MultiplicativeSynthesisError::ZeroInputs);
    }
    for (resource, observed, limit) in [
        ("input_bits", problem.input_bits, limits.max_input_bits),
        ("output_bits", problem.output_bits, limits.max_output_bits),
        ("and_gates", problem.and_gates, limits.max_and_gates),
    ] {
        if observed > limit {
            return Err(MultiplicativeSynthesisError::LimitExceeded {
                resource,
                observed,
                limit,
            });
        }
    }
    let rows = 1_usize
        .checked_shl(u32::try_from(problem.input_bits).unwrap_or(u32::MAX))
        .unwrap_or(usize::MAX);
    if problem.truth_table.len() != rows {
        return Err(MultiplicativeSynthesisError::TruthTableLength {
            expected: rows,
            observed: problem.truth_table.len(),
        });
    }
    let output_limit = if problem.output_bits == 64 {
        None
    } else {
        Some(1_u64 << problem.output_bits)
    };
    if let Some((row, &value)) = problem
        .truth_table
        .iter()
        .enumerate()
        .find(|&(_, value)| output_limit.is_some_and(|limit| *value >= limit))
    {
        return Err(MultiplicativeSynthesisError::TruthTableValueOutOfRange { row, value });
    }
    Ok(rows)
}

fn row_input(problem: &MultiplicativeSynthesisProblem, row: usize, input: usize) -> bool {
    let shift = problem.input_bits - input - 1;
    ((row >> shift) & 1) != 0
}

fn affine_terms(
    builder: &mut RawBuilder,
    coefficients: &[usize],
    earlier_values: &[usize],
    problem: &MultiplicativeSynthesisProblem,
    row: usize,
) -> Result<Vec<usize>, MultiplicativeSynthesisError> {
    let mut terms = vec![coefficients[0]];
    for input in 0..problem.input_bits {
        if row_input(problem, row, input) {
            terms.push(coefficients[1 + input]);
        }
    }
    for (earlier, &value) in earlier_values.iter().enumerate() {
        let product = builder.variable()?;
        builder.and_equiv(
            product,
            coefficients[1 + problem.input_bits + earlier],
            value,
        )?;
        terms.push(product);
    }
    Ok(terms)
}

#[derive(Debug, Clone, Copy)]
enum AlgebraicNode {
    Constant(bool),
    Variable(usize),
}

fn algebraic_and(
    builder: &mut RawBuilder,
    left: AlgebraicNode,
    right: AlgebraicNode,
) -> Result<AlgebraicNode, MultiplicativeSynthesisError> {
    match (left, right) {
        (AlgebraicNode::Constant(false), _) | (_, AlgebraicNode::Constant(false)) => {
            Ok(AlgebraicNode::Constant(false))
        }
        (AlgebraicNode::Constant(true), node) | (node, AlgebraicNode::Constant(true)) => Ok(node),
        (AlgebraicNode::Variable(a), AlgebraicNode::Variable(b)) if a == b => {
            Ok(AlgebraicNode::Variable(a))
        }
        (AlgebraicNode::Variable(a), AlgebraicNode::Variable(b)) => {
            let output = builder.variable()?;
            builder.and_equiv(output, a, b)?;
            Ok(AlgebraicNode::Variable(output))
        }
    }
}

fn algebraic_xor(
    builder: &mut RawBuilder,
    left: AlgebraicNode,
    right: AlgebraicNode,
) -> Result<AlgebraicNode, MultiplicativeSynthesisError> {
    match (left, right) {
        (AlgebraicNode::Constant(false), node) | (node, AlgebraicNode::Constant(false)) => Ok(node),
        (AlgebraicNode::Constant(a), AlgebraicNode::Constant(b)) => {
            Ok(AlgebraicNode::Constant(a ^ b))
        }
        (AlgebraicNode::Variable(a), AlgebraicNode::Variable(b)) if a == b => {
            Ok(AlgebraicNode::Constant(false))
        }
        (AlgebraicNode::Variable(a), AlgebraicNode::Variable(b)) => {
            let output = builder.variable()?;
            builder.xor_equiv(output, a, b)?;
            Ok(AlgebraicNode::Variable(output))
        }
        (AlgebraicNode::Constant(true), AlgebraicNode::Variable(variable))
        | (AlgebraicNode::Variable(variable), AlgebraicNode::Constant(true)) => {
            let output = builder.variable()?;
            // output = !variable.
            builder.clause(&[(variable, false), (output, false)])?;
            builder.clause(&[(variable, true), (output, true)])?;
            Ok(AlgebraicNode::Variable(output))
        }
    }
}

fn algebraic_affine(
    builder: &mut RawBuilder,
    coefficients: &[usize],
    prior: &[Vec<AlgebraicNode>],
    input_bits: usize,
    monomials: usize,
) -> Result<Vec<AlgebraicNode>, MultiplicativeSynthesisError> {
    let mut result = vec![AlgebraicNode::Constant(false); monomials];
    result[0] = AlgebraicNode::Variable(coefficients[0]);
    for input in 0..input_bits {
        let mask = 1 << (input_bits - input - 1);
        result[mask] = algebraic_xor(
            builder,
            result[mask],
            AlgebraicNode::Variable(coefficients[1 + input]),
        )?;
    }
    for (gate, polynomial) in prior.iter().enumerate() {
        let selector = AlgebraicNode::Variable(coefficients[1 + input_bits + gate]);
        for (mask, &coefficient) in polynomial.iter().enumerate() {
            let selected = algebraic_and(builder, selector, coefficient)?;
            result[mask] = algebraic_xor(builder, result[mask], selected)?;
        }
    }
    Ok(result)
}

fn algebraic_product(
    builder: &mut RawBuilder,
    left: &[AlgebraicNode],
    right: &[AlgebraicNode],
) -> Result<Vec<AlgebraicNode>, MultiplicativeSynthesisError> {
    let mut result = vec![AlgebraicNode::Constant(false); left.len()];
    for (left_mask, &left_coefficient) in left.iter().enumerate() {
        for (right_mask, &right_coefficient) in right.iter().enumerate() {
            let product = algebraic_and(builder, left_coefficient, right_coefficient)?;
            let mask = left_mask | right_mask;
            result[mask] = algebraic_xor(builder, result[mask], product)?;
        }
    }
    Ok(result)
}

fn truth_coordinate_anf(problem: &MultiplicativeSynthesisProblem, output: usize) -> Vec<bool> {
    let shift = problem.output_bits - output - 1;
    let mut coefficients: Vec<bool> = problem
        .truth_table
        .iter()
        .map(|value| ((value >> shift) & 1) != 0)
        .collect();
    for bit in 0..problem.input_bits {
        for mask in 0..coefficients.len() {
            if (mask & (1 << bit)) != 0 {
                coefficients[mask] ^= coefficients[mask ^ (1 << bit)];
            }
        }
    }
    coefficients
}

fn selector_layout(problem: &MultiplicativeSynthesisProblem) -> (SelectorLayout, usize) {
    let mut next = 0;
    let mut vector = |count: usize| {
        let start = next;
        next += count;
        (start..next).collect::<Vec<_>>()
    };
    let mut left = Vec::new();
    let mut right = Vec::new();
    for gate in 0..problem.and_gates {
        let basis = 1 + problem.input_bits + gate;
        left.push(vector(basis));
        right.push(vector(basis));
    }
    let outputs = (0..problem.output_bits)
        .map(|_| vector(1 + problem.input_bits + problem.and_gates))
        .collect();
    (
        SelectorLayout {
            left,
            right,
            outputs,
        },
        next,
    )
}

fn add_nonzero_equation(
    system: &mut BooleanAnfSystem,
    equation: BooleanAnfPolynomial,
) -> Result<(), MultiplicativeSynthesisError> {
    if !equation.is_zero() {
        system.add_equation(equation)?;
    }
    Ok(())
}

fn anf_affine_coefficient_equation(
    selectors: &[usize],
    prior_coefficients: &[Vec<usize>],
    value_variable: usize,
    mask: usize,
    input_bits: usize,
    max_monomials: usize,
) -> Result<BooleanAnfPolynomial, MultiplicativeSynthesisError> {
    let mut equation = BooleanAnfPolynomial::variable(value_variable);
    if mask == 0 {
        equation.xor_assign(&BooleanAnfPolynomial::variable(selectors[0]));
    }
    for input in 0..input_bits {
        if mask == 1 << (input_bits - input - 1) {
            equation.xor_assign(&BooleanAnfPolynomial::variable(selectors[1 + input]));
        }
    }
    for (gate, coefficients) in prior_coefficients.iter().enumerate() {
        let selector = BooleanAnfPolynomial::variable(selectors[1 + input_bits + gate]);
        let coefficient = BooleanAnfPolynomial::variable(coefficients[mask]);
        equation.xor_assign(&selector.product(&coefficient, max_monomials)?);
    }
    Ok(equation)
}

fn add_anf_gate_equations(
    system: &mut BooleanAnfSystem,
    selectors: (&[usize], &[usize]),
    prior_coefficients: &[Vec<usize>],
    first_variable: usize,
    monomial_masks: usize,
    input_bits: usize,
    max_monomials: usize,
) -> Result<(Vec<usize>, usize), MultiplicativeSynthesisError> {
    let left: Vec<usize> = (first_variable..first_variable + monomial_masks).collect();
    let right_start = first_variable + monomial_masks;
    let right: Vec<usize> = (right_start..right_start + monomial_masks).collect();
    let output_start = right_start + monomial_masks;
    let output: Vec<usize> = (output_start..output_start + monomial_masks).collect();
    for mask in 0..monomial_masks {
        let equation = anf_affine_coefficient_equation(
            selectors.0,
            prior_coefficients,
            left[mask],
            mask,
            input_bits,
            max_monomials,
        )?;
        add_nonzero_equation(system, equation)?;
        let equation = anf_affine_coefficient_equation(
            selectors.1,
            prior_coefficients,
            right[mask],
            mask,
            input_bits,
            max_monomials,
        )?;
        add_nonzero_equation(system, equation)?;

        let mut product_equation = BooleanAnfPolynomial::variable(output[mask]);
        for (left_mask, &left_variable) in left.iter().enumerate() {
            for (right_mask, &right_variable) in right.iter().enumerate() {
                if left_mask | right_mask == mask {
                    let left_term = BooleanAnfPolynomial::variable(left_variable);
                    let right_term = BooleanAnfPolynomial::variable(right_variable);
                    product_equation.xor_assign(&left_term.product(&right_term, max_monomials)?);
                }
            }
        }
        add_nonzero_equation(system, product_equation)?;
    }
    Ok((output, output_start + monomial_masks))
}

/// Build the exact selector-level Boolean ANF system used by algebraic
/// multiplicative-complexity tools such as Bosphorus.
///
/// Unlike [`encode_multiplicative_circuit_anf`], this introduces named ANF
/// coefficients for every gate operand and output instead of Tseitin-encoding
/// Boolean operations or fully expanding the selector polynomials. The sparse
/// quadratic equation DAG is equisatisfiable by construction and exposes its
/// algebraic structure to a preprocessor. Any SAT model must still pass
/// [`MultiplicativeAnfEncoding::lift_assignment`]; UNSAT from an external
/// transformation is not trusted without a checked equivalence route.
///
/// # Errors
///
/// Returns typed malformed-input, Boolean-ANF, or resource-admission errors.
pub fn encode_multiplicative_anf_system(
    problem: &MultiplicativeSynthesisProblem,
    limits: MultiplicativeSynthesisLimits,
    options: MultiplicativeEncodingOptions,
) -> Result<MultiplicativeAnfEncoding, MultiplicativeSynthesisError> {
    let monomial_masks = validate_problem(problem, limits)?;
    let (layout, selector_variables) = selector_layout(problem);
    let auxiliary_variables = problem
        .and_gates
        .saturating_mul(monomial_masks)
        .saturating_mul(3);
    let variable_count = selector_variables.saturating_add(auxiliary_variables);
    let anf_limits = BooleanAnfLimits {
        max_variables: limits.max_variables,
        max_monomials_per_polynomial: limits.max_clauses,
        max_equations: limits.max_clauses,
        max_total_monomials: limits.max_clauses,
    };
    let mut system = BooleanAnfSystem::new(variable_count, anf_limits)?;

    if options.eliminate_internal_constants {
        for gate in 0..problem.and_gates {
            add_nonzero_equation(
                &mut system,
                BooleanAnfPolynomial::variable(layout.left[gate][0]),
            )?;
            add_nonzero_equation(
                &mut system,
                BooleanAnfPolynomial::variable(layout.right[gate][0]),
            )?;
        }
        for (output, selectors) in layout.outputs.iter().enumerate() {
            let shift = problem.output_bits - output - 1;
            let mut equation = BooleanAnfPolynomial::variable(selectors[0]);
            if ((problem.truth_table[0] >> shift) & 1) != 0 {
                equation.toggle_constant();
            }
            add_nonzero_equation(&mut system, equation)?;
        }
    }
    if options.partial_operand_order {
        for gate in 0..problem.and_gates {
            let left = BooleanAnfPolynomial::variable(layout.left[gate][1]);
            let right = BooleanAnfPolynomial::variable(layout.right[gate][1]);
            let mut equation = left.product(&right, limits.max_clauses)?;
            equation.xor_assign(&right);
            add_nonzero_equation(&mut system, equation)?;
        }
    }

    let mut next_variable = selector_variables;
    let mut gate_coefficients = Vec::<Vec<usize>>::new();
    for gate in 0..problem.and_gates {
        let (output, next) = add_anf_gate_equations(
            &mut system,
            (&layout.left[gate], &layout.right[gate]),
            &gate_coefficients,
            next_variable,
            monomial_masks,
            problem.input_bits,
            limits.max_clauses,
        )?;
        next_variable = next;
        gate_coefficients.push(output);
    }
    debug_assert_eq!(next_variable, variable_count);
    for output in 0..problem.output_bits {
        for (mask, expected) in truth_coordinate_anf(problem, output)
            .into_iter()
            .enumerate()
        {
            let mut equation = BooleanAnfPolynomial::zero();
            if mask == 0 {
                equation.xor_assign(&BooleanAnfPolynomial::variable(layout.outputs[output][0]));
            }
            for input in 0..problem.input_bits {
                if mask == 1 << (problem.input_bits - input - 1) {
                    equation.xor_assign(&BooleanAnfPolynomial::variable(
                        layout.outputs[output][1 + input],
                    ));
                }
            }
            for (gate, coefficients) in gate_coefficients.iter().enumerate() {
                let selector = BooleanAnfPolynomial::variable(
                    layout.outputs[output][1 + problem.input_bits + gate],
                );
                let coefficient = BooleanAnfPolynomial::variable(coefficients[mask]);
                equation.xor_assign(&selector.product(&coefficient, limits.max_clauses)?);
            }
            if expected {
                equation.toggle_constant();
            }
            add_nonzero_equation(&mut system, equation)?;
        }
    }
    Ok(MultiplicativeAnfEncoding {
        system,
        layout,
        problem: problem.clone(),
    })
}

fn constrain_algebraic_node(
    builder: &mut RawBuilder,
    node: AlgebraicNode,
    expected: bool,
) -> Result<(), MultiplicativeSynthesisError> {
    match node {
        AlgebraicNode::Constant(value) if value == expected => Ok(()),
        AlgebraicNode::Constant(_) => builder.clause(&[]),
        AlgebraicNode::Variable(variable) => builder.clause(&[(variable, !expected)]),
    }
}

fn allocate_selector_layout(
    builder: &mut RawBuilder,
    problem: &MultiplicativeSynthesisProblem,
) -> Result<SelectorLayout, MultiplicativeSynthesisError> {
    let mut left = Vec::new();
    let mut right = Vec::new();
    for gate in 0..problem.and_gates {
        let basis = 1 + problem.input_bits + gate;
        left.push(allocate_vector(builder, basis)?);
        right.push(allocate_vector(builder, basis)?);
    }
    let outputs = (0..problem.output_bits)
        .map(|_| allocate_vector(builder, 1 + problem.input_bits + problem.and_gates))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(SelectorLayout {
        left,
        right,
        outputs,
    })
}

fn apply_encoding_options(
    builder: &mut RawBuilder,
    problem: &MultiplicativeSynthesisProblem,
    layout: &SelectorLayout,
    options: MultiplicativeEncodingOptions,
) -> Result<(), MultiplicativeSynthesisError> {
    if options.eliminate_internal_constants {
        for gate in 0..problem.and_gates {
            builder.clause(&[(layout.left[gate][0], true)])?;
            builder.clause(&[(layout.right[gate][0], true)])?;
        }
        for (output, selectors) in layout.outputs.iter().enumerate() {
            let shift = problem.output_bits - output - 1;
            let constant = ((problem.truth_table[0] >> shift) & 1) != 0;
            builder.clause(&[(selectors[0], !constant)])?;
        }
    }
    if options.partial_operand_order {
        for gate in 0..problem.and_gates {
            builder.clause(&[(layout.left[gate][1], false), (layout.right[gate][1], true)])?;
        }
    }
    Ok(())
}

/// Build Zhang--Huang's algebraic-expression encoding by constraining ANF
/// coefficients directly instead of duplicating wire values for every row.
///
/// The selector layout and accepted circuits are the same as the truth-table
/// backend. SAT models are therefore lifted and exhaustively replayed through
/// the same independent path.
///
/// # Errors
///
/// Returns typed malformed-input or resource-admission errors.
pub fn encode_multiplicative_circuit_anf(
    problem: &MultiplicativeSynthesisProblem,
    limits: MultiplicativeSynthesisLimits,
    options: MultiplicativeEncodingOptions,
) -> Result<MultiplicativeEncoding, MultiplicativeSynthesisError> {
    let monomials = validate_problem(problem, limits)?;
    let mut builder = RawBuilder::new(limits);
    let layout = allocate_selector_layout(&mut builder, problem)?;
    apply_encoding_options(&mut builder, problem, &layout, options)?;

    let mut and_polynomials = Vec::<Vec<AlgebraicNode>>::new();
    for gate in 0..problem.and_gates {
        let left = algebraic_affine(
            &mut builder,
            &layout.left[gate],
            &and_polynomials,
            problem.input_bits,
            monomials,
        )?;
        let right = algebraic_affine(
            &mut builder,
            &layout.right[gate],
            &and_polynomials,
            problem.input_bits,
            monomials,
        )?;
        and_polynomials.push(algebraic_product(&mut builder, &left, &right)?);
    }
    for output in 0..problem.output_bits {
        let polynomial = algebraic_affine(
            &mut builder,
            &layout.outputs[output],
            &and_polynomials,
            problem.input_bits,
            monomials,
        )?;
        let target = truth_coordinate_anf(problem, output);
        for (&node, expected) in polynomial.iter().zip(target) {
            constrain_algebraic_node(&mut builder, node, expected)?;
        }
    }
    Ok(MultiplicativeEncoding {
        formula: builder.finish()?,
        layout,
        problem: problem.clone(),
    })
}

/// Build the deterministic complete multiplicative-complexity synthesis CNF.
///
/// # Errors
///
/// Returns a typed error for malformed truth tables or any exceeded admission
/// limit. It never silently truncates the gate basis or semantic rows.
pub fn encode_multiplicative_circuit(
    problem: &MultiplicativeSynthesisProblem,
    limits: MultiplicativeSynthesisLimits,
) -> Result<MultiplicativeEncoding, MultiplicativeSynthesisError> {
    encode_multiplicative_circuit_with_options(
        problem,
        limits,
        MultiplicativeEncodingOptions::default(),
    )
}

/// Build the deterministic synthesis CNF with explicit completeness-preserving
/// representation reductions.
///
/// # Errors
///
/// Returns the same typed malformed-input and resource errors as
/// [`encode_multiplicative_circuit`].
pub fn encode_multiplicative_circuit_with_options(
    problem: &MultiplicativeSynthesisProblem,
    limits: MultiplicativeSynthesisLimits,
    options: MultiplicativeEncodingOptions,
) -> Result<MultiplicativeEncoding, MultiplicativeSynthesisError> {
    let rows = validate_problem(problem, limits)?;
    let mut builder = RawBuilder::new(limits);
    let mut left = Vec::new();
    let mut right = Vec::new();
    for gate in 0..problem.and_gates {
        let basis = 1 + problem.input_bits + gate;
        left.push(allocate_vector(&mut builder, basis)?);
        right.push(allocate_vector(&mut builder, basis)?);
    }
    let outputs = (0..problem.output_bits)
        .map(|_| allocate_vector(&mut builder, 1 + problem.input_bits + problem.and_gates))
        .collect::<Result<Vec<_>, _>>()?;

    if options.eliminate_internal_constants {
        for gate in 0..problem.and_gates {
            builder.clause(&[(left[gate][0], true)])?;
            builder.clause(&[(right[gate][0], true)])?;
        }
        for (output, selectors) in outputs.iter().enumerate() {
            let shift = problem.output_bits - output - 1;
            let constant = ((problem.truth_table[0] >> shift) & 1) != 0;
            builder.clause(&[(selectors[0], !constant)])?;
        }
    }
    if options.partial_operand_order {
        for gate in 0..problem.and_gates {
            // Forbid left_first=0, right_first=1. Operand commutativity makes
            // one of the two orientations available for every assignment.
            builder.clause(&[(left[gate][1], false), (right[gate][1], true)])?;
        }
    }
    let gate_values = (0..problem.and_gates)
        .map(|_| allocate_vector(&mut builder, rows))
        .collect::<Result<Vec<_>, _>>()?;

    for (row, _) in problem.truth_table.iter().enumerate() {
        for gate in 0..problem.and_gates {
            let earlier: Vec<usize> = (0..gate).map(|index| gate_values[index][row]).collect();
            let mut left_terms = affine_terms(&mut builder, &left[gate], &earlier, problem, row)?;
            let left_value = builder.variable()?;
            left_terms.push(left_value);
            builder.parity_equals(&left_terms, false)?;

            let mut right_terms = affine_terms(&mut builder, &right[gate], &earlier, problem, row)?;
            let right_value = builder.variable()?;
            right_terms.push(right_value);
            builder.parity_equals(&right_terms, false)?;
            builder.and_equiv(gate_values[gate][row], left_value, right_value)?;
        }
        let all_gate_values: Vec<usize> = (0..problem.and_gates)
            .map(|gate| gate_values[gate][row])
            .collect();
        for (output, coefficients) in outputs.iter().enumerate() {
            let terms = affine_terms(&mut builder, coefficients, &all_gate_values, problem, row)?;
            let shift = problem.output_bits - output - 1;
            let expected = ((problem.truth_table[row] >> shift) & 1) != 0;
            builder.parity_equals(&terms, expected)?;
        }
    }

    Ok(MultiplicativeEncoding {
        formula: builder.finish()?,
        layout: SelectorLayout {
            left,
            right,
            outputs,
        },
        problem: problem.clone(),
    })
}

fn emit_affine(
    prefix: &str,
    inputs: &[String],
    nonlinear: &[String],
    coefficients: &[usize],
    model: &[bool],
    gates: &mut Vec<BooleanGate>,
) -> String {
    let constant = model[coefficients[0]];
    let mut terms: Vec<String> = inputs
        .iter()
        .chain(nonlinear.iter())
        .zip(&coefficients[1..])
        .filter(|&(_, coefficient)| model[*coefficient])
        .map(|(wire, _)| wire.clone())
        .collect();
    if terms.is_empty() {
        let output = format!("{prefix}_constant");
        gates.push(BooleanGate {
            output: output.clone(),
            op: if constant {
                BooleanGateOp::Xnor
            } else {
                BooleanGateOp::Xor
            },
            inputs: vec![inputs[0].clone(), inputs[0].clone()],
        });
        return output;
    }
    let mut current = terms.remove(0);
    for (index, term) in terms.into_iter().enumerate() {
        let output = format!("{prefix}_xor{index}");
        gates.push(BooleanGate {
            output: output.clone(),
            op: BooleanGateOp::Xor,
            inputs: vec![current, term],
        });
        current = output;
    }
    if constant {
        let output = format!("{prefix}_not");
        gates.push(BooleanGate {
            output: output.clone(),
            op: BooleanGateOp::Not,
            inputs: vec![current],
        });
        current = output;
    }
    current
}

/// Encode, solve, independently check, and lift one bounded synthesis problem.
///
/// # Errors
///
/// Returns malformed/admission errors from encoding and refuses any SAT or
/// UNSAT handoff that fails its independent replay checker.
pub fn synthesize_multiplicative_circuit(
    problem: &MultiplicativeSynthesisProblem,
    limits: MultiplicativeSynthesisLimits,
    deadline: Option<Instant>,
) -> Result<MultiplicativeSynthesisOutcome, MultiplicativeSynthesisError> {
    synthesize_multiplicative_circuit_with_options(
        problem,
        limits,
        MultiplicativeEncodingOptions::default(),
        deadline,
    )
}

/// Encode and solve with explicit completeness-preserving reductions.
///
/// # Errors
///
/// Returns the same checked encoding, model-lifting, and proof-handoff errors
/// as [`synthesize_multiplicative_circuit`].
pub fn synthesize_multiplicative_circuit_with_options(
    problem: &MultiplicativeSynthesisProblem,
    limits: MultiplicativeSynthesisLimits,
    options: MultiplicativeEncodingOptions,
    deadline: Option<Instant>,
) -> Result<MultiplicativeSynthesisOutcome, MultiplicativeSynthesisError> {
    let encoding = encode_multiplicative_circuit_with_options(problem, limits, options)?;
    match solve_with_drat_proof_with_limits(encoding.formula(), deadline, limits.max_conflicts) {
        ProofSolveOutcome::Sat(model) => Ok(MultiplicativeSynthesisOutcome::Sat(
            encoding.lift_model(&model)?,
        )),
        ProofSolveOutcome::Unsat(proof) => {
            if check_drat_backward(encoding.formula(), &proof) != Ok(true) {
                return Err(MultiplicativeSynthesisError::InvalidUnsatProof);
            }
            Ok(MultiplicativeSynthesisOutcome::Unsat {
                formula: encoding.formula,
                proof,
            })
        }
        ProofSolveOutcome::ResourceOut => Ok(MultiplicativeSynthesisOutcome::ResourceOut),
        ProofSolveOutcome::Interrupted => Ok(MultiplicativeSynthesisOutcome::Interrupted),
    }
}

/// Solve the ANF-coefficient backend with the same checked SAT/UNSAT handoff.
///
/// # Errors
///
/// Returns typed encoding, model-lifting, or proof-checking errors.
pub fn synthesize_multiplicative_circuit_anf(
    problem: &MultiplicativeSynthesisProblem,
    limits: MultiplicativeSynthesisLimits,
    options: MultiplicativeEncodingOptions,
    deadline: Option<Instant>,
) -> Result<MultiplicativeSynthesisOutcome, MultiplicativeSynthesisError> {
    let encoding = encode_multiplicative_circuit_anf(problem, limits, options)?;
    match solve_with_drat_proof_with_limits(encoding.formula(), deadline, limits.max_conflicts) {
        ProofSolveOutcome::Sat(model) => Ok(MultiplicativeSynthesisOutcome::Sat(
            encoding.lift_model(&model)?,
        )),
        ProofSolveOutcome::Unsat(proof) => {
            if check_drat_backward(encoding.formula(), &proof) != Ok(true) {
                return Err(MultiplicativeSynthesisError::InvalidUnsatProof);
            }
            Ok(MultiplicativeSynthesisOutcome::Unsat {
                formula: encoding.formula,
                proof,
            })
        }
        ProofSolveOutcome::ResourceOut => Ok(MultiplicativeSynthesisOutcome::ResourceOut),
        ProofSolveOutcome::Interrupted => Ok(MultiplicativeSynthesisOutcome::Interrupted),
    }
}

#[cfg(test)]
mod tests {
    use axeyum_cnf::check_drat;

    use super::*;

    fn problem(table: &[u64], and_gates: usize) -> MultiplicativeSynthesisProblem {
        MultiplicativeSynthesisProblem {
            input_bits: 2,
            output_bits: 1,
            truth_table: table.to_vec(),
            and_gates,
        }
    }

    #[test]
    fn xor_is_affine_and_lifts_without_an_and_gate() {
        let outcome = synthesize_multiplicative_circuit(
            &problem(&[0, 1, 1, 0], 0),
            MultiplicativeSynthesisLimits::default(),
            None,
        )
        .unwrap();
        let MultiplicativeSynthesisOutcome::Sat(artifact) = outcome else {
            panic!("xor must synthesize at multiplicative complexity zero");
        };
        assert_eq!(
            artifact
                .gates
                .iter()
                .filter(|gate| gate.op == BooleanGateOp::And)
                .count(),
            0
        );
    }

    #[test]
    fn and_has_a_checked_zero_gate_refutation_and_one_gate_witness() {
        let limits = MultiplicativeSynthesisLimits::default();
        let zero =
            synthesize_multiplicative_circuit(&problem(&[0, 0, 0, 1], 0), limits, None).unwrap();
        let MultiplicativeSynthesisOutcome::Unsat { formula, proof } = zero else {
            panic!("and is not affine");
        };
        assert_eq!(check_drat(&formula, &proof), Ok(true));

        let one =
            synthesize_multiplicative_circuit(&problem(&[0, 0, 0, 1], 1), limits, None).unwrap();
        let MultiplicativeSynthesisOutcome::Sat(artifact) = one else {
            panic!("and needs one gate");
        };
        assert_eq!(
            artifact
                .gates
                .iter()
                .filter(|gate| gate.op == BooleanGateOp::And)
                .count(),
            1
        );
    }

    #[test]
    fn all_two_input_functions_match_their_anf_degree_boundary() {
        let limits = MultiplicativeSynthesisLimits::default();
        for packed in 0_u16..16 {
            let table: Vec<u64> = (0..4).map(|row| u64::from((packed >> row) & 1)).collect();
            let quadratic = (packed ^ (packed >> 1) ^ (packed >> 2) ^ (packed >> 3)) & 1 != 0;
            let zero =
                synthesize_multiplicative_circuit(&problem(&table, 0), limits, None).unwrap();
            assert_eq!(
                matches!(zero, MultiplicativeSynthesisOutcome::Sat(_)),
                !quadratic
            );
            let one = synthesize_multiplicative_circuit(&problem(&table, 1), limits, None).unwrap();
            assert!(matches!(one, MultiplicativeSynthesisOutcome::Sat(_)));
        }
    }

    #[test]
    fn proved_reductions_preserve_all_two_input_boundaries() {
        let limits = MultiplicativeSynthesisLimits::default();
        let options = MultiplicativeEncodingOptions {
            eliminate_internal_constants: true,
            partial_operand_order: true,
        };
        for packed in 0_u16..16 {
            let table: Vec<u64> = (0..4).map(|row| u64::from((packed >> row) & 1)).collect();
            for budget in 0..=1 {
                let basic =
                    synthesize_multiplicative_circuit(&problem(&table, budget), limits, None)
                        .unwrap();
                let reduced = synthesize_multiplicative_circuit_with_options(
                    &problem(&table, budget),
                    limits,
                    options,
                    None,
                )
                .unwrap();
                assert_eq!(
                    matches!(basic, MultiplicativeSynthesisOutcome::Sat(_)),
                    matches!(reduced, MultiplicativeSynthesisOutcome::Sat(_)),
                    "packed={packed}, budget={budget}"
                );
            }
        }
    }

    #[test]
    fn anf_and_truth_table_backends_agree_on_all_two_input_functions() {
        let limits = MultiplicativeSynthesisLimits::default();
        for options in [
            MultiplicativeEncodingOptions::default(),
            MultiplicativeEncodingOptions {
                eliminate_internal_constants: true,
                partial_operand_order: true,
            },
        ] {
            for packed in 0_u16..16 {
                let table: Vec<u64> = (0..4).map(|row| u64::from((packed >> row) & 1)).collect();
                for budget in 0..=1 {
                    let row = synthesize_multiplicative_circuit_with_options(
                        &problem(&table, budget),
                        limits,
                        options,
                        None,
                    )
                    .unwrap();
                    let anf = synthesize_multiplicative_circuit_anf(
                        &problem(&table, budget),
                        limits,
                        options,
                        None,
                    )
                    .unwrap();
                    assert_eq!(
                        matches!(row, MultiplicativeSynthesisOutcome::Sat(_)),
                        matches!(anf, MultiplicativeSynthesisOutcome::Sat(_)),
                        "packed={packed}, budget={budget}, options={options:?}"
                    );
                }
            }
        }
    }

    #[test]
    fn portable_anf_system_matches_the_and_gate_boundary_and_lifts() {
        let limits = MultiplicativeSynthesisLimits::default();
        let zero = encode_multiplicative_anf_system(
            &problem(&[0, 0, 0, 1], 0),
            limits,
            MultiplicativeEncodingOptions::default(),
        )
        .unwrap();
        let zero_width = zero.system().variable_count();
        assert!((0..(1_usize << zero_width)).all(|packed| {
            let assignment: Vec<bool> = (0..zero_width)
                .map(|bit| ((packed >> bit) & 1) != 0)
                .collect();
            zero.system().evaluate(&assignment) == Ok(false)
        }));

        let one = encode_multiplicative_anf_system(
            &problem(&[0, 0, 0, 1], 1),
            limits,
            MultiplicativeEncodingOptions::default(),
        )
        .unwrap();
        let width = one.system().variable_count();
        let mut assignment = vec![false; width];
        assignment[one.layout.left[0][1]] = true;
        assignment[one.layout.right[0][2]] = true;
        assignment[one.layout.outputs[0][3]] = true;
        let auxiliary_start = one.layout.outputs.iter().flatten().max().copied().unwrap() + 1;
        assignment[auxiliary_start + 2] = true; // left operand is x0
        assignment[auxiliary_start + 4 + 1] = true; // right operand is x1
        assignment[auxiliary_start + 8 + 3] = true; // gate output is x0*x1
        assert_eq!(one.system().evaluate(&assignment), Ok(true));
        let artifact = one.lift_assignment(&assignment).unwrap();
        assert_eq!(
            artifact
                .gates
                .iter()
                .filter(|gate| gate.op == BooleanGateOp::And)
                .count(),
            1
        );
    }

    #[test]
    fn malformed_and_resource_limited_inputs_fail_before_search() {
        let malformed = MultiplicativeSynthesisProblem {
            input_bits: 2,
            output_bits: 1,
            truth_table: vec![0, 1],
            and_gates: 0,
        };
        assert!(matches!(
            encode_multiplicative_circuit(&malformed, MultiplicativeSynthesisLimits::default()),
            Err(MultiplicativeSynthesisError::TruthTableLength { .. })
        ));
        let limits = MultiplicativeSynthesisLimits {
            max_variables: 1,
            ..MultiplicativeSynthesisLimits::default()
        };
        assert!(matches!(
            encode_multiplicative_circuit(&problem(&[0, 0, 0, 1], 1), limits),
            Err(MultiplicativeSynthesisError::LimitExceeded {
                resource: "variables",
                ..
            })
        ));
    }
}
