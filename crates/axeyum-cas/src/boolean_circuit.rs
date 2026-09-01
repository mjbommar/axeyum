//! Exhaustive checking of portable finite Boolean-circuit witnesses.
//!
//! The circuit is a topologically ordered named-wire program.  Its truth table
//! is interpreted independently on every input row; a successful result checks
//! all rows, not only the rows mentioned by the producer.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

/// Version tag for portable Boolean-circuit artifacts.
pub const BOOLEAN_CIRCUIT_SCHEMA: &str = "axeyum.boolean-circuit.v1";

/// Supported Boolean gate operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum BooleanGateOp {
    /// Conjunction.
    And,
    /// Disjunction.
    Or,
    /// Exclusive or.
    Xor,
    /// Negation.
    Not,
    /// Negated conjunction.
    Nand,
    /// Negated disjunction.
    Nor,
    /// Equivalence.
    Xnor,
}

impl BooleanGateOp {
    fn arity(self) -> usize {
        if self == Self::Not { 1 } else { 2 }
    }

    fn apply(self, inputs: &[bool]) -> bool {
        match self {
            Self::And => inputs[0] & inputs[1],
            Self::Or => inputs[0] | inputs[1],
            Self::Xor => inputs[0] ^ inputs[1],
            Self::Not => !inputs[0],
            Self::Nand => !(inputs[0] & inputs[1]),
            Self::Nor => !(inputs[0] | inputs[1]),
            Self::Xnor => !(inputs[0] ^ inputs[1]),
        }
    }
}

/// One named gate in topological order.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct BooleanGate {
    /// New wire defined by this gate.
    pub output: String,
    /// Gate operation.
    pub op: BooleanGateOp,
    /// Previously defined input wires.
    pub inputs: Vec<String>,
}

/// Portable circuit plus its claimed complete truth table.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct BooleanCircuitArtifact {
    /// Must equal [`BOOLEAN_CIRCUIT_SCHEMA`].
    pub schema: String,
    /// Input wire names from most-significant to least-significant bit.
    pub inputs: Vec<String>,
    /// Topologically ordered gates.
    pub gates: Vec<BooleanGate>,
    /// Output wire names from most-significant to least-significant bit.
    pub outputs: Vec<String>,
    /// Claimed output integer for every input integer in ascending order.
    pub truth_table: Vec<u64>,
}

/// Admission limits for exhaustive circuit replay.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BooleanCircuitLimits {
    /// Maximum input width. Replay has `2^width` rows.
    pub max_input_bits: usize,
    /// Maximum output width representable by this v1 artifact.
    pub max_output_bits: usize,
    /// Maximum number of gates.
    pub max_gates: usize,
    /// Maximum cumulative input-wire references.
    pub max_gate_inputs: usize,
}

impl Default for BooleanCircuitLimits {
    fn default() -> Self {
        Self {
            max_input_bits: 20,
            max_output_bits: 64,
            max_gates: 1_000_000,
            max_gate_inputs: 2_000_000,
        }
    }
}

/// Successful or falsified exhaustive replay.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BooleanCircuitCheck {
    /// Every truth-table row matched.
    Verified {
        /// Number of checked rows.
        rows_checked: usize,
        /// Gate counts by stable operation name.
        gate_counts: BTreeMap<BooleanGateOp, usize>,
    },
    /// First input row whose output differs.
    Failed {
        /// Input integer under the declared MSB-first convention.
        input: u64,
        /// Truth-table output.
        expected: u64,
        /// Circuit output.
        observed: u64,
    },
}

/// Malformed or resource-inadmissible circuit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BooleanCircuitError {
    /// Artifact version is unsupported.
    UnsupportedSchema(String),
    /// A stable resource limit was exceeded.
    LimitExceeded {
        /// Resource name.
        resource: &'static str,
        /// Observed value.
        observed: usize,
        /// Configured maximum.
        limit: usize,
    },
    /// Truth-table row count differs from `2^input_bits`.
    TruthTableLength {
        /// Expected rows.
        expected: usize,
        /// Supplied rows.
        observed: usize,
    },
    /// A truth-table output does not fit the declared output width.
    TruthTableValueOutOfRange {
        /// Row containing the value.
        row: usize,
        /// Supplied output integer.
        value: u64,
    },
    /// A wire name is empty or defined more than once.
    InvalidDefinition(String),
    /// A gate refers to a wire not yet defined.
    UndefinedWire {
        /// Gate output being evaluated.
        gate: String,
        /// Undefined dependency.
        wire: String,
    },
    /// A gate has the wrong number of inputs.
    Arity {
        /// Gate output name.
        gate: String,
        /// Required arity.
        expected: usize,
        /// Supplied arity.
        observed: usize,
    },
    /// A declared output wire is undefined.
    UndefinedOutput(String),
}

fn validate_circuit(
    artifact: &BooleanCircuitArtifact,
    limits: BooleanCircuitLimits,
) -> Result<usize, BooleanCircuitError> {
    if artifact.schema != BOOLEAN_CIRCUIT_SCHEMA {
        return Err(BooleanCircuitError::UnsupportedSchema(
            artifact.schema.clone(),
        ));
    }
    for (resource, observed, limit) in [
        ("input_bits", artifact.inputs.len(), limits.max_input_bits),
        (
            "output_bits",
            artifact.outputs.len(),
            limits.max_output_bits,
        ),
        ("gates", artifact.gates.len(), limits.max_gates),
    ] {
        if observed > limit {
            return Err(BooleanCircuitError::LimitExceeded {
                resource,
                observed,
                limit,
            });
        }
    }
    let gate_inputs = artifact
        .gates
        .iter()
        .try_fold(0_usize, |total, gate| total.checked_add(gate.inputs.len()))
        .unwrap_or(usize::MAX);
    if gate_inputs > limits.max_gate_inputs {
        return Err(BooleanCircuitError::LimitExceeded {
            resource: "gate_inputs",
            observed: gate_inputs,
            limit: limits.max_gate_inputs,
        });
    }
    let rows = 1_usize
        .checked_shl(u32::try_from(artifact.inputs.len()).unwrap_or(u32::MAX))
        .unwrap_or(usize::MAX);
    if artifact.truth_table.len() != rows {
        return Err(BooleanCircuitError::TruthTableLength {
            expected: rows,
            observed: artifact.truth_table.len(),
        });
    }
    let output_limit = if artifact.outputs.len() == 64 {
        None
    } else {
        Some(1_u64 << artifact.outputs.len())
    };
    if let Some((row, &value)) = artifact
        .truth_table
        .iter()
        .enumerate()
        .find(|&(_, value)| output_limit.is_some_and(|limit| *value >= limit))
    {
        return Err(BooleanCircuitError::TruthTableValueOutOfRange { row, value });
    }

    let mut defined = BTreeSet::<String>::new();
    for input in &artifact.inputs {
        if input.is_empty() || !defined.insert(input.clone()) {
            return Err(BooleanCircuitError::InvalidDefinition(input.clone()));
        }
    }
    for gate in &artifact.gates {
        if gate.output.is_empty() || defined.contains(&gate.output) {
            return Err(BooleanCircuitError::InvalidDefinition(gate.output.clone()));
        }
        if gate.inputs.len() != gate.op.arity() {
            return Err(BooleanCircuitError::Arity {
                gate: gate.output.clone(),
                expected: gate.op.arity(),
                observed: gate.inputs.len(),
            });
        }
        if let Some(wire) = gate.inputs.iter().find(|wire| !defined.contains(*wire)) {
            return Err(BooleanCircuitError::UndefinedWire {
                gate: gate.output.clone(),
                wire: wire.clone(),
            });
        }
        defined.insert(gate.output.clone());
    }
    if let Some(output) = artifact
        .outputs
        .iter()
        .find(|output| !defined.contains(*output))
    {
        return Err(BooleanCircuitError::UndefinedOutput(output.clone()));
    }
    Ok(rows)
}

/// Exhaustively check a Boolean circuit against its complete declared truth table.
///
/// # Errors
///
/// Returns an error before replay when the artifact is malformed or exceeds an
/// explicit admission limit.
pub fn check_boolean_circuit(
    artifact: &BooleanCircuitArtifact,
    limits: BooleanCircuitLimits,
) -> Result<BooleanCircuitCheck, BooleanCircuitError> {
    let rows = validate_circuit(artifact, limits)?;
    let mut gate_counts = BTreeMap::new();
    for gate in &artifact.gates {
        *gate_counts.entry(gate.op).or_insert(0) += 1;
    }
    for row in 0..rows {
        let mut wires = BTreeMap::<&str, bool>::new();
        for (index, input) in artifact.inputs.iter().enumerate() {
            let shift = artifact.inputs.len() - index - 1;
            wires.insert(input, ((row >> shift) & 1) != 0);
        }
        for gate in &artifact.gates {
            let values: Vec<bool> = gate
                .inputs
                .iter()
                .map(|wire| wires[wire.as_str()])
                .collect();
            wires.insert(&gate.output, gate.op.apply(&values));
        }
        let observed = artifact.outputs.iter().fold(0_u64, |value, output| {
            (value << 1) | u64::from(wires[output.as_str()])
        });
        if observed != artifact.truth_table[row] {
            return Ok(BooleanCircuitCheck::Failed {
                input: u64::try_from(row).unwrap_or(u64::MAX),
                expected: artifact.truth_table[row],
                observed,
            });
        }
    }
    Ok(BooleanCircuitCheck::Verified {
        rows_checked: rows,
        gate_counts,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn xor_artifact() -> BooleanCircuitArtifact {
        BooleanCircuitArtifact {
            schema: BOOLEAN_CIRCUIT_SCHEMA.to_owned(),
            inputs: vec!["x0".to_owned(), "x1".to_owned()],
            gates: vec![BooleanGate {
                output: "y0".to_owned(),
                op: BooleanGateOp::Xor,
                inputs: vec!["x0".to_owned(), "x1".to_owned()],
            }],
            outputs: vec!["y0".to_owned()],
            truth_table: vec![0, 1, 1, 0],
        }
    }

    #[test]
    fn xor_matches_every_row() {
        assert!(matches!(
            check_boolean_circuit(&xor_artifact(), BooleanCircuitLimits::default()),
            Ok(BooleanCircuitCheck::Verified {
                rows_checked: 4,
                ..
            })
        ));
    }

    #[test]
    fn truth_table_mutation_reports_the_exact_row() {
        let mut artifact = xor_artifact();
        artifact.truth_table[2] = 0;
        assert_eq!(
            check_boolean_circuit(&artifact, BooleanCircuitLimits::default()),
            Ok(BooleanCircuitCheck::Failed {
                input: 2,
                expected: 0,
                observed: 1,
            })
        );
    }

    #[test]
    fn forward_reference_is_rejected() {
        let mut artifact = xor_artifact();
        artifact.gates[0].inputs[0] = "future".to_owned();
        assert!(matches!(
            check_boolean_circuit(&artifact, BooleanCircuitLimits::default()),
            Err(BooleanCircuitError::UndefinedWire { .. })
        ));
    }

    /// A purely-NAND (13-gate) 1-bit full adder: `sum = a xor b xor cin`,
    /// `cout = (a and b) or (cin and (a xor b))`.  This is a concrete witness
    /// to NAND's functional completeness for binary addition, not merely an
    /// assertion of it -- `nand_only_full_adder_matches_arithmetic_for_every_row`
    /// replays all eight rows against the two-output truth table.
    ///
    /// The first four gates (`n1..xor_ab`) are the standard 4-NAND XOR gadget
    /// applied to `(a, b)`; the next four (`n5..sum`) apply the same gadget to
    /// `(xor_ab, cin)` to get `sum`.  `cout` is built by De Morgan's law from
    /// two ANDs recovered from NAND by self-NANDing (`ab`, `cin_xor`) and an OR
    /// realised as NAND of the two complements (`na`, `nb`, `cout`).
    fn nand_only_full_adder_artifact() -> BooleanCircuitArtifact {
        fn nand(output: &str, inputs: [&str; 2]) -> BooleanGate {
            BooleanGate {
                output: output.to_owned(),
                op: BooleanGateOp::Nand,
                inputs: inputs.iter().map(|wire| (*wire).to_owned()).collect(),
            }
        }
        BooleanCircuitArtifact {
            schema: BOOLEAN_CIRCUIT_SCHEMA.to_owned(),
            inputs: vec!["a".to_owned(), "b".to_owned(), "cin".to_owned()],
            gates: vec![
                nand("n1", ["a", "b"]),
                nand("n2", ["a", "n1"]),
                nand("n3", ["b", "n1"]),
                nand("xor_ab", ["n2", "n3"]),
                nand("n5", ["xor_ab", "cin"]),
                nand("n6", ["xor_ab", "n5"]),
                nand("n7", ["cin", "n5"]),
                nand("sum", ["n6", "n7"]),
                nand("ab", ["n1", "n1"]),
                nand("cin_xor", ["n5", "n5"]),
                nand("na", ["ab", "ab"]),
                nand("nb", ["cin_xor", "cin_xor"]),
                nand("cout", ["na", "nb"]),
            ],
            outputs: vec!["sum".to_owned(), "cout".to_owned()],
            // row = (a<<2)|(b<<1)|cin, value = (sum<<1)|cout, independently
            // computed from the arithmetic definition, not from this circuit.
            truth_table: vec![0, 2, 2, 1, 2, 1, 1, 3],
        }
    }

    #[test]
    fn nand_only_full_adder_matches_arithmetic_for_every_row() {
        assert_eq!(
            check_boolean_circuit(
                &nand_only_full_adder_artifact(),
                BooleanCircuitLimits::default(),
            ),
            Ok(BooleanCircuitCheck::Verified {
                rows_checked: 8,
                gate_counts: BTreeMap::from([(BooleanGateOp::Nand, 13)]),
            })
        );
    }

    /// Negative control: mutate one truth-table entry (row 3: `a=0,b=1,cin=1`,
    /// correctly `sum=0,cout=1` i.e. value 1) and confirm the checker names the
    /// exact row and both values rather than merely returning an error.
    #[test]
    fn nand_only_full_adder_truth_table_mutation_is_rejected() {
        let mut artifact = nand_only_full_adder_artifact();
        artifact.truth_table[3] = 3;
        assert_eq!(
            check_boolean_circuit(&artifact, BooleanCircuitLimits::default()),
            Ok(BooleanCircuitCheck::Failed {
                input: 3,
                expected: 3,
                observed: 1,
            })
        );
    }
}
