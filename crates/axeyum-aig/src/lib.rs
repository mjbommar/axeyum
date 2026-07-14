//! And-inverter graph layer for Axeyum.
//!
//! This crate is the first Phase 4 circuit layer. It deliberately stops short
//! of term bit-lowering and CNF: it owns deterministic AIG node construction,
//! structural hashing, circuit evaluation, and ASCII AIGER debug export.

use std::{collections::BTreeMap, fmt::Write as _};

/// Stable ID for an AIG node in one [`Aig`] graph.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct AigNodeId(u32);

impl AigNodeId {
    /// Dense node index. Node 0 is always constant false.
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// Stable ID for an input in one [`Aig`] graph.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct AigInputId(u32);

impl AigInputId {
    /// Dense input index in creation order.
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// A possibly inverted reference to an AIG node.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct AigLit {
    node: AigNodeId,
    inverted: bool,
}

impl AigLit {
    /// Constant false literal.
    pub const FALSE: Self = Self {
        node: AigNodeId(0),
        inverted: false,
    };

    /// Constant true literal.
    pub const TRUE: Self = Self {
        node: AigNodeId(0),
        inverted: true,
    };

    /// Returns the referenced node.
    pub fn node(self) -> AigNodeId {
        self.node
    }

    /// Returns `true` when this literal complements its node.
    pub fn is_inverted(self) -> bool {
        self.inverted
    }

    /// Returns the complemented literal.
    #[must_use]
    pub fn negated(self) -> Self {
        Self {
            node: self.node,
            inverted: !self.inverted,
        }
    }

    /// Returns the positive literal for `node`.
    pub fn positive(node: AigNodeId) -> Self {
        Self {
            node,
            inverted: false,
        }
    }
}

/// Input metadata in creation order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AigInput {
    /// Stable input ID.
    pub id: AigInputId,
    /// Node representing this input.
    pub node: AigNodeId,
    /// Human-readable label for diagnostics and future lift maps.
    pub label: String,
}

/// One AIG node.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AigNode {
    /// Constant false. Constant true is the inverted literal of this node.
    ConstFalse,
    /// Primary input.
    Input(AigInputId),
    /// Conjunction of two literals. Inputs are stored in canonical order.
    And(AigLit, AigLit),
}

/// Deterministic construction counters for the primitive AND unique table.
///
/// Every call to [`Aig::and`] is classified exactly once as a trivial Boolean
/// simplification, a local absorption/consensus simplification, a structural
/// hash hit, or a newly allocated AND node. The counters are diagnostic only;
/// they do not affect construction order or graph semantics.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct AigConstructionStats {
    /// Total primitive AND requests, including requests made by OR/XOR/mux helpers.
    pub and_requests: u64,
    /// Requests eliminated by constant, identity, idempotence, or complement rules.
    pub and_trivial_simplifications: u64,
    /// Requests eliminated by absorption or consensus rules over existing nodes.
    pub and_absorption_simplifications: u64,
    /// Requests reusing an existing canonical AND node.
    pub and_structural_hash_hits: u64,
    /// Requests allocating a new canonical AND node.
    pub and_nodes_created: u64,
}

/// A deterministic structurally hashed AIG.
#[derive(Debug, Clone)]
pub struct Aig {
    nodes: Vec<AigNode>,
    inputs: Vec<AigInput>,
    and_table: BTreeMap<(AigLit, AigLit), AigNodeId>,
    construction_stats: AigConstructionStats,
}

impl Aig {
    /// Creates an empty graph containing only the constant-false node.
    pub fn new() -> Self {
        Self {
            nodes: vec![AigNode::ConstFalse],
            inputs: Vec::new(),
            and_table: BTreeMap::new(),
            construction_stats: AigConstructionStats::default(),
        }
    }

    /// Returns the number of nodes, including constant false and inputs.
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// Returns the number of primary inputs.
    pub fn input_count(&self) -> usize {
        self.inputs.len()
    }

    /// Returns primitive AND construction counters accumulated by this graph.
    pub fn construction_stats(&self) -> AigConstructionStats {
        self.construction_stats
    }

    /// Returns input metadata in deterministic creation order.
    pub fn inputs(&self) -> &[AigInput] {
        &self.inputs
    }

    /// Iterates over nodes in dense ID order.
    ///
    /// The iterator is exact-size and double-ended, so consumers that need
    /// reverse dense-ID order do not have to materialize a temporary copy.
    ///
    /// # Panics
    ///
    /// Panics only if the internal node vector exceeds `u32::MAX` entries,
    /// which construction already prevents.
    pub fn nodes(
        &self,
    ) -> impl DoubleEndedIterator<Item = (AigNodeId, AigNode)> + ExactSizeIterator + '_ {
        self.nodes.iter().copied().enumerate().map(|(index, node)| {
            (
                AigNodeId(u32::try_from(index).expect("node index fits u32")),
                node,
            )
        })
    }

    /// Returns the node for `id`, if `id` belongs to this graph.
    pub fn node(&self, id: AigNodeId) -> Option<AigNode> {
        self.nodes.get(id.index()).copied()
    }

    /// Creates a new primary input and returns its positive literal.
    ///
    /// # Panics
    ///
    /// Panics only if a graph grows beyond `u32::MAX` inputs or nodes.
    pub fn input(&mut self, label: impl Into<String>) -> AigLit {
        let id = AigInputId(u32::try_from(self.inputs.len()).expect("input count fits u32"));
        let node = self.push_node(AigNode::Input(id));
        self.inputs.push(AigInput {
            id,
            node,
            label: label.into(),
        });
        AigLit::positive(node)
    }

    /// Builds a structurally hashed AND of two literals.
    pub fn and(&mut self, lhs: AigLit, rhs: AigLit) -> AigLit {
        self.construction_stats.and_requests =
            self.construction_stats.and_requests.saturating_add(1);
        match simplify_and(lhs, rhs) {
            SimplifiedAnd::Literal(lit) => {
                self.construction_stats.and_trivial_simplifications = self
                    .construction_stats
                    .and_trivial_simplifications
                    .saturating_add(1);
                lit
            }
            SimplifiedAnd::Node(mut a, mut b) => {
                if b < a {
                    std::mem::swap(&mut a, &mut b);
                }
                if let Some(lit) = self.simplify_and_by_absorption(a, b) {
                    self.construction_stats.and_absorption_simplifications = self
                        .construction_stats
                        .and_absorption_simplifications
                        .saturating_add(1);
                    return lit;
                }
                let key = (a, b);
                if let Some(node) = self.and_table.get(&key) {
                    self.construction_stats.and_structural_hash_hits = self
                        .construction_stats
                        .and_structural_hash_hits
                        .saturating_add(1);
                    return AigLit::positive(*node);
                }
                let node = self.push_node(AigNode::And(a, b));
                self.and_table.insert(key, node);
                self.construction_stats.and_nodes_created =
                    self.construction_stats.and_nodes_created.saturating_add(1);
                AigLit::positive(node)
            }
        }
    }

    fn simplify_and_by_absorption(&mut self, lhs: AigLit, rhs: AigLit) -> Option<AigLit> {
        self.absorb_or_rhs(lhs, rhs)
            .or_else(|| self.absorb_or_rhs(rhs, lhs))
            .or_else(|| self.simplify_and_by_or_consensus(lhs, rhs))
    }

    fn absorb_or_rhs(&mut self, lit: AigLit, maybe_or: AigLit) -> Option<AigLit> {
        let (or_lhs, or_rhs) = self.or_operands(maybe_or)?;
        if lit == or_lhs || lit == or_rhs {
            return Some(lit);
        }
        if lit == or_lhs.negated() {
            return Some(self.and(lit, or_rhs));
        }
        if lit == or_rhs.negated() {
            return Some(self.and(lit, or_lhs));
        }
        None
    }

    fn simplify_and_by_or_consensus(&self, lhs: AigLit, rhs: AigLit) -> Option<AigLit> {
        let lhs_operands = self.or_operands(lhs)?;
        let rhs_operands = self.or_operands(rhs)?;
        consensus_shared_operand(lhs_operands, rhs_operands)
    }

    fn or_operands(&self, lit: AigLit) -> Option<(AigLit, AigLit)> {
        if !lit.is_inverted() {
            return None;
        }
        let AigNode::And(lhs, rhs) = self.node(lit.node())? else {
            return None;
        };
        Some((lhs.negated(), rhs.negated()))
    }

    /// Builds OR from AND and complemented edges.
    pub fn or(&mut self, lhs: AigLit, rhs: AigLit) -> AigLit {
        self.and(lhs.negated(), rhs.negated()).negated()
    }

    /// Builds XOR from AND, OR, and complemented edges.
    pub fn xor(&mut self, lhs: AigLit, rhs: AigLit) -> AigLit {
        if lhs == AigLit::FALSE {
            return rhs;
        }
        if rhs == AigLit::FALSE {
            return lhs;
        }
        if lhs == AigLit::TRUE {
            return rhs.negated();
        }
        if rhs == AigLit::TRUE {
            return lhs.negated();
        }
        if lhs == rhs {
            return AigLit::FALSE;
        }
        if lhs == rhs.negated() {
            return AigLit::TRUE;
        }
        let left = self.and(lhs, rhs.negated());
        let right = self.and(lhs.negated(), rhs);
        self.or(left, right)
    }

    /// Builds a 1-bit mux: `condition ? then_lit : else_lit`.
    pub fn mux(&mut self, condition: AigLit, then_lit: AigLit, else_lit: AigLit) -> AigLit {
        if condition == AigLit::TRUE {
            return then_lit;
        }
        if condition == AigLit::FALSE {
            return else_lit;
        }
        if then_lit == else_lit {
            return then_lit;
        }
        if then_lit == AigLit::TRUE && else_lit == AigLit::FALSE {
            return condition;
        }
        if then_lit == AigLit::FALSE && else_lit == AigLit::TRUE {
            return condition.negated();
        }
        if then_lit == condition {
            return self.or(condition, else_lit);
        }
        if then_lit == condition.negated() {
            return self.and(condition.negated(), else_lit);
        }
        if else_lit == condition {
            return self.and(condition, then_lit);
        }
        if else_lit == condition.negated() {
            return self.or(condition.negated(), then_lit);
        }
        if then_lit == else_lit.negated() {
            return self.xor(condition, then_lit).negated();
        }
        if then_lit == AigLit::TRUE {
            return self.or(condition, else_lit);
        }
        if then_lit == AigLit::FALSE {
            return self.and(condition.negated(), else_lit);
        }
        if else_lit == AigLit::TRUE {
            return self.or(condition.negated(), then_lit);
        }
        if else_lit == AigLit::FALSE {
            return self.and(condition, then_lit);
        }
        if let Some(lit) = self.simplify_mux_by_condition(condition, then_lit, else_lit) {
            return lit;
        }
        if let Some(lit) = self.simplify_mux_by_branch_absorption(condition, then_lit, else_lit) {
            return lit;
        }
        let when_true = self.and(condition, then_lit);
        let when_false = self.and(condition.negated(), else_lit);
        self.or(when_true, when_false)
    }

    fn simplify_mux_by_condition(
        &mut self,
        condition: AigLit,
        then_lit: AigLit,
        else_lit: AigLit,
    ) -> Option<AigLit> {
        if let Some(other) = self.and_other_operand(then_lit, condition) {
            return Some(self.mux(condition, other, else_lit));
        }
        if self
            .and_other_operand(then_lit, condition.negated())
            .is_some()
        {
            return Some(self.and(condition.negated(), else_lit));
        }
        if self.and_other_operand(else_lit, condition).is_some() {
            return Some(self.and(condition, then_lit));
        }
        if let Some(other) = self.and_other_operand(else_lit, condition.negated()) {
            return Some(self.mux(condition, then_lit, other));
        }
        if self.or_other_operand(then_lit, condition).is_some() {
            return Some(self.or(condition, else_lit));
        }
        if let Some(other) = self.or_other_operand(then_lit, condition.negated()) {
            return Some(self.mux(condition, other, else_lit));
        }
        if let Some(other) = self.or_other_operand(else_lit, condition) {
            return Some(self.mux(condition, then_lit, other));
        }
        if self
            .or_other_operand(else_lit, condition.negated())
            .is_some()
        {
            return Some(self.or(condition.negated(), then_lit));
        }
        None
    }

    fn simplify_mux_by_branch_absorption(
        &mut self,
        condition: AigLit,
        then_lit: AigLit,
        else_lit: AigLit,
    ) -> Option<AigLit> {
        if let Some(other) = self.and_other_operand(else_lit, then_lit) {
            let condition_or_other = self.or(condition, other);
            return Some(self.and(then_lit, condition_or_other));
        }
        if let Some(other) = self.and_other_operand(then_lit, else_lit) {
            let not_condition_or_other = self.or(condition.negated(), other);
            return Some(self.and(else_lit, not_condition_or_other));
        }
        if let Some(other) = self.or_other_operand(else_lit, then_lit) {
            let not_condition_and_other = self.and(condition.negated(), other);
            return Some(self.or(then_lit, not_condition_and_other));
        }
        if let Some(other) = self.or_other_operand(then_lit, else_lit) {
            let condition_and_other = self.and(condition, other);
            return Some(self.or(else_lit, condition_and_other));
        }
        None
    }

    fn and_other_operand(&self, lit: AigLit, operand: AigLit) -> Option<AigLit> {
        let (lhs, rhs) = self.and_operands(lit)?;
        if lhs == operand {
            Some(rhs)
        } else if rhs == operand {
            Some(lhs)
        } else {
            None
        }
    }

    fn or_other_operand(&self, lit: AigLit, operand: AigLit) -> Option<AigLit> {
        let (lhs, rhs) = self.or_operands(lit)?;
        if lhs == operand {
            Some(rhs)
        } else if rhs == operand {
            Some(lhs)
        } else {
            None
        }
    }

    fn and_operands(&self, lit: AigLit) -> Option<(AigLit, AigLit)> {
        if lit.is_inverted() {
            return None;
        }
        let AigNode::And(lhs, rhs) = self.node(lit.node())? else {
            return None;
        };
        Some((lhs, rhs))
    }

    /// Evaluates one literal from input values in creation order.
    ///
    /// # Errors
    ///
    /// Returns [`AigError::InputCountMismatch`] when `inputs.len()` differs
    /// from [`Aig::input_count`].
    pub fn eval(&self, root: AigLit, inputs: &[bool]) -> Result<bool, AigError> {
        let values = self.evaluate_nodes(inputs)?;
        Ok(eval_lit(root, &values))
    }

    /// Evaluates several literals with one node pass.
    ///
    /// # Errors
    ///
    /// Returns [`AigError::InputCountMismatch`] when `inputs.len()` differs
    /// from [`Aig::input_count`].
    pub fn eval_many(&self, roots: &[AigLit], inputs: &[bool]) -> Result<Vec<bool>, AigError> {
        let values = self.evaluate_nodes(inputs)?;
        Ok(roots.iter().map(|&root| eval_lit(root, &values)).collect())
    }

    /// Renders this combinational AIG as ASCII AIGER (`aag`) with `outputs`.
    ///
    /// The output is intended for deterministic debugging and external tool
    /// inspection. It uses the graph's dense node IDs as AIGER variable indices,
    /// emits no latches, preserves input order, and emits AND definitions in
    /// dense node order. Output symbols are named `rootN`.
    pub fn to_aiger_ascii(&self, outputs: &[AigLit]) -> String {
        let and_count = self
            .nodes
            .iter()
            .filter(|node| matches!(node, AigNode::And(_, _)))
            .count();
        let max_variable = self.node_count().saturating_sub(1);
        let mut out = format!(
            "aag {} {} 0 {} {}\n",
            max_variable,
            self.input_count(),
            outputs.len(),
            and_count
        );

        for input in &self.inputs {
            let _ = writeln!(out, "{}", aiger_node_literal(input.node));
        }
        for &output in outputs {
            let _ = writeln!(out, "{}", aiger_literal(output));
        }
        for (node_id, node) in self.nodes() {
            if let AigNode::And(lhs, rhs) = node {
                let _ = writeln!(
                    out,
                    "{} {} {}",
                    aiger_node_literal(node_id),
                    aiger_literal(lhs),
                    aiger_literal(rhs)
                );
            }
        }
        for (index, input) in self.inputs.iter().enumerate() {
            let _ = writeln!(out, "i{index} {}", input.label);
        }
        for index in 0..outputs.len() {
            let _ = writeln!(out, "o{index} root{index}");
        }
        out.push_str("c\n");
        out.push_str("generated by axeyum-aig\n");
        out
    }

    fn push_node(&mut self, node: AigNode) -> AigNodeId {
        let id = AigNodeId(u32::try_from(self.nodes.len()).expect("node count fits u32"));
        self.nodes.push(node);
        id
    }

    fn evaluate_nodes(&self, inputs: &[bool]) -> Result<Vec<bool>, AigError> {
        if inputs.len() != self.inputs.len() {
            return Err(AigError::InputCountMismatch {
                expected: self.inputs.len(),
                found: inputs.len(),
            });
        }

        let mut values = vec![false; self.nodes.len()];
        for (index, node) in self.nodes.iter().copied().enumerate() {
            values[index] = match node {
                AigNode::ConstFalse => false,
                AigNode::Input(input) => inputs[input.index()],
                AigNode::And(lhs, rhs) => eval_lit(lhs, &values) && eval_lit(rhs, &values),
            };
        }
        Ok(values)
    }
}

impl Default for Aig {
    fn default() -> Self {
        Self::new()
    }
}

/// AIG evaluation errors.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AigError {
    /// The supplied input assignment did not match the graph input count.
    InputCountMismatch {
        /// Expected number of input bits.
        expected: usize,
        /// Actual number of input bits.
        found: usize,
    },
}

impl core::fmt::Display for AigError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            AigError::InputCountMismatch { expected, found } => {
                write!(f, "expected {expected} AIG inputs, found {found}")
            }
        }
    }
}

impl core::error::Error for AigError {}

enum SimplifiedAnd {
    Literal(AigLit),
    Node(AigLit, AigLit),
}

fn simplify_and(lhs: AigLit, rhs: AigLit) -> SimplifiedAnd {
    if lhs == AigLit::FALSE || rhs == AigLit::FALSE || lhs == rhs.negated() {
        return SimplifiedAnd::Literal(AigLit::FALSE);
    }
    if lhs == AigLit::TRUE {
        return SimplifiedAnd::Literal(rhs);
    }
    if rhs == AigLit::TRUE || lhs == rhs {
        return SimplifiedAnd::Literal(lhs);
    }
    SimplifiedAnd::Node(lhs, rhs)
}

fn consensus_shared_operand(lhs: (AigLit, AigLit), rhs: (AigLit, AigLit)) -> Option<AigLit> {
    for (shared, lhs_other) in [(lhs.0, lhs.1), (lhs.1, lhs.0)] {
        for (rhs_candidate, rhs_other) in [(rhs.0, rhs.1), (rhs.1, rhs.0)] {
            if shared == rhs_candidate && lhs_other == rhs_other.negated() {
                return Some(shared);
            }
        }
    }
    None
}

fn eval_lit(lit: AigLit, values: &[bool]) -> bool {
    values[lit.node.index()] ^ lit.inverted
}

fn aiger_node_literal(node: AigNodeId) -> usize {
    node.index() * 2
}

fn aiger_literal(lit: AigLit) -> usize {
    aiger_node_literal(lit.node()) + usize::from(lit.is_inverted())
}

#[cfg(test)]
mod tests {
    use super::{Aig, AigError, AigLit, AigNode};

    #[test]
    fn constants_and_inputs_evaluate() {
        let mut aig = Aig::new();
        let p = aig.input("p");
        let q = aig.input("q");

        assert_eq!(aig.node_count(), 3);
        assert_eq!(aig.input_count(), 2);
        assert_eq!(aig.inputs()[0].label, "p");
        assert_eq!(aig.inputs()[1].label, "q");
        assert_eq!(aig.node(p.node()), Some(AigNode::Input(aig.inputs()[0].id)));
        assert!(!aig.eval(AigLit::FALSE, &[true, false]).unwrap());
        assert!(aig.eval(AigLit::TRUE, &[true, false]).unwrap());
        assert!(aig.eval(p, &[true, false]).unwrap());
        assert!(!aig.eval(q, &[true, false]).unwrap());
    }

    #[test]
    fn nodes_iterate_in_dense_order_from_either_end() {
        let mut aig = Aig::new();
        let first = aig.input("first");
        let second = aig.input("second");
        let _root = aig.and(first, second);

        assert_eq!(
            aig.nodes()
                .map(|(node_id, _)| node_id.index())
                .collect::<Vec<_>>(),
            vec![0, 1, 2, 3]
        );
        assert_eq!(
            aig.nodes()
                .rev()
                .map(|(node_id, _)| node_id.index())
                .collect::<Vec<_>>(),
            vec![3, 2, 1, 0]
        );
    }

    #[test]
    fn and_nodes_are_structurally_hashed_and_simplified() {
        let mut aig = Aig::new();
        let p = aig.input("p");
        let q = aig.input("q");
        let p_and_q = aig.and(p, q);
        let q_and_p = aig.and(q, p);

        assert_eq!(p_and_q, q_and_p);
        assert_eq!(aig.node_count(), 4, "second AND reuses the first node");
        assert_eq!(aig.and(p, AigLit::TRUE), p);
        assert_eq!(aig.and(p, AigLit::FALSE), AigLit::FALSE);
        assert_eq!(aig.and(p, p), p);
        assert_eq!(aig.and(p, p.negated()), AigLit::FALSE);

        let p_or_q = aig.or(p, q);
        assert_eq!(aig.and(p, p_or_q), p);
        assert_eq!(aig.and(p_or_q, p), p);

        let not_p_or_q = aig.or(p.negated(), q);
        let p_and_q = aig.and(p, q);
        assert_eq!(aig.and(p, not_p_or_q), p_and_q);
        assert_eq!(aig.and(not_p_or_q, p), p_and_q);

        let p_or_q = aig.or(p, q);
        let not_p_or_q = aig.or(p.negated(), q);
        assert_eq!(aig.and(p_or_q, not_p_or_q), q);
        assert_eq!(aig.and(not_p_or_q, p_or_q), q);

        let p_or_not_q = aig.or(p, q.negated());
        assert_eq!(aig.and(p_or_q, p_or_not_q), p);
        assert_eq!(aig.and(p_or_not_q, p_or_q), p);
    }

    #[test]
    fn construction_stats_classify_every_primitive_and_request() {
        let mut aig = Aig::new();
        let p = aig.input("p");
        let q = aig.input("q");

        assert_eq!(aig.and(p, p), p); // trivial
        let p_and_q = aig.and(p, q); // new node
        assert_eq!(aig.and(q, p), p_and_q); // structural-hash hit
        let p_or_q = aig.or(p, q); // one new primitive AND
        assert_eq!(aig.and(p, p_or_q), p); // absorption

        let stats = aig.construction_stats();
        assert_eq!(stats.and_requests, 5);
        assert_eq!(stats.and_trivial_simplifications, 1);
        assert_eq!(stats.and_absorption_simplifications, 1);
        assert_eq!(stats.and_structural_hash_hits, 1);
        assert_eq!(stats.and_nodes_created, 2);
        assert_eq!(
            stats.and_requests,
            stats.and_trivial_simplifications
                + stats.and_absorption_simplifications
                + stats.and_structural_hash_hits
                + stats.and_nodes_created,
            "every primitive AND request has exactly one outcome"
        );
    }

    #[test]
    fn derived_gates_match_truth_tables() {
        let mut aig = Aig::new();
        let p = aig.input("p");
        let q = aig.input("q");
        let either = aig.or(p, q);
        let exactly_one = aig.xor(p, q);
        let mux = aig.mux(p, q, q.negated());

        for p_value in [false, true] {
            for q_value in [false, true] {
                let assignment = [p_value, q_value];
                assert_eq!(aig.eval(either, &assignment).unwrap(), p_value || q_value);
                assert_eq!(
                    aig.eval(exactly_one, &assignment).unwrap(),
                    p_value ^ q_value
                );
                assert_eq!(
                    aig.eval(mux, &assignment).unwrap(),
                    if p_value { q_value } else { !q_value }
                );
            }
        }
    }

    #[test]
    fn xor_and_mux_simplify_common_identities() {
        let mut aig = Aig::new();
        let p = aig.input("p");
        let q = aig.input("q");

        assert_eq!(aig.xor(p, AigLit::FALSE), p);
        assert_eq!(aig.xor(AigLit::FALSE, p), p);
        assert_eq!(aig.xor(p, AigLit::TRUE), p.negated());
        assert_eq!(aig.xor(AigLit::TRUE, p), p.negated());
        assert_eq!(aig.xor(p, p), AigLit::FALSE);
        assert_eq!(aig.xor(p, p.negated()), AigLit::TRUE);

        assert_eq!(aig.mux(AigLit::TRUE, p, q), p);
        assert_eq!(aig.mux(AigLit::FALSE, p, q), q);
        assert_eq!(aig.mux(p, q, q), q);
        assert_eq!(aig.mux(p, AigLit::TRUE, AigLit::FALSE), p);
        assert_eq!(aig.mux(p, AigLit::FALSE, AigLit::TRUE), p.negated());
        assert_eq!(aig.mux(p, q, AigLit::FALSE), aig.and(p, q));
        assert_eq!(aig.mux(p, AigLit::FALSE, q), aig.and(p.negated(), q));
        assert_eq!(aig.mux(p, p, q), aig.or(p, q));
        assert_eq!(aig.mux(p, p.negated(), q), aig.and(p.negated(), q));
        assert_eq!(aig.mux(p, q, p), aig.and(p, q));
        assert_eq!(aig.mux(p, q, p.negated()), aig.or(p.negated(), q));
        assert_eq!(aig.mux(p, q, q.negated()), aig.xor(p, q).negated());

        let p_and_q = aig.and(p, q);
        assert_eq!(aig.mux(p, p_and_q, q), q);
        assert_eq!(aig.mux(p, q, p_and_q), p_and_q);

        let not_p_and_q = aig.and(p.negated(), q);
        assert_eq!(aig.mux(p, not_p_and_q, q), not_p_and_q);
        assert_eq!(aig.mux(p, q, not_p_and_q), q);

        let p_or_q = aig.or(p, q);
        assert_eq!(aig.mux(p, p_or_q, q), p_or_q);
        assert_eq!(aig.mux(p, q, p_or_q), q);

        let not_p_or_q = aig.or(p.negated(), q);
        assert_eq!(aig.mux(p, not_p_or_q, q), q);
        assert_eq!(aig.mux(p, q, not_p_or_q), not_p_or_q);

        let r = aig.input("r");
        let q_and_r = aig.and(q, r);
        let p_or_r = aig.or(p, r);
        let not_p_or_r = aig.or(p.negated(), r);
        assert_eq!(aig.mux(p, q, q_and_r), aig.and(q, p_or_r));
        assert_eq!(aig.mux(p, q_and_r, q), aig.and(q, not_p_or_r));

        let q_or_r = aig.or(q, r);
        let not_p_and_r = aig.and(p.negated(), r);
        let p_and_r = aig.and(p, r);
        assert_eq!(aig.mux(p, q, q_or_r), aig.or(q, not_p_and_r));
        assert_eq!(aig.mux(p, q_or_r, q), aig.or(q, p_and_r));

        let before = aig.node_count();
        let root = aig.mux(p, AigLit::TRUE, q);
        assert_eq!(root, aig.or(p, q));
        assert!(
            aig.node_count() <= before + 1,
            "mux true branch simplifies to at most one OR node"
        );
        for p_value in [false, true] {
            for q_value in [false, true] {
                assert_eq!(
                    aig.eval(root, &[p_value, q_value, false]).unwrap(),
                    if p_value { true } else { q_value }
                );
            }
        }
    }

    #[test]
    fn deterministic_construction_produces_stable_ids() {
        fn build() -> (usize, usize, usize) {
            let mut aig = Aig::new();
            let p = aig.input("p");
            let q = aig.input("q");
            let either = aig.or(p, q);
            let exactly_one = aig.xor(p, q);
            let root = aig.and(either, exactly_one);
            (p.node().index(), q.node().index(), root.node().index())
        }

        assert_eq!(build(), build());
    }

    #[test]
    fn evaluation_rejects_wrong_input_count() {
        let mut aig = Aig::new();
        let p = aig.input("p");

        assert!(matches!(
            aig.eval(p, &[]),
            Err(AigError::InputCountMismatch {
                expected: 1,
                found: 0
            })
        ));
        assert!(matches!(
            aig.eval_many(&[p], &[true, false]),
            Err(AigError::InputCountMismatch {
                expected: 1,
                found: 2
            })
        ));
    }

    #[test]
    fn ascii_aiger_export_is_deterministic_and_replayable() {
        let mut aig = Aig::new();
        let p = aig.input("p");
        let q = aig.input("q");
        let root = aig.xor(p, q);

        assert_eq!(
            aig.to_aiger_ascii(&[root]),
            "\
aag 5 2 0 1 3
2
4
11
6 2 5
8 3 4
10 7 9
i0 p
i1 q
o0 root0
c
generated by axeyum-aig
"
        );
        assert!(aig.eval(root, &[true, false]).unwrap());
        assert!(!aig.eval(root, &[true, true]).unwrap());
    }
}
