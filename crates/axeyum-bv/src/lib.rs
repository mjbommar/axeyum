//! Bit-vector lowering from Axeyum terms to AIG wires.
//!
//! This first Phase 4 lowering slice is intentionally small: constants,
//! symbols, Boolean connectives, bit-vector bitwise operators, structural BV
//! operators, and the first arithmetic/comparison/shift circuits. It records
//! explicit term-bit and symbol-input maps so later CNF and SAT layers can
//! lift assignments back to original terms instead of trusting the lowered
//! form.

use std::collections::{BTreeMap, BTreeSet};

use axeyum_aig::{Aig, AigInputId, AigLit, AigNode};
use axeyum_ir::{
    Assignment, IrError, Op, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval,
    lsb_bits_to_value, value_to_lsb_bits,
};

/// Lowers one or more root terms into an AIG.
///
/// # Errors
///
/// Returns [`BitLowerError`] if a term uses an operator outside the initial
/// Phase 4 lowering subset, an assignment is missing during replay, or an
/// internal lowering invariant is violated.
pub fn lower_terms(arena: &TermArena, roots: &[TermId]) -> Result<BitLowering, BitLowerError> {
    LoweringBuilder::new(arena).lower_roots(roots)
}

/// Returns the first operator outside the current bit-lowering subset.
///
/// This is a cheap preflight for callers that need unsupported triage before
/// applying size budgets.
pub fn first_unsupported_op(arena: &TermArena, roots: &[TermId]) -> Option<(TermId, Op)> {
    let mut seen = BTreeSet::new();
    let mut stack = roots.iter().rev().copied().collect::<Vec<_>>();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        let TermNode::App { op, args } = arena.node(term) else {
            continue;
        };
        if is_unsupported_op(*op) {
            return Some((term, *op));
        }
        stack.extend(args.iter().rev().copied());
    }
    None
}

/// Returns the first subterm whose sort the bit-blaster cannot represent
/// directly — an integer (ADR-0014) or an array (ADR-0010). Such terms must be
/// eliminated or otherwise handled before bit lowering; this preflight lets
/// callers triage them as `Unsupported` (it catches sorts that the op-based
/// [`first_unsupported_op`] misses, e.g. a bare integer leaf under `=`).
pub fn first_unsupported_sort(arena: &TermArena, roots: &[TermId]) -> Option<(TermId, Sort)> {
    let mut seen = BTreeSet::new();
    let mut stack = roots.iter().rev().copied().collect::<Vec<_>>();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        match arena.sort_of(term) {
            // Floating-point lowers structurally to BitVec(exp+sig) (ADR-0026).
            Sort::Bool | Sort::BitVec(_) | Sort::Float { .. } => {}
            other => return Some((term, other)),
        }
        if let TermNode::App { args, .. } = arena.node(term) {
            stack.extend(args.iter().rev().copied());
        }
    }
    None
}

/// Lowered term bits in ADR-0006 LSB-first order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoweredTerm {
    term: TermId,
    sort: Sort,
    bits: Vec<AigLit>,
}

impl LoweredTerm {
    /// Original source term.
    pub fn term(&self) -> TermId {
        self.term
    }

    /// Source term sort.
    pub fn sort(&self) -> Sort {
        self.sort
    }

    /// AIG literals for this term. For `BV(w)`, element `i` is bit `i`.
    /// For `Bool`, the slice has length one.
    pub fn bits(&self) -> &[AigLit] {
        &self.bits
    }
}

/// Mapping from one original term bit to one AIG literal.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TermBitBinding {
    /// Source term.
    pub term: TermId,
    /// Bit index in ADR-0006 LSB-first order. Boolean terms use bit 0.
    pub bit_index: u32,
    /// AIG literal implementing this bit.
    pub literal: AigLit,
}

/// Mapping from one source symbol bit to one AIG input.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SymbolBitInput {
    /// Source symbol.
    pub symbol: SymbolId,
    /// Source symbol name, copied for diagnostics and future serialized maps.
    pub symbol_name: String,
    /// Source symbol sort.
    pub sort: Sort,
    /// Bit index in ADR-0006 LSB-first order. Boolean symbols use bit 0.
    pub bit_index: u32,
    /// AIG input ID in creation order.
    pub input: AigInputId,
    /// Positive AIG literal for this input.
    pub literal: AigLit,
}

/// AIG plus lift-map metadata for lowered roots.
#[derive(Debug, Clone)]
pub struct BitLowering {
    aig: Aig,
    roots: Vec<LoweredTerm>,
    term_bits: Vec<TermBitBinding>,
    term_bit_lookup: BTreeMap<(TermId, u32), AigLit>,
    symbol_inputs: Vec<SymbolBitInput>,
}

impl BitLowering {
    /// The generated AIG.
    pub fn aig(&self) -> &Aig {
        &self.aig
    }

    /// Lowered roots in input order.
    pub fn roots(&self) -> &[LoweredTerm] {
        &self.roots
    }

    /// Term-bit lift-map entries in deterministic lowering order.
    pub fn term_bits(&self) -> &[TermBitBinding] {
        &self.term_bits
    }

    /// Symbol-bit to AIG-input map entries in AIG input order.
    pub fn symbol_inputs(&self) -> &[SymbolBitInput] {
        &self.symbol_inputs
    }

    /// Looks up the AIG literal for one original term bit.
    pub fn literal_for_term_bit(&self, term: TermId, bit_index: u32) -> Option<AigLit> {
        self.term_bit_lookup.get(&(term, bit_index)).copied()
    }

    /// Converts an Axeyum assignment into AIG input values in creation order.
    ///
    /// # Errors
    ///
    /// Returns [`BitLowerError::Ir`] for unbound symbols or invalid values,
    /// and [`BitLowerError::AssignmentSortMismatch`] when a binding has the
    /// wrong sort for its symbol.
    pub fn input_values(&self, assignment: &Assignment) -> Result<Vec<bool>, BitLowerError> {
        let mut inputs = Vec::with_capacity(self.symbol_inputs.len());
        for binding in &self.symbol_inputs {
            let value = assignment
                .get(binding.symbol)
                .ok_or(IrError::UnboundSymbol(binding.symbol))?;
            if value.sort() != binding.sort {
                return Err(BitLowerError::AssignmentSortMismatch {
                    symbol: binding.symbol,
                    expected: binding.sort,
                    found: value.sort(),
                });
            }
            let bits = value_to_lsb_bits(value)?;
            let bit = bits.get(binding.bit_index as usize).copied().ok_or(
                BitLowerError::BadInputBit {
                    symbol: binding.symbol,
                    bit_index: binding.bit_index,
                },
            )?;
            inputs.push(bit);
        }
        Ok(inputs)
    }

    /// Evaluates one lowered root and reconstructs an Axeyum value.
    ///
    /// # Errors
    ///
    /// Returns [`BitLowerError`] if input conversion, AIG evaluation, or value
    /// reconstruction fails.
    pub fn evaluate_root(
        &self,
        root_index: usize,
        assignment: &Assignment,
    ) -> Result<Value, BitLowerError> {
        let root = self
            .roots
            .get(root_index)
            .ok_or(BitLowerError::UnknownRoot(root_index))?;
        let inputs = self.input_values(assignment)?;
        let bits = self.aig.eval_many(root.bits(), &inputs)?;
        Ok(lsb_bits_to_value(root.sort, &bits)?)
    }

    /// Evaluates every lowered root and reconstructs Axeyum values.
    ///
    /// # Errors
    ///
    /// Returns [`BitLowerError`] if input conversion, AIG evaluation, or value
    /// reconstruction fails.
    pub fn evaluate_roots(&self, assignment: &Assignment) -> Result<Vec<Value>, BitLowerError> {
        let inputs = self.input_values(assignment)?;
        self.roots
            .iter()
            .map(|root| {
                let bits = self.aig.eval_many(root.bits(), &inputs)?;
                Ok(lsb_bits_to_value(root.sort, &bits)?)
            })
            .collect()
    }

    /// Reconstructs an Axeyum model from replayed AIG node values.
    ///
    /// # Errors
    ///
    /// Returns [`BitLowerError`] if the AIG values have the wrong length, do not
    /// match the AIG semantics, or are missing a symbol bit.
    pub fn assignment_from_aig_values(
        &self,
        node_values: &[bool],
    ) -> Result<Assignment, BitLowerError> {
        assignment_from_aig_node_values(&self.aig, &self.symbol_inputs, node_values)
    }

    /// Reconstructs one lowered root value from replayed AIG node values.
    ///
    /// # Errors
    ///
    /// Returns [`BitLowerError`] if the root is unknown or the AIG values do not
    /// validate.
    pub fn root_value_from_aig_values(
        &self,
        root_index: usize,
        node_values: &[bool],
    ) -> Result<Value, BitLowerError> {
        self.validate_aig_values(node_values)?;
        let root = self
            .roots
            .get(root_index)
            .ok_or(BitLowerError::UnknownRoot(root_index))?;
        let bits = root
            .bits()
            .iter()
            .copied()
            .map(|lit| aig_lit_from_node_values(lit, node_values))
            .collect::<Result<Vec<_>, BitLowerError>>()?;
        Ok(lsb_bits_to_value(root.sort, &bits)?)
    }

    /// Reconstructs all lowered root values from replayed AIG node values.
    ///
    /// # Errors
    ///
    /// Returns [`BitLowerError`] if the AIG values do not validate.
    pub fn root_values_from_aig_values(
        &self,
        node_values: &[bool],
    ) -> Result<Vec<Value>, BitLowerError> {
        self.validate_aig_values(node_values)?;
        self.roots
            .iter()
            .map(|root| {
                let bits = root
                    .bits()
                    .iter()
                    .copied()
                    .map(|lit| aig_lit_from_node_values(lit, node_values))
                    .collect::<Result<Vec<_>, BitLowerError>>()?;
                Ok(lsb_bits_to_value(root.sort, &bits)?)
            })
            .collect()
    }

    fn validate_aig_values(&self, node_values: &[bool]) -> Result<(), BitLowerError> {
        validate_aig_node_values(&self.aig, node_values)
    }
}

/// Checks that `node_values` is a consistent valuation of every AIG node.
///
/// Shared by [`BitLowering`] and [`IncrementalLowering`] so both use the same
/// trusted replay check.
///
/// # Errors
///
/// Returns [`BitLowerError::AigValueLengthMismatch`] for the wrong length or
/// [`BitLowerError::AigValueMismatch`] when a node value contradicts the AIG.
fn validate_aig_node_values(aig: &Aig, node_values: &[bool]) -> Result<(), BitLowerError> {
    if node_values.len() != aig.node_count() {
        return Err(BitLowerError::AigValueLengthMismatch {
            expected: aig.node_count(),
            found: node_values.len(),
        });
    }
    for (node_id, node) in aig.nodes() {
        let expected = match node {
            AigNode::ConstFalse => false,
            AigNode::Input(_) => continue,
            AigNode::And(lhs, rhs) => {
                aig_lit_from_node_values(lhs, node_values)?
                    && aig_lit_from_node_values(rhs, node_values)?
            }
        };
        let found = node_values[node_id.index()];
        if found != expected {
            return Err(BitLowerError::AigValueMismatch {
                node: node_id.index(),
                expected,
                found,
            });
        }
    }
    Ok(())
}

/// Reconstructs an Axeyum assignment from replayed AIG node values, using the
/// symbol-input map. Shared by [`BitLowering`] and [`IncrementalLowering`].
///
/// # Errors
///
/// Returns [`BitLowerError`] if the AIG values are inconsistent, a symbol bit is
/// out of range, or a model bit is missing.
fn assignment_from_aig_node_values(
    aig: &Aig,
    symbol_inputs: &[SymbolBitInput],
    node_values: &[bool],
) -> Result<Assignment, BitLowerError> {
    validate_aig_node_values(aig, node_values)?;

    let mut symbol_bits: BTreeMap<SymbolId, SymbolModelBits> = BTreeMap::new();
    for binding in symbol_inputs {
        let entry = symbol_bits
            .entry(binding.symbol)
            .or_insert_with(|| SymbolModelBits::new(binding.sort));
        let bit_index = binding.bit_index as usize;
        if bit_index >= entry.bits.len() {
            return Err(BitLowerError::BadInputBit {
                symbol: binding.symbol,
                bit_index: binding.bit_index,
            });
        }
        entry.bits[bit_index] = aig_lit_from_node_values(binding.literal, node_values)?;
        entry.seen[bit_index] = true;
    }

    let mut assignment = Assignment::new();
    for (symbol, bits) in symbol_bits {
        for (bit_index, seen) in (0u32..).zip(bits.seen.iter().copied()) {
            if !seen {
                return Err(BitLowerError::MissingModelBit { symbol, bit_index });
            }
        }
        assignment.set(symbol, lsb_bits_to_value(bits.sort, &bits.bits)?);
    }
    Ok(assignment)
}

/// Persistent, incremental term-to-AIG lowering (ADR-0009 stage 2).
///
/// Unlike [`lower_terms`], which lowers a fixed batch into a fresh AIG, this
/// keeps one AIG and one symbol/term memo across many [`IncrementalLowering::lower`]
/// calls. A symbol always maps to the same AIG inputs, and shared subterms are
/// lowered once and reused, so an incremental backend can bit-blast each newly
/// asserted term without redoing the shared prefix.
///
/// Term and symbol IDs are arena-stable, so the **same arena** must be used
/// across all calls on one instance.
#[derive(Debug, Default)]
pub struct IncrementalLowering {
    aig: Aig,
    memo: BTreeMap<TermId, Vec<AigLit>>,
    term_bits: Vec<TermBitBinding>,
    term_bit_lookup: BTreeMap<(TermId, u32), AigLit>,
    symbol_inputs: Vec<SymbolBitInput>,
}

impl IncrementalLowering {
    /// Creates an empty incremental lowering context.
    pub fn new() -> Self {
        Self::default()
    }

    /// The persistent AIG built so far.
    pub fn aig(&self) -> &Aig {
        &self.aig
    }

    /// Number of AIG nodes built so far (including constant-false and inputs).
    ///
    /// Callers can record this before [`IncrementalLowering::lower`] to learn
    /// which nodes are new afterwards (the new range is `[before, after)`).
    pub fn node_count(&self) -> usize {
        self.aig.node_count()
    }

    /// Symbol-bit to AIG-input map entries in AIG input order.
    pub fn symbol_inputs(&self) -> &[SymbolBitInput] {
        &self.symbol_inputs
    }

    /// Lowers `root` into the persistent AIG, reusing already-lowered shared
    /// subterms, and returns the lowered root (its bit literals and sort).
    ///
    /// # Errors
    ///
    /// Returns [`BitLowerError`] if a term uses an operator outside the lowering
    /// subset or an internal lowering invariant is violated. On error the
    /// partially-built AIG state is retained.
    pub fn lower(&mut self, arena: &TermArena, root: TermId) -> Result<LoweredTerm, BitLowerError> {
        // Move the persistent accumulators into a one-shot builder, reuse the
        // existing lowering logic, then move the grown state back. The memo
        // makes shared subterms (and symbols) lower once across calls.
        let mut builder = LoweringBuilder {
            arena,
            aig: core::mem::take(&mut self.aig),
            memo: core::mem::take(&mut self.memo),
            term_bits: core::mem::take(&mut self.term_bits),
            term_bit_lookup: core::mem::take(&mut self.term_bit_lookup),
            symbol_inputs: core::mem::take(&mut self.symbol_inputs),
        };
        let result = builder.lower_term(root);
        self.aig = builder.aig;
        self.memo = builder.memo;
        self.term_bits = builder.term_bits;
        self.term_bit_lookup = builder.term_bit_lookup;
        self.symbol_inputs = builder.symbol_inputs;
        let bits = result?;
        Ok(LoweredTerm {
            term: root,
            sort: arena.sort_of(root),
            bits,
        })
    }

    /// Reconstructs an Axeyum model from replayed AIG node values, using the
    /// accumulated symbol-input map.
    ///
    /// # Errors
    ///
    /// See [`BitLowering::assignment_from_aig_values`].
    pub fn assignment_from_aig_values(
        &self,
        node_values: &[bool],
    ) -> Result<Assignment, BitLowerError> {
        assignment_from_aig_node_values(&self.aig, &self.symbol_inputs, node_values)
    }
}

/// Errors produced by the initial bit-lowering layer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BitLowerError {
    /// Error from the IR layer.
    Ir(IrError),
    /// Error from the AIG layer.
    Aig(axeyum_aig::AigError),
    /// Operator is outside the currently supported lowering subset.
    UnsupportedOp {
        /// Source term containing the unsupported operator.
        term: TermId,
        /// Unsupported operator.
        op: Op,
    },
    /// A lowered term had the wrong number of bits for its sort.
    BitWidthMismatch {
        /// Source term.
        term: TermId,
        /// Expected bit count.
        expected: u32,
        /// Actual bit count.
        found: usize,
    },
    /// Assignment value sort does not match the symbol sort.
    AssignmentSortMismatch {
        /// Source symbol.
        symbol: SymbolId,
        /// Expected symbol sort.
        expected: Sort,
        /// Assignment value sort.
        found: Sort,
    },
    /// Internal invariant failure: a symbol input referenced a missing bit.
    BadInputBit {
        /// Source symbol.
        symbol: SymbolId,
        /// Requested bit index.
        bit_index: u32,
    },
    /// Requested root index does not exist.
    UnknownRoot(usize),
    /// Replayed AIG values do not match the generated AIG node count.
    AigValueLengthMismatch {
        /// Expected node count.
        expected: usize,
        /// Actual value count.
        found: usize,
    },
    /// Replayed AIG values do not match a node definition.
    AigValueMismatch {
        /// AIG node index.
        node: usize,
        /// Expected value from the node definition.
        expected: bool,
        /// Replayed node value.
        found: bool,
    },
    /// A reconstructed symbol model is missing one of its bits.
    MissingModelBit {
        /// Source symbol.
        symbol: SymbolId,
        /// Missing bit index.
        bit_index: u32,
    },
}

impl From<IrError> for BitLowerError {
    fn from(error: IrError) -> Self {
        Self::Ir(error)
    }
}

impl From<axeyum_aig::AigError> for BitLowerError {
    fn from(error: axeyum_aig::AigError) -> Self {
        Self::Aig(error)
    }
}

impl core::fmt::Display for BitLowerError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            BitLowerError::Ir(error) => write!(f, "{error}"),
            BitLowerError::Aig(error) => write!(f, "{error}"),
            BitLowerError::UnsupportedOp { term, op } => {
                write!(
                    f,
                    "term #{} uses unsupported lowering operator {op:?}",
                    term.index()
                )
            }
            BitLowerError::BitWidthMismatch {
                term,
                expected,
                found,
            } => write!(
                f,
                "term #{} lowered to {found} bits, expected {expected}",
                term.index()
            ),
            BitLowerError::AssignmentSortMismatch {
                symbol,
                expected,
                found,
            } => write!(
                f,
                "symbol #{} assignment has sort {found}, expected {expected}",
                symbol.index()
            ),
            BitLowerError::BadInputBit { symbol, bit_index } => write!(
                f,
                "symbol #{} input map referenced missing bit {bit_index}",
                symbol.index()
            ),
            BitLowerError::UnknownRoot(index) => write!(f, "unknown lowered root #{index}"),
            BitLowerError::AigValueLengthMismatch { expected, found } => {
                write!(f, "expected {expected} AIG node values, found {found}")
            }
            BitLowerError::AigValueMismatch {
                node,
                expected,
                found,
            } => write!(
                f,
                "AIG node #{node} replayed as {found}, expected {expected}"
            ),
            BitLowerError::MissingModelBit { symbol, bit_index } => write!(
                f,
                "symbol #{} reconstructed model is missing bit {bit_index}",
                symbol.index()
            ),
        }
    }
}

impl core::error::Error for BitLowerError {}

struct LoweringBuilder<'a> {
    arena: &'a TermArena,
    aig: Aig,
    memo: BTreeMap<TermId, Vec<AigLit>>,
    term_bits: Vec<TermBitBinding>,
    term_bit_lookup: BTreeMap<(TermId, u32), AigLit>,
    symbol_inputs: Vec<SymbolBitInput>,
}

struct SymbolModelBits {
    sort: Sort,
    bits: Vec<bool>,
    seen: Vec<bool>,
}

impl SymbolModelBits {
    fn new(sort: Sort) -> Self {
        let width = sort_width(sort);
        Self {
            sort,
            bits: vec![false; width],
            seen: vec![false; width],
        }
    }
}

impl<'a> LoweringBuilder<'a> {
    fn new(arena: &'a TermArena) -> Self {
        Self {
            arena,
            aig: Aig::new(),
            memo: BTreeMap::new(),
            term_bits: Vec::new(),
            term_bit_lookup: BTreeMap::new(),
            symbol_inputs: Vec::new(),
        }
    }

    fn lower_roots(mut self, roots: &[TermId]) -> Result<BitLowering, BitLowerError> {
        let mut lowered_roots = Vec::with_capacity(roots.len());
        for &root in roots {
            let bits = self.lower_term(root)?;
            lowered_roots.push(LoweredTerm {
                term: root,
                sort: self.arena.sort_of(root),
                bits,
            });
        }
        Ok(BitLowering {
            aig: self.aig,
            roots: lowered_roots,
            term_bits: self.term_bits,
            term_bit_lookup: self.term_bit_lookup,
            symbol_inputs: self.symbol_inputs,
        })
    }

    fn lower_term(&mut self, root: TermId) -> Result<Vec<AigLit>, BitLowerError> {
        let mut stack = vec![(root, false)];
        while let Some((term, children_ready)) = stack.pop() {
            if self.memo.contains_key(&term) {
                continue;
            }
            match self.arena.node(term) {
                TermNode::BoolConst(value) => {
                    self.record(term, vec![const_lit(*value)])?;
                }
                TermNode::BvConst { width, value } => {
                    let bits = axeyum_ir::bv_value_to_lsb_bits(*width, *value)?
                        .into_iter()
                        .map(const_lit)
                        .collect::<Vec<_>>();
                    self.record(term, bits)?;
                }
                TermNode::WideBvConst(w) => {
                    // A >128-bit constant lowers to its LSB-first bit literals
                    // (wide-BV; the AIG is bit-level so width is unbounded).
                    let bits = w
                        .to_lsb_bits()
                        .into_iter()
                        .map(const_lit)
                        .collect::<Vec<_>>();
                    self.record(term, bits)?;
                }
                TermNode::IntConst(_) => {
                    // Integers are not bit-blasted (ADR-0014); callers preflight
                    // with `first_unsupported_sort`.
                    unreachable!("integer terms are rejected before bit lowering (ADR-0014)")
                }
                TermNode::RealConst(_) => {
                    // Reals are not bit-blasted (ADR-0015); callers preflight
                    // with `first_unsupported_sort`.
                    unreachable!("real terms are rejected before bit lowering (ADR-0015)")
                }
                TermNode::Symbol(symbol) => {
                    let bits = self.lower_symbol(*symbol);
                    self.record(term, bits)?;
                }
                TermNode::App { op, args } if children_ready => {
                    let operand_bits = args
                        .iter()
                        .map(|arg| {
                            self.memo
                                .get(arg)
                                .cloned()
                                .expect("children are lowered before parent")
                        })
                        .collect::<Vec<_>>();
                    let bits = self.lower_app(term, *op, &operand_bits)?;
                    self.record(term, bits)?;
                }
                TermNode::App { args, .. } => {
                    stack.push((term, true));
                    for &arg in args.iter().rev() {
                        stack.push((arg, false));
                    }
                }
            }
        }
        Ok(self
            .memo
            .get(&root)
            .cloned()
            .expect("root has been lowered"))
    }

    fn lower_symbol(&mut self, symbol: SymbolId) -> Vec<AigLit> {
        let (name, sort) = self.arena.symbol(symbol);
        match sort {
            Sort::Bool => vec![self.symbol_input(symbol, name, sort, 0)],
            // Floating-point shares the bit-vector lowering: `exp + sig` input bits.
            Sort::BitVec(_) | Sort::Float { .. } => {
                (0..sort.lowered_width().expect("bitvec/float has a width"))
                    .map(|bit_index| self.symbol_input(symbol, name, sort, bit_index))
                    .collect()
            }
            // Array symbols are eliminated to bit-vectors before lowering
            // (ADR-0010); callers preflight with `first_unsupported_op`.
            Sort::Array { .. } => {
                unreachable!("array terms are eliminated before bit lowering (ADR-0010)")
            }
            Sort::Int => {
                unreachable!("integer terms are rejected before bit lowering (ADR-0014)")
            }
            Sort::Real => {
                unreachable!("real terms are rejected before bit lowering (ADR-0015)")
            }
            Sort::Datatype(_) => {
                unreachable!("datatype terms are rejected before bit lowering (ADR-0022)")
            }
            Sort::Uninterpreted(_) => {
                unreachable!("uninterpreted-sort terms are rejected before bit lowering")
            }
            Sort::Seq(_) => {
                unreachable!("sequence terms are rejected before bit lowering (P2.7)")
            }
        }
    }

    fn symbol_input(&mut self, symbol: SymbolId, name: &str, sort: Sort, bit_index: u32) -> AigLit {
        let label = match sort {
            Sort::Bool => format!("{name}:bool"),
            Sort::BitVec(_) | Sort::Float { .. } => format!("{name}[{bit_index}]"),
            Sort::Array { .. } => {
                unreachable!("array terms are eliminated before bit lowering (ADR-0010)")
            }
            Sort::Int => {
                unreachable!("integer terms are rejected before bit lowering (ADR-0014)")
            }
            Sort::Real => {
                unreachable!("real terms are rejected before bit lowering (ADR-0015)")
            }
            Sort::Datatype(_) => {
                unreachable!("datatype terms are rejected before bit lowering (ADR-0022)")
            }
            Sort::Uninterpreted(_) => {
                unreachable!("uninterpreted-sort terms are rejected before bit lowering")
            }
            Sort::Seq(_) => {
                unreachable!("sequence terms are rejected before bit lowering (P2.7)")
            }
        };
        let literal = self.aig.input(label);
        let input = match self
            .aig
            .node(literal.node())
            .expect("new input node exists in AIG")
        {
            AigNode::Input(input) => input,
            AigNode::ConstFalse | AigNode::And(_, _) => {
                unreachable!("AIG input construction returned a non-input node")
            }
        };
        self.symbol_inputs.push(SymbolBitInput {
            symbol,
            symbol_name: name.to_owned(),
            sort,
            bit_index,
            input,
            literal,
        });
        literal
    }

    #[allow(clippy::too_many_lines)]
    fn lower_app(
        &mut self,
        term: TermId,
        op: Op,
        operands: &[Vec<AigLit>],
    ) -> Result<Vec<AigLit>, BitLowerError> {
        let bits =
            match op {
                Op::BoolNot => vec![expect_bool(term, &operands[0])?.negated()],
                Op::BoolAnd => vec![self.aig.and(
                    expect_bool(term, &operands[0])?,
                    expect_bool(term, &operands[1])?,
                )],
                Op::BoolOr => vec![self.aig.or(
                    expect_bool(term, &operands[0])?,
                    expect_bool(term, &operands[1])?,
                )],
                Op::BoolXor => vec![self.aig.xor(
                    expect_bool(term, &operands[0])?,
                    expect_bool(term, &operands[1])?,
                )],
                Op::BoolImplies => {
                    let antecedent = expect_bool(term, &operands[0])?;
                    let consequent = expect_bool(term, &operands[1])?;
                    vec![self.aig.or(antecedent.negated(), consequent)]
                }
                Op::BvNot => operands[0].iter().map(|bit| bit.negated()).collect(),
                Op::BvAnd => self.lower_pairwise(term, operands, Aig::and)?,
                Op::BvOr => self.lower_pairwise(term, operands, Aig::or)?,
                Op::BvXor => self.lower_pairwise(term, operands, Aig::xor)?,
                Op::BvNand => self
                    .lower_pairwise(term, operands, |aig, lhs, rhs| aig.and(lhs, rhs).negated())?,
                Op::BvNor => {
                    self.lower_pairwise(term, operands, |aig, lhs, rhs| aig.or(lhs, rhs).negated())?
                }
                Op::BvXnor => self
                    .lower_pairwise(term, operands, |aig, lhs, rhs| aig.xor(lhs, rhs).negated())?,
                Op::Eq | Op::BvComp => self.lower_equality_op(term, operands)?,
                Op::Ite => self.lower_ite_op(term, operands)?,
                Op::Extract { hi, lo } => Self::lower_extract(term, operands, hi, lo)?,
                Op::Concat => Self::lower_concat(term, operands)?,
                Op::ZeroExt { by } => Self::lower_zero_ext(term, operands, by)?,
                Op::SignExt { by } => Self::lower_sign_ext(term, operands, by)?,
                Op::BvNeg => self.lower_neg_op(term, operands)?,
                Op::BvAdd => self.lower_add_op(term, operands)?,
                Op::BvSub => self.lower_sub_op(term, operands)?,
                Op::BvMul => self.lower_mul_op(term, operands)?,
                Op::BvUdiv => self.lower_udiv_op(term, operands)?,
                Op::BvUrem => self.lower_urem_op(term, operands)?,
                Op::BvSdiv => self.lower_sdiv_op(term, operands)?,
                Op::BvSrem => self.lower_srem_op(term, operands)?,
                Op::BvSmod => self.lower_smod_op(term, operands)?,
                Op::BvUlt
                | Op::BvUle
                | Op::BvUgt
                | Op::BvUge
                | Op::BvSlt
                | Op::BvSle
                | Op::BvSgt
                | Op::BvSge => self.lower_compare_op(term, op, operands)?,
                Op::BvShl | Op::BvLshr | Op::BvAshr => self.lower_shift_op(term, op, operands)?,
                Op::RotateLeft { by } => Self::lower_rotate_op(term, operands, by, true)?,
                Op::RotateRight { by } => Self::lower_rotate_op(term, operands, by, false)?,
                // A floating-point reinterpret is identity on the bits (ADR-0026).
                Op::FpFromBits { .. } => {
                    let [source] = operands else {
                        return Err(BitLowerError::BitWidthMismatch {
                            term,
                            expected: 1,
                            found: operands.len(),
                        });
                    };
                    source.clone()
                }
                // Arrays are eliminated to QF_BV before lowering (ADR-0010);
                // uninterpreted functions via Ackermann reduction (ADR-0013);
                // integer arithmetic is not bit-blasted in this slice (ADR-0014).
                Op::Select
                | Op::Store
                | Op::ConstArray { .. }
                | Op::IntToReal
                | Op::RealToInt
                | Op::RealIsInt
                | Op::Bv2Nat
                | Op::Int2Bv { .. }
                | Op::Apply(_)
                | Op::IntNeg
                | Op::IntAdd
                | Op::IntSub
                | Op::IntMul
                | Op::IntDiv
                | Op::IntMod
                | Op::IntAbs
                | Op::IntLt
                | Op::IntLe
                | Op::IntGt
                | Op::IntGe
                | Op::RealNeg
                | Op::RealAdd
                | Op::RealSub
                | Op::RealMul
                | Op::RealDiv
                | Op::RealLt
                | Op::RealLe
                | Op::RealGt
                | Op::RealGe
                | Op::Forall(_)
                | Op::Exists(_)
                | Op::DtConstruct { .. }
                | Op::DtSelect { .. }
                | Op::DtTest(_) => {
                    return Err(BitLowerError::UnsupportedOp { term, op });
                }
            };
        self.check_width(term, &bits)?;
        Ok(bits)
    }

    fn lower_neg_op(
        &mut self,
        term: TermId,
        operands: &[Vec<AigLit>],
    ) -> Result<Vec<AigLit>, BitLowerError> {
        let [source] = operands else {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: 1,
                found: operands.len(),
            });
        };
        let inverted = source.iter().map(|bit| bit.negated()).collect::<Vec<_>>();
        Ok(self.lower_increment(&inverted))
    }

    fn lower_add_op(
        &mut self,
        term: TermId,
        operands: &[Vec<AigLit>],
    ) -> Result<Vec<AigLit>, BitLowerError> {
        let [lhs, rhs] = operands else {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: 2,
                found: operands.len(),
            });
        };
        self.lower_add_bits(term, lhs, rhs, AigLit::FALSE)
    }

    fn lower_sub_op(
        &mut self,
        term: TermId,
        operands: &[Vec<AigLit>],
    ) -> Result<Vec<AigLit>, BitLowerError> {
        let [lhs, rhs] = operands else {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: 2,
                found: operands.len(),
            });
        };
        let inverted_rhs = rhs.iter().map(|bit| bit.negated()).collect::<Vec<_>>();
        self.lower_add_bits(term, lhs, &inverted_rhs, AigLit::TRUE)
    }

    fn lower_mul_op(
        &mut self,
        term: TermId,
        operands: &[Vec<AigLit>],
    ) -> Result<Vec<AigLit>, BitLowerError> {
        let [lhs, rhs] = operands else {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: 2,
                found: operands.len(),
            });
        };
        if lhs.len() != rhs.len() {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: u32::try_from(lhs.len()).unwrap_or(u32::MAX),
                found: rhs.len(),
            });
        }
        let width = lhs.len();
        // Shift-and-add multiplier, truncated to `width` bits (SMT-LIB bvmul is
        // multiplication modulo 2^width). Partial product `i` is `lhs << i`
        // gated by `rhs[i]`; bits shifted past the top are dropped, so the
        // running sum stays `width` bits and equals the wrapping product. The
        // AIG folds the gated-`false` and shifted-in `false` bits, so low
        // multiplier bits and leading partial bits cost no gates.
        //
        // A modified-Booth (radix-4) recoding was implemented and verified
        // (exhaustive evaluator equality + DRAT miter) and then reverted: it
        // halves the partial-product *count* but its per-digit select/negate
        // logic is ~4x heavier than a single AND, so the net AND-node change was
        // only +6% at width 8, -8% at width 16, -14% at width 24. The public
        // QF_BV frontier instances are 8-bit, where Booth is a *regression*, so
        // it is not the right size lever here (see PLAN.md Status 2026-06-13).
        let mut result = vec![AigLit::FALSE; width];
        for i in 0..width {
            let multiplier_bit = rhs[i];
            let mut partial = vec![AigLit::FALSE; width];
            for j in i..width {
                partial[j] = self.aig.and(lhs[j - i], multiplier_bit);
            }
            result = self.lower_add_bits(term, &result, &partial, AigLit::FALSE)?;
        }
        Ok(result)
    }

    fn lower_udiv_op(
        &mut self,
        term: TermId,
        operands: &[Vec<AigLit>],
    ) -> Result<Vec<AigLit>, BitLowerError> {
        let (dividend, divisor) = expect_two(term, operands)?;
        let (quotient, _remainder) = self.unsigned_divrem(term, dividend, divisor)?;
        Ok(quotient)
    }

    fn lower_urem_op(
        &mut self,
        term: TermId,
        operands: &[Vec<AigLit>],
    ) -> Result<Vec<AigLit>, BitLowerError> {
        let (dividend, divisor) = expect_two(term, operands)?;
        let (_quotient, remainder) = self.unsigned_divrem(term, dividend, divisor)?;
        Ok(remainder)
    }

    /// Combinational restoring divider.
    ///
    /// Returns `(quotient, remainder)` for the unsigned division of `dividend`
    /// by `divisor`, both `width` bits, applying SMT-LIB totality: division by
    /// zero yields an all-ones quotient and the dividend as remainder. The AIG's
    /// structural hashing deduplicates the shared circuit when both `bvudiv` and
    /// `bvurem` of the same operands appear.
    fn unsigned_divrem(
        &mut self,
        term: TermId,
        dividend: &[AigLit],
        divisor: &[AigLit],
    ) -> Result<(Vec<AigLit>, Vec<AigLit>), BitLowerError> {
        let width = dividend.len();
        if divisor.len() != width {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: u32::try_from(width).unwrap_or(u32::MAX),
                found: divisor.len(),
            });
        }

        // Zero-extend the divisor by one bit so the partial-remainder compare
        // and subtract never overflow: the invariant `remainder < divisor`
        // keeps `shifted = 2*remainder + bit < 2*divisor`, which fits in
        // `width + 1` bits, and the post-step value is again `< divisor`.
        let mut divisor_ext = divisor.to_vec();
        divisor_ext.push(AigLit::FALSE);
        let negated_divisor_ext = divisor_ext
            .iter()
            .map(|bit| bit.negated())
            .collect::<Vec<_>>();

        let mut remainder = vec![AigLit::FALSE; width];
        let mut quotient = vec![AigLit::FALSE; width];

        for index in (0..width).rev() {
            // shifted = (remainder << 1) | dividend[index], width + 1 bits.
            let mut shifted = Vec::with_capacity(width + 1);
            shifted.push(dividend[index]);
            shifted.extend_from_slice(&remainder);

            let less = self.lower_unsigned_less(term, &shifted, &divisor_ext)?;
            let greater_equal = less.negated();
            // diff = shifted - divisor (two's complement add of the negation).
            let diff = self.lower_add_bits(term, &shifted, &negated_divisor_ext, AigLit::TRUE)?;
            let next = self.mux_bits(greater_equal, &diff, &shifted);
            // The post-step value is `< divisor`, so its top bit is zero.
            remainder = next[..width].to_vec();
            quotient[index] = greater_equal;
        }

        // SMT-LIB totality: `bvudiv x 0 = ~0`, `bvurem x 0 = x`.
        let divisor_is_zero = self.lower_all_bits_clear(divisor);
        let all_ones = vec![AigLit::TRUE; width];
        let quotient = self.mux_bits(divisor_is_zero, &all_ones, &quotient);
        let remainder = self.mux_bits(divisor_is_zero, dividend, &remainder);
        Ok((quotient, remainder))
    }

    fn mux_bits(
        &mut self,
        condition: AigLit,
        then_bits: &[AigLit],
        else_bits: &[AigLit],
    ) -> Vec<AigLit> {
        then_bits
            .iter()
            .copied()
            .zip(else_bits.iter().copied())
            .map(|(then_bit, else_bit)| self.aig.mux(condition, then_bit, else_bit))
            .collect()
    }

    /// Two's-complement negation: invert and increment.
    fn negate_bits(&mut self, bits: &[AigLit]) -> Vec<AigLit> {
        let inverted = bits.iter().map(|bit| bit.negated()).collect::<Vec<_>>();
        self.lower_increment(&inverted)
    }

    /// Absolute value under two's complement: `msb ? -x : x` (the most-negative
    /// value maps to itself, matching the SMT-LIB signed-division expansion).
    fn absolute_bits(&mut self, bits: &[AigLit]) -> Vec<AigLit> {
        let sign = bits[bits.len() - 1];
        let negated = self.negate_bits(bits);
        self.mux_bits(sign, &negated, bits)
    }

    /// Selects one of four equal-width vectors by two sign bits:
    /// `(sign_a, sign_b) -> v00 | v10 | v01 | v11`.
    fn select_by_signs(
        &mut self,
        sign_a: AigLit,
        sign_b: AigLit,
        v00: &[AigLit],
        v10: &[AigLit],
        v01: &[AigLit],
        v11: &[AigLit],
    ) -> Vec<AigLit> {
        let when_a_clear = self.mux_bits(sign_b, v01, v00);
        let when_a_set = self.mux_bits(sign_b, v11, v10);
        self.mux_bits(sign_a, &when_a_set, &when_a_clear)
    }

    /// Shared signed-division core: returns the operand sign bits and the
    /// unsigned quotient/remainder of the operands' absolute values. The AIG's
    /// structural hashing deduplicates this across `bvsdiv`/`bvsrem`/`bvsmod` of
    /// the same operands.
    fn signed_divrem_abs(
        &mut self,
        term: TermId,
        dividend: &[AigLit],
        divisor: &[AigLit],
    ) -> Result<(AigLit, AigLit, Vec<AigLit>, Vec<AigLit>), BitLowerError> {
        let width = dividend.len();
        if divisor.len() != width {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: u32::try_from(width).unwrap_or(u32::MAX),
                found: divisor.len(),
            });
        }
        let sign_dividend = dividend[width - 1];
        let sign_divisor = divisor[width - 1];
        let abs_dividend = self.absolute_bits(dividend);
        let abs_divisor = self.absolute_bits(divisor);
        let (quotient, remainder) = self.unsigned_divrem(term, &abs_dividend, &abs_divisor)?;
        Ok((sign_dividend, sign_divisor, quotient, remainder))
    }

    fn lower_sdiv_op(
        &mut self,
        term: TermId,
        operands: &[Vec<AigLit>],
    ) -> Result<Vec<AigLit>, BitLowerError> {
        let (dividend, divisor) = expect_two(term, operands)?;
        let (sign_dividend, sign_divisor, quotient, _remainder) =
            self.signed_divrem_abs(term, dividend, divisor)?;
        // The quotient is negated exactly when the operand signs differ.
        let signs_differ = self.aig.xor(sign_dividend, sign_divisor);
        let negated_quotient = self.negate_bits(&quotient);
        Ok(self.mux_bits(signs_differ, &negated_quotient, &quotient))
    }

    fn lower_srem_op(
        &mut self,
        term: TermId,
        operands: &[Vec<AigLit>],
    ) -> Result<Vec<AigLit>, BitLowerError> {
        let (dividend, divisor) = expect_two(term, operands)?;
        let (sign_dividend, _sign_divisor, _quotient, remainder) =
            self.signed_divrem_abs(term, dividend, divisor)?;
        // The remainder's sign follows the dividend.
        let negated_remainder = self.negate_bits(&remainder);
        Ok(self.mux_bits(sign_dividend, &negated_remainder, &remainder))
    }

    fn lower_smod_op(
        &mut self,
        term: TermId,
        operands: &[Vec<AigLit>],
    ) -> Result<Vec<AigLit>, BitLowerError> {
        let (dividend, divisor) = expect_two(term, operands)?;
        let (sign_dividend, sign_divisor, _quotient, remainder) =
            self.signed_divrem_abs(term, dividend, divisor)?;
        // The result's sign follows the divisor (SMT-LIB bvsmod expansion); a
        // zero unsigned remainder yields zero regardless of signs.
        let remainder_is_zero = self.lower_all_bits_clear(&remainder);
        let negated_remainder = self.negate_bits(&remainder);
        let both_nonneg = remainder.clone();
        let dividend_neg = self.lower_add_bits(term, &negated_remainder, divisor, AigLit::FALSE)?;
        let divisor_neg = self.lower_add_bits(term, &remainder, divisor, AigLit::FALSE)?;
        let both_neg = negated_remainder.clone();
        let selected = self.select_by_signs(
            sign_dividend,
            sign_divisor,
            &both_nonneg,
            &dividend_neg,
            &divisor_neg,
            &both_neg,
        );
        Ok(self.mux_bits(remainder_is_zero, &remainder, &selected))
    }

    fn lower_compare_op(
        &mut self,
        term: TermId,
        op: Op,
        operands: &[Vec<AigLit>],
    ) -> Result<Vec<AigLit>, BitLowerError> {
        let [lhs, rhs] = operands else {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: 2,
                found: operands.len(),
            });
        };
        let comparison = match op {
            Op::BvUlt => self.lower_unsigned_less(term, lhs, rhs)?,
            Op::BvUle => self.lower_unsigned_less(term, rhs, lhs)?.negated(),
            Op::BvUgt => self.lower_unsigned_less(term, rhs, lhs)?,
            Op::BvUge => self.lower_unsigned_less(term, lhs, rhs)?.negated(),
            Op::BvSlt => self.lower_signed_less(term, lhs, rhs)?,
            Op::BvSle => self.lower_signed_less(term, rhs, lhs)?.negated(),
            Op::BvSgt => self.lower_signed_less(term, rhs, lhs)?,
            Op::BvSge => self.lower_signed_less(term, lhs, rhs)?.negated(),
            _ => unreachable!("caller only passes comparison operators"),
        };
        Ok(vec![comparison])
    }

    fn lower_shift_op(
        &mut self,
        term: TermId,
        op: Op,
        operands: &[Vec<AigLit>],
    ) -> Result<Vec<AigLit>, BitLowerError> {
        let [source, amount] = operands else {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: 2,
                found: operands.len(),
            });
        };
        if source.len() != amount.len() {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: u32::try_from(source.len()).unwrap_or(u32::MAX),
                found: amount.len(),
            });
        }

        let sign = *source
            .last()
            .expect("BitVec widths are non-zero by construction");
        let overflow_result = match op {
            Op::BvShl | Op::BvLshr => vec![AigLit::FALSE; source.len()],
            Op::BvAshr => vec![sign; source.len()],
            _ => unreachable!("caller only passes shift operators"),
        };

        let mut result = source.clone();
        let mut stage_shift = 1usize;
        let mut amount_bit = 0usize;
        while stage_shift < source.len() {
            let shifted = Self::shifted_bits(op, &result, stage_shift);
            result = self.lower_mux_bits(term, amount[amount_bit], &shifted, &result)?;
            stage_shift <<= 1;
            amount_bit += 1;
        }

        let width_constant = constant_lits(
            amount.len(),
            u128::try_from(source.len()).expect("width fits u128"),
        );
        let in_range = self.lower_unsigned_less(term, amount, &width_constant)?;
        result = self.lower_mux_bits(term, in_range, &result, &overflow_result)?;
        Ok(result)
    }

    fn lower_rotate_op(
        term: TermId,
        operands: &[Vec<AigLit>],
        by: u32,
        left: bool,
    ) -> Result<Vec<AigLit>, BitLowerError> {
        let [source] = operands else {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: 1,
                found: operands.len(),
            });
        };
        let width = source.len();
        let shift = usize::try_from(by).expect("rotate amount fits usize") % width;
        Ok((0..width)
            .map(|index| {
                let source_index = if left {
                    (index + width - shift) % width
                } else {
                    (index + shift) % width
                };
                source[source_index]
            })
            .collect())
    }

    fn lower_equality_op(
        &mut self,
        term: TermId,
        operands: &[Vec<AigLit>],
    ) -> Result<Vec<AigLit>, BitLowerError> {
        let [lhs, rhs] = operands else {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: 2,
                found: operands.len(),
            });
        };
        Ok(vec![self.lower_equal(term, lhs, rhs)?])
    }

    fn lower_ite_op(
        &mut self,
        term: TermId,
        operands: &[Vec<AigLit>],
    ) -> Result<Vec<AigLit>, BitLowerError> {
        let [condition, then_bits, else_bits] = operands else {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: 3,
                found: operands.len(),
            });
        };
        let condition = expect_bool(term, condition)?;
        self.lower_mux_bits(term, condition, then_bits, else_bits)
    }

    fn lower_extract(
        term: TermId,
        operands: &[Vec<AigLit>],
        hi: u32,
        lo: u32,
    ) -> Result<Vec<AigLit>, BitLowerError> {
        let [bits] = operands else {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: 1,
                found: operands.len(),
            });
        };
        Ok(bits[lo as usize..=hi as usize].to_vec())
    }

    fn lower_concat(term: TermId, operands: &[Vec<AigLit>]) -> Result<Vec<AigLit>, BitLowerError> {
        let [high, low] = operands else {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: 2,
                found: operands.len(),
            });
        };
        Ok(low.iter().chain(high).copied().collect())
    }

    fn lower_zero_ext(
        term: TermId,
        operands: &[Vec<AigLit>],
        by: u32,
    ) -> Result<Vec<AigLit>, BitLowerError> {
        let [source] = operands else {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: 1,
                found: operands.len(),
            });
        };
        let mut bits = source.clone();
        bits.extend(std::iter::repeat_n(AigLit::FALSE, by as usize));
        Ok(bits)
    }

    fn lower_sign_ext(
        term: TermId,
        operands: &[Vec<AigLit>],
        by: u32,
    ) -> Result<Vec<AigLit>, BitLowerError> {
        let [source] = operands else {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: 1,
                found: operands.len(),
            });
        };
        let mut bits = source.clone();
        let sign = *bits
            .last()
            .expect("BitVec widths are non-zero by construction");
        bits.extend(std::iter::repeat_n(sign, by as usize));
        Ok(bits)
    }

    fn lower_equal(
        &mut self,
        term: TermId,
        lhs: &[AigLit],
        rhs: &[AigLit],
    ) -> Result<AigLit, BitLowerError> {
        if lhs.len() != rhs.len() {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: u32::try_from(lhs.len()).unwrap_or(u32::MAX),
                found: rhs.len(),
            });
        }
        let mut equal = AigLit::TRUE;
        for (lhs, rhs) in lhs.iter().copied().zip(rhs.iter().copied()) {
            let bit_equal = self.aig.xor(lhs, rhs).negated();
            equal = self.aig.and(equal, bit_equal);
        }
        Ok(equal)
    }

    fn lower_mux_bits(
        &mut self,
        term: TermId,
        condition: AigLit,
        then_bits: &[AigLit],
        else_bits: &[AigLit],
    ) -> Result<Vec<AigLit>, BitLowerError> {
        if then_bits.len() != else_bits.len() {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: u32::try_from(then_bits.len()).unwrap_or(u32::MAX),
                found: else_bits.len(),
            });
        }
        Ok(then_bits
            .iter()
            .copied()
            .zip(else_bits.iter().copied())
            .map(|(then_lit, else_lit)| self.aig.mux(condition, then_lit, else_lit))
            .collect())
    }

    fn lower_increment(&mut self, bits: &[AigLit]) -> Vec<AigLit> {
        let mut carry = AigLit::TRUE;
        bits.iter()
            .copied()
            .map(|bit| {
                let sum = self.aig.xor(bit, carry);
                carry = self.aig.and(bit, carry);
                sum
            })
            .collect()
    }

    fn lower_add_bits(
        &mut self,
        term: TermId,
        lhs: &[AigLit],
        rhs: &[AigLit],
        mut carry: AigLit,
    ) -> Result<Vec<AigLit>, BitLowerError> {
        if lhs.len() != rhs.len() {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: u32::try_from(lhs.len()).unwrap_or(u32::MAX),
                found: rhs.len(),
            });
        }
        let mut result = Vec::with_capacity(lhs.len());
        for (lhs, rhs) in lhs.iter().copied().zip(rhs.iter().copied()) {
            let pair_sum = self.aig.xor(lhs, rhs);
            let sum = self.aig.xor(pair_sum, carry);
            let carry_from_pair = self.aig.and(lhs, rhs);
            let carry_from_input = self.aig.and(pair_sum, carry);
            carry = self.aig.or(carry_from_pair, carry_from_input);
            result.push(sum);
        }
        Ok(result)
    }

    fn lower_unsigned_less(
        &mut self,
        term: TermId,
        lhs: &[AigLit],
        rhs: &[AigLit],
    ) -> Result<AigLit, BitLowerError> {
        if lhs.len() != rhs.len() {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: u32::try_from(lhs.len()).unwrap_or(u32::MAX),
                found: rhs.len(),
            });
        }
        if lhs == rhs || constant_bits_are(rhs, false) || constant_bits_are(lhs, true) {
            return Ok(AigLit::FALSE);
        }
        if let Some(lhs_value) = constant_bits_value(lhs)
            && let Some(rhs_value) = constant_bits_value(rhs)
        {
            return Ok(const_lit(lhs_value < rhs_value));
        }
        if constant_bits_are(lhs, false) {
            return Ok(self.lower_any_bit_set(rhs));
        }
        if constant_bits_are(rhs, true) {
            return Ok(self.lower_any_bit_clear(lhs));
        }
        if let Some(lhs_value) = constant_bits_value(lhs)
            && let Some(next) = lhs_value.checked_add(1)
            && next.is_power_of_two()
        {
            let first_possible_greater_bit =
                usize::try_from(next.trailing_zeros()).expect("trailing zeros fits usize");
            return Ok(self.lower_any_bit_set(&rhs[first_possible_greater_bit..]));
        }
        if let Some(rhs_value) = constant_bits_value(rhs)
            && rhs_value.is_power_of_two()
        {
            let first_forbidden_bit =
                usize::try_from(rhs_value.trailing_zeros()).expect("trailing zeros fits usize");
            return Ok(self.lower_all_bits_clear(&lhs[first_forbidden_bit..]));
        }
        let mut less = AigLit::FALSE;
        let mut equal = AigLit::TRUE;
        for index in (0..lhs.len()).rev() {
            let lhs = lhs[index];
            let rhs = rhs[index];
            let bit_less = self.aig.and(lhs.negated(), rhs);
            let active_less = self.aig.and(equal, bit_less);
            less = self.aig.or(less, active_less);
            if index > 0 {
                let bits_equal = self.aig.xor(lhs, rhs).negated();
                equal = self.aig.and(equal, bits_equal);
            }
        }
        Ok(less)
    }

    fn lower_signed_less(
        &mut self,
        term: TermId,
        lhs: &[AigLit],
        rhs: &[AigLit],
    ) -> Result<AigLit, BitLowerError> {
        let lhs_sign = *lhs
            .last()
            .expect("BitVec widths are non-zero by construction");
        let rhs_sign = *rhs
            .last()
            .expect("BitVec widths are non-zero by construction");
        match (constant_lit_value(lhs_sign), constant_lit_value(rhs_sign)) {
            (Some(false), Some(true)) => return Ok(AigLit::FALSE),
            (Some(true), Some(false)) => return Ok(AigLit::TRUE),
            (Some(_), Some(_)) => {
                return self.lower_unsigned_less(
                    term,
                    &lhs[..lhs.len() - 1],
                    &rhs[..rhs.len() - 1],
                );
            }
            (None, Some(false)) if constant_bits_are(&rhs[..rhs.len() - 1], false) => {
                return Ok(lhs_sign);
            }
            (None, Some(false)) => {
                let magnitude_less =
                    self.lower_unsigned_less(term, &lhs[..lhs.len() - 1], &rhs[..rhs.len() - 1])?;
                return Ok(self.aig.or(lhs_sign, magnitude_less));
            }
            (None, Some(true)) => {
                let magnitude_less =
                    self.lower_unsigned_less(term, &lhs[..lhs.len() - 1], &rhs[..rhs.len() - 1])?;
                return Ok(self.aig.and(lhs_sign, magnitude_less));
            }
            (Some(false), None) => {
                let magnitude_less =
                    self.lower_unsigned_less(term, &lhs[..lhs.len() - 1], &rhs[..rhs.len() - 1])?;
                return Ok(self.aig.and(rhs_sign.negated(), magnitude_less));
            }
            (Some(true), None) => {
                let magnitude_less =
                    self.lower_unsigned_less(term, &lhs[..lhs.len() - 1], &rhs[..rhs.len() - 1])?;
                return Ok(self.aig.or(rhs_sign.negated(), magnitude_less));
            }
            (None, None) => {}
        }
        let magnitude_less =
            self.lower_unsigned_less(term, &lhs[..lhs.len() - 1], &rhs[..rhs.len() - 1])?;
        let signs_equal = self.aig.xor(lhs_sign, rhs_sign).negated();
        let lhs_negative_rhs_nonnegative = self.aig.and(lhs_sign, rhs_sign.negated());
        let same_sign_less = self.aig.and(signs_equal, magnitude_less);
        Ok(self.aig.or(lhs_negative_rhs_nonnegative, same_sign_less))
    }

    fn shifted_bits(op: Op, source: &[AigLit], shift: usize) -> Vec<AigLit> {
        let sign = *source
            .last()
            .expect("BitVec widths are non-zero by construction");
        (0..source.len())
            .map(|index| match op {
                Op::BvShl => index
                    .checked_sub(shift)
                    .map_or(AigLit::FALSE, |source_index| source[source_index]),
                Op::BvLshr => source.get(index + shift).copied().unwrap_or(AigLit::FALSE),
                Op::BvAshr => source.get(index + shift).copied().unwrap_or(sign),
                _ => unreachable!("caller only passes shift operators"),
            })
            .collect()
    }

    fn lower_pairwise(
        &mut self,
        term: TermId,
        operands: &[Vec<AigLit>],
        build: impl Fn(&mut Aig, AigLit, AigLit) -> AigLit,
    ) -> Result<Vec<AigLit>, BitLowerError> {
        let [lhs, rhs] = &operands else {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: self.expected_width(term),
                found: operands.len(),
            });
        };
        if lhs.len() != rhs.len() {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: u32::try_from(lhs.len()).unwrap_or(u32::MAX),
                found: rhs.len(),
            });
        }
        Ok(lhs
            .iter()
            .copied()
            .zip(rhs.iter().copied())
            .map(|(lhs, rhs)| build(&mut self.aig, lhs, rhs))
            .collect())
    }

    fn lower_any_bit_set(&mut self, bits: &[AigLit]) -> AigLit {
        bits.iter()
            .copied()
            .fold(AigLit::FALSE, |acc, bit| self.aig.or(acc, bit))
    }

    fn lower_any_bit_clear(&mut self, bits: &[AigLit]) -> AigLit {
        bits.iter()
            .copied()
            .fold(AigLit::FALSE, |acc, bit| self.aig.or(acc, bit.negated()))
    }

    fn lower_all_bits_clear(&mut self, bits: &[AigLit]) -> AigLit {
        self.lower_any_bit_set(bits).negated()
    }

    fn record(&mut self, term: TermId, bits: Vec<AigLit>) -> Result<(), BitLowerError> {
        self.check_width(term, &bits)?;
        for (index, &literal) in bits.iter().enumerate() {
            let bit_index = u32::try_from(index).expect("bit index fits u32");
            let binding = TermBitBinding {
                term,
                bit_index,
                literal,
            };
            self.term_bits.push(binding);
            self.term_bit_lookup.insert((term, bit_index), literal);
        }
        self.memo.insert(term, bits);
        Ok(())
    }

    fn check_width(&self, term: TermId, bits: &[AigLit]) -> Result<(), BitLowerError> {
        let expected = self.expected_width(term);
        if bits.len() == expected as usize {
            Ok(())
        } else {
            Err(BitLowerError::BitWidthMismatch {
                term,
                expected,
                found: bits.len(),
            })
        }
    }

    fn expected_width(&self, term: TermId) -> u32 {
        match self.arena.sort_of(term) {
            Sort::Bool => 1,
            Sort::BitVec(width) => width,
            Sort::Float { exp, sig } => exp + sig,
            Sort::Array { .. } => {
                unreachable!("array terms are eliminated before bit lowering (ADR-0010)")
            }
            Sort::Int => {
                unreachable!("integer terms are rejected before bit lowering (ADR-0014)")
            }
            Sort::Real => {
                unreachable!("real terms are rejected before bit lowering (ADR-0015)")
            }
            Sort::Datatype(_) => {
                unreachable!("datatype terms are rejected before bit lowering (ADR-0022)")
            }
            Sort::Uninterpreted(_) => {
                unreachable!("uninterpreted-sort terms are rejected before bit lowering")
            }
            Sort::Seq(_) => {
                unreachable!("sequence terms are rejected before bit lowering (P2.7)")
            }
        }
    }
}

fn const_lit(value: bool) -> AigLit {
    if value { AigLit::TRUE } else { AigLit::FALSE }
}

fn constant_lit_value(lit: AigLit) -> Option<bool> {
    if lit == AigLit::FALSE {
        Some(false)
    } else if lit == AigLit::TRUE {
        Some(true)
    } else {
        None
    }
}

fn constant_bits_are(bits: &[AigLit], value: bool) -> bool {
    bits.iter()
        .copied()
        .all(|bit| constant_lit_value(bit) == Some(value))
}

fn constant_bits_value(bits: &[AigLit]) -> Option<u128> {
    if bits.len() > u128::BITS as usize {
        return None;
    }
    let mut value = 0u128;
    for (index, bit) in bits.iter().copied().enumerate() {
        if constant_lit_value(bit)? {
            value |= 1u128 << index;
        }
    }
    Some(value)
}

fn sort_width(sort: Sort) -> usize {
    match sort {
        Sort::Bool => 1,
        Sort::BitVec(width) => width as usize,
        Sort::Float { exp, sig } => (exp + sig) as usize,
        Sort::Array { .. } => {
            unreachable!("array terms are eliminated before bit lowering (ADR-0010)")
        }
        Sort::Int => {
            unreachable!("integer terms are rejected before bit lowering (ADR-0014)")
        }
        Sort::Real => {
            unreachable!("real terms are rejected before bit lowering (ADR-0015)")
        }
        Sort::Datatype(_) => {
            unreachable!("datatype terms are rejected before bit lowering (ADR-0022)")
        }
        Sort::Uninterpreted(_) => {
            unreachable!("uninterpreted-sort terms are rejected before bit lowering")
        }
        Sort::Seq(_) => {
            unreachable!("sequence terms are rejected before bit lowering (P2.7)")
        }
    }
}

fn aig_lit_from_node_values(lit: AigLit, node_values: &[bool]) -> Result<bool, BitLowerError> {
    let value = node_values.get(lit.node().index()).copied().ok_or(
        BitLowerError::AigValueLengthMismatch {
            expected: lit.node().index() + 1,
            found: node_values.len(),
        },
    )?;
    Ok(value ^ lit.is_inverted())
}

fn constant_lits(width: usize, value: u128) -> Vec<AigLit> {
    // `width` may exceed 128 (wide bit-vectors), while `value` always fits a
    // `u128` (callers pass a bit-width). Bits at position `>= 128` of a `u128`
    // are zero, so guard the shift to avoid a shift-amount overflow panic.
    (0..width)
        .map(|bit| const_lit(bit < 128 && ((value >> bit) & 1) == 1))
        .collect()
}

fn expect_bool(term: TermId, bits: &[AigLit]) -> Result<AigLit, BitLowerError> {
    if let [bit] = bits {
        Ok(*bit)
    } else {
        Err(BitLowerError::BitWidthMismatch {
            term,
            expected: 1,
            found: bits.len(),
        })
    }
}

fn expect_two(
    term: TermId,
    operands: &[Vec<AigLit>],
) -> Result<(&[AigLit], &[AigLit]), BitLowerError> {
    if let [lhs, rhs] = operands {
        Ok((lhs, rhs))
    } else {
        Err(BitLowerError::BitWidthMismatch {
            term,
            expected: 2,
            found: operands.len(),
        })
    }
}

fn is_unsupported_op(op: Op) -> bool {
    // The full scalar QF_BV operator set lowers; array operations are eliminated
    // to QF_BV before lowering (ADR-0010) and uninterpreted-function
    // applications via Ackermann reduction (ADR-0013), so neither is supported
    // by the bit-blaster directly.
    matches!(
        op,
        Op::Select
            | Op::Store
            | Op::ConstArray { .. }
            | Op::IntToReal
            | Op::RealToInt
            | Op::RealIsInt
            | Op::Bv2Nat
            | Op::Int2Bv { .. }
            | Op::Apply(_)
            | Op::IntNeg
            | Op::IntAdd
            | Op::IntSub
            | Op::IntMul
            | Op::IntLt
            | Op::IntLe
            | Op::IntGt
            | Op::IntGe
            | Op::RealNeg
            | Op::RealAdd
            | Op::RealSub
            | Op::RealMul
            | Op::RealDiv
            | Op::RealLt
            | Op::RealLe
            | Op::RealGt
            | Op::RealGe
            | Op::Forall(_)
            | Op::Exists(_)
            | Op::DtConstruct { .. }
            | Op::DtSelect { .. }
            | Op::DtTest(_)
    )
}

/// Evaluates an original term and its lowered AIG root under the same
/// assignment.
///
/// This helper is intended for tests and future differential harnesses.
///
/// # Errors
///
/// Returns [`BitLowerError`] if lowering, IR evaluation, or AIG evaluation
/// fails.
pub fn eval_lowered_once(
    arena: &TermArena,
    term: TermId,
    assignment: &Assignment,
) -> Result<(Value, Value), BitLowerError> {
    let lowering = lower_terms(arena, &[term])?;
    let expected = eval(arena, term, assignment)?;
    let lowered = lowering.evaluate_root(0, assignment)?;
    Ok((expected, lowered))
}

#[cfg(test)]
mod tests {
    use axeyum_aig::AigLit;
    use axeyum_ir::{Assignment, IrError, Sort, TermArena, Value, eval};

    use super::{BitLowerError, IncrementalLowering, eval_lowered_once, lower_terms};

    fn bv(width: u32, value: u128) -> Value {
        Value::Bv { width, value }
    }

    #[test]
    fn constants_lower_to_lsb_first_literals_and_lift_map() {
        let mut arena = TermArena::new();
        let bool_true = arena.bool_const(true);
        let bv_value = arena.bv_const(4, 0b1010).unwrap();
        let lowering = lower_terms(&arena, &[bool_true, bv_value]).unwrap();

        assert_eq!(lowering.roots()[0].bits(), &[AigLit::TRUE]);
        assert_eq!(
            lowering.roots()[1].bits(),
            &[AigLit::FALSE, AigLit::TRUE, AigLit::FALSE, AigLit::TRUE]
        );
        assert_eq!(
            lowering.literal_for_term_bit(bv_value, 0),
            Some(AigLit::FALSE)
        );
        assert_eq!(
            lowering.literal_for_term_bit(bv_value, 1),
            Some(AigLit::TRUE)
        );
        assert_eq!(lowering.term_bits().len(), 5);
        assert!(lowering.symbol_inputs().is_empty());
    }

    #[test]
    fn symbols_create_stable_input_map_and_replay_assignments() {
        let mut arena = TermArena::new();
        let x_sym = arena.declare("x", Sort::BitVec(3)).unwrap();
        let p_sym = arena.declare("p", Sort::Bool).unwrap();
        let x = arena.var(x_sym);
        let p = arena.var(p_sym);

        let lowering = lower_terms(&arena, &[x, p]).unwrap();
        assert_eq!(lowering.aig().input_count(), 4);
        assert_eq!(
            lowering
                .symbol_inputs()
                .iter()
                .map(|input| (input.symbol_name.as_str(), input.bit_index))
                .collect::<Vec<_>>(),
            vec![("x", 0), ("x", 1), ("x", 2), ("p", 0)]
        );

        let mut assignment = Assignment::new();
        assignment.set(x_sym, bv(3, 0b101));
        assignment.set(p_sym, Value::Bool(true));
        assert_eq!(
            lowering.input_values(&assignment).unwrap(),
            vec![true, false, true, true]
        );
        assert_eq!(
            lowering.evaluate_roots(&assignment).unwrap(),
            vec![bv(3, 0b101), Value::Bool(true)]
        );
    }

    #[test]
    fn boolean_connectives_match_ground_evaluator() {
        let mut arena = TermArena::new();
        let p_sym = arena.declare("p", Sort::Bool).unwrap();
        let q_sym = arena.declare("q", Sort::Bool).unwrap();
        let p = arena.var(p_sym);
        let q = arena.var(q_sym);
        let not_q = arena.not(q).unwrap();
        let p_and_not_q = arena.and(p, not_q).unwrap();
        let p_implies_q = arena.implies(p, q).unwrap();
        let root = arena.xor(p_and_not_q, p_implies_q).unwrap();
        let lowering = lower_terms(&arena, &[root]).unwrap();

        for p_value in [false, true] {
            for q_value in [false, true] {
                let mut assignment = Assignment::new();
                assignment.set(p_sym, Value::Bool(p_value));
                assignment.set(q_sym, Value::Bool(q_value));
                assert_eq!(
                    lowering.evaluate_root(0, &assignment).unwrap(),
                    eval(&arena, root, &assignment).unwrap()
                );
            }
        }
    }

    #[test]
    fn bv_bitwise_ops_match_ground_evaluator() {
        let mut arena = TermArena::new();
        let x_sym = arena.declare("x", Sort::BitVec(3)).unwrap();
        let y_sym = arena.declare("y", Sort::BitVec(3)).unwrap();
        let x = arena.var(x_sym);
        let y = arena.var(y_sym);
        let not_x = arena.bv_not(x).unwrap();
        let x_and_y = arena.bv_and(x, y).unwrap();
        let y_or_not_x = arena.bv_or(y, not_x).unwrap();
        let xnor = arena.bv_xnor(x_and_y, y_or_not_x).unwrap();
        let nand = arena.bv_nand(x, y).unwrap();
        let root = arena.bv_xor(xnor, nand).unwrap();
        let lowering = lower_terms(&arena, &[root]).unwrap();

        for x_value in 0..8 {
            for y_value in 0..8 {
                let mut assignment = Assignment::new();
                assignment.set(x_sym, bv(3, x_value));
                assignment.set(y_sym, bv(3, y_value));
                assert_eq!(
                    lowering.evaluate_root(0, &assignment).unwrap(),
                    eval(&arena, root, &assignment).unwrap(),
                    "x={x_value} y={y_value}"
                );
            }
        }
    }

    #[test]
    fn structural_ops_match_ground_evaluator() {
        let mut arena = TermArena::new();
        let x_sym = arena.declare("x", Sort::BitVec(3)).unwrap();
        let y_sym = arena.declare("y", Sort::BitVec(3)).unwrap();
        let z_sym = arena.declare("z", Sort::BitVec(2)).unwrap();
        let p_sym = arena.declare("p", Sort::Bool).unwrap();
        let x = arena.var(x_sym);
        let y = arena.var(y_sym);
        let z = arena.var(z_sym);
        let p = arena.var(p_sym);

        let x_low = arena.extract(1, 0, x).unwrap();
        let x_high = arena.extract(2, 1, x).unwrap();
        let concat = arena.concat(x_high, z).unwrap();
        let zero_ext = arena.zero_ext(2, x_low).unwrap();
        let sign_ext = arena.sign_ext(2, x_low).unwrap();
        let eq_bv = arena.eq(x, y).unwrap();
        let bv_comp = arena.bv_comp(x, y).unwrap();
        let ite_bv = arena.ite(eq_bv, zero_ext, sign_ext).unwrap();
        let not_eq_bv = arena.not(eq_bv).unwrap();
        let ite_bool = arena.ite(p, eq_bv, not_eq_bv).unwrap();
        let not_p = arena.not(p).unwrap();
        let eq_bool = arena.eq(p, not_p).unwrap();
        let roots = [
            eq_bv, bv_comp, x_low, x_high, concat, zero_ext, sign_ext, ite_bv, ite_bool, eq_bool,
        ];
        let lowering = lower_terms(&arena, &roots).unwrap();

        for x_value in 0..8 {
            for y_value in 0..8 {
                for z_value in 0..4 {
                    for p_value in [false, true] {
                        let mut assignment = Assignment::new();
                        assignment.set(x_sym, bv(3, x_value));
                        assignment.set(y_sym, bv(3, y_value));
                        assignment.set(z_sym, bv(2, z_value));
                        assignment.set(p_sym, Value::Bool(p_value));
                        let expected = roots
                            .iter()
                            .copied()
                            .map(|root| eval(&arena, root, &assignment))
                            .collect::<Result<Vec<_>, _>>()
                            .unwrap();
                        assert_eq!(
                            lowering.evaluate_roots(&assignment).unwrap(),
                            expected,
                            "x={x_value} y={y_value} z={z_value} p={p_value}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn arithmetic_ops_match_ground_evaluator() {
        let mut arena = TermArena::new();
        let x_sym = arena.declare("x", Sort::BitVec(4)).unwrap();
        let y_sym = arena.declare("y", Sort::BitVec(4)).unwrap();
        let x = arena.var(x_sym);
        let y = arena.var(y_sym);
        let neg_x = arena.bv_neg(x).unwrap();
        let neg_y = arena.bv_neg(y).unwrap();
        let add = arena.bv_add(x, y).unwrap();
        let sub = arena.bv_sub(x, y).unwrap();
        let reverse_sub = arena.bv_sub(y, x).unwrap();
        let add_then_sub = arena.bv_sub(add, x).unwrap();
        let roots = [neg_x, neg_y, add, sub, reverse_sub, add_then_sub];
        let lowering = lower_terms(&arena, &roots).unwrap();

        for x_value in 0..16 {
            for y_value in 0..16 {
                let mut assignment = Assignment::new();
                assignment.set(x_sym, bv(4, x_value));
                assignment.set(y_sym, bv(4, y_value));
                let expected = roots
                    .iter()
                    .copied()
                    .map(|root| eval(&arena, root, &assignment))
                    .collect::<Result<Vec<_>, _>>()
                    .unwrap();
                assert_eq!(
                    lowering.evaluate_roots(&assignment).unwrap(),
                    expected,
                    "x={x_value} y={y_value}"
                );
            }
        }
    }

    #[test]
    fn comparison_ops_match_ground_evaluator() {
        let mut arena = TermArena::new();
        let x_sym = arena.declare("x", Sort::BitVec(3)).unwrap();
        let y_sym = arena.declare("y", Sort::BitVec(3)).unwrap();
        let x = arena.var(x_sym);
        let y = arena.var(y_sym);
        let roots = [
            arena.bv_ult(x, y).unwrap(),
            arena.bv_ule(x, y).unwrap(),
            arena.bv_ugt(x, y).unwrap(),
            arena.bv_uge(x, y).unwrap(),
            arena.bv_slt(x, y).unwrap(),
            arena.bv_sle(x, y).unwrap(),
            arena.bv_sgt(x, y).unwrap(),
            arena.bv_sge(x, y).unwrap(),
        ];
        let lowering = lower_terms(&arena, &roots).unwrap();

        for x_value in 0..8 {
            for y_value in 0..8 {
                let mut assignment = Assignment::new();
                assignment.set(x_sym, bv(3, x_value));
                assignment.set(y_sym, bv(3, y_value));
                let expected = roots
                    .iter()
                    .copied()
                    .map(|root| eval(&arena, root, &assignment))
                    .collect::<Result<Vec<_>, _>>()
                    .unwrap();
                assert_eq!(
                    lowering.evaluate_roots(&assignment).unwrap(),
                    expected,
                    "x={x_value} y={y_value}"
                );
            }
        }
    }

    #[test]
    fn shift_ops_match_ground_evaluator() {
        assert_shift_ops_match_ground_evaluator(1);
        assert_shift_ops_match_ground_evaluator(4);
        assert_shift_ops_match_ground_evaluator(5);
    }

    fn assert_shift_ops_match_ground_evaluator(width: u32) {
        let mut arena = TermArena::new();
        let x_sym = arena.declare("x", Sort::BitVec(width)).unwrap();
        let k_sym = arena.declare("k", Sort::BitVec(width)).unwrap();
        let x = arena.var(x_sym);
        let k = arena.var(k_sym);
        let roots = [
            arena.bv_shl(x, k).unwrap(),
            arena.bv_lshr(x, k).unwrap(),
            arena.bv_ashr(x, k).unwrap(),
        ];
        let lowering = lower_terms(&arena, &roots).unwrap();

        let value_count = 1u128 << width;
        for x_value in 0..value_count {
            for k_value in 0..value_count {
                let mut assignment = Assignment::new();
                assignment.set(x_sym, bv(width, x_value));
                assignment.set(k_sym, bv(width, k_value));
                let expected = roots
                    .iter()
                    .copied()
                    .map(|root| eval(&arena, root, &assignment))
                    .collect::<Result<Vec<_>, _>>()
                    .unwrap();
                assert_eq!(
                    lowering.evaluate_roots(&assignment).unwrap(),
                    expected,
                    "width={width} x={x_value} k={k_value}"
                );
            }
        }
    }

    #[test]
    fn rotate_ops_match_ground_evaluator() {
        let mut arena = TermArena::new();
        let x_sym = arena.declare("x", Sort::BitVec(5)).unwrap();
        let x = arena.var(x_sym);
        let mut roots = Vec::new();
        for by in 0..10 {
            roots.push(arena.rotate_left(by, x).unwrap());
            roots.push(arena.rotate_right(by, x).unwrap());
        }
        let lowering = lower_terms(&arena, &roots).unwrap();

        for x_value in 0..32 {
            let mut assignment = Assignment::new();
            assignment.set(x_sym, bv(5, x_value));
            let expected = roots
                .iter()
                .copied()
                .map(|root| eval(&arena, root, &assignment))
                .collect::<Result<Vec<_>, _>>()
                .unwrap();
            assert_eq!(
                lowering.evaluate_roots(&assignment).unwrap(),
                expected,
                "x={x_value}"
            );
        }
    }

    #[test]
    fn concat_lift_map_preserves_lsb_first_order() {
        let mut arena = TermArena::new();
        let high_sym = arena.declare("high", Sort::BitVec(2)).unwrap();
        let low_sym = arena.declare("low", Sort::BitVec(2)).unwrap();
        let high = arena.var(high_sym);
        let low = arena.var(low_sym);
        let concat = arena.concat(high, low).unwrap();
        let lowering = lower_terms(&arena, &[concat]).unwrap();
        let root_bits = lowering.roots()[0].bits();

        assert_eq!(root_bits.len(), 4);
        assert_eq!(
            Some(root_bits[0]),
            lowering.literal_for_term_bit(low, 0),
            "concat bit 0 comes from the low operand bit 0"
        );
        assert_eq!(
            Some(root_bits[1]),
            lowering.literal_for_term_bit(low, 1),
            "concat bit 1 comes from the low operand bit 1"
        );
        assert_eq!(
            Some(root_bits[2]),
            lowering.literal_for_term_bit(high, 0),
            "concat bit 2 comes from the high operand bit 0"
        );
        assert_eq!(
            Some(root_bits[3]),
            lowering.literal_for_term_bit(high, 1),
            "concat bit 3 comes from the high operand bit 1"
        );
    }

    #[test]
    fn incremental_lowering_matches_batch_and_shares_subterms() {
        let mut arena = TermArena::new();
        let x = arena.bv_var("x", 8).unwrap();
        let y = arena.bv_var("y", 8).unwrap();
        let sum = arena.bv_add(x, y).unwrap();
        let prod = arena.bv_mul(x, y).unwrap();
        let seven = arena.bv_const(8, 7).unwrap();
        let a = arena.eq(sum, seven).unwrap();
        // `b` shares `sum`, `x`, and `y` with `a`.
        let b = arena.bv_ult(prod, sum).unwrap();

        let batch = lower_terms(&arena, &[a, b]).unwrap();

        let mut incremental = IncrementalLowering::new();
        let lowered_a = incremental.lower(&arena, a).unwrap();
        let lowered_b = incremental.lower(&arena, b).unwrap();

        // Incremental lowering builds the same AIG and the same root bits as a
        // single batch lowering, so it inherits the batch path's correctness.
        assert_eq!(lowered_a.bits(), batch.roots()[0].bits());
        assert_eq!(lowered_b.bits(), batch.roots()[1].bits());
        assert_eq!(incremental.node_count(), batch.aig().node_count());
        assert_eq!(incremental.symbol_inputs(), batch.symbol_inputs());

        // Re-lowering an already-lowered term adds no AIG nodes (memoized).
        let before = incremental.node_count();
        let lowered_again = incremental.lower(&arena, a).unwrap();
        assert_eq!(lowered_again.bits(), lowered_a.bits());
        assert_eq!(
            incremental.node_count(),
            before,
            "shared subterms must not be re-lowered"
        );
    }

    #[test]
    fn signed_division_matches_ground_evaluator() {
        for width in [1u32, 2, 3, 4, 5] {
            let mut arena = TermArena::new();
            let x_sym = arena.declare("x", Sort::BitVec(width)).unwrap();
            let y_sym = arena.declare("y", Sort::BitVec(width)).unwrap();
            let x = arena.var(x_sym);
            let y = arena.var(y_sym);
            // Signed divide/rem/mod over all input pairs, including negative
            // operands, the most-negative value, and the divide-by-zero path.
            let roots = [
                arena.bv_sdiv(x, y).unwrap(),
                arena.bv_srem(x, y).unwrap(),
                arena.bv_smod(x, y).unwrap(),
            ];
            let lowering = lower_terms(&arena, &roots).unwrap();

            let bound = 1u128 << width;
            for x_value in 0..bound {
                for y_value in 0..bound {
                    let mut assignment = Assignment::new();
                    assignment.set(x_sym, bv(width, x_value));
                    assignment.set(y_sym, bv(width, y_value));
                    let expected = roots
                        .iter()
                        .copied()
                        .map(|root| eval(&arena, root, &assignment))
                        .collect::<Result<Vec<_>, _>>()
                        .unwrap();
                    assert_eq!(
                        lowering.evaluate_roots(&assignment).unwrap(),
                        expected,
                        "width={width} x={x_value} y={y_value}"
                    );
                }
            }
        }
    }

    #[test]
    fn unsigned_division_matches_ground_evaluator() {
        for width in [1u32, 2, 3, 4, 5] {
            let mut arena = TermArena::new();
            let x_sym = arena.declare("x", Sort::BitVec(width)).unwrap();
            let y_sym = arena.declare("y", Sort::BitVec(width)).unwrap();
            let x = arena.var(x_sym);
            let y = arena.var(y_sym);
            // Cover divide-by-symbol, divide-by-constant, and self-division so
            // the divide-by-zero totality path is exercised (y ranges over 0).
            let three = arena.bv_const(width, 3 & ((1u128 << width) - 1)).unwrap();
            let roots = [
                arena.bv_udiv(x, y).unwrap(),
                arena.bv_urem(x, y).unwrap(),
                arena.bv_udiv(x, three).unwrap(),
                arena.bv_urem(x, three).unwrap(),
            ];
            let lowering = lower_terms(&arena, &roots).unwrap();

            let bound = 1u128 << width;
            for x_value in 0..bound {
                for y_value in 0..bound {
                    let mut assignment = Assignment::new();
                    assignment.set(x_sym, bv(width, x_value));
                    assignment.set(y_sym, bv(width, y_value));
                    let expected = roots
                        .iter()
                        .copied()
                        .map(|root| eval(&arena, root, &assignment))
                        .collect::<Result<Vec<_>, _>>()
                        .unwrap();
                    assert_eq!(
                        lowering.evaluate_roots(&assignment).unwrap(),
                        expected,
                        "width={width} x={x_value} y={y_value}"
                    );
                }
            }
        }
    }

    #[test]
    fn multiplication_matches_ground_evaluator() {
        // Widths span Booth radix-4 grouping cases: 1 (degenerate), even, and
        // odd (last digit straddles the top bit).
        for width in [1u32, 2, 3, 4, 5, 6, 7] {
            let mut arena = TermArena::new();
            let x_sym = arena.declare("x", Sort::BitVec(width)).unwrap();
            let y_sym = arena.declare("y", Sort::BitVec(width)).unwrap();
            let x = arena.var(x_sym);
            let y = arena.var(y_sym);
            // Cover symbol*symbol, squaring (shared operand), and
            // symbol*constant so partial-product folding is exercised too.
            let width_mask = (1u128 << width) - 1;
            let three = arena.bv_const(width, 3 & width_mask).unwrap();
            let roots = [
                arena.bv_mul(x, y).unwrap(),
                arena.bv_mul(x, x).unwrap(),
                arena.bv_mul(x, three).unwrap(),
            ];
            let lowering = lower_terms(&arena, &roots).unwrap();

            let bound = 1u128 << width;
            for x_value in 0..bound {
                for y_value in 0..bound {
                    let mut assignment = Assignment::new();
                    assignment.set(x_sym, bv(width, x_value));
                    assignment.set(y_sym, bv(width, y_value));
                    let expected = roots
                        .iter()
                        .copied()
                        .map(|root| eval(&arena, root, &assignment))
                        .collect::<Result<Vec<_>, _>>()
                        .unwrap();
                    assert_eq!(
                        lowering.evaluate_roots(&assignment).unwrap(),
                        expected,
                        "width={width} x={x_value} y={y_value}"
                    );
                }
            }
        }
    }

    #[test]
    fn assignment_errors_are_reported_before_aig_evaluation() {
        let mut arena = TermArena::new();
        let x_sym = arena.declare("x", Sort::BitVec(2)).unwrap();
        let x = arena.var(x_sym);
        let lowering = lower_terms(&arena, &[x]).unwrap();

        assert!(matches!(
            lowering.input_values(&Assignment::new()),
            Err(BitLowerError::Ir(IrError::UnboundSymbol(symbol))) if symbol == x_sym
        ));

        let mut wrong_sort = Assignment::new();
        wrong_sort.set(x_sym, Value::Bool(true));
        assert!(matches!(
            lowering.input_values(&wrong_sort),
            Err(BitLowerError::AssignmentSortMismatch {
                expected: Sort::BitVec(2),
                found: Sort::Bool,
                ..
            })
        ));
    }

    #[test]
    fn eval_lowered_once_returns_evaluator_and_aig_values() {
        let mut arena = TermArena::new();
        let x_sym = arena.declare("x", Sort::BitVec(2)).unwrap();
        let y_sym = arena.declare("y", Sort::BitVec(2)).unwrap();
        let x = arena.var(x_sym);
        let y = arena.var(y_sym);
        let root = arena.bv_or(x, y).unwrap();
        let mut assignment = Assignment::new();
        assignment.set(x_sym, bv(2, 0b01));
        assignment.set(y_sym, bv(2, 0b10));

        assert_eq!(
            eval_lowered_once(&arena, root, &assignment).unwrap(),
            (bv(2, 0b11), bv(2, 0b11))
        );
    }
}
