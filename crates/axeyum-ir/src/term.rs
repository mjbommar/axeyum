//! Term and symbol identifiers, operators, and term nodes.

/// Handle to an interned term in a [`crate::TermArena`].
///
/// Plain `Copy` ID with no lifetime parameter; validity is a contract with
/// the owning arena (api-design note). IDs are assigned densely in
/// insertion order, so identical construction sequences yield identical IDs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TermId(pub(crate) u32);

impl TermId {
    /// The dense index of this term within its arena.
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// Handle to a declared symbol (free variable) in a [`crate::TermArena`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SymbolId(pub(crate) u32);

impl SymbolId {
    /// The dense index of this symbol within its arena.
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// Operators of the M0 subset (ADR-0001, ADR-0003).
///
/// Bool and bit-vector families are distinct; `Eq` and `Ite` are
/// polymorphic with same-sort checking in the builders. `Extract` carries
/// its bounds as operator parameters, not term arguments.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Op {
    /// Boolean negation.
    BoolNot,
    /// Boolean conjunction (binary).
    BoolAnd,
    /// Boolean disjunction (binary).
    BoolOr,
    /// Boolean exclusive or.
    BoolXor,
    /// Bit-vector bitwise negation.
    BvNot,
    /// Bit-vector bitwise and.
    BvAnd,
    /// Bit-vector bitwise or.
    BvOr,
    /// Bit-vector bitwise xor.
    BvXor,
    /// Bit-vector addition, wrapping modulo `2^width`.
    BvAdd,
    /// Bit-vector unsigned less-than; result sort is `Bool`.
    BvUlt,
    /// Equality over any shared sort; result sort is `Bool`.
    Eq,
    /// If-then-else: `Bool` condition, same-sort branches.
    Ite,
    /// Bit slice `[hi:lo]` inclusive; result width is `hi - lo + 1`.
    Extract {
        /// High bit index (inclusive).
        hi: u32,
        /// Low bit index (inclusive).
        lo: u32,
    },
    /// Bit-vector concatenation; first argument becomes the high bits.
    Concat,
}

/// The structural body of a term, used as the hash-consing key.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TermNode {
    /// A Boolean constant.
    BoolConst(bool),
    /// A bit-vector constant; `value` is masked to `width` at build time.
    BvConst {
        /// Width in bits.
        width: u32,
        /// The constant value; always fits in `width` bits.
        value: u128,
    },
    /// A free variable referring to a declared symbol.
    Symbol(SymbolId),
    /// An operator application.
    App {
        /// The operator.
        op: Op,
        /// Operand term IDs, in operator-defined order.
        args: Box<[TermId]>,
    },
}
