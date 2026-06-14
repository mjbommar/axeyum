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

/// Handle to a declared uninterpreted function in a [`crate::TermArena`].
///
/// Functions are declared separately from variables (they have a signature,
/// not a sort) and are not first-class terms; the only way to use one is an
/// [`Op::Apply`] application. Like [`SymbolId`], this is a `Copy` ID with no
/// lifetime, valid only against its owning arena.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FuncId(pub(crate) u32);

impl FuncId {
    /// The dense index of this function within its arena.
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// A declared (possibly recursive) datatype, interned in the arena (ADR-0022).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DatatypeId(pub(crate) u32);

impl DatatypeId {
    /// The dense index of this datatype within its arena.
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// A constructor of some datatype, interned globally in the arena (ADR-0022).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ConstructorId(pub(crate) u32);

impl ConstructorId {
    /// The dense index of this constructor within its arena.
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// Operators of the scalar `QF_BV` fragment (Phase 1 set).
///
/// Bool and bit-vector families are distinct; `Eq` and `Ite` are
/// polymorphic with same-sort checking in the builders. Parameterized
/// operators (`Extract`, extensions, rotates) carry their parameters in the
/// operator, not as term arguments. Edge-case semantics follow SMT-LIB
/// exactly (bv-semantics note): division and remainder are total, shifts by
/// amounts `>= width` saturate, rotates normalize modulo width.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Op {
    // --- Boolean -------------------------------------------------------
    /// Boolean negation.
    BoolNot,
    /// Boolean conjunction (binary).
    BoolAnd,
    /// Boolean disjunction (binary).
    BoolOr,
    /// Boolean exclusive or.
    BoolXor,
    /// Boolean implication.
    BoolImplies,
    // --- bit-vector bitwise ---------------------------------------------
    /// Bitwise negation.
    BvNot,
    /// Bitwise and.
    BvAnd,
    /// Bitwise or.
    BvOr,
    /// Bitwise xor.
    BvXor,
    /// Bitwise nand.
    BvNand,
    /// Bitwise nor.
    BvNor,
    /// Bitwise xnor.
    BvXnor,
    // --- bit-vector arithmetic -------------------------------------------
    /// Two's-complement negation, wrapping.
    BvNeg,
    /// Addition modulo `2^width`.
    BvAdd,
    /// Subtraction modulo `2^width`.
    BvSub,
    /// Multiplication modulo `2^width`.
    BvMul,
    /// Unsigned division; division by zero yields all-ones.
    BvUdiv,
    /// Unsigned remainder; remainder by zero yields the dividend.
    BvUrem,
    /// Signed division (truncating); by zero: `-1` if dividend
    /// non-negative, `+1` otherwise (SMT-LIB expansion).
    BvSdiv,
    /// Signed remainder, sign follows the dividend; by zero: the dividend.
    BvSrem,
    /// Signed modulo, sign follows the divisor; by zero: the dividend.
    BvSmod,
    // --- shifts -----------------------------------------------------------
    /// Logical shift left; amounts `>= width` yield zero.
    BvShl,
    /// Logical shift right; amounts `>= width` yield zero.
    BvLshr,
    /// Arithmetic shift right; amounts `>= width` yield all sign bits.
    BvAshr,
    // --- comparisons (result sort `Bool`) ---------------------------------
    /// Unsigned less-than.
    BvUlt,
    /// Unsigned less-or-equal.
    BvUle,
    /// Unsigned greater-than.
    BvUgt,
    /// Unsigned greater-or-equal.
    BvUge,
    /// Signed less-than.
    BvSlt,
    /// Signed less-or-equal.
    BvSle,
    /// Signed greater-than.
    BvSgt,
    /// Signed greater-or-equal.
    BvSge,
    // --- polymorphic -------------------------------------------------------
    /// Equality over any shared sort; result sort is `Bool`.
    Eq,
    /// If-then-else: `Bool` condition, same-sort branches.
    Ite,
    // --- structural --------------------------------------------------------
    /// Equality as a bit: `BV(1)` one if operands are equal, else zero.
    BvComp,
    /// Bit slice `[hi:lo]` inclusive; result width is `hi - lo + 1`.
    Extract {
        /// High bit index (inclusive).
        hi: u32,
        /// Low bit index (inclusive).
        lo: u32,
    },
    /// Bit-vector concatenation; first argument becomes the high bits.
    Concat,
    /// Zero extension by `by` bits (result width `width + by`).
    ZeroExt {
        /// Number of zero bits appended at the high end.
        by: u32,
    },
    /// Sign extension by `by` bits (result width `width + by`).
    SignExt {
        /// Number of sign bits appended at the high end.
        by: u32,
    },
    /// Rotate left by a constant amount, normalized modulo width at build.
    RotateLeft {
        /// Rotation amount, already reduced modulo the operand width.
        by: u32,
    },
    /// Rotate right by a constant amount, normalized modulo width at build.
    RotateRight {
        /// Rotation amount, already reduced modulo the operand width.
        by: u32,
    },
    // --- arrays (ADR-0010) -------------------------------------------------
    /// Array read: `select(array, index)`; result is the element sort.
    Select,
    /// Array write: `store(array, index, element)`; result is the array sort.
    Store,
    // --- uninterpreted functions (ADR-0013) --------------------------------
    /// Application of a declared uninterpreted function; the argument terms are
    /// the operands and the result sort is the function's declared result.
    Apply(FuncId),
    // --- linear integer arithmetic (ADR-0014) ------------------------------
    /// Integer negation.
    IntNeg,
    /// Integer addition.
    IntAdd,
    /// Integer subtraction.
    IntSub,
    /// Integer multiplication (linear use enforced by downstream procedures).
    IntMul,
    /// Integer Euclidean division (SMT-LIB `div`): `div a b` with
    /// `a = b·(div a b) + (mod a b)` and `0 ≤ mod a b < |b|` for `b ≠ 0`; by the
    /// in-tree convention `div a 0 = 0`.
    IntDiv,
    /// Integer Euclidean modulo (SMT-LIB `mod`): the remainder of [`Op::IntDiv`],
    /// always in `0..|b|` for `b ≠ 0`; by convention `mod a 0 = a`.
    IntMod,
    /// Integer absolute value (SMT-LIB `abs`).
    IntAbs,
    /// Integer less-than (result sort `Bool`).
    IntLt,
    /// Integer less-or-equal (result sort `Bool`).
    IntLe,
    /// Integer greater-than (result sort `Bool`).
    IntGt,
    /// Integer greater-or-equal (result sort `Bool`).
    IntGe,
    // --- linear real arithmetic (ADR-0015) ---------------------------------
    /// Real negation.
    RealNeg,
    /// Real addition.
    RealAdd,
    /// Real subtraction.
    RealSub,
    /// Real multiplication (linear use enforced by downstream procedures).
    RealMul,
    /// Real less-than (result sort `Bool`).
    RealLt,
    /// Real less-or-equal (result sort `Bool`).
    RealLe,
    /// Real greater-than (result sort `Bool`).
    RealGt,
    /// Real greater-or-equal (result sort `Bool`).
    RealGe,
    // --- quantifiers (ADR-0016) --------------------------------------------
    /// Universal quantifier binding `SymbolId` over a `Bool` body (the single
    /// argument); result sort `Bool`.
    Forall(SymbolId),
    /// Existential quantifier binding `SymbolId` over a `Bool` body (the single
    /// argument); result sort `Bool`.
    Exists(SymbolId),

    // --- datatypes (ADR-0022) ----------------------------------------------
    /// Applies a datatype constructor to its field arguments; result sort is the
    /// constructor's datatype (carried so evaluation needs no arena access).
    DtConstruct {
        /// The constructor applied.
        constructor: ConstructorId,
        /// The datatype it builds.
        datatype: DatatypeId,
    },
    /// Selects field `index` of a value built by `constructor`; the single
    /// argument is a datatype value; result sort is the field's sort.
    DtSelect {
        /// The constructor whose field is selected.
        constructor: ConstructorId,
        /// The field index within that constructor.
        index: u32,
    },
    /// Tests whether its single datatype argument was built by `constructor`;
    /// result sort `Bool`.
    DtTest(ConstructorId),
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
    /// An integer constant (ADR-0014).
    IntConst(i128),
    /// A real constant as an exact rational (ADR-0015).
    RealConst(crate::rational::Rational),
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
