//! Term and symbol identifiers, operators, and term nodes.

use crate::sort::ArraySortKey;

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
    /// Constant array `((as const (Array I E)) v)`: every index maps to the
    /// single element argument `v`. The index sort is carried here; the element
    /// sort comes from `v`. Result is the array sort.
    ConstArray {
        /// Sort of the array index.
        index: ArraySortKey,
    },
    // --- bit-vector / integer coercions ------------------------------------
    /// `to_real`: the real number equal to an integer (the exact numeric
    /// embedding `Int → Real`).
    IntToReal,
    /// `to_int`: the floor of a real, as an integer (`Real → Int`).
    RealToInt,
    /// `is_int`: whether a real is an integer (`Real → Bool`).
    RealIsInt,
    /// `bv2nat`: the unsigned integer value of a bit-vector (result sort `Int`,
    /// mathematically in `0..2^w`).
    ///
    /// The ground evaluator's integers are the `i128` reference range, so the
    /// result is exact for widths up to 127 (and any value `<= i128::MAX`). A
    /// `>= 128`-bit value whose high bits make it exceed `i128::MAX` has no
    /// non-negative `i128` representation; the evaluator reports
    /// [`crate::IrError::ArithmeticOverflow`] (never a wrapped negative integer),
    /// and a dependent sat model degrades to a graceful `unknown`.
    Bv2Nat,
    /// `(_ int2bv n)`: the bit-vector of width `n` whose value is the operand
    /// integer reduced mod `2^n` (result sort `BitVec(n)`).
    Int2Bv {
        /// Bit-width of the result.
        width: u32,
    },
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
    /// `int.pow2`: the cvc5 total integer power-of-two `pow2(x)` (unary,
    /// `Int → Int`). Semantics follow cvc5's evaluator verbatim (authoritative,
    /// checked against `references/cvc5/src/theory/evaluator.cpp`): `pow2(x) = 2^x`
    /// for `x ≥ 0`, and — crucially — the **defined** value `pow2(x) = 0` for
    /// `x < 0` (NOT underspecified: cvc5's `ARITH_NL_POW2_NEG_REFINE` lemma
    /// `x < 0 ⇒ pow2(x) = 0` and its `pow2-native-0` regression, which is *unsat*
    /// on `x < 0 ∧ pow2(x) ≠ 0`, both pin the negative case to `0`). The ground
    /// evaluator reports [`crate::IrError::ArithmeticOverflow`] when `2^x` would
    /// exceed the `i128` reference range (a dependent sat model degrades to a
    /// graceful `unknown`, never a wrong value).
    IntPow2,
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
    /// Real division (`/`). Total per SMT-LIB; division by zero is unspecified,
    /// and the in-tree evaluator uses the convention `x / 0 = 0`.
    RealDiv,
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
    // --- floating point (ADR-0026) -----------------------------------------
    /// Reinterprets a `BitVec(exp + sig)` operand as a floating-point value of
    /// format `(exp, sig)` (result sort `Float { exp, sig }`). This is a pure
    /// bit reinterpret — identity on the bits — used to stamp the floating-point
    /// sort onto a value built by the (bit-vector) FP formula builders, so
    /// conversions can tell a floating-point operand from a plain bit-vector.
    FpFromBits {
        /// Exponent bits of the result float.
        exp: u32,
        /// Significand bits (including the hidden bit) of the result float.
        sig: u32,
    },
    /// Stamps the five-element `RoundingMode` sort onto a three-bit code.  Codes
    /// `5..=7` canonicalize to RTZ at lowering/evaluation boundaries.
    RoundingModeFromBits,
    // --- sequences (ADR-0051, P2.7) ----------------------------------------
    /// `str.len`: the length of a sequence, as an `Int`. The single argument is
    /// any `Sort::Seq`; the result is `Sort::Int` (the shared `len` term that
    /// bridges the sequence theory and LIA, Nelson–Oppen-style).
    SeqLen,
    /// `seq.empty`: the empty sequence of element key `element` (a nullary
    /// constant); result sort `Seq(element)`. The element key is carried here
    /// (like [`Op::ConstArray`]'s index) because there is no argument to read it
    /// from.
    SeqEmpty(ArraySortKey),
    /// `seq.unit`: the one-element sequence `[x]`. The single argument `x` has any
    /// *scalar* element sort `E`; the result is `Seq(E)`. Nested sequences
    /// (`Seq(Seq …)`) are deferred, so the builder rejects a sequence argument.
    SeqUnit,
    /// `str.++`: concatenation of two sequences of the same sort `Seq(E)`; result
    /// is that same `Seq(E)`.
    SeqConcat,
}

/// The structural body of a term, used as the hash-consing key.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TermNode {
    /// A Boolean constant.
    BoolConst(bool),
    /// A bit-vector constant of width `≤ 128`; `value` is masked to `width` at
    /// build time. Wider constants are [`TermNode::WideBvConst`].
    BvConst {
        /// Width in bits.
        width: u32,
        /// The constant value; always fits in `width` bits.
        value: u128,
    },
    /// A bit-vector constant of width `> 128` (wide-BV).
    WideBvConst(crate::wide::WideUint),
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
