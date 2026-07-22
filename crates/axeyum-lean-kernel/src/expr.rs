//! Lean expressions (`Expr`), interned to lifetime-free [`ExprId`]s.
//!
//! Expressions use a locally-nameless representation: bound variables are de
//! Bruijn indices ([`ExprNode::BVar`]), and free/local variables carry a unique
//! id ([`ExprNode::FVar`]). Each interned node caches metadata used to make the
//! de Bruijn operations efficient and to short-circuit traversal:
//!
//! - `num_loose_bvars` — one more than the largest loose de Bruijn index that
//!   escapes this node (`0` means the node is closed), exactly as in nanoda.
//! - `has_fvars` — whether any free variable occurs in the node.
//!
//! Ported from nanoda's `expr.rs`, adapted to axeyum's interned handles instead
//! of a lifetime-tagged arena (ADR-0036). `Proj` is represented directly;
//! inference, reduction, and structure eta land in their separately gated
//! TL2.3--TL2.5 slices. `Lit::Nat` uses canonical arbitrary-precision storage;
//! typing and reduction remain separately gated by TL2.7 (see [`Lit`]).

use std::fmt;

use crate::level::LevelId;
use crate::name::NameId;
use num_bigint::BigUint;

/// A lifetime-free, `Copy` handle to an interned [`ExprNode`].
///
/// IDs are assigned densely in insertion order by the interner (determinism
/// rule). Using an `ExprId` with a different [`super::Kernel`] is a contract
/// violation caught only by bounds checks.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ExprId(pub(crate) u32);

impl ExprId {
    /// The index of this expression in its owning kernel's expr table.
    #[must_use]
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// The binder annotation on a `Lam`/`Pi`/`FVar` binder.
///
/// These mirror Lean's binder brackets and are used only by elaboration and
/// pretty-printing; they do **not** affect type checking or definitional
/// equality.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinderInfo {
    /// `(x : T)` — an ordinary explicit binder.
    Default,
    /// `{x : T}` — an implicit binder.
    Implicit,
    /// `{{x : T}}` — a strict implicit binder.
    StrictImplicit,
    /// `[x : T]` — an instance-implicit (type-class) binder.
    InstImplicit,
}

/// Canonical arbitrary-precision payload for a Lean natural-number literal.
///
/// Decimal parsing accepts only a non-empty sequence of ASCII digits. Leading
/// zeroes are normalized by the numeric representation, and formatting always
/// emits the canonical base-10 spelling. No fixed-width conversion is used.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NatLit(BigUint);

impl NatLit {
    /// Parses a non-negative base-10 integer without imposing a width bound.
    #[must_use]
    pub fn from_decimal(value: &str) -> Option<Self> {
        if value.is_empty() || !value.bytes().all(|byte| byte.is_ascii_digit()) {
            return None;
        }
        BigUint::parse_bytes(value.as_bytes(), 10).map(Self)
    }

    /// Whether this natural is zero.
    pub(crate) fn is_zero(&self) -> bool {
        self.0 == BigUint::default()
    }

    /// The predecessor of a positive natural.
    pub(crate) fn predecessor(&self) -> Option<Self> {
        if self.is_zero() {
            None
        } else {
            Some(Self(&self.0 - BigUint::from(1_u8)))
        }
    }

    /// The successor of this natural.
    pub(crate) fn successor(&self) -> Self {
        Self(&self.0 + BigUint::from(1_u8))
    }
}

impl fmt::Display for NatLit {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(formatter)
    }
}

macro_rules! impl_nat_lit_from_unsigned {
    ($($ty:ty),+ $(,)?) => {
        $(
            impl From<$ty> for NatLit {
                fn from(value: $ty) -> Self {
                    Self(BigUint::from(value))
                }
            }
        )+
    };
}

impl_nat_lit_from_unsigned!(u8, u16, u32, u64, u128, usize);

/// A literal value embeddable in an expression.
///
/// Representation is complete for arbitrary-precision natural numbers, but
/// literal typing and reduction remain fail-closed until TL2.7.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Lit {
    /// A natural-number literal with no fixed-width ceiling.
    Nat(NatLit),
    /// A string literal.
    Str(String),
}

impl Lit {
    /// Constructs a natural-number literal from any supported unsigned value.
    pub fn nat(value: impl Into<NatLit>) -> Self {
        Self::Nat(value.into())
    }
}

/// Cached structural metadata recomputed once at intern time.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct ExprMeta {
    /// One more than the largest loose de Bruijn index escaping this node
    /// (`0` ⇒ closed). Matches nanoda's `num_loose_bvars`.
    pub(crate) num_loose_bvars: u32,
    /// Whether any free variable ([`ExprNode::FVar`]) occurs in this node.
    pub(crate) has_fvars: bool,
}

/// The structural node of a Lean expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ExprNode {
    /// A bound variable as a de Bruijn index (0 = innermost binder).
    BVar(u32),
    /// A free/local variable identified by a unique id.
    FVar(u64),
    /// A type universe at the given level.
    Sort(LevelId),
    /// A constant reference with universe arguments.
    Const(NameId, Vec<LevelId>),
    /// A structure projection: structure type name, zero-based field index,
    /// and the structure-valued expression being projected.
    ///
    /// The field index excludes constructor parameters, matching Lean's core
    /// `Expr::Proj` and `lean4export` format 3.1. It is a fixed-width `u32` so
    /// the representation is deterministic across native and WASM targets;
    /// wire values outside this range must decline before construction.
    Proj(NameId, u32, ExprId),
    /// Function application `fun arg`.
    App(ExprId, ExprId),
    /// `fun (name : ty) => body` with binder info.
    Lam(NameId, ExprId, ExprId, BinderInfo),
    /// `(name : ty) -> body` (dependent function type) with binder info.
    Pi(NameId, ExprId, ExprId, BinderInfo),
    /// `let name : ty := val; body`.
    Let(NameId, ExprId, ExprId, ExprId),
    /// A literal value.
    Lit(Lit),
}
