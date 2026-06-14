//! Finite enumeration datatypes, lowered to bit-vectors.
//!
//! A first, sound slice of datatype support (toward Z3/cvc5 datatype parity): a
//! **finite enumeration** — a sort with `k` distinct nullary constructors, no
//! selectors, no recursion (e.g. `(declare-datatype Color ((red) (green)
//! (blue)))`). It compiles to a `BitVec(ceil(log2 k))`: constructor `i` is the
//! constant `i`, the `is-c` tester is equality with that constant, and a value
//! is constrained to a valid constructor by a `< k` domain constraint (omitted
//! when `k` is exactly a power of two). Everything reduces to the bit-vector
//! theory, which is decided and replayed soundly — so enum reasoning needs no
//! new core IR sort and no new decision procedure.
//!
//! Constructors with arguments, selectors, testers over recursive datatypes, and
//! mutual recursion are out of scope here; those need a first-class datatype sort
//! in the IR and are a later, larger increment.

use axeyum_ir::{Sort, TermArena, TermId, Value};

/// An error building or using an [`EnumSort`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EnumError {
    /// An enumeration needs at least one constructor.
    Empty,
    /// Two constructors share a name.
    DuplicateConstructor(String),
    /// A constructor name is not part of this enumeration.
    UnknownConstructor(String),
    /// An underlying IR builder error.
    Ir(String),
}

impl std::fmt::Display for EnumError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EnumError::Empty => write!(f, "enumeration has no constructors"),
            EnumError::DuplicateConstructor(name) => {
                write!(f, "duplicate enum constructor `{name}`")
            }
            EnumError::UnknownConstructor(name) => write!(f, "unknown enum constructor `{name}`"),
            EnumError::Ir(detail) => write!(f, "enum IR error: {detail}"),
        }
    }
}

impl std::error::Error for EnumError {}

impl From<axeyum_ir::IrError> for EnumError {
    fn from(error: axeyum_ir::IrError) -> Self {
        EnumError::Ir(error.to_string())
    }
}

/// A declared variable of an enumeration sort: the bit-vector term plus, when the
/// constructor count is not a power of two, the domain constraint asserting it
/// denotes a valid constructor. **Callers must assert `domain` (when present)**
/// alongside the variable's use, or the solver may pick an out-of-range value.
#[derive(Debug, Clone, Copy)]
pub struct EnumVar {
    /// The bit-vector term standing for the enum variable.
    pub term: TermId,
    /// `value < count` when `count` is not a power of two; otherwise `None`.
    pub domain: Option<TermId>,
}

/// A finite enumeration datatype, represented as a bit-vector of minimal width.
#[derive(Debug, Clone)]
pub struct EnumSort {
    name: String,
    constructors: Vec<String>,
    width: u32,
}

impl EnumSort {
    /// Builds an enumeration with the given (distinct, ordered) constructors.
    ///
    /// # Errors
    ///
    /// [`EnumError::Empty`] if there are no constructors, or
    /// [`EnumError::DuplicateConstructor`] on a repeated name.
    pub fn new(
        name: impl Into<String>,
        constructors: impl IntoIterator<Item = impl Into<String>>,
    ) -> Result<Self, EnumError> {
        let constructors: Vec<String> = constructors.into_iter().map(Into::into).collect();
        if constructors.is_empty() {
            return Err(EnumError::Empty);
        }
        for i in 0..constructors.len() {
            for j in (i + 1)..constructors.len() {
                if constructors[i] == constructors[j] {
                    return Err(EnumError::DuplicateConstructor(constructors[i].clone()));
                }
            }
        }
        let width = enum_width(constructors.len());
        Ok(Self {
            name: name.into(),
            constructors,
            width,
        })
    }

    /// The enumeration's name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The number of constructors.
    pub fn count(&self) -> usize {
        self.constructors.len()
    }

    /// The bit-width the enumeration lowers to.
    pub fn width(&self) -> u32 {
        self.width
    }

    /// The bit-vector sort this enumeration lowers to.
    pub fn sort(&self) -> Sort {
        Sort::BitVec(self.width)
    }

    /// The index of a constructor by name.
    fn index_of(&self, ctor: &str) -> Option<usize> {
        self.constructors.iter().position(|c| c == ctor)
    }

    /// The bit-vector constant term for a constructor.
    ///
    /// # Errors
    ///
    /// [`EnumError::UnknownConstructor`] if `ctor` is not in this enumeration.
    pub fn constructor(&self, arena: &mut TermArena, ctor: &str) -> Result<TermId, EnumError> {
        let index = self
            .index_of(ctor)
            .ok_or_else(|| EnumError::UnknownConstructor(ctor.to_owned()))?;
        Ok(arena.bv_const(self.width, index as u128)?)
    }

    /// Declares a fresh variable of this enumeration sort and computes its domain
    /// constraint (if the count is not a power of two).
    ///
    /// # Errors
    ///
    /// [`EnumError::Ir`] on an IR builder failure.
    pub fn var(&self, arena: &mut TermArena, var_name: &str) -> Result<EnumVar, EnumError> {
        let term = arena.bv_var(var_name, self.width)?;
        let domain = self.domain_constraint(arena, term)?;
        Ok(EnumVar { term, domain })
    }

    /// The domain constraint `value < count` for an enum-sorted term, or `None`
    /// when `count` is exactly `2^width` (every bit pattern is valid).
    ///
    /// # Errors
    ///
    /// [`EnumError::Ir`] on an IR builder failure.
    pub fn domain_constraint(
        &self,
        arena: &mut TermArena,
        value: TermId,
    ) -> Result<Option<TermId>, EnumError> {
        let count = self.constructors.len() as u128;
        if count == 1u128 << self.width {
            return Ok(None);
        }
        let bound = arena.bv_const(self.width, count)?;
        Ok(Some(arena.bv_ult(value, bound)?))
    }

    /// The `is-ctor` tester for `value`: `value == constructor(ctor)`.
    ///
    /// # Errors
    ///
    /// [`EnumError::UnknownConstructor`] if `ctor` is unknown, or
    /// [`EnumError::Ir`] on an IR builder failure.
    pub fn tester(
        &self,
        arena: &mut TermArena,
        value: TermId,
        ctor: &str,
    ) -> Result<TermId, EnumError> {
        let ctor_term = self.constructor(arena, ctor)?;
        Ok(arena.eq(value, ctor_term)?)
    }

    /// Maps a solved bit-vector value back to its constructor name, if it denotes
    /// a valid constructor.
    pub fn value_name(&self, value: &Value) -> Option<&str> {
        let (_, raw) = value.as_bv()?;
        let index = usize::try_from(raw).ok()?;
        self.constructors.get(index).map(String::as_str)
    }
}

/// The minimal bit-width to index `count` constructors (at least 1).
fn enum_width(count: usize) -> u32 {
    debug_assert!(count >= 1);
    if count <= 1 {
        return 1;
    }
    // Bits to represent the largest index `count - 1`.
    let max_index = (count - 1) as u128;
    u128::BITS - max_index.leading_zeros()
}
