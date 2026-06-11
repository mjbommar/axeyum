//! Concrete values produced by evaluation and carried by models.

use crate::sort::Sort;

/// A concrete value of some [`Sort`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Value {
    /// A Boolean value.
    Bool(bool),
    /// A bit-vector value; `value` always fits in `width` bits.
    Bv {
        /// Width in bits.
        width: u32,
        /// The value, masked to `width` bits.
        value: u128,
    },
}

impl Value {
    /// The sort of this value.
    pub fn sort(self) -> Sort {
        match self {
            Value::Bool(_) => Sort::Bool,
            Value::Bv { width, .. } => Sort::BitVec(width),
        }
    }

    /// Returns the Boolean payload, or `None` for non-Boolean values.
    pub fn as_bool(self) -> Option<bool> {
        match self {
            Value::Bool(b) => Some(b),
            Value::Bv { .. } => None,
        }
    }

    /// Returns the bit-vector payload `(width, value)`, or `None`.
    pub fn as_bv(self) -> Option<(u32, u128)> {
        match self {
            Value::Bool(_) => None,
            Value::Bv { width, value } => Some((width, value)),
        }
    }
}

impl core::fmt::Display for Value {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Value::Bool(b) => write!(f, "{b}"),
            Value::Bv { width, value } => {
                write!(f, "#x{value:0>pad$x}", pad = (*width as usize).div_ceil(4))
            }
        }
    }
}
