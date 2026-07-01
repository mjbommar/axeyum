//! Shared bit-vector value conversion helpers.
//!
//! Phase 4 fixes one public convention before bit lowering exists: bit-vector
//! wire vectors are LSB-first. Element `i` is SMT-LIB bit index `i` and has
//! numeric weight `2^i`.

use crate::sort::{ArraySortKey, MAX_BV_WIDTH};
use crate::{IrError, Sort, Value};

/// Bit order used when lowering bit-vector values to Boolean wires.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BitOrder {
    /// Least-significant bit first: element `i` has numeric weight `2^i`.
    LsbFirst,
}

/// The Phase 4 bit-vector wire order fixed by ADR-0006.
pub const BIT_VECTOR_WIRE_ORDER: BitOrder = BitOrder::LsbFirst;

/// Converts a concrete value to LSB-first Boolean bits.
///
/// A Boolean value converts to one bit. A bit-vector value converts to `width`
/// bits where bit `i` is at index `i`.
///
/// # Errors
///
/// Returns [`IrError::InvalidWidth`] for invalid bit-vector widths and
/// [`IrError::ValueOutOfRange`] when a manually constructed [`Value::Bv`]
/// payload does not fit its width.
pub fn value_to_lsb_bits(value: Value) -> Result<Vec<bool>, IrError> {
    match value {
        Value::Bool(bit) => Ok(vec![bit]),
        Value::Bv { width, value } => bv_value_to_lsb_bits(width, value),
        Value::WideBv(w) => Ok(w.to_lsb_bits()),
        Value::Array(array) => Err(IrError::SortMismatch {
            expected: "Bool or BitVec",
            found: Sort::Array {
                index: ArraySortKey::BitVec(array.index_width()),
                element: ArraySortKey::BitVec(array.element_width()),
            },
        }),
        Value::GenericArray(array) => Err(IrError::SortMismatch {
            expected: "Bool or BitVec",
            found: Sort::Array {
                index: array.index_sort(),
                element: array.element_sort(),
            },
        }),
        Value::Int(_) => Err(IrError::SortMismatch {
            expected: "Bool or BitVec",
            found: Sort::Int,
        }),
        Value::Real(_) | Value::RealAlgebraic(_) => Err(IrError::SortMismatch {
            expected: "Bool or BitVec",
            found: Sort::Real,
        }),
        Value::Datatype { datatype, .. } => Err(IrError::SortMismatch {
            expected: "Bool or BitVec",
            found: Sort::Datatype(datatype),
        }),
        Value::Uninterpreted { sort, .. } => Err(IrError::SortMismatch {
            expected: "Bool or BitVec",
            found: Sort::Uninterpreted(sort),
        }),
        // A sequence has no scalar bit encoding; decline exactly like the
        // array/datatype siblings (ADR-0051, P2.7).
        Value::Seq(elements) => Err(IrError::SortMismatch {
            expected: "Bool or BitVec",
            found: Value::Seq(elements).sort(),
        }),
    }
}

/// Converts a bit-vector payload to LSB-first Boolean bits.
///
/// # Errors
///
/// Returns [`IrError::InvalidWidth`] for widths outside `1..=128`, and
/// [`IrError::ValueOutOfRange`] if `value` does not fit in `width` bits.
pub fn bv_value_to_lsb_bits(width: u32, value: u128) -> Result<Vec<bool>, IrError> {
    validate_bv_payload(width, value)?;
    if width > 128 {
        // A `u128` cannot hold a wider value; callers use the `WideUint` path.
        return Err(IrError::InvalidWidth(width));
    }
    Ok((0..width).map(|bit| ((value >> bit) & 1) == 1).collect())
}

/// Converts LSB-first Boolean bits into a bit-vector [`Value`].
///
/// # Errors
///
/// Returns [`IrError::InvalidWidth`] when `bits.len()` is outside `1..=128`.
pub fn lsb_bits_to_bv_value(bits: &[bool]) -> Result<Value, IrError> {
    let width = u32::try_from(bits.len()).unwrap_or(u32::MAX);
    validate_width(width)?;
    if width > 128 {
        // Use `Value::WideBv` (via `lsb_bits_to_value`) for wider bit-vectors.
        return Err(IrError::InvalidWidth(width));
    }
    let mut value = 0u128;
    for (index, bit) in bits.iter().copied().enumerate() {
        if bit {
            value |= 1u128 << index;
        }
    }
    Ok(Value::Bv { width, value })
}

/// Converts LSB-first Boolean bits into a concrete value of `sort`.
///
/// # Errors
///
/// Returns [`IrError::BitCountMismatch`] when the bit count does not match
/// `sort`, or [`IrError::InvalidWidth`] for invalid bit-vector widths.
pub fn lsb_bits_to_value(sort: Sort, bits: &[bool]) -> Result<Value, IrError> {
    match sort {
        Sort::Bool => {
            if bits.len() == 1 {
                Ok(Value::Bool(bits[0]))
            } else {
                Err(IrError::BitCountMismatch {
                    expected: 1,
                    found: bits.len(),
                })
            }
        }
        // Floating-point shares the bit-vector representation: `exp + sig` bits.
        Sort::BitVec(_) | Sort::Float { .. } => {
            let width = match sort {
                Sort::BitVec(w) => w,
                Sort::Float { exp, sig } => exp + sig,
                _ => 0, // unreachable given the outer arm, but keeps this total
            };
            validate_width(width)?;
            if bits.len() != width as usize {
                return Err(IrError::BitCountMismatch {
                    expected: width,
                    found: bits.len(),
                });
            }
            if width > 128 {
                // Wide bit-vector model value (ADR wide-BV).
                Ok(Value::WideBv(crate::wide::WideUint::from_lsb_bits(bits)))
            } else {
                lsb_bits_to_bv_value(bits)
            }
        }
        Sort::Array { .. }
        | Sort::Int
        | Sort::Real
        | Sort::Datatype(_)
        | Sort::Uninterpreted(_)
        | Sort::Seq(_) => Err(IrError::SortMismatch {
            expected: "Bool or BitVec",
            found: sort,
        }),
    }
}

fn validate_bv_payload(width: u32, value: u128) -> Result<(), IrError> {
    validate_width(width)?;
    if width < 128 && value >= (1u128 << width) {
        Err(IrError::ValueOutOfRange { width, value })
    } else {
        Ok(())
    }
}

fn validate_width(width: u32) -> Result<(), IrError> {
    if (1..=MAX_BV_WIDTH).contains(&width) {
        Ok(())
    } else {
        Err(IrError::InvalidWidth(width))
    }
}
