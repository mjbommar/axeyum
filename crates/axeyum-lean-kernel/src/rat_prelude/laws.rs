//! The ordered-commutative-ring laws over `ℚ`.

use super::RatPrelude;
use crate::KernelError;
use crate::int_prelude::ops::IntDev;

/// Placeholder for the order laws.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_order_laws(_d: &mut IntDev<'_>, _p: RatPrelude) -> Result<(), KernelError> {
    Ok(())
}

/// Placeholder for the ring laws.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_ring_laws(_d: &mut IntDev<'_>, _p: RatPrelude) -> Result<(), KernelError> {
    Ok(())
}
