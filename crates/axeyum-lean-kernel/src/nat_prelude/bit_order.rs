//! `Nat.lt_of_testBit` (Nat-valued local analogue) and its supporting
//! arithmetic toolkit (`self_lt_two_pow`, `self_lt_two_pow_add`) — pieces
//! toward `F:ml430-nat-lt-xor-cases-c43a1e85`. See
//! `docs/plan/status/260-nat-lt-xor-cases.md` /
//! `docs/plan/status/263-nat-testbit-xor.md` for pieces 1 and the overall
//! plan; `docs/plan/status/265-nat-msb-order.md` for this lane's handoff.
//!
//! WORK IN PROGRESS scaffold: dispatch is a no-op until each declaration is
//! landed below.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::expr::ExprId;

/// Everything this module declares, in dependency order.
pub(super) fn declare_bit_order_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let _ = (d, p);
    Ok(())
}
