//! Reader-facing presentation for A0 construction errors.
//!
//! This presentation layer stays outside `a0.rs`, whose complete source digest
//! is a versioned semantic input to the book's replayable A0 evidence.

use core::fmt;

use crate::a0::A0Error;

impl fmt::Display for A0Error {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidWordWidth(width) => write!(
                formatter,
                "invalid A0 word width {width}; expected 8, 16, ..., or 64"
            ),
            Self::InvalidWidthConversion { from, to } => {
                write!(formatter, "invalid width conversion from {from} to {to}")
            }
            Self::StateWidthMismatch {
                component,
                expected,
                actual,
            } => write!(
                formatter,
                "state component {component} has width {actual}; expected {expected}"
            ),
            Self::InvalidStateEncoding(reason) => {
                write!(formatter, "invalid A0 state encoding: {reason}")
            }
            Self::DuplicateMemoryAddress(address) => {
                write!(formatter, "duplicate A0 memory address {address}")
            }
            Self::InvalidMemoryAddress { width, address } => write!(
                formatter,
                "A0 memory address {address} does not fit width {width}"
            ),
            Self::WidthMismatch { expected, actual } => {
                write!(
                    formatter,
                    "width mismatch: expected {expected}, got {actual}"
                )
            }
            Self::InvalidRegister(register) => {
                write!(
                    formatter,
                    "invalid A0 register r{register}; expected r0 through r7"
                )
            }
            Self::IllegalEncoding(bytes) => {
                write!(formatter, "illegal A0 encoding {bytes:02x?}")
            }
        }
    }
}

impl std::error::Error for A0Error {}
