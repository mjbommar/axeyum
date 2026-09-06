//! The workspace's **single naming point** for the arbitrary-precision
//! numeric types and the numeric traits they come with.
//!
//! ADR-1710's whole argument is that eight modules grew their own bignum path
//! because each one named `num-bigint` and `num-rational` for itself. A crate
//! that can write `use num_bigint::BigInt;` can also write its own gcd, its
//! own `pow_mod`, and its own Sturm chain — and eight of them did. So the
//! boundary is enforced rather than described: every other crate in the
//! workspace imports these names **from here**, and
//! `scripts/check-arith-boundary.sh` fails the build if one names the upstream
//! crates directly.
//!
//! Nothing here is a wrapper. These are plain `pub use` re-exports, so the
//! types are the same types, `BigRational::new` is the same constructor, and a
//! consumer pays nothing for going through this module. What it buys is one
//! place to answer the design note's first open question — whether the base
//! layer moves from `num-bigint` to `dashu` — instead of forty.
//!
//! # What is re-exported, and why only this much
//!
//! The set is the measured one: every path any consumer in the workspace
//! actually named, and nothing else. Adding to it is cheap; adding to it
//! *speculatively* would make the boundary a formality.

pub use num_bigint::{BigInt, BigUint, Sign};
pub use num_integer::Integer;
pub use num_rational::BigRational;
pub use num_traits::{One, Signed, ToPrimitive, Zero};
