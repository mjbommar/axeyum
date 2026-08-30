//! Executable instruction-set semantics for Axeyum.
//!
//! This crate is the semantic authority for the machine examples used by
//! *Instruction Sets, Programs, and Proofs*. Search and proof production live
//! elsewhere. This layer defines concrete words, states, decoders, steps, and
//! replayable traces before any solver formula is allowed to stand for a
//! machine claim.

pub mod a0;
