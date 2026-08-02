//! SMT-LIB 2 reader and writer for the Axeyum `QF_BV` slice.
//!
//! Reader: benchmark ingestion (formats note) — `declare-const`/0-ary
//! `declare-fun`, `define-fun` aliases, `let`, the full Phase 1 operator
//! set, hex/binary/indexed literals, `:status` ground truth. Incremental
//! scripting is rejected explicitly.
//!
//! Writer: sharing-preserving export — shared nodes become 0-ary
//! `define-fun`s so output is linear in the DAG, never the unfolded tree
//! (query-cost-control hard rule).
//!
//! Both directions are iterative; adversarially deep input cannot overflow
//! the stack.

mod bounded_completeness;
mod parse;
mod regex;
mod regex_membership;
mod sexpr;
mod write;

pub use bounded_completeness::is_bounded_complete;
pub use parse::{
    FpUsage, IntBound, IntBoundKind, Script, ScriptCommand, SourceStringSatProblem,
    SourceStringWitness, WordObligation, WordProblem, decode_packed_string, packed_string_max_len,
    parse_script, parse_script_with_string_bound, parse_script_with_string_bound_within,
    parse_script_within,
};
pub use regex_membership::{MemberConcatDefinition, MemberVar, MembershipProblem};
pub use sexpr::{SExpr, read_all};
pub use write::write_script;

use axeyum_ir::IrError;

/// Errors from SMT-LIB reading.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SmtError {
    /// Malformed input text.
    Syntax(String),
    /// Valid SMT-LIB outside the supported `QF_BV` benchmark slice.
    Unsupported(String),
    /// Sort or width error from term construction.
    Ir(IrError),
    /// The caller's wall-clock deadline expired during ingest.
    ///
    /// Parsing is a *phase*, not an instant: a 58 MB benchmark takes ~54 s to
    /// read, and an adversarially nested source can spend minutes in semantic
    /// analysis. With no deadline in the parser, a 24 s budget produced measured
    /// runs of 39.9 s, 49.4 s and 66 s — and under SMT-COMP those are SIGKILLed
    /// processes, which score strictly worse than the first-class `unknown` a
    /// resource-exhausted solver owes its caller.
    ///
    /// This is a RESOURCE limit, never a statement about the query: a caller
    /// must map it to `unknown`, never to a verdict.
    DeadlineExceeded(String),
}

impl From<IrError> for SmtError {
    fn from(e: IrError) -> Self {
        SmtError::Ir(e)
    }
}

impl core::fmt::Display for SmtError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            SmtError::Syntax(s) => write!(f, "syntax error: {s}"),
            SmtError::Unsupported(s) => write!(f, "unsupported: {s}"),
            SmtError::Ir(e) => write!(f, "term error: {e}"),
            SmtError::DeadlineExceeded(s) => write!(f, "deadline exceeded during ingest: {s}"),
        }
    }
}

impl core::error::Error for SmtError {}
