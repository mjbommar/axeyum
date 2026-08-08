//! SMT-LIB 2 reader and sharing-preserving writer for Axeyum.
//!
//! The reader covers the typed command and term surface admitted by the current
//! parser, including arrays, arithmetic, floating point, strings, quantifiers,
//! functions, datatypes, objectives, output requests, and ordered incremental
//! `push`/`pop`/query commands. Parsing support is not the same as solver-route
//! support; callers must preserve explicit unsupported/resource outcomes.
//!
//! The writer emits complete scripts and turns shared nodes into 0-ary
//! `define-fun`s so output is linear in the DAG, never the unfolded tree
//! (query-cost-control hard rule).
//!
//! Both directions are iterative; adversarially deep input cannot overflow
//! the stack.
//!
//! # Example
//!
//! ```
//! use axeyum_smtlib::{parse_script, write_script};
//!
//! let script = parse_script(
//!     "(set-logic QF_BV) (declare-const x (_ BitVec 8)) \
//!      (assert (= x #x2a)) (check-sat)"
//! )?;
//! assert_eq!(script.logic.as_deref(), Some("QF_BV"));
//! assert_eq!(script.assertions.len(), 1);
//! assert_eq!(script.check_sats, 1);
//!
//! let exported = write_script(&script.arena, &script.assertions);
//! assert!(exported.contains("(check-sat)"));
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```

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
    /// Well-formed SMT-LIB outside the parser's admitted typed surface.
    Unsupported(String),
    /// Sort or width error from term construction.
    Ir(IrError),
    /// The caller's wall-clock deadline expired during ingest.
    ///
    /// Parsing is a *phase*, not an instant: a 58 MB benchmark takes ~54 s to
    /// read, and an adversarially nested source can spend minutes in semantic
    /// analysis. With no deadline in the parser, a 24 s budget produced measured
    /// runs of 39.9 s, 49.4 s and 66 s — and under SMT-COMP those are `SIGKILL`ed
    /// processes, which score strictly worse than the first-class `unknown` a
    /// resource-exhausted solver owes its caller.
    ///
    /// This is a RESOURCE limit, never a statement about the query: a caller
    /// must map it to `unknown`, never to a verdict.
    DeadlineExceeded(String),
    /// A deterministic ingest work ceiling was exceeded.
    ///
    /// Unlike [`SmtError::Unsupported`], this does not mean the source uses an
    /// unimplemented construct. The construct is supported, but its eager
    /// representation would exceed a documented resource budget. Callers must
    /// map this to `unknown(ResourceLimit)`, never to a verdict or parse error.
    ResourceLimit(String),
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
            SmtError::ResourceLimit(s) => write!(f, "resource limit during ingest: {s}"),
        }
    }
}

impl core::error::Error for SmtError {}
