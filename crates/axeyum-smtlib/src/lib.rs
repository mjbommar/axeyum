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

mod parse;
mod sexpr;
mod write;

pub use parse::{Script, ScriptCommand, parse_script};
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
        }
    }
}

impl core::error::Error for SmtError {}
