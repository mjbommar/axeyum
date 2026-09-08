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
mod ingest_stats;
mod parse;
mod regex;
mod regex_membership;
mod sexpr;
mod write;

pub use bounded_completeness::is_bounded_complete;
pub use ingest_stats::{IngestStats, IngestStatsGuard, last_ingest_stats};
pub use parse::{
    FpUsage, IntBound, IntBoundKind, Script, ScriptCommand, SourceStringSatProblem,
    SourceStringWitness, WordObligation, WordProblem, decode_packed_string, packed_string_max_len,
    parse_script, parse_script_with_string_bound, parse_script_with_string_bound_within,
    parse_script_within,
};
pub use regex_membership::{MemberConcatDefinition, MemberVar, MembershipProblem};
pub use sexpr::{SExpr, read_all};
pub use write::{sort_text, write_script};

use axeyum_ir::IrError;

/// The Unicode code points of an SMT-LIB string-literal token — the atom as the
/// reader produced it, **surrounding quotes included** — or `None` when `atom` is
/// not a well-formed string literal (or an escape names a code point above
/// `\u{2FFFF}`, which SMT-LIB does not have).
///
/// This is the one decoder every route already shares internally (the byte-model
/// bounded encoder and the code-point word/regex routes all go through it), so
/// `"\u{62}"` is the single character `b` everywhere and `""""` is the single
/// character `"`. It is public because a *certificate* over source
/// s-expressions needs the same literal lengths the solver reasoned with: a
/// second decoder is a second chance to disagree, and a disagreement about
/// `|"\u{1F600}"|` is a disagreement about a verdict.
#[must_use]
pub fn string_literal_code_points(atom: &str) -> Option<Vec<u32>> {
    if atom.len() < 2 || !atom.starts_with('"') || !atom.ends_with('"') {
        return None;
    }
    let inner = atom[1..atom.len() - 1].replace("\"\"", "\"");
    parse::decode_string_code_points(&inner)
}

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
    /// **This "58 MB / ~54 s" figure (~1.1 MB/s) is ~30x slower than
    /// `parse_script` measures on committed files up to 10.5 MB (30–58 MB/s,
    /// roughly linear) — an open discrepancy, not a correction, because the
    /// 58 MB file is not in the tree
    /// (`docs/research/12-performance/bench-primitives-2026-09-07.md`,
    /// Finding 2).** `ingest_stats::IngestStatsGuard` was added to test the
    /// leading candidate explanation, "the file's *shape* is the cost, not
    /// its size": none of three synthetic shapes up to 8 MB (flat
    /// declarations, a 65k-entry symbol table, `bvnot` nesting to depth
    /// 1,000,000) reproduced a rate anywhere near 1.1 MB/s — deep nesting
    /// alone shows real super-linear cost (100k→1M deep is 10x the bytes but
    /// ~17x the time) but stays at 13.8 MB/s even at that extreme, so shape
    /// alone is not a plausible sole explanation at sizes this deep. See
    /// `docs/research/12-performance/foundation-counters-2026-09-07.md` and
    /// `examples/ingest_shape_probe.rs`.
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
