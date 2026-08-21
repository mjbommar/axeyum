//! Doc-IR assembly and emitters: Axeyum artifacts rendered as documents that
//! cannot lie.
//!
//! A rendered document here is a checker output, not prose about one. The
//! package has exactly two halves and the split is the whole design:
//!
//! * [`assemble`] -- the resolver. Loads run records and fact-ledger entries,
//!   re-hashes every declared input, resolves every reference, and computes each
//!   claim's rendered status. **Everything that can fail, fails here.**
//! * [`emit_md`], [`emit_tex`] (and DESIGN's `emit_html`) -- the emitters. Pure
//!   functions from a [`assemble::ResolvedDocument`] to bytes. **Total and
//!   dumb**: no I/O, no judgment, no error path.
//!
//! Keeping the trusted logic in one small file is what makes the fail-closed law
//! auditable. An emitter that could decide anything would be a second place a
//! green badge could come from.
//!
//! # The `Emitter` contract
//!
//! This is the contract DESIGN's `emit_html.rs` implements, stated in full
//! because a third emitter that satisfies it plugs in with no change to
//! assembly, and one that does not is a hole in the cross-format property.
//!
//! An implementation of [`Emitter`]:
//!
//! 1. **Is a pure function of its argument.** No file reads, no environment,
//!    no clock, no randomness, no global state. Two calls with equal inputs
//!    return equal outputs, in the same process or a different one. The epoch
//!    is [`assemble::ResolvedDocument::epoch_unix`]; there is no other source of
//!    time and asking the OS for one breaks every golden test in the package.
//! 2. **Is total.** [`Emitter::emit`] returns [`EmitOutput`], not a `Result`.
//!    Every [`assemble::ResolvedKind`] must render to something; there is no
//!    "unsupported block" escape hatch, because an emitter that could refuse
//!    would be a second failure surface and the one in [`assemble`] is the one
//!    that is tested. A kind an emitter cannot draw renders as its data (a
//!    listing, a link) -- never as nothing, and never as an apology.
//! 3. **Never inspects evidence to decide anything.** In particular it never
//!    reads [`assemble::ResolvedEvidence::exit_status`] or `outcome` to choose
//!    a badge. The badge is
//!    [`assemble::ResolvedKind::Claim::status`], already computed, and the
//!    emitter's only job is to print
//!    [`ir::EvidenceStatus::badge`] for it. Exit status may be DISPLAYED (it is
//!    useful to a reader); it may not be branched on.
//! 4. **Honours [`ir::Verbosity`] mechanically.** `Essential` renders in the
//!    body; `Detail` renders folded (`<details>` / appendix / live toggle);
//!    `Archive` renders as a link to the artifact and its content does not
//!    appear. Choosing what a reader may skip is an editorial decision that
//!    belongs to the manifest, not the renderer.
//! 5. **Emits every claim recoverably.** For each `(label, status)` in
//!    [`assemble::ResolvedDocument::claims`], the emitted bytes must contain a
//!    machine-recoverable pairing of that label with
//!    `status.badge()` -- the exact uppercase token, not a synonym, not a
//!    colour, not an icon alone. `render/tests/cross_format.rs` recovers the set
//!    from the BYTES of each format and requires the three sets to be equal, so
//!    an emitter cannot pass this by omitting a claim: an omitted claim is a
//!    failing test, which is the point.
//! 6. **Is deterministic in ordering.** Blocks in document order; maps iterated
//!    as `BTreeMap`; no `HashMap` anywhere in output-producing code.
//! 7. **Writes side files through [`EmitOutput::aux`]**, never to disk. The
//!    caller decides where bytes land. `aux` keys are relative file names
//!    (`axeyum.sty`, `fig-weights.svg`); the map is a `BTreeMap` so the write
//!    order is fixed.
//! 8. **Produces ASCII.** Repository-wide rule; the HTML emitter escapes rather
//!    than emitting a literal non-ASCII byte.
//!
//! An emitter is registered by [`emitter_for`]; adding one means adding an arm
//! there and a golden test, nothing else.

pub mod assemble;
pub mod emit_md;
pub mod emit_tex;
pub mod ir;

// DESIGN owns these two modules (render/src/emit_html.rs, render/src/layout.rs).
// They are behind the off-by-default `html` feature so this package builds
// before they exist; round-2 integration turns the feature on by default.
#[cfg(feature = "html")]
pub mod emit_html;
#[cfg(feature = "html")]
pub mod layout;

use std::collections::BTreeMap;

use assemble::ResolvedDocument;

/// What an emitter produces: one primary document plus any side files.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct EmitOutput {
    /// The document itself.
    pub primary: String,
    /// Side files, keyed by relative file name. A `BTreeMap` so the write order
    /// is fixed and a golden test can compare the whole set.
    pub aux: BTreeMap<String, String>,
}

impl EmitOutput {
    /// An output with no side files.
    pub fn new(primary: String) -> Self {
        Self {
            primary,
            aux: BTreeMap::new(),
        }
    }

    /// Attach a side file.
    #[must_use]
    pub fn with_aux(mut self, name: impl Into<String>, contents: impl Into<String>) -> Self {
        self.aux.insert(name.into(), contents.into());
        self
    }
}

/// A renderer for one output format.
///
/// See the module documentation for the full contract. The short version:
/// pure, total, deterministic, and forbidden from computing a status.
pub trait Emitter {
    /// Stable short name: `md`, `tex`, `html`. Used by the CLI and by tests.
    fn format_name(&self) -> &'static str;

    /// Extension for the primary output, without the dot.
    fn primary_extension(&self) -> &'static str;

    /// Render a resolved document. Cannot fail; see contract point 2.
    fn emit(&self, doc: &ResolvedDocument) -> EmitOutput;
}

/// The emitter for a format name, or `None` if this build has none.
///
/// `html` returns `None` until DESIGN's emitter is wired (the `html` feature),
/// and the CLI turns that into an explicit "not yet wired" message rather than
/// silently falling back to another format.
pub fn emitter_for(format: &str) -> Option<Box<dyn Emitter>> {
    match format {
        "md" | "markdown" => Some(Box::new(emit_md::MarkdownEmitter)),
        "tex" | "latex" => Some(Box::new(emit_tex::LatexEmitter)),
        #[cfg(feature = "html")]
        "html" => Some(Box::new(emit_html::HtmlEmitter)),
        _ => None,
    }
}

/// Canonical JSON: sorted keys, two-space indent, one trailing newline.
///
/// This is the exact form `scripts/validate-docir.py --canonicalize` prints, and
/// the schema round-trip test compares the two byte for byte. Sorted keys come
/// free from `serde_json`'s default `Map` being a `BTreeMap` -- which is why the
/// `preserve_order` feature is deliberately not enabled.
///
/// # Errors
/// Propagates a `serde_json` failure to serialize the value.
pub fn canonical_json<T: serde::Serialize>(value: &T) -> Result<String, serde_json::Error> {
    let v = serde_json::to_value(value)?;
    Ok(serde_json::to_string_pretty(&v)? + "\n")
}
