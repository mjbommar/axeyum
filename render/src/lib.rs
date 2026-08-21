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
//! 2. **Is total, and is not silent.** [`Emitter::emit`] returns
//!    [`EmitOutput`], not a `Result`. Every [`assemble::ResolvedKind`] must
//!    render to something; there is no "unsupported block" escape hatch,
//!    because an emitter that could refuse would be a second failure surface
//!    and the one in [`assemble`] is the one that is tested. A kind an emitter
//!    cannot draw renders as its data (a listing, a link) -- never as nothing,
//!    and never as an apology.
//!
//!    Totality has a hole in it that round 1 found by looking at a page: an
//!    emitter handed something it does not understand can satisfy every rule
//!    above by DROPPING it, and the document is then simply shorter. Nothing
//!    fails, nothing says anything, and a reader cannot tell a document that
//!    omits a figure from one that never had one. So totality is paired with a
//!    second requirement, and the two together are the contract:
//!
//!    * **the page says so** -- an unrenderable block renders as a loud,
//!      visible box stating that the document is incomplete (the HTML
//!      emitter's `ax-unrenderable`), never as absence; and
//!    * **the caller can find out** -- [`Emitter::diagnostics`] returns one
//!      line per such block, so a gate can refuse a build that produced any.
//!      `render/check.sh` runs exactly that check over every committed
//!      manifest, in every format, and a non-empty list fails it.
//!
//!    This is not a second judgment about evidence and it cannot upgrade
//!    anything: assembly remains the sole authority on status. It reports only
//!    that the emitter did not draw something it was handed. The distinction
//!    that makes it safe: assembly REFUSES, an emitter REPORTS.
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

    /// One line per block this emitter could not draw, in document order.
    ///
    /// Empty for an emitter that renders everything it is handed, which is why
    /// the default is empty rather than `unimplemented`. A non-empty list means
    /// the emitted bytes contain a visible "this document is incomplete" box
    /// -- see contract point 2. It is a REPORT, never a refusal: the bytes are
    /// still returned, and the decision to fail a build on them belongs to the
    /// caller (`render/check.sh` makes it).
    fn diagnostics(&self, _doc: &ResolvedDocument) -> Vec<String> {
        Vec::new()
    }
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

/// A cross-document reference resolved to the page it names, or `None`.
///
/// Doc-IR carries a reference to another document as the RELATIVE PATH OF THAT
/// DOCUMENT'S SOURCE (`cards/F-nat-add-comm.doc.json`, `../fact-atlas.doc.json`),
/// relative to the referring document's own output file. That is deliberate:
/// the source file is the thing that exists on disk and can be checked, and a
/// producer that wrote `.html` into the IR would be encoding one emitter's
/// output layout into the data.
///
/// Every emitter resolves such a reference to the same place -- the HTML page,
/// because the corpus is published as an HTML site and that is the only format
/// the whole 324-card set is rendered in. A Markdown atlas linking into the
/// HTML cards is a live link; one linking to `.md` files nobody generated
/// would be a dead one, and this strand does not ship dead links that look
/// live.
///
/// `None` for anything that is not a SAFE RELATIVE reference: an absolute URL,
/// an absolute path, a Windows path, anything carrying whitespace, a quote, or
/// a fragment, and anything that does not name a Doc-IR source file. Callers
/// treat `None` as "not a document link" and fall back to plain text, so a
/// malformed reference can never become a live-looking anchor.
///
/// ```
/// use axeyum_render::doc_link_target;
/// assert_eq!(doc_link_target("cards/F-a.doc.json").as_deref(), Some("cards/F-a.html"));
/// assert_eq!(doc_link_target("../atlas.doc.json").as_deref(), Some("../atlas.html"));
/// assert_eq!(doc_link_target("../a.doc.json#index").as_deref(), Some("../a.html#index"));
/// assert_eq!(doc_link_target("https://x/a.doc.json"), None);
/// assert_eq!(doc_link_target("/abs/a.doc.json"), None);
/// assert_eq!(doc_link_target("a.json"), None);
/// ```
#[must_use]
pub fn doc_link_target(href: &str) -> Option<String> {
    const SUFFIX: &str = ".doc.json";
    // A fragment is allowed and travels through untouched: a card links UP to
    // the component figure it belongs to on the atlas
    // (`../facts-atlas.doc.json#dep-graph-c02`), which is a reference to a
    // place in another document, not to a different document.
    let (path, fragment) = match href.split_once('#') {
        Some((p, f)) => (p, Some(f)),
        None => (href, None),
    };
    let stem = path.strip_suffix(SUFFIX)?;
    if stem.is_empty() {
        return None;
    }
    if path.starts_with('/') || path.contains(':') {
        return None;
    }
    if href
        .chars()
        .any(|c| c.is_whitespace() || c.is_control() || matches!(c, '"' | '\'' | '<' | '>' | '\\'))
    {
        return None;
    }
    // A second `#` would make the fragment ambiguous, and `?` is a query a
    // static site has no way to answer.
    if fragment.is_some_and(|f| f.contains('#') || f.is_empty()) || href.contains('?') {
        return None;
    }
    Some(match fragment {
        Some(f) => format!("{stem}.html#{f}"),
        None => format!("{stem}.html"),
    })
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
