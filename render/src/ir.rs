//! The Doc-IR: serde structs mirroring `artifacts/ontology/docir.schema.json`.
//!
//! This module is the Rust half of a two-implementation discipline. The schema
//! file is the other half and `scripts/validate-docir.py` enforces it
//! independently; neither is allowed to be the only definition of the format.
//! When they disagree, the disagreement is the bug -- `render/tests/schema.rs`
//! exists to make it a failing test rather than a surprise in production.
//!
//! Two rules govern edits here:
//!
//! * `deny_unknown_fields` on every struct that the schema marks
//!   `additionalProperties: false`. A manifest with a misspelled key is a
//!   build error, not a silently ignored field -- which is how a `tag` that
//!   should have folded a block instead renders it in full.
//! * `BTreeMap` and `Vec`, never `HashMap`. Determinism is a repository-wide
//!   API promise and hash iteration order is the standard way to break it.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

/// The Doc-IR schema version this build reads and writes.
pub const SCHEMA_VERSION: u32 = 1;

/// A renderable document: prose plus references, never transcribed content.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Document {
    /// Format version; must equal [`SCHEMA_VERSION`].
    pub schema_version: u32,
    /// Identity and build-wide settings.
    pub meta: DocMeta,
    /// The body, in reading order.
    pub blocks: Vec<Block>,
    /// How the document itself was produced, when a producer generated it.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub provenance: Option<Provenance>,
}

/// Document identity and build-wide settings. Everything here is input.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DocMeta {
    /// Stable slug; the output file stem and the anchor namespace.
    pub doc_id: String,
    /// Human title.
    pub title: String,
    /// Optional subtitle.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub subtitle: Option<String>,
    /// Which rendering product this is.
    #[serde(default)]
    pub genre: Genre,
    /// Human authors of the prose only; machine content is attributed by its
    /// [`Provenance::generator`].
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub authors: Vec<String>,
    /// Optional abstract.
    #[serde(rename = "abstract", default, skip_serializing_if = "Option::is_none")]
    pub abstract_text: Option<RichText>,
    /// The document's notion of "now", supplied as data.
    pub epoch: Epoch,
    /// The repository state archive links are pinned to.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub repo: Option<RepoPin>,
    /// Per-format rendering options.
    #[serde(default, skip_serializing_if = "Options::is_empty")]
    pub options: Options,
}

/// Which of the two rendering products a document is.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Genre {
    /// What Axeyum did: a derivation, a certificate run.
    #[default]
    System,
    /// What is established: fact cards, an atlas.
    Result,
    /// An integrated project whose claim-bearing content is generated.
    Paper,
}

/// The repository state a document is pinned to.
#[derive(Debug, Clone, PartialEq, Default, Serialize, Deserialize)]
pub struct RepoPin {
    /// Repository URL.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub url: Option<String>,
    /// Pinned commit.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub commit: Option<String>,
    /// Path prefix that artifact paths resolve against.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub root: Option<String>,
}

/// Per-format rendering options. Emitters read these and never write them.
#[derive(Debug, Clone, PartialEq, Default, Serialize, Deserialize)]
pub struct Options {
    /// LaTeX options; `detail` is `inline` | `appendix` | `drop-with-href`.
    #[serde(default, skip_serializing_if = "serde_json::Map::is_empty")]
    pub latex: serde_json::Map<String, serde_json::Value>,
    /// Markdown options.
    #[serde(default, skip_serializing_if = "serde_json::Map::is_empty")]
    pub markdown: serde_json::Map<String, serde_json::Value>,
    /// HTML options; owned by DESIGN's emitter.
    #[serde(default, skip_serializing_if = "serde_json::Map::is_empty")]
    pub html: serde_json::Map<String, serde_json::Value>,
}

impl Options {
    /// True when no option is set in any format.
    pub fn is_empty(&self) -> bool {
        self.latex.is_empty() && self.markdown.is_empty() && self.html.is_empty()
    }

    /// Look up a string option for one format, e.g. `("latex", "detail")`.
    pub fn get_str(&self, format: &str, key: &str) -> Option<&str> {
        let map = match format {
            "latex" => &self.latex,
            "markdown" => &self.markdown,
            "html" => &self.html,
            _ => return None,
        };
        map.get(key).and_then(serde_json::Value::as_str)
    }
}

/// The document's notion of "now", supplied as data rather than observed.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Epoch {
    /// Seconds since the Unix epoch, UTC.
    pub unix: i64,
    /// Where the value came from.
    pub source: EpochSource,
    /// The commit, when `source` is `commit`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub commit: Option<String>,
}

/// Where an [`Epoch`] came from.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum EpochSource {
    /// The pinned commit's committer time.
    Commit,
    /// The reproducible-builds environment variable.
    SourceDateEpoch,
    /// A constant written into a manifest or fixture.
    Fixed,
}

/// How much of a block reaches the reader.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Verbosity {
    /// Always shown.
    Essential,
    /// Shown folded.
    Detail,
    /// Dropped from the body; rendered as a link.
    Archive,
}

/// One block of a document.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Block {
    /// Document-unique, stable id: the anchor target and the golden-diff name.
    pub id: String,
    /// Verbosity tier.
    pub tag: Verbosity,
    /// The payload.
    pub kind: BlockKind,
    /// How this block's content was produced, when a machine produced it. Its
    /// absence is the honest signal that a human wrote the block.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub provenance: Option<Provenance>,
    /// Optional heading, also used as the fold summary.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub title: Option<String>,
    /// Optional human-facing anchor slug overriding `id` in output.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub anchor: Option<String>,
}

/// The block payload. A closed set: a new kind lands in every emitter in the
/// same change or not at all, because an emitter is total and has no error path.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "lowercase", deny_unknown_fields)]
pub enum BlockKind {
    /// Human narrative: the only block kind a person writes.
    Prose {
        /// CommonMark-flavoured source, or the bare-string shorthand.
        text: RichTextInline,
        /// Verbatim LaTeX override.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        latex: Option<String>,
        /// When present, renders as a heading at this level.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        heading_level: Option<u8>,
    },
    /// An assertion bound to the evidence that establishes it.
    Claim {
        /// Short human-facing name; the key of the cross-format property.
        label: String,
        /// What is asserted: prose, or a checked reference.
        statement: StatementSource,
        /// The status the producer DECLARES. A ceiling, not a result.
        status: EvidenceStatus,
        /// At least one reference to a recorded run.
        evidence: Vec<EvidenceRef>,
        /// Optional aside.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        note: Option<RichText>,
    },
    /// A statement of record pulled by checked reference. Deliberately has no
    /// text field: there is no fallback to inlined prose.
    Statement {
        /// The reference.
        #[serde(rename = "ref")]
        reference: FormalRef,
        /// Which resolved parts to render, in this order.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        show: Option<Vec<StatementField>>,
        /// Optional aside.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        note: Option<RichText>,
    },
    /// A derivation as (input, op, output) triples.
    Steps {
        /// Optional caption.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        caption: Option<RichText>,
        /// The steps, in order.
        steps: Vec<Step>,
    },
    /// Tabular data with the provenance of the run that produced it.
    ///
    /// Either `from_run` names a record and one of its tables -- the preferred
    /// form, in which the numbers exist in exactly one place -- or `columns`,
    /// `rows` and `source` are supplied literally, which puts numbers a human
    /// typed into the manifest and is the weaker form.
    Table {
        /// Optional caption.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        caption: Option<RichText>,
        /// Take the columns, rows and provenance out of a run record.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        from_run: Option<TableFromRun>,
        /// Column specifications, in order. Required unless `from_run` is set.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        columns: Option<Vec<Column>>,
        /// Rows; each must have exactly `columns.len()` cells.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        rows: Option<Vec<Vec<serde_json::Value>>>,
        /// A table with no producing command is a transcription.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        source: Option<Provenance>,
    },
    /// A checkable artifact presented as such, with its replay command.
    Certificate {
        /// What kind of thing is certified, which fixes what a reader trusts.
        cert_kind: CertKind,
        /// One-line human summary.
        summary: RichText,
        /// Files the reader can fetch and check.
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        artifact_refs: Vec<ArtifactRef>,
        /// How to re-run it.
        replay: Command,
        /// Optional run records; may be empty, unlike a claim's.
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        evidence: Vec<EvidenceRef>,
    },
    /// A figure specified as data wherever possible.
    Figure {
        /// Optional caption.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        caption: Option<RichText>,
        /// Text alternative.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        alt: Option<String>,
        /// The specification.
        spec: FigureSpec,
    },
    /// An external artifact referenced from the document.
    Include {
        /// Path, resolved against the pinned commit.
        path: String,
        /// How a format that can inline it should do so.
        render_hint: RenderHint,
        /// Syntax-highlighting language for `code`.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        language: Option<String>,
        /// Optional caption.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        caption: Option<RichText>,
        /// Digest; verified by assembly when present.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        sha256: Option<String>,
        /// Inlining budget; a larger file degrades to a link.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        max_bytes: Option<u64>,
    },
}

/// Where a table takes its data from, when it takes it from a recorded run.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TableFromRun {
    /// Path to the run-record JSON, resolved like an [`EvidenceRef`].
    pub run_record: String,
    /// Key in the record's `tables` map.
    pub table: String,
    /// Expected record id; a mismatch is a build error.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub record_id: Option<String>,
}

/// One column of a table.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Column {
    /// Stable key.
    pub key: String,
    /// Header text.
    pub header: String,
    /// Alignment.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub align: Option<Align>,
    /// Optional note.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub note: Option<String>,
}

/// Column alignment.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Align {
    /// Left-aligned.
    Left,
    /// Centred.
    Center,
    /// Right-aligned.
    Right,
}

/// What kind of thing a certificate block certifies.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum CertKind {
    /// A model, checked by evaluating the original term.
    Sat,
    /// A refutation, checked by an independent DRAT checker.
    UnsatDrat,
    /// A proof term, checked by re-deriving its type.
    KernelAdmission,
    /// A recorded report run.
    ReportRun,
    /// A replayed witness.
    WitnessReplay,
    /// A cube cover.
    CubeCover,
}

impl CertKind {
    /// Stable display name used by every emitter.
    pub fn label(self) -> &'static str {
        match self {
            Self::Sat => "SAT model",
            Self::UnsatDrat => "UNSAT (DRAT)",
            Self::KernelAdmission => "kernel admission",
            Self::ReportRun => "report run",
            Self::WitnessReplay => "witness replay",
            Self::CubeCover => "cube cover",
        }
    }
}

/// How an included artifact should be rendered by a format that can inline it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum RenderHint {
    /// Always a link.
    Link,
    /// A fenced code block.
    Code,
    /// Verbatim text.
    Text,
    /// An image.
    Image,
    /// Pretty-printed JSON.
    Json,
    /// A table.
    Table,
}

/// Which resolved parts of a referenced statement to render.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum StatementField {
    /// The statement's title.
    Title,
    /// The prose statement.
    Prose,
    /// The machine-readable statement plus its language.
    Formal,
    /// Both status axes.
    Status,
    /// What the establishing evidence rests on that was not itself proved.
    AxiomFootprint,
    /// Which machine established it.
    ProofRoute,
    /// The statements it rests on.
    DependsOn,
    /// How many evidence rows it carries.
    EvidenceCount,
}

/// One (input, op, output) triple of a derivation.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Step {
    /// Optional explicit index.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub index: Option<u32>,
    /// What went in.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub input: Option<RichText>,
    /// The transformation applied.
    pub op: String,
    /// What came out.
    pub output: RichText,
    /// Optional aside.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub note: Option<RichText>,
    /// Optional checked reference to the fact that licenses this step. A
    /// dangling justification is a build error, not a plausible rule name.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub justification: Option<FormalRef>,
}

/// A span of human text with optional per-format overrides.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RichText {
    /// CommonMark-flavoured source; inline math in `$...$` survives both
    /// emitters unmodified.
    pub text: String,
    /// Verbatim LaTeX replacing the mechanical conversion of `text`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub latex: Option<String>,
    /// Verbatim HTML; the Markdown and LaTeX emitters ignore it.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub html: Option<String>,
}

impl RichText {
    /// A plain span with no overrides.
    pub fn plain(text: impl Into<String>) -> Self {
        Self {
            text: text.into(),
            latex: None,
            html: None,
        }
    }
}

/// A [`RichText`], or a bare string shorthand for one.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum RichTextInline {
    /// The `{ "text": ... }` shorthand.
    Plain(String),
    /// The full form.
    Rich(RichText),
}

impl RichTextInline {
    /// Normalise to the full form.
    pub fn to_rich(&self) -> RichText {
        match self {
            Self::Plain(s) => RichText::plain(s.clone()),
            Self::Rich(r) => r.clone(),
        }
    }
}

/// What a claim asserts: prose for this document, or a checked reference.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "source", rename_all = "lowercase", deny_unknown_fields)]
pub enum StatementSource {
    /// Prose written for this document.
    Text {
        /// The prose.
        text: String,
        /// Verbatim LaTeX override.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        latex: Option<String>,
        /// Verbatim HTML override.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        html: Option<String>,
    },
    /// A checked reference to a statement of record.
    Ref {
        /// The reference.
        #[serde(rename = "ref")]
        reference: FormalRef,
    },
}

/// A checked reference to a statement of record. Dangling is a build error.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "lowercase", deny_unknown_fields)]
pub enum FormalRef {
    /// A fact-ledger entry, `artifacts/facts/F-<rest>.json`.
    Fact {
        /// Fact id, `F:`-prefixed.
        id: String,
    },
    /// A kernel declaration, resolved against an inventory snapshot -- never by
    /// searching source, which cannot see the interned-name-id declarations.
    Kernel {
        /// Declaration name as the inventory prints it.
        name: String,
        /// Path to the inventory snapshot JSON.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        inventory: Option<String>,
    },
}

impl FormalRef {
    /// Stable display key for diagnostics and output.
    pub fn key(&self) -> String {
        match self {
            Self::Fact { id } => id.clone(),
            Self::Kernel { name, .. } => name.clone(),
        }
    }
}

/// A pointer from a claim to a recorded run. The whole fail-closed mechanism:
/// a claim's rendered status is computed from the resolved record, so a
/// document cannot be edited into looking correct.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EvidenceRef {
    /// Path to the run-record JSON, relative to the manifest's directory.
    pub run_record: String,
    /// Expected record id; a mismatch is a build error.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub record_id: Option<String>,
    /// Which entry of the record's `claims` list this reference means.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub claim_key: Option<String>,
    /// What this reference contributes. Independence is the value, not count.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub role: Option<EvidenceRole>,
    /// Optional note.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub note: Option<String>,
}

/// What an evidence reference contributes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum EvidenceRole {
    /// The producing run.
    Primary,
    /// An independent re-derivation.
    Replication,
    /// A replay of a recorded witness.
    Replay,
    /// Agreement from a different implementation.
    CrossOracle,
}

impl EvidenceRole {
    /// Stable display name.
    pub fn label(self) -> &'static str {
        match self {
            Self::Primary => "primary",
            Self::Replication => "replication",
            Self::Replay => "replay",
            Self::CrossOracle => "cross-oracle",
        }
    }
}

/// The renderable badge vocabulary, consumed as data. The renderer never infers
/// or upgrades a status.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum EvidenceStatus {
    /// Kernel-admitted, or a complete written proof.
    Proved,
    /// Evidence independently replayed.
    Checked,
    /// A finite computation, carrying no universal credit.
    Evidence,
    /// A run that was not comparable; no baseline may be raised from it.
    Advisory,
    /// A witness against the statement.
    Refuted,
    /// Not established here.
    Open,
}

impl EvidenceStatus {
    /// Uppercase badge token. The same token in every format, because the
    /// cross-format property test compares badges across emitters.
    pub fn badge(self) -> &'static str {
        match self {
            Self::Proved => "PROVED",
            Self::Checked => "CHECKED",
            Self::Evidence => "EVIDENCE",
            Self::Advisory => "ADVISORY",
            Self::Refuted => "REFUTED",
            Self::Open => "OPEN",
        }
    }

    /// Strength ordering used ONLY to take minima when several caps apply.
    ///
    /// `refuted` is deliberately absent from this scale: it is a verdict, not a
    /// weaker grade of establishment, and [`min_strength`](Self::min_strength)
    /// treats it as absorbing so red evidence can never be averaged away.
    fn strength(self) -> u8 {
        match self {
            Self::Proved => 5,
            Self::Checked => 4,
            Self::Evidence => 3,
            Self::Advisory => 2,
            Self::Open => 1,
            Self::Refuted => 0,
        }
    }

    /// The weaker of two statuses, with `refuted` absorbing.
    #[must_use]
    pub fn min_strength(self, other: Self) -> Self {
        if self == Self::Refuted || other == Self::Refuted {
            return Self::Refuted;
        }
        if self.strength() <= other.strength() {
            self
        } else {
            other
        }
    }

    /// True for statuses that assert something was established.
    pub fn is_established(self) -> bool {
        matches!(
            self,
            Self::Proved | Self::Checked | Self::Evidence | Self::Advisory
        )
    }
}

/// How a piece of machine-produced content came to exist.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Provenance {
    /// What produced the content, named specifically enough to find.
    pub generator: String,
    /// The command line as run, verbatim; a reader must be able to paste it.
    pub command: String,
    /// Every file the run depended on, with its digest. Re-hashed every build.
    pub inputs: Vec<InputHash>,
    /// Process exit status. Nonzero demotes every claim resting on this run.
    pub exit_status: i32,
    /// The run's epoch.
    pub epoch: Epoch,
    /// Optional machine identifier; advisory, never affects a status.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub host: Option<String>,
    /// Optional measured duration; advisory, never in a golden output.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub duration_ms: Option<u64>,
}

/// One input file and its digest.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct InputHash {
    /// Path, relative to the repository root.
    pub path: String,
    /// Lowercase hex SHA-256.
    pub sha256: String,
    /// Optional label, e.g. `corpus`, `manifest`, `binary`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub role: Option<String>,
}

/// A command a reader can run.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Command {
    /// What gets printed.
    pub line: String,
    /// Working directory.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub cwd: Option<String>,
    /// Exit status a successful replay produces.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub expected_exit_status: Option<i32>,
    /// Measured typical seconds on a quiet machine.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub expected_seconds: Option<u64>,
}

/// A file a certificate points at.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ArtifactRef {
    /// Path to the artifact.
    pub path: String,
    /// Digest; verified by assembly when present.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub sha256: Option<String>,
    /// Human label.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub label: Option<String>,
    /// Size in bytes.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub bytes: Option<u64>,
    /// Media type.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub media_type: Option<String>,
}

/// A figure as data. Never carries a rendered image AND its data, because then
/// the two could disagree.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "figure_type", rename_all = "kebab-case", deny_unknown_fields)]
pub enum FigureSpec {
    /// Pre-rendered SVG, inline or by path.
    Svg {
        /// Complete `<svg>...</svg>`, ASCII, no external references.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        svg: Option<String>,
        /// Path to a checked-in SVG.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        src: Option<String>,
        /// Digest of `src`.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        sha256: Option<String>,
        /// Width hint.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        width: Option<u32>,
        /// Height hint.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        height: Option<u32>,
    },
    /// A plot from its underlying points.
    Plot {
        /// Mark type.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        plot_type: Option<PlotType>,
        /// X axis label.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        x_label: Option<String>,
        /// Y axis label.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        y_label: Option<String>,
        /// Explicit x range.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        x_range: Option<[f64; 2]>,
        /// Explicit y range.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        y_range: Option<[f64; 2]>,
        /// The data.
        series: Vec<Series>,
    },
    /// A dependency DAG.
    DepGraph {
        /// Nodes.
        nodes: Vec<GraphNode>,
        /// Edges.
        edges: Vec<GraphEdge>,
        /// Layout direction.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        rankdir: Option<String>,
    },
    /// An explicit polygon / point-set figure.
    Polygon {
        /// Hull vertices in order.
        vertices: Vec<[f64; 2]>,
        /// Additional marked points.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        points: Option<Vec<[f64; 2]>>,
        /// Whether the path closes.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        closed: Option<bool>,
        /// X axis label.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        x_label: Option<String>,
        /// Y axis label.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        y_label: Option<String>,
    },
}

/// Mark type for a plot.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum PlotType {
    /// Step function.
    Steps,
    /// Polyline.
    Line,
    /// Points only.
    Scatter,
    /// Bars.
    Bar,
}

/// One labelled data series.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Series {
    /// Series label.
    pub label: String,
    /// The points.
    pub points: Vec<[f64; 2]>,
    /// Optional style hint for the HTML emitter.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub style: Option<String>,
}

/// One node of a dependency graph.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GraphNode {
    /// Node id.
    pub id: String,
    /// Display label.
    pub label: String,
    /// Status badge; must come from resolved data, never from the author.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub status: Option<EvidenceStatus>,
    /// Link target.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub href: Option<String>,
    /// Grouping key.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub group: Option<String>,
}

/// One edge of a dependency graph.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GraphEdge {
    /// Source node id.
    pub from: String,
    /// Target node id.
    pub to: String,
    /// Optional edge label.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub label: Option<String>,
}

/// The evidence artifact: one recorded execution.
///
/// A claim references a record; assembly loads it, re-hashes its declared
/// inputs and computes the claim's rendered status from what it finds. Editing
/// the document cannot change any of that, and that asymmetry is the entire
/// fail-closed guarantee.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RunRecord {
    /// Format version; must equal [`SCHEMA_VERSION`].
    pub schema_version: u32,
    /// Stable identifier, `R:`-prefixed.
    pub id: String,
    /// What ran, over which bytes, and whether it succeeded.
    pub provenance: Provenance,
    /// One line a human can read: what this run did and what it found.
    pub summary: String,
    /// What the run FOUND, as distinct from whether it completed.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub outcome: Option<Outcome>,
    /// The claims this run establishes.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub claims: Vec<RunClaim>,
    /// Named scalar measurements.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub stats: BTreeMap<String, serde_json::Value>,
    /// Named tabular results, so a table block can be built from a record.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub tables: BTreeMap<String, RunTable>,
    /// Files the run wrote.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub artifacts: Vec<ArtifactRef>,
    /// How to re-run it.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub replay: Option<Command>,
    /// Free-form notes.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub notes: Option<String>,
}

/// What a run found, as distinct from whether it completed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Outcome {
    /// The run found what it was looking for.
    Established,
    /// The run found a counterexample.
    Refuted,
    /// The run did not settle the question.
    Inconclusive,
}

/// One claim a run establishes.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RunClaim {
    /// Reference key.
    pub key: String,
    /// The run's own status for this claim; caps any document claim using it.
    pub status: EvidenceStatus,
    /// What the run asserts, in one line.
    pub statement: String,
    /// Optional fact or kernel statement this supports.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub supports: Option<FormalRef>,
    /// Optional note.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub note: Option<String>,
}

/// A tabular result carried by a run record.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RunTable {
    /// Column headers, in order.
    pub columns: Vec<String>,
    /// Rows; each must have exactly `columns.len()` cells.
    pub rows: Vec<Vec<serde_json::Value>>,
}
