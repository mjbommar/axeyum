//! Assembly: the resolver, and the only place in this package that can fail.
//!
//! Assembly turns a [`Document`] full of references into a [`ResolvedDocument`]
//! full of data. Every judgment happens here -- loading a run record, re-hashing
//! declared inputs, fetching a fact from the ledger, deciding what status a
//! claim renders at -- so that emitters can be total and dumb (see
//! [`crate::Emitter`]). The trusted logic of this pipeline is this file.
//!
//! # The fail-closed law
//!
//! From `docs/render-2026-08/01-goals-and-requirements.md`, with the guard that
//! enforces each rule named, because `render/tests/negative.rs` deletes them one
//! at a time and requires that exactly one test dies:
//!
//! 1. A claim with no evidence is a build error --
//!    [`AssembleError::ClaimWithoutEvidence`], raised in [`resolve_claim`].
//! 2. Evidence that exited nonzero DEMOTES the claim --
//!    [`rendered_status`]; under [`AssembleOptions::strict`] it is
//!    [`AssembleError::RedEvidence`] instead. There is no path from red
//!    evidence to a green claim, because emitters cannot compute status at all.
//! 3. A dangling reference is a build error --
//!    [`AssembleError::DanglingFactRef`] / [`AssembleError::DanglingKernelRef`]
//!    in [`Assembler::resolve_formal_ref`].
//! 4. A declared input whose bytes no longer hash to the recorded digest is a
//!    build error -- [`AssembleError::HashMismatch`] in
//!    [`Assembler::verify_inputs`]. This is deliberately redundant with cargo's
//!    freshness logic, which is mtime-based and therefore blind to a source file
//!    older than its cached artifact; re-hashing every input every build is what
//!    makes a stale render impossible rather than unlikely.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::ir::{
    ArtifactRef, Block, BlockKind, CertKind, Column, Command, Document, EvidenceRef, EvidenceRole,
    EvidenceStatus, FigureSpec, FormalRef, Genre, Outcome, Provenance, RecordRole, RenderHint,
    RichText, RunRecord, SCHEMA_VERSION, StatementField, StatementSource, Step, TableFromRun,
    Verbosity,
};

/// Everything assembly needs to resolve a manifest.
#[derive(Debug, Clone)]
pub struct AssembleOptions {
    /// Repository root; `Provenance.inputs` paths and artifact paths resolve
    /// against it.
    pub repo_root: PathBuf,
    /// Directory the manifest lives in; `EvidenceRef.run_record` paths resolve
    /// against it.
    pub manifest_dir: PathBuf,
    /// The fact ledger.
    pub facts_dir: PathBuf,
    /// When true, red evidence is a build error instead of a demoted claim.
    pub strict: bool,
}

impl AssembleOptions {
    /// Defaults rooted at `repo_root`, with the manifest's own directory.
    pub fn new(repo_root: impl Into<PathBuf>, manifest_dir: impl Into<PathBuf>) -> Self {
        let repo_root = repo_root.into();
        let facts_dir = repo_root.join("artifacts/facts");
        Self {
            repo_root,
            manifest_dir: manifest_dir.into(),
            facts_dir,
            strict: false,
        }
    }
}

/// Every way assembly refuses to produce a document.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AssembleError {
    /// The document or a record declares a schema version this build cannot read.
    SchemaVersion {
        /// What the file said.
        found: u32,
        /// What this build supports.
        expected: u32,
        /// Which file.
        what: String,
    },
    /// Two blocks share an id, so anchors and golden diffs would be ambiguous.
    DuplicateBlockId(String),
    /// Rule 1: a claim carries no evidence.
    ClaimWithoutEvidence {
        /// Block id.
        block: String,
        /// Claim label.
        label: String,
    },
    /// Rule 3: a fact id resolves to no ledger entry.
    DanglingFactRef {
        /// The id that did not resolve.
        id: String,
        /// Where it was looked for.
        looked_in: String,
    },
    /// Rule 3: a kernel name resolves to no inventory entry.
    DanglingKernelRef {
        /// The name that did not resolve.
        name: String,
        /// The inventory consulted, or a note that none was given.
        inventory: String,
    },
    /// A run record could not be read.
    MissingRunRecord {
        /// The path referenced.
        path: String,
        /// The underlying reason.
        reason: String,
    },
    /// A claim cites a NEGATIVE-CONTROL record as ordinary support.
    ///
    /// The record is a recording of a deliberately broken run. Citing it under
    /// `primary` / `replication` / `replay` / `cross-oracle` asserts it
    /// supports the claim, which it never does -- so the build refuses instead
    /// of rendering a claim propped up by a mutant.
    NegativeControlCitedAsSupport {
        /// Path to the record.
        path: String,
        /// The record's id.
        record: String,
        /// The role the reference declared.
        declared_role: String,
    },
    /// A certificate says there is no recorded run AND cites one.
    ///
    /// `no_exit_reason` is the honest form of "nothing recorded an execution
    /// of this". A block that also names a run record makes two contradictory
    /// statements about the same box, and a reader cannot tell which one the
    /// page means. Refused rather than rendered, in the same spirit as the
    /// negative-control pairing rules above: a discriminator that one side can
    /// contradict is decoration.
    CertificateExitReasonWithEvidence {
        /// Block id.
        block: String,
        /// The stated reason.
        reason: String,
        /// How many records it cites.
        records: usize,
    },
    /// A reference declares the `negative-control` role over a record that is
    /// not one.
    ///
    /// The mirror of the rule above, and it exists for the same reason: the
    /// role must mean something. A page that labels a real production run as a
    /// negative control is telling the reader that a green run was expected to
    /// fail.
    NotANegativeControl {
        /// Path to the record.
        path: String,
        /// The record's id.
        record: String,
    },
    /// A run record's id is not the one the reference expected.
    RecordIdMismatch {
        /// Path to the record.
        path: String,
        /// What the reference expected.
        expected: String,
        /// What the record said.
        found: String,
    },
    /// A reference names a claim key the record does not carry.
    MissingClaimKey {
        /// Path to the record.
        path: String,
        /// The key.
        key: String,
        /// The keys the record does carry.
        available: Vec<String>,
    },
    /// A declared input file is gone.
    MissingInput {
        /// Path as declared.
        path: String,
        /// Who declared it.
        declared_by: String,
    },
    /// Rule 4: a declared input's bytes no longer match its digest.
    HashMismatch {
        /// Path as declared.
        path: String,
        /// The digest recorded when the run happened.
        declared: String,
        /// The digest of the bytes on disk now.
        actual: String,
        /// Who declared it.
        declared_by: String,
    },
    /// Rule 2 under strict mode: evidence that exited nonzero.
    RedEvidence {
        /// Block id.
        block: String,
        /// Claim label.
        label: String,
        /// The record.
        record: String,
        /// Its exit status.
        exit_status: i32,
    },
    /// A row does not have one cell per column.
    TableRowArity {
        /// Block id.
        block: String,
        /// Row index.
        row: usize,
        /// Cells found.
        found: usize,
        /// Columns declared.
        expected: usize,
    },
    /// A table cell is not a scalar.
    NonScalarCell {
        /// Block id.
        block: String,
        /// Row index.
        row: usize,
        /// Column index.
        col: usize,
    },
    /// An included or referenced artifact could not be read.
    MissingArtifact {
        /// Path as declared.
        path: String,
        /// The underlying reason.
        reason: String,
    },
    /// A figure declares neither inline SVG nor a source path.
    EmptyFigure(String),
    /// A table names a run-record table the record does not carry.
    MissingRecordTable {
        /// Path to the record.
        path: String,
        /// The table key.
        table: String,
        /// The keys the record does carry.
        available: Vec<String>,
    },
    /// A table supplies neither `from_run` nor literal columns/rows/source.
    TableWithoutData(String),
    /// The manifest itself could not be read or parsed.
    Manifest {
        /// Path.
        path: String,
        /// Reason.
        reason: String,
    },
}

impl fmt::Display for AssembleError {
    #[allow(clippy::too_many_lines)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::SchemaVersion {
                found,
                expected,
                what,
            } => write!(
                f,
                "{what}: schema_version {found} is not the {expected} this build reads"
            ),
            Self::DuplicateBlockId(id) => {
                write!(
                    f,
                    "duplicate block id `{id}`: anchors and golden diffs would be ambiguous"
                )
            }
            Self::ClaimWithoutEvidence { block, label } => write!(
                f,
                "block `{block}`: claim `{label}` carries no evidence. \
                 A claim with no evidence is prose asserting a result with nothing behind it, \
                 which is the transcription this pipeline exists to prevent \
                 (fail-closed law rule 1)"
            ),
            Self::DanglingFactRef { id, looked_in } => write!(
                f,
                "dangling fact reference `{id}`: no such entry in {looked_in} (fail-closed law rule 3)"
            ),
            Self::DanglingKernelRef { name, inventory } => write!(
                f,
                "dangling kernel reference `{name}`: not in {inventory} (fail-closed law rule 3). \
                 Kernel names are resolved against an inventory snapshot, never by searching source"
            ),
            Self::MissingRunRecord { path, reason } => {
                write!(f, "run record `{path}` could not be read: {reason}")
            }
            Self::NegativeControlCitedAsSupport {
                path,
                record,
                declared_role,
            } => write!(
                f,
                "run record `{path}` (`{record}`) declares `role: negative-control` -- it is a \
                 recording of a deliberately broken run -- but it is cited as `{declared_role}`, \
                 i.e. as support. A negative control never supports a claim. Cite it with \
                 `\"role\": \"negative-control\"` if the document is reporting the control, or \
                 point the claim at a production record"
            ),
            Self::CertificateExitReasonWithEvidence {
                block,
                reason,
                records,
            } => write!(
                f,
                "certificate block `{block}` states `no_exit_reason` (\"{reason}\") and yet cites                  {records} run record(s). Those are contradictory statements about the same box:                  either an execution was recorded or it was not. Drop the reason, or drop the                  evidence"
            ),
            Self::NotANegativeControl { path, record } => write!(
                f,
                "the reference to run record `{path}` (`{record}`) declares \
                 `role: negative-control`, but the record does not: it is a production run. \
                 Labelling a real run as a control tells the reader a green run was expected \
                 to fail"
            ),
            Self::RecordIdMismatch {
                path,
                expected,
                found,
            } => write!(
                f,
                "run record `{path}` is `{found}`, but the reference expects `{expected}`: \
                 the manifest is pointed at a rebuilt-but-different record"
            ),
            Self::MissingClaimKey {
                path,
                key,
                available,
            } => write!(
                f,
                "run record `{path}` has no claim `{key}` (it has: {})",
                if available.is_empty() {
                    "none".to_string()
                } else {
                    available.join(", ")
                }
            ),
            Self::MissingInput { path, declared_by } => {
                write!(f, "{declared_by}: declared input `{path}` does not exist")
            }
            Self::HashMismatch {
                path,
                declared,
                actual,
                declared_by,
            } => write!(
                f,
                "{declared_by}: input `{path}` hashed {actual} but the run recorded {declared}. \
                 The evidence describes bytes that are no longer there (fail-closed law rule 4)"
            ),
            Self::RedEvidence {
                block,
                label,
                record,
                exit_status,
            } => write!(
                f,
                "strict mode: block `{block}` claim `{label}` rests on run record `{record}` \
                 which exited {exit_status} (fail-closed law rule 2)"
            ),
            Self::TableRowArity {
                block,
                row,
                found,
                expected,
            } => write!(
                f,
                "block `{block}`: table row {row} has {found} cells but {expected} columns are declared"
            ),
            Self::NonScalarCell { block, row, col } => write!(
                f,
                "block `{block}`: table cell (row {row}, column {col}) is not a scalar; \
                 a richer cell is a place to hide prose in a table"
            ),
            Self::MissingArtifact { path, reason } => {
                write!(f, "artifact `{path}` could not be read: {reason}")
            }
            Self::MissingRecordTable {
                path,
                table,
                available,
            } => write!(
                f,
                "run record `{path}` has no table `{table}` (it has: {})",
                if available.is_empty() {
                    "none".to_string()
                } else {
                    available.join(", ")
                }
            ),
            Self::TableWithoutData(block) => write!(
                f,
                "block `{block}`: a table must either name a run-record table (`from_run`) or \
                 supply `columns`, `rows` and `source`. A table with no producing command is a \
                 transcription"
            ),
            Self::EmptyFigure(block) => {
                write!(
                    f,
                    "block `{block}`: svg figure declares neither `svg` nor `src`"
                )
            }
            Self::Manifest { path, reason } => write!(f, "manifest `{path}`: {reason}"),
        }
    }
}

impl std::error::Error for AssembleError {}

/// A document with every reference replaced by the data it referred to.
///
/// This is the emitters' entire input. It contains no path that still needs
/// following and no status that still needs computing.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct ResolvedDocument {
    /// Document title.
    pub title: String,
    /// Optional subtitle.
    pub subtitle: Option<String>,
    /// Stable slug.
    pub doc_id: String,
    /// Genre (selects emitter defaults; never a different truth).
    pub genre: Genre,
    /// Prose authors.
    pub authors: Vec<String>,
    /// Optional abstract.
    pub abstract_text: Option<RichText>,
    /// The epoch, as data.
    pub epoch_unix: i64,
    /// Where the epoch came from.
    pub epoch_source: String,
    /// The pinned commit, when there is one.
    pub commit: Option<String>,
    /// Base URL for archive links.
    pub repo_url: Option<String>,
    /// Per-format options.
    pub options: crate::ir::Options,
    /// Cross-document navigation, in reading order. Copied from the manifest;
    /// assembly resolves nothing here, because a link to a sibling document is
    /// not evidence and carries no status. `render/tests/link_integrity.rs` is
    /// what checks these resolve, over the emitted site.
    pub nav: Vec<crate::ir::NavLink>,
    /// The resolved body, in reading order.
    pub blocks: Vec<ResolvedBlock>,
    /// Every claim in the document as `(label, rendered status)`, in document
    /// order.
    ///
    /// This is the cross-format contract: the Markdown, LaTeX and HTML
    /// emissions of one document must yield the identical set, and
    /// `render/tests/cross_format.rs` recovers it from the emitted bytes rather
    /// than from this field, so an emitter cannot pass by omission.
    pub claims: Vec<(String, EvidenceStatus)>,
}

/// A block with its references resolved.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct ResolvedBlock {
    /// Block id.
    pub id: String,
    /// Anchor slug (defaults to `id`).
    pub anchor: String,
    /// Verbosity tier; emitters honour it mechanically.
    pub tag: Verbosity,
    /// Optional heading / fold summary.
    pub title: Option<String>,
    /// How the content was produced, when a machine produced it.
    pub provenance: Option<Provenance>,
    /// The resolved payload.
    pub kind: ResolvedKind,
}

/// The resolved payload of a block.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum ResolvedKind {
    /// Human narrative.
    Prose {
        /// The text.
        text: RichText,
        /// Verbatim LaTeX override.
        latex: Option<String>,
        /// Heading level, when it is a heading.
        heading_level: Option<u8>,
    },
    /// A claim, with its declared status, its computed status and its evidence.
    Claim {
        /// Short human-facing name.
        label: String,
        /// What is asserted, already resolved.
        statement: ResolvedStatementText,
        /// What the producer declared: a ceiling.
        declared_status: EvidenceStatus,
        /// What it renders at. Never higher than `declared_status`.
        status: EvidenceStatus,
        /// The resolved evidence.
        evidence: Vec<ResolvedEvidence>,
        /// Optional aside.
        note: Option<RichText>,
    },
    /// A statement of record, fetched.
    Statement {
        /// The fields to render, in order.
        show: Vec<StatementField>,
        /// The fetched statement.
        formal: ResolvedFormal,
        /// Optional aside.
        note: Option<RichText>,
    },
    /// A derivation.
    Steps {
        /// Optional caption.
        caption: Option<RichText>,
        /// The steps, each with its justification resolved.
        steps: Vec<ResolvedStep>,
    },
    /// A table whose source provenance verified.
    Table {
        /// Optional caption.
        caption: Option<RichText>,
        /// Columns, in order.
        columns: Vec<Column>,
        /// Rows, as pre-rendered scalar strings so every emitter prints the
        /// identical characters for a number.
        rows: Vec<Vec<String>>,
        /// Alignment per column, defaulted.
        source: Provenance,
    },
    /// A certificate.
    Certificate {
        /// What is certified.
        cert_kind: CertKind,
        /// Human summary.
        summary: RichText,
        /// Files a reader can check.
        artifact_refs: Vec<ArtifactRef>,
        /// How to re-run it.
        replay: Command,
        /// Resolved run records, possibly empty.
        evidence: Vec<ResolvedEvidence>,
        /// Why there is no recorded run, when there is none. See
        /// [`crate::ir::BlockKind::Certificate`].
        no_exit_reason: Option<String>,
    },
    /// A figure.
    Figure {
        /// Optional caption.
        caption: Option<RichText>,
        /// Text alternative.
        alt: Option<String>,
        /// The specification.
        spec: FigureSpec,
    },
    /// An external artifact.
    Include {
        /// Path as declared.
        path: String,
        /// How to render it.
        render_hint: RenderHint,
        /// Syntax language for `code`.
        language: Option<String>,
        /// Optional caption.
        caption: Option<RichText>,
        /// Contents, when the hint says inline and the budget allowed it.
        inline: Option<String>,
        /// Byte length on disk.
        bytes: u64,
    },
}

/// A claim's statement after resolution.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct ResolvedStatementText {
    /// Text for Markdown and HTML.
    pub text: String,
    /// Verbatim LaTeX override.
    pub latex: Option<String>,
    /// Verbatim HTML override.
    pub html: Option<String>,
    /// The reference it came from, when it came from one.
    pub from_ref: Option<String>,
}

/// One resolved evidence reference.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct ResolvedEvidence {
    /// The record's id.
    pub record_id: String,
    /// The path referenced, as written in the manifest.
    pub path: String,
    /// One line: what the run did and what it found.
    pub summary: String,
    /// What produced it.
    pub generator: String,
    /// The command line as run.
    pub command: String,
    /// Whether the run completed.
    pub exit_status: i32,
    /// What the run found.
    pub outcome: Outcome,
    /// The referenced claim key, when the reference named one.
    pub claim_key: Option<String>,
    /// The record's own status for that claim, which caps the document claim.
    pub claim_status: Option<EvidenceStatus>,
    /// What the record asserts for that claim.
    pub claim_statement: Option<String>,
    /// What this reference contributes.
    pub role: EvidenceRole,
    /// How to replay it.
    pub replay: Option<Command>,
    /// How many inputs were re-hashed and matched.
    pub inputs_verified: usize,
}

/// One resolved derivation step.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct ResolvedStep {
    /// One-based index.
    pub index: u32,
    /// What went in.
    pub input: Option<RichText>,
    /// The transformation.
    pub op: String,
    /// What came out.
    pub output: RichText,
    /// Optional aside.
    pub note: Option<RichText>,
    /// The resolved licensing statement, when the step named one.
    pub justification: Option<ResolvedFormal>,
}

/// A statement of record, fetched from the ledger or a kernel inventory.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct ResolvedFormal {
    /// `fact` or `kernel`.
    pub source: String,
    /// The reference key as written.
    pub key: String,
    /// Human title.
    pub title: String,
    /// The proposition in prose.
    pub prose: String,
    /// The language of `formal`.
    pub language: String,
    /// The proposition, machine-readably.
    pub formal: String,
    /// The theory that decides it.
    pub fragment: Option<String>,
    /// What THIS system established.
    pub epistemic_status: String,
    /// What mathematics knows, when recorded.
    pub external_status: Option<String>,
    /// Which machine established it.
    pub proof_route: Option<String>,
    /// What the establishing evidence rests on that was not itself proved.
    pub axiom_footprint: Option<Vec<String>>,
    /// The statements it rests on.
    pub depends_on: Vec<String>,
    /// How many evidence rows it carries.
    pub evidence_count: usize,
}

// ---------------------------------------------------------------------------
// Fact-ledger and kernel-inventory readers
// ---------------------------------------------------------------------------

/// The parts of a fact-ledger entry a document can render.
///
/// Deliberately a partial view with `deny_unknown_fields` OFF: the fact schema
/// is owned elsewhere and grows, and a renderer that refused to read a fact
/// because the ledger gained a field would be a renderer that breaks whenever
/// mathematics is added. What it MUST NOT do is invent a field, which is why
/// every field here is either required by the fact schema or an `Option`.
#[derive(Debug, Clone, Deserialize)]
struct FactEntry {
    id: String,
    title: String,
    statement: String,
    formal: FactFormal,
    epistemic_status: String,
    #[serde(default)]
    external_status: Option<String>,
    #[serde(default)]
    proof_route: Option<String>,
    #[serde(default)]
    axiom_footprint: Option<Vec<String>>,
    #[serde(default)]
    depends_on: Vec<String>,
    #[serde(default)]
    evidence: Vec<serde_json::Value>,
}

#[derive(Debug, Clone, Deserialize)]
struct FactFormal {
    language: String,
    statement: String,
    #[serde(default)]
    fragment: Option<String>,
}

/// One declaration of a kernel inventory snapshot.
#[derive(Debug, Clone, Deserialize)]
struct KernelDecl {
    name: String,
    #[serde(default)]
    #[allow(dead_code)]
    kind: Option<String>,
    #[serde(rename = "type")]
    ty: String,
    #[serde(default)]
    axiom_footprint: Option<Vec<String>>,
}

#[derive(Debug, Clone, Deserialize)]
struct KernelInventory {
    declarations: Vec<KernelDecl>,
}

// ---------------------------------------------------------------------------
// The assembler
// ---------------------------------------------------------------------------

/// The resolver. One instance per build; caches nothing across builds, because
/// a cache is a way to render bytes that are no longer on disk.
pub struct Assembler {
    opts: AssembleOptions,
    inventories: BTreeMap<String, KernelInventory>,
}

impl Assembler {
    /// A resolver with the given options.
    pub fn new(opts: AssembleOptions) -> Self {
        Self {
            opts,
            inventories: BTreeMap::new(),
        }
    }

    /// Read and parse a manifest, then resolve it.
    ///
    /// # Errors
    /// Any [`AssembleError`]; a manifest that cannot be read or parsed is
    /// [`AssembleError::Manifest`].
    pub fn assemble_path(&mut self, manifest: &Path) -> Result<ResolvedDocument, AssembleError> {
        let bytes = std::fs::read(manifest).map_err(|e| AssembleError::Manifest {
            path: manifest.display().to_string(),
            reason: e.to_string(),
        })?;
        let doc: Document =
            serde_json::from_slice(&bytes).map_err(|e| AssembleError::Manifest {
                path: manifest.display().to_string(),
                reason: e.to_string(),
            })?;
        self.assemble(&doc)
    }

    /// Resolve a parsed document.
    ///
    /// # Errors
    /// Any [`AssembleError`]. This is the fail-closed gate: everything that can
    /// refuse to render refuses here.
    pub fn assemble(&mut self, doc: &Document) -> Result<ResolvedDocument, AssembleError> {
        if doc.schema_version != SCHEMA_VERSION {
            return Err(AssembleError::SchemaVersion {
                found: doc.schema_version,
                expected: SCHEMA_VERSION,
                what: "document".to_string(),
            });
        }
        if let Some(p) = &doc.provenance {
            self.verify_inputs(p, "document provenance")?;
        }

        let mut seen: BTreeSet<&str> = BTreeSet::new();
        let mut blocks = Vec::with_capacity(doc.blocks.len());
        let mut claims = Vec::new();

        for block in &doc.blocks {
            if !seen.insert(block.id.as_str()) {
                return Err(AssembleError::DuplicateBlockId(block.id.clone()));
            }
            if let Some(p) = &block.provenance {
                self.verify_inputs(p, &format!("block `{}` provenance", block.id))?;
            }
            let kind = self.resolve_kind(block)?;
            if let ResolvedKind::Claim { label, status, .. } = &kind {
                claims.push((label.clone(), *status));
            }
            blocks.push(ResolvedBlock {
                anchor: block.anchor.clone().unwrap_or_else(|| block.id.clone()),
                id: block.id.clone(),
                tag: block.tag,
                title: block.title.clone(),
                provenance: block.provenance.clone(),
                kind,
            });
        }

        Ok(ResolvedDocument {
            title: doc.meta.title.clone(),
            subtitle: doc.meta.subtitle.clone(),
            doc_id: doc.meta.doc_id.clone(),
            genre: doc.meta.genre,
            authors: doc.meta.authors.clone(),
            abstract_text: doc.meta.abstract_text.clone(),
            epoch_unix: doc.meta.epoch.unix,
            epoch_source: match doc.meta.epoch.source {
                crate::ir::EpochSource::Commit => "commit".to_string(),
                crate::ir::EpochSource::SourceDateEpoch => "source-date-epoch".to_string(),
                crate::ir::EpochSource::Fixed => "fixed".to_string(),
            },
            commit: doc
                .meta
                .epoch
                .commit
                .clone()
                .or_else(|| doc.meta.repo.as_ref().and_then(|r| r.commit.clone())),
            repo_url: doc.meta.repo.as_ref().and_then(|r| r.url.clone()),
            options: doc.meta.options.clone(),
            nav: doc.meta.nav.clone(),
            blocks,
            claims,
        })
    }

    // One arm per block kind. Splitting it hides the totality that the emitter
    // contract depends on: this match is the list of kinds that exist.
    #[allow(clippy::too_many_lines)]
    fn resolve_kind(&mut self, block: &Block) -> Result<ResolvedKind, AssembleError> {
        match &block.kind {
            BlockKind::Prose {
                text,
                latex,
                heading_level,
            } => Ok(ResolvedKind::Prose {
                text: text.to_rich(),
                latex: latex.clone(),
                heading_level: *heading_level,
            }),
            BlockKind::Claim {
                label,
                statement,
                status,
                evidence,
                note,
            } => self.resolve_claim(block, label, statement, *status, evidence, note.as_ref()),
            BlockKind::Statement {
                reference,
                show,
                note,
            } => {
                let formal = self.resolve_formal_ref(reference)?;
                Ok(ResolvedKind::Statement {
                    show: show.clone().unwrap_or_else(default_statement_fields),
                    formal,
                    note: note.clone(),
                })
            }
            BlockKind::Steps { caption, steps } => {
                let mut out = Vec::with_capacity(steps.len());
                for (i, step) in steps.iter().enumerate() {
                    out.push(self.resolve_step(i, step)?);
                }
                Ok(ResolvedKind::Steps {
                    caption: caption.clone(),
                    steps: out,
                })
            }
            BlockKind::Table {
                caption,
                from_run,
                columns,
                rows,
                source,
            } => self.resolve_table(
                block,
                caption.as_ref(),
                from_run.as_ref(),
                columns.as_deref(),
                rows.as_deref(),
                source.as_ref(),
            ),
            BlockKind::Certificate {
                cert_kind,
                summary,
                artifact_refs,
                replay,
                evidence,
                no_exit_reason,
            } => {
                // A box cannot both say "nothing recorded a run" and name the
                // run it recorded.
                if let Some(reason) = no_exit_reason
                    && !evidence.is_empty()
                {
                    return Err(AssembleError::CertificateExitReasonWithEvidence {
                        block: block.id.clone(),
                        reason: reason.clone(),
                        records: evidence.len(),
                    });
                }
                for a in artifact_refs {
                    self.verify_artifact(a, &format!("block `{}` artifact", block.id))?;
                }
                let mut resolved = Vec::with_capacity(evidence.len());
                for e in evidence {
                    resolved.push(self.resolve_evidence(e)?);
                }
                Ok(ResolvedKind::Certificate {
                    cert_kind: *cert_kind,
                    summary: summary.clone(),
                    artifact_refs: artifact_refs.clone(),
                    replay: replay.clone(),
                    evidence: resolved,
                    no_exit_reason: no_exit_reason.clone(),
                })
            }
            BlockKind::Figure { caption, alt, spec } => {
                if let FigureSpec::Svg {
                    svg, src, sha256, ..
                } = spec
                {
                    if svg.is_none() && src.is_none() {
                        return Err(AssembleError::EmptyFigure(block.id.clone()));
                    }
                    if let Some(src) = src {
                        let a = ArtifactRef {
                            path: src.clone(),
                            sha256: sha256.clone(),
                            label: None,
                            bytes: None,
                            media_type: None,
                        };
                        self.verify_artifact(&a, &format!("block `{}` figure", block.id))?;
                    }
                }
                Ok(ResolvedKind::Figure {
                    caption: caption.clone(),
                    alt: alt.clone(),
                    spec: spec.clone(),
                })
            }
            BlockKind::Include {
                path,
                render_hint,
                language,
                caption,
                sha256,
                max_bytes,
            } => {
                let abs = self.opts.repo_root.join(path);
                let bytes = std::fs::read(&abs).map_err(|e| AssembleError::MissingArtifact {
                    path: path.clone(),
                    reason: e.to_string(),
                })?;
                if let Some(want) = sha256 {
                    let got = hex_digest(&bytes);
                    if &got != want {
                        return Err(AssembleError::HashMismatch {
                            path: path.clone(),
                            declared: want.clone(),
                            actual: got,
                            declared_by: format!("block `{}` include", block.id),
                        });
                    }
                }
                let budget = max_bytes.unwrap_or(u64::MAX);
                let inline = if matches!(render_hint, RenderHint::Link | RenderHint::Image)
                    || bytes.len() as u64 > budget
                {
                    None
                } else {
                    Some(String::from_utf8_lossy(&bytes).into_owned())
                };
                Ok(ResolvedKind::Include {
                    path: path.clone(),
                    render_hint: *render_hint,
                    language: language.clone(),
                    caption: caption.clone(),
                    inline,
                    bytes: bytes.len() as u64,
                })
            }
        }
    }

    fn resolve_claim(
        &mut self,
        block: &Block,
        label: &str,
        statement: &StatementSource,
        declared: EvidenceStatus,
        evidence: &[EvidenceRef],
        note: Option<&RichText>,
    ) -> Result<ResolvedKind, AssembleError> {
        // GUARD (fail-closed law rule 1). Deleting these three lines must kill
        // exactly `claim_without_evidence_is_a_build_error` and nothing else.
        if evidence.is_empty() {
            return Err(AssembleError::ClaimWithoutEvidence {
                block: block.id.clone(),
                label: label.to_string(),
            });
        }

        let mut resolved = Vec::with_capacity(evidence.len());
        for e in evidence {
            resolved.push(self.resolve_evidence(e)?);
        }

        let status = rendered_status(declared, &resolved);

        // GUARD (fail-closed law rule 2, strict half). Deleting this block must
        // kill exactly `nonzero_exit_status_is_an_error_in_strict_mode`.
        if self.opts.strict
            && let Some(red) = resolved.iter().find(|e| e.exit_status != 0)
        {
            return Err(AssembleError::RedEvidence {
                block: block.id.clone(),
                label: label.to_string(),
                record: red.record_id.clone(),
                exit_status: red.exit_status,
            });
        }

        let statement = match statement {
            StatementSource::Text { text, latex, html } => ResolvedStatementText {
                text: text.clone(),
                latex: latex.clone(),
                html: html.clone(),
                from_ref: None,
            },
            StatementSource::Ref { reference } => {
                let formal = self.resolve_formal_ref(reference)?;
                ResolvedStatementText {
                    text: formal.prose.clone(),
                    latex: None,
                    html: None,
                    from_ref: Some(formal.key.clone()),
                }
            }
        };

        Ok(ResolvedKind::Claim {
            label: label.to_string(),
            statement,
            declared_status: declared,
            status,
            evidence: resolved,
            note: note.cloned(),
        })
    }

    fn resolve_step(&mut self, i: usize, step: &Step) -> Result<ResolvedStep, AssembleError> {
        let justification = match &step.justification {
            Some(r) => Some(self.resolve_formal_ref(r)?),
            None => None,
        };
        Ok(ResolvedStep {
            index: step
                .index
                .unwrap_or_else(|| u32::try_from(i + 1).unwrap_or(u32::MAX)),
            input: step.input.clone(),
            op: step.op.clone(),
            output: step.output.clone(),
            note: step.note.clone(),
            justification,
        })
    }

    fn resolve_table(
        &mut self,
        block: &Block,
        caption: Option<&RichText>,
        from_run: Option<&TableFromRun>,
        columns: Option<&[Column]>,
        rows: Option<&[Vec<serde_json::Value>]>,
        source: Option<&Provenance>,
    ) -> Result<ResolvedKind, AssembleError> {
        // The preferred form: the numbers live in the record and are copied
        // here, so nothing has to be kept in step by hand.
        let (columns, rows, source) = match from_run {
            Some(fr) => {
                let record = self.load_record(&fr.run_record, fr.record_id.as_deref())?;
                self.verify_inputs(
                    &record.provenance,
                    &format!("run record `{}` (table source)", record.id),
                )?;
                let table = record.tables.get(&fr.table).ok_or_else(|| {
                    AssembleError::MissingRecordTable {
                        path: fr.run_record.clone(),
                        table: fr.table.clone(),
                        available: record.tables.keys().cloned().collect(),
                    }
                })?;
                let cols: Vec<Column> = table
                    .columns
                    .iter()
                    .map(|h| Column {
                        key: h.clone(),
                        header: h.clone(),
                        align: None,
                        note: None,
                    })
                    .collect();
                (cols, table.rows.clone(), record.provenance.clone())
            }
            None => match (columns, rows, source) {
                (Some(c), Some(r), Some(p)) => (c.to_vec(), r.to_vec(), p.clone()),
                _ => return Err(AssembleError::TableWithoutData(block.id.clone())),
            },
        };

        self.verify_inputs(&source, &format!("block `{}` table source", block.id))?;
        let mut out = Vec::with_capacity(rows.len());
        for (r, row) in rows.iter().enumerate() {
            if row.len() != columns.len() {
                return Err(AssembleError::TableRowArity {
                    block: block.id.clone(),
                    row: r,
                    found: row.len(),
                    expected: columns.len(),
                });
            }
            let mut cells = Vec::with_capacity(row.len());
            for (c, cell) in row.iter().enumerate() {
                cells.push(scalar_to_string(cell).ok_or(AssembleError::NonScalarCell {
                    block: block.id.clone(),
                    row: r,
                    col: c,
                })?);
            }
            out.push(cells);
        }
        Ok(ResolvedKind::Table {
            caption: caption.cloned(),
            columns,
            rows: out,
            source,
        })
    }

    /// Read a run record, checking its schema version and (when given) its id.
    fn load_record(&self, rel: &str, expect_id: Option<&str>) -> Result<RunRecord, AssembleError> {
        let path = self.opts.manifest_dir.join(rel);
        let bytes = std::fs::read(&path).map_err(|e| AssembleError::MissingRunRecord {
            path: rel.to_string(),
            reason: e.to_string(),
        })?;
        let record: RunRecord =
            serde_json::from_slice(&bytes).map_err(|e| AssembleError::MissingRunRecord {
                path: rel.to_string(),
                reason: e.to_string(),
            })?;
        if record.schema_version != SCHEMA_VERSION {
            return Err(AssembleError::SchemaVersion {
                found: record.schema_version,
                expected: SCHEMA_VERSION,
                what: format!("run record `{rel}`"),
            });
        }
        if let Some(want) = expect_id
            && want != record.id
        {
            return Err(AssembleError::RecordIdMismatch {
                path: rel.to_string(),
                expected: want.to_string(),
                found: record.id.clone(),
            });
        }
        Ok(record)
    }

    fn resolve_evidence(&mut self, ev: &EvidenceRef) -> Result<ResolvedEvidence, AssembleError> {
        let record = self.load_record(&ev.run_record, ev.record_id.as_deref())?;
        // A negative control is evidence about the CHECKER, never about the
        // mathematics, and the pairing is enforced in both directions so that
        // the role means something in each.
        let declared = ev.role.unwrap_or(EvidenceRole::Primary);
        let is_control = record.role.unwrap_or_default() == RecordRole::NegativeControl;
        if is_control && declared != EvidenceRole::NegativeControl {
            return Err(AssembleError::NegativeControlCitedAsSupport {
                path: ev.run_record.clone(),
                record: record.id.clone(),
                declared_role: declared.label().to_string(),
            });
        }
        if !is_control && declared == EvidenceRole::NegativeControl {
            return Err(AssembleError::NotANegativeControl {
                path: ev.run_record.clone(),
                record: record.id.clone(),
            });
        }
        let inputs_verified =
            self.verify_inputs(&record.provenance, &format!("run record `{}`", record.id))?;
        for a in &record.artifacts {
            self.verify_artifact(a, &format!("run record `{}` artifact", record.id))?;
        }

        let (claim_status, claim_statement) = match &ev.claim_key {
            None => (None, None),
            Some(key) => {
                let found = record.claims.iter().find(|c| &c.key == key);
                match found {
                    Some(c) => (Some(c.status), Some(c.statement.clone())),
                    None => {
                        return Err(AssembleError::MissingClaimKey {
                            path: ev.run_record.clone(),
                            key: key.clone(),
                            available: record.claims.iter().map(|c| c.key.clone()).collect(),
                        });
                    }
                }
            }
        };

        Ok(ResolvedEvidence {
            record_id: record.id.clone(),
            path: ev.run_record.clone(),
            summary: record.summary.clone(),
            generator: record.provenance.generator.clone(),
            command: record.provenance.command.clone(),
            exit_status: record.provenance.exit_status,
            outcome: record.outcome.unwrap_or(Outcome::Established),
            claim_key: ev.claim_key.clone(),
            claim_status,
            claim_statement,
            role: declared,
            replay: record.replay.clone(),
            inputs_verified,
        })
    }

    fn resolve_formal_ref(&mut self, r: &FormalRef) -> Result<ResolvedFormal, AssembleError> {
        match r {
            FormalRef::Fact { id } => {
                let file = fact_filename(id);
                let path = self.opts.facts_dir.join(&file);
                // GUARD (fail-closed law rule 3, fact half). Replacing this
                // `?` with a synthesised placeholder must kill exactly
                // `dangling_fact_ref_is_a_build_error`.
                let bytes = std::fs::read(&path).map_err(|_| AssembleError::DanglingFactRef {
                    id: id.clone(),
                    looked_in: self.opts.facts_dir.display().to_string(),
                })?;
                let fact: FactEntry =
                    serde_json::from_slice(&bytes).map_err(|_| AssembleError::DanglingFactRef {
                        id: id.clone(),
                        looked_in: self.opts.facts_dir.display().to_string(),
                    })?;
                if fact.id != *id {
                    return Err(AssembleError::DanglingFactRef {
                        id: id.clone(),
                        looked_in: self.opts.facts_dir.display().to_string(),
                    });
                }
                Ok(ResolvedFormal {
                    source: "fact".to_string(),
                    key: fact.id,
                    title: fact.title,
                    prose: fact.statement,
                    language: fact.formal.language,
                    formal: fact.formal.statement,
                    fragment: fact.formal.fragment,
                    epistemic_status: fact.epistemic_status,
                    external_status: fact.external_status,
                    proof_route: fact.proof_route,
                    axiom_footprint: fact.axiom_footprint,
                    depends_on: fact.depends_on,
                    evidence_count: fact.evidence.len(),
                })
            }
            FormalRef::Kernel { name, inventory } => {
                let inv_path = inventory.clone().unwrap_or_default();
                if inv_path.is_empty() {
                    return Err(AssembleError::DanglingKernelRef {
                        name: name.clone(),
                        inventory: "no inventory snapshot given; a kernel reference with \
                                    nothing to check against is not a checked reference"
                            .to_string(),
                    });
                }
                let inv = self.load_inventory(&inv_path)?;
                let decl = inv
                    .declarations
                    .iter()
                    .find(|d| &d.name == name)
                    .ok_or_else(|| AssembleError::DanglingKernelRef {
                        name: name.clone(),
                        inventory: inv_path.clone(),
                    })?;
                Ok(ResolvedFormal {
                    source: "kernel".to_string(),
                    key: decl.name.clone(),
                    title: decl.name.clone(),
                    prose: decl.ty.clone(),
                    language: "lean4".to_string(),
                    formal: decl.ty.clone(),
                    fragment: None,
                    epistemic_status: "proved".to_string(),
                    external_status: None,
                    proof_route: Some("kernel-lean".to_string()),
                    axiom_footprint: decl.axiom_footprint.clone(),
                    depends_on: Vec::new(),
                    evidence_count: 0,
                })
            }
        }
    }

    fn load_inventory(&mut self, rel: &str) -> Result<&KernelInventory, AssembleError> {
        if !self.inventories.contains_key(rel) {
            let path = self.opts.repo_root.join(rel);
            let bytes = std::fs::read(&path).map_err(|e| AssembleError::MissingArtifact {
                path: rel.to_string(),
                reason: e.to_string(),
            })?;
            let inv: KernelInventory =
                serde_json::from_slice(&bytes).map_err(|e| AssembleError::MissingArtifact {
                    path: rel.to_string(),
                    reason: e.to_string(),
                })?;
            self.inventories.insert(rel.to_string(), inv);
        }
        Ok(&self.inventories[rel])
    }

    /// Re-hash every declared input and compare. Returns how many were checked.
    fn verify_inputs(&self, p: &Provenance, who: &str) -> Result<usize, AssembleError> {
        for input in &p.inputs {
            let path = self.opts.repo_root.join(&input.path);
            let bytes = std::fs::read(&path).map_err(|_| AssembleError::MissingInput {
                path: input.path.clone(),
                declared_by: who.to_string(),
            })?;
            let actual = hex_digest(&bytes);
            // GUARD (fail-closed law rule 4). Deleting this comparison must
            // kill exactly `input_hash_mismatch_is_a_build_error`.
            if actual != input.sha256 {
                return Err(AssembleError::HashMismatch {
                    path: input.path.clone(),
                    declared: input.sha256.clone(),
                    actual,
                    declared_by: who.to_string(),
                });
            }
        }
        Ok(p.inputs.len())
    }

    fn verify_artifact(&self, a: &ArtifactRef, who: &str) -> Result<(), AssembleError> {
        let Some(want) = &a.sha256 else { return Ok(()) };
        let path = self.opts.repo_root.join(&a.path);
        let bytes = std::fs::read(&path).map_err(|e| AssembleError::MissingArtifact {
            path: a.path.clone(),
            reason: e.to_string(),
        })?;
        let actual = hex_digest(&bytes);
        if &actual != want {
            return Err(AssembleError::HashMismatch {
                path: a.path.clone(),
                declared: want.clone(),
                actual,
                declared_by: who.to_string(),
            });
        }
        Ok(())
    }
}

/// The rendered status of a claim, given what the producer declared and what
/// the evidence turned out to be.
///
/// The ONE rule: this function can only lower. `declared` is a ceiling, each
/// piece of evidence is another ceiling, and red evidence is absorbing. There is
/// deliberately no branch that raises a status, which is what makes "no styling
/// path from red evidence to a green claim" a property of the code rather than a
/// convention.
///
/// A nonzero exit status means the run did not complete successfully, so it
/// establishes nothing; whether that renders as `refuted` or `open` is read from
/// the record's own `outcome`, never guessed. A run that completed and reports
/// `outcome: refuted` also demotes, because a completed run that found a
/// counterexample has not established the claim either.
pub fn rendered_status(declared: EvidenceStatus, evidence: &[ResolvedEvidence]) -> EvidenceStatus {
    let mut status = declared;
    for e in evidence {
        // GUARD (fail-closed law rule 2, demotion half). Deleting this `if`
        // must kill exactly `nonzero_exit_status_demotes_the_claim`.
        if e.exit_status != 0 {
            let demoted = match e.outcome {
                Outcome::Refuted => EvidenceStatus::Refuted,
                Outcome::Established | Outcome::Inconclusive => EvidenceStatus::Open,
            };
            status = status.min_strength(demoted);
        } else if e.outcome == Outcome::Refuted {
            status = status.min_strength(EvidenceStatus::Refuted);
        } else if e.outcome == Outcome::Inconclusive {
            status = status.min_strength(EvidenceStatus::Open);
        }
        if let Some(cap) = e.claim_status {
            status = status.min_strength(cap);
        }
    }
    status
}

fn default_statement_fields() -> Vec<StatementField> {
    vec![
        StatementField::Title,
        StatementField::Prose,
        StatementField::Formal,
        StatementField::Status,
    ]
}

/// The ledger filename for a fact id: `F:bool-and-comm` -> `F-bool-and-comm.json`.
fn fact_filename(id: &str) -> String {
    format!("{}.json", id.replacen(':', "-", 1))
}

/// Render a JSON scalar exactly once, so every emitter prints the identical
/// characters for a number and a cross-format diff cannot be a float format.
fn scalar_to_string(v: &serde_json::Value) -> Option<String> {
    match v {
        serde_json::Value::Null => Some(String::new()),
        serde_json::Value::Bool(b) => Some(b.to_string()),
        serde_json::Value::Number(n) => Some(n.to_string()),
        serde_json::Value::String(s) => Some(s.clone()),
        _ => None,
    }
}

/// Lowercase hex SHA-256, the digest `sha256sum` prints.
pub fn hex_digest(bytes: &[u8]) -> String {
    let mut h = Sha256::new();
    h.update(bytes);
    let out = h.finalize();
    let mut s = String::with_capacity(64);
    for b in out {
        use fmt::Write as _;
        let _ = write!(s, "{b:02x}");
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ev(exit: i32, outcome: Outcome, cap: Option<EvidenceStatus>) -> ResolvedEvidence {
        ResolvedEvidence {
            record_id: "R:t".into(),
            path: "t.json".into(),
            summary: "t".into(),
            generator: "t".into(),
            command: "t".into(),
            exit_status: exit,
            outcome,
            claim_key: None,
            claim_status: cap,
            claim_statement: None,
            role: EvidenceRole::Primary,
            replay: None,
            inputs_verified: 0,
        }
    }

    #[test]
    fn green_evidence_never_raises_a_status() {
        let s = rendered_status(
            EvidenceStatus::Evidence,
            &[ev(0, Outcome::Established, Some(EvidenceStatus::Proved))],
        );
        assert_eq!(
            s,
            EvidenceStatus::Evidence,
            "a record must not upgrade a declared claim"
        );
    }

    #[test]
    fn red_evidence_is_absorbing_across_several_records() {
        let s = rendered_status(
            EvidenceStatus::Proved,
            &[
                ev(0, Outcome::Established, None),
                ev(1, Outcome::Refuted, None),
            ],
        );
        assert_eq!(s, EvidenceStatus::Refuted);
    }

    #[test]
    fn nonzero_exit_without_a_counterexample_renders_open_not_refuted() {
        let s = rendered_status(EvidenceStatus::Proved, &[ev(2, Outcome::Established, None)]);
        assert_eq!(s, EvidenceStatus::Open);
    }

    #[test]
    fn fact_filename_only_replaces_the_prefix_colon() {
        assert_eq!(fact_filename("F:bool-and-comm"), "F-bool-and-comm.json");
    }

    #[test]
    fn hex_digest_matches_sha256sum_of_the_empty_input() {
        assert_eq!(
            hex_digest(b""),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
    }
}
