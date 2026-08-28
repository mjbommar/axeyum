//! The ledger-shaped record a completed statement-only import yields.
//!
//! ADR-0604 §2 makes [`crate::import_statement_ndjson`] the front door for
//! posing a Lean-authored statement as an axeyum goal, and requires that
//! `formal.statement` in an `artifacts/facts/` entry be "the kernel's own
//! rendering of the imported type" — never a hand-transcribed surface string.
//! This module is the bridge: it turns a [`crate::CompletedStatementImport`]
//! into the exact fields a fact needs, computed FROM the checked kernel
//! (`Kernel::render_lean`, [`crate::identity::DeclarationIdentity`]), never
//! retyped or paraphrased.
//!
//! This module does not know the `artifacts/facts/` JSON Schema and does not
//! write facts — it produces a typed record. Wrapping it into the schema's
//! exact `formal`/`provenance` shape is a caller concern (see
//! `examples/statement_goal_record.rs`), deliberately kept out of this crate
//! so a schema change elsewhere never requires touching admission logic.
//!
//! **Nothing here admits anything new to a kernel.** It only reads back what
//! [`crate::import_statement_ndjson`] (or
//! [`crate::import_candidate_statement_ndjson`]) already admitted and
//! refused — the "admits nothing beyond the goal's own definition
//! dependencies" property is entirely that function's, not this one's.

use std::fmt;

use sha2::{Digest, Sha256};

use crate::{CompletedStatementImport, DeclarationIdentity};

/// Why a completed statement import could not be turned into a goal record.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StatementGoalRecordError {
    /// No declaration identity in the completed import's report matches
    /// `target` exactly. This should be unreachable for a `target` that was
    /// actually used to build the `CompletedStatementImport` (the import
    /// itself resolves the same name), so its presence here would indicate a
    /// caller passing a *different* string than the one that produced
    /// `completed` — never a case this module can silently paper over.
    TargetIdentityMissing {
        /// The name the caller asked for.
        target: String,
    },
    /// The completed import's report carries a nonempty axiom inventory.
    /// [`crate::import_statement_ndjson`]'s own gate refuses every `Axiom`
    /// kind unconditionally (never exempted, unlike `Theorem`), so this
    /// should be unreachable for any import that actually went through that
    /// gate — it exists so this module fails LOUDLY rather than silently
    /// emitting a goal record for an environment it did not itself verify is
    /// axiom-free, if it is ever called on a `CompletedStatementImport` built
    /// some other way in the future.
    UnexpectedAxioms {
        /// The axiom names present.
        observed: Vec<String>,
    },
}

impl fmt::Display for StatementGoalRecordError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TargetIdentityMissing { target } => {
                write!(f, "no declaration identity matches target {target:?}")
            }
            Self::UnexpectedAxioms { observed } => write!(
                f,
                "completed statement import carries {} axiom(s): {observed:?}",
                observed.len()
            ),
        }
    }
}

impl std::error::Error for StatementGoalRecordError {}

/// The ledger-shaped record produced from one completed, proof-isolated
/// statement import.
///
/// Every field here is derived from the checked kernel or the import's own
/// ADR-0350 identity manifest — never from the untrusted wire `type`/`value`
/// text, and never retyped by hand. `lean_version`/`lean_githash` are the
/// exporter's own wire-reported metadata (see [`crate::ImportReport`]'s
/// field docs) and are recorded as claimed, not independently verified by
/// this crate; a caller binding a fact's provenance to a *specific* pinned
/// Mathlib/lean4export checkout must still record and verify that pin itself
/// (see `docs/autogenesis/294-…`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StatementGoalRecord {
    /// The exact rendered source declaration name the goal was imported for.
    pub target_name: String,
    /// The kernel's own Lean rendering of the imported goal
    /// (`Kernel::render_lean`), suitable for `formal.statement` under
    /// `formal.language: "lean4"`.
    pub goal_lean4: String,
    /// SHA-256 of `goal_lean4`'s UTF-8 bytes, lowercase hex. A stable content
    /// binding independent of any future change to `render_lean`'s exact
    /// output for other expressions.
    pub goal_sha256: String,
    /// The target declaration's own ADR-0350 structural content identity
    /// (`DeclarationIdentity::content_sha256`) — independent of `goal_sha256`
    /// because it hashes the checked kernel term structure, not its rendered
    /// text.
    pub target_content_sha256: String,
    /// Number of direct dependency bindings the target declaration carries,
    /// per its `DeclarationIdentity`.
    pub target_dependency_count: usize,
    /// Total declarations admitted into the goal's kernel (the target plus
    /// every definition dependency needed to state it) — never the target
    /// alone, since a bare count of 1 would misreport what was actually
    /// checked.
    pub admitted_declaration_count: usize,
    /// Exact names of any trusted declaration this import exempted via
    /// independent, kernel-reconstructed substitution
    /// (`crate::trusted_substitution`) rather than trusting the wire. Empty
    /// for the overwhelmingly common case; nonempty here is precisely the
    /// fact this module exists to NOT hide — a fact built from a record with
    /// a nonempty list here rests on this crate's own reconstruction of that
    /// name, not on an assumption.
    pub substituted_theorems: Vec<String>,
    /// Exporter-reported Lean version (wire-claimed, not independently
    /// verified — see this struct's own doc comment).
    pub lean_version: String,
    /// Exporter-reported Lean source hash (wire-claimed).
    pub lean_githash: String,
    /// Exporter-reported NDJSON format version (wire-claimed).
    pub format_version: String,
}

fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut out = String::with_capacity(digest.len() * 2);
    for byte in digest {
        use core::fmt::Write as _;
        let _ = write!(out, "{byte:02x}");
    }
    out
}

fn find_target_identity<'a>(
    identities: &'a [DeclarationIdentity],
    target: &str,
) -> Option<&'a DeclarationIdentity> {
    identities.iter().find(|identity| identity.name == target)
}

/// Build a [`StatementGoalRecord`] from a completed, proof-isolated statement
/// import.
///
/// `target` must be the exact same string used to build `completed` (the
/// string handed to [`crate::import_statement_ndjson`] or
/// [`crate::import_candidate_statement_ndjson`]); this function re-resolves
/// it against the report's own identity manifest rather than trusting a
/// caller's memory of it, so a mismatch is a typed error, not a silently
/// wrong record.
///
/// # Errors
///
/// Returns [`StatementGoalRecordError::TargetIdentityMissing`] if `target`
/// does not match any admitted declaration's identity, or
/// [`StatementGoalRecordError::UnexpectedAxioms`] if the completed import
/// somehow carries a nonempty axiom inventory (unreachable for an import that
/// went through [`crate::import_statement_ndjson`]'s own gate, which is
/// exactly why this is checked rather than assumed).
pub fn build_statement_goal_record(
    completed: &CompletedStatementImport,
    target: &str,
) -> Result<StatementGoalRecord, StatementGoalRecordError> {
    let report = completed.report();
    if !report.axioms.is_empty() {
        return Err(StatementGoalRecordError::UnexpectedAxioms {
            observed: report.axioms.clone(),
        });
    }
    let identity =
        find_target_identity(&report.declaration_identities, target).ok_or_else(|| {
            StatementGoalRecordError::TargetIdentityMissing {
                target: target.to_owned(),
            }
        })?;
    let goal_lean4 = completed.kernel().render_lean(completed.goal());
    let goal_sha256 = sha256_hex(goal_lean4.as_bytes());
    Ok(StatementGoalRecord {
        target_name: target.to_owned(),
        goal_lean4,
        goal_sha256,
        target_content_sha256: identity.content_sha256.clone(),
        target_dependency_count: identity.dependencies.len(),
        admitted_declaration_count: report.declaration_identities.len(),
        substituted_theorems: report.substituted_theorems.clone(),
        lean_version: report.lean_version.clone(),
        lean_githash: report.lean_githash.clone(),
        format_version: report.format_version.clone(),
    })
}

#[cfg(test)]
mod tests {
    use std::io::Cursor;

    use axeyum_lean_kernel::{
        BinderInfo, Declaration, Kernel, Lean4ExportMetadata, ReducibilityHint,
    };

    use super::*;
    use crate::{ImportLimits, import_statement_ndjson};

    const TARGET: &str = "Axeyum.Autogenesis.Statement.target";

    fn target_name(kernel: &mut Kernel) -> axeyum_lean_kernel::NameId {
        let root = kernel.anon();
        let axeyum = kernel.name_str(root, "Axeyum");
        let autogenesis = kernel.name_str(axeyum, "Autogenesis");
        let statement = kernel.name_str(autogenesis, "Statement");
        kernel.name_str(statement, "target")
    }

    fn proposition(
        kernel: &mut Kernel,
    ) -> (axeyum_lean_kernel::ExprId, axeyum_lean_kernel::ExprId) {
        let zero = kernel.level_zero();
        let prop = kernel.sort(zero);
        let p = kernel.bvar(0);
        let root = kernel.anon();
        let binder = kernel.name_str(root, "p");
        let goal = kernel.pi(binder, prop, p, BinderInfo::Default);
        (prop, goal)
    }

    fn definition_stream() -> String {
        let mut kernel = Kernel::new();
        let name = target_name(&mut kernel);
        let (prop, goal) = proposition(&mut kernel);
        kernel
            .add_declaration(Declaration::Definition {
                name,
                uparams: vec![],
                ty: prop,
                value: goal,
                hint: ReducibilityHint::Regular(0),
            })
            .expect("goal definition must check");
        kernel
            .render_lean4export_ndjson(&Lean4ExportMetadata::axeyum("4.30.0"))
            .expect("test stream must render")
    }

    #[test]
    fn a_valid_statement_yields_a_goal_whose_rendered_type_matches_the_source() {
        let completed = import_statement_ndjson(
            Cursor::new(definition_stream()),
            ImportLimits::default(),
            TARGET,
        )
        .expect("proof-free statement must import");
        let record = build_statement_goal_record(&completed, TARGET)
            .expect("a successfully imported target must yield a goal record");
        assert_eq!(record.target_name, TARGET);
        assert_eq!(record.goal_lean4, "((p : Prop) -> p)");
        assert_eq!(record.goal_sha256, sha256_hex(record.goal_lean4.as_bytes()));
        assert_eq!(record.admitted_declaration_count, 1);
        assert_eq!(record.target_dependency_count, 0);
        assert!(record.substituted_theorems.is_empty());
        assert_eq!(record.lean_version, "4.30.0");
        // Two independent calls on the same completed import must agree —
        // the record is a pure read of already-checked state, not a fresh
        // derivation that could vary run to run.
        let record2 = build_statement_goal_record(&completed, TARGET).unwrap();
        assert_eq!(record, record2);
    }

    #[test]
    fn a_mismatched_target_name_is_a_typed_error_not_a_silent_wrong_record() {
        let completed = import_statement_ndjson(
            Cursor::new(definition_stream()),
            ImportLimits::default(),
            TARGET,
        )
        .expect("proof-free statement must import");
        let error = build_statement_goal_record(&completed, "Some.Other.Name")
            .expect_err("a name the import never resolved must not yield a record");
        assert_eq!(
            error,
            StatementGoalRecordError::TargetIdentityMissing {
                target: "Some.Other.Name".to_owned()
            }
        );
    }

    #[test]
    fn sha256_hex_matches_a_known_vector() {
        // Empty-input SHA-256, RFC-independent known-answer test.
        assert_eq!(
            sha256_hex(b""),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
    }
}
