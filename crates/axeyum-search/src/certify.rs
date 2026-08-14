//! Offline certification of a dumped cover.
//!
//! [`harness::run_cover`](crate::harness::run_cover) separates the jobs with
//! different cost profiles: cells solve in seconds while their proofs can take
//! minutes to check, so [`CheckMode::Deferred`](crate::CheckMode) (or a
//! [`check_step_cap`](crate::CoverOptions::check_step_cap)) dumps proofs to
//! disk and records the cell as [`CellCheck::Deferred`]. Deferring is what
//! turned one cover from 42% complete after 5.5 hours into complete in 153
//! seconds — but a deferred cover certifies nothing until every dumped proof
//! has actually been checked. [`certify_dumped_cover`] is that second pass.
//!
//! Nothing here trusts the producing run: each cell's augmenting unit clauses
//! are recomputed from the ledger's recorded choices through the
//! [`BranchPlan`], never read from the proof file, and the certificate is
//! issued by [`certify_cover`], which re-verifies all four cover obligations
//! from scratch.

use std::fs;
use std::path::Path;
use std::time::Instant;

use axeyum_cnf::{CnfClause, CnfFormula, DratStep, check_drat, check_drat_backward, parse_drat};

use crate::SearchError;
use crate::cover::{
    BranchPlan, CellCheck, CellRecord, CellVerdict, CoverCertificate, certify_cover,
    certify_tree_cover,
};
use crate::harness::{CheckMode, cell_proof_path};

/// Checks every deferred cell's dumped proof and certifies the cover.
///
/// Rows whose check already [`Passed`](CellCheck::Passed) are kept as they
/// are; rows recorded [`Deferred`](CellCheck::Deferred) are re-checked from
/// `proof_dir` against `formula` plus the unit clauses the [`BranchPlan`]
/// derives from the row's own recorded choices. The upgraded ledger then goes
/// through [`certify_cover`], so a certificate from this function carries
/// exactly the same four obligations as an online one.
///
/// `steps`, `adds`, and `check_time` on re-checked rows are recomputed from
/// the parsed proof and the measured check, not copied from the search run.
///
/// # Errors
///
/// Returns [`SearchError::InvalidParameter`] if `mode` is
/// [`CheckMode::Deferred`] (this pass exists to *end* deferral),
/// [`SearchError::ProofUnavailable`] if a deferred cell's proof file cannot
/// be read, [`SearchError::Drat`] if one fails to parse, and every
/// [`certify_cover`] obligation failure — including
/// [`SearchError::CellCheckFailed`] when a dumped proof does not hold up.
pub fn certify_dumped_cover(
    formula: &CnfFormula,
    plan: &BranchPlan,
    records: &[CellRecord],
    proof_dir: &Path,
    proof_prefix: &str,
    mode: CheckMode,
) -> Result<CoverCertificate, SearchError> {
    let upgraded = recheck_dumped(formula, plan, records, proof_dir, proof_prefix, mode)?;
    certify_cover(formula, plan, &upgraded)
}

/// [`certify_dumped_cover`] for a **tree** cover, as produced by
/// [`run_adaptive_cover`](crate::harness::run_adaptive_cover).
///
/// The only differences are that a row's augmenting units come from
/// [`BranchPlan::literals_for_prefix`] (a cube's path can be shorter than the
/// plan's depth) and that the certificate is issued by
/// [`certify_tree_cover`], whose obligation 3 is the complete-trie check
/// rather than the flat product check.
///
/// `records` is normally the concatenation of every run's ledger: a resumed
/// run's rows carry the same shape-independent cube codes, so the union
/// certifies as one cover or names the cube that is missing from it.
///
/// # Errors
///
/// As [`certify_dumped_cover`], with [`certify_tree_cover`]'s obligations.
pub fn certify_dumped_tree_cover(
    formula: &CnfFormula,
    plan: &BranchPlan,
    records: &[CellRecord],
    proof_dir: &Path,
    proof_prefix: &str,
    mode: CheckMode,
) -> Result<CoverCertificate, SearchError> {
    let upgraded = recheck_dumped(formula, plan, records, proof_dir, proof_prefix, mode)?;
    certify_tree_cover(formula, plan, &upgraded)
}

/// Re-checks every deferred row's dumped proof, returning the upgraded ledger.
///
/// Shared by the flat and tree certification passes so the two cannot drift on
/// what a re-check does. The augmented formula is rebuilt from the row's own
/// recorded choices through the plan; the proof file contributes only the
/// proof.
fn recheck_dumped(
    formula: &CnfFormula,
    plan: &BranchPlan,
    records: &[CellRecord],
    proof_dir: &Path,
    proof_prefix: &str,
    mode: CheckMode,
) -> Result<Vec<CellRecord>, SearchError> {
    if matches!(mode, CheckMode::Deferred) {
        return Err(SearchError::InvalidParameter {
            what: "certify_dumped_cover needs a checking mode; Deferred would defer forever"
                .to_string(),
        });
    }
    let mut upgraded = Vec::with_capacity(records.len());
    for record in records {
        if record.verdict != CellVerdict::Unsat || !matches!(record.check, CellCheck::Deferred) {
            // Passed rows were checked in-process; Failed rows and non-unsat
            // verdicts pass through for `certify_cover` to reject precisely.
            upgraded.push(record.clone());
            continue;
        }
        let path = cell_proof_path(proof_dir, proof_prefix, record.index);
        let text = fs::read_to_string(&path).map_err(|error| SearchError::ProofUnavailable {
            index: record.index,
            message: format!("{}: {error}", path.display()),
        })?;
        let proof = parse_drat(&text)?;

        // Rebuild F + cell units from the RECORDED choices via the plan. The
        // proof file contributes only the proof. `literals_for_prefix` accepts
        // a full-depth cell and a shorter cube alike, so one path serves both
        // cover shapes.
        let mut augmented = formula.clone();
        for literal in plan.literals_for_prefix(&record.choices)? {
            augmented.add_clause(CnfClause::new(vec![literal]))?;
        }

        let steps = proof.len();
        let adds = proof
            .iter()
            .filter(|step| matches!(step, DratStep::Add(_)))
            .count();
        let started = Instant::now();
        let verdict = match mode {
            CheckMode::Backward => check_drat_backward(&augmented, &proof),
            CheckMode::Forward => check_drat(&augmented, &proof),
            CheckMode::Deferred => unreachable!("refused above"),
        };
        let check_time = started.elapsed();
        let check = match verdict {
            Ok(true) => CellCheck::Passed,
            Ok(false) => CellCheck::Failed("no empty clause derived".to_string()),
            Err(error) => CellCheck::Failed(error.to_string()),
        };
        upgraded.push(CellRecord {
            steps,
            adds,
            check,
            check_time,
            ..record.clone()
        });
    }
    Ok(upgraded)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    use crate::cover::colour_branch_plan;
    use crate::family::{ColouringFamily, Schur};
    use crate::harness::{CoverOptions, SilentObserver, run_cover};

    fn scratch_dir(tag: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "axeyum-search-certify-{tag}-{}",
            std::process::id()
        ));
        if dir.exists() {
            fs::remove_dir_all(&dir).expect("clear scratch dir");
        }
        fs::create_dir_all(&dir).expect("create scratch dir");
        dir
    }

    fn deferred_schur_cover(tag: &str) -> (CnfFormula, BranchPlan, Vec<CellRecord>, PathBuf) {
        // Schur's theorem: [1, 5] has no sum-free 2-colouring.
        let family = Schur::new(2).expect("family");
        let problem = family.problem(5).expect("problem");
        let formula = problem.encode().expect("encode");
        let plan = colour_branch_plan(&problem, &[2, 3]).expect("plan");
        let dir = scratch_dir(tag);
        let options = CoverOptions {
            check: CheckMode::Deferred,
            proof_dir: Some(dir.clone()),
            ..CoverOptions::default()
        };
        let outcome = run_cover(&formula, &plan, &options, &SilentObserver).expect("cover");
        assert!(
            outcome.certificate().is_none(),
            "a deferred cover must not certify online"
        );
        let records = outcome.records().to_vec();
        assert!(
            records
                .iter()
                .all(|record| matches!(record.check, CellCheck::Deferred)),
            "every cell should be deferred"
        );
        (formula, plan, records, dir)
    }

    #[test]
    fn certifies_a_deferred_cover_from_its_dumped_proofs() {
        let (formula, plan, records, dir) = deferred_schur_cover("ok");

        // The online gate refuses the deferred ledger…
        assert!(matches!(
            certify_cover(&formula, &plan, &records),
            Err(SearchError::CellNotChecked { .. })
        ));
        // …and the offline pass completes it.
        let certificate = certify_dumped_cover(
            &formula,
            &plan,
            &records,
            &dir,
            &CoverOptions::default().proof_prefix,
            CheckMode::Backward,
        )
        .expect("certify");
        assert_eq!(certificate.cells, plan.cell_count());
        assert!(certificate.steps > 0, "recomputed steps should be counted");
        fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn a_tampered_proof_fails_rather_than_certifying() {
        let (formula, plan, records, dir) = deferred_schur_cover("tampered");
        let prefix = CoverOptions::default().proof_prefix;
        // An empty proof parses but derives nothing.
        fs::write(cell_proof_path(&dir, &prefix, records[0].index), b"").expect("tamper");
        assert!(matches!(
            certify_dumped_cover(&formula, &plan, &records, &dir, &prefix, CheckMode::Backward),
            Err(SearchError::CellCheckFailed { index, .. }) if index == records[0].index
        ));
        fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn a_missing_proof_is_reported_not_skipped() {
        let (formula, plan, records, dir) = deferred_schur_cover("missing");
        let prefix = CoverOptions::default().proof_prefix;
        fs::remove_file(cell_proof_path(&dir, &prefix, records[1].index)).expect("remove");
        assert!(matches!(
            certify_dumped_cover(&formula, &plan, &records, &dir, &prefix, CheckMode::Backward),
            Err(SearchError::ProofUnavailable { index, .. }) if index == records[1].index
        ));
        fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn certifies_a_deferred_tree_cover_and_rejects_an_incomplete_one() {
        use crate::harness::{AdaptiveOptions, AdaptiveOutcome, run_adaptive_cover};

        // S(3) = 14 with a starved budget: the run must split, so the cover is
        // a genuine mixed-depth tree rather than the flat product.
        let family = Schur::new(3).expect("family");
        let problem = family.problem(14).expect("problem");
        let formula = problem.encode().expect("encode");
        let plan = colour_branch_plan(&problem, &[2, 3, 4, 5]).expect("plan");
        let dir = scratch_dir("tree");
        let options = CoverOptions {
            cell_conflicts: 1,
            check: CheckMode::Deferred,
            proof_dir: Some(dir.clone()),
            ..CoverOptions::default()
        };
        let outcome = run_adaptive_cover(
            &formula,
            &plan,
            &options,
            &AdaptiveOptions {
                initial_depth: 1,
                ..AdaptiveOptions::default()
            },
            &SilentObserver,
        )
        .expect("run");
        let AdaptiveOutcome::Refuted {
            records, splits, ..
        } = &outcome
        else {
            panic!("expected a refutation, got {outcome:?}");
        };
        assert!(*splits > 0, "the cover should be a tree, not a product");
        assert!(
            outcome.certificate().is_none(),
            "deferred certifies nothing"
        );

        let prefix = options.proof_prefix.clone();
        let certificate =
            certify_dumped_tree_cover(&formula, &plan, records, &dir, &prefix, CheckMode::Backward)
                .expect("certify");
        assert_eq!(certificate.cells, records.len());
        assert!(certificate.steps > 0, "a certified cover has proof steps");

        // SOUNDNESS-NEGATIVE: drop one cube's row. The proofs on disk are
        // untouched and every remaining row still checks, so only the
        // completeness obligation stands between this and a fabricated result.
        let mut holed = records.clone();
        let dropped = holed.remove(records.len() / 2);
        assert!(
            matches!(
                certify_dumped_tree_cover(
                    &formula,
                    &plan,
                    &holed,
                    &dir,
                    &prefix,
                    CheckMode::Backward
                ),
                Err(SearchError::MissingCell { .. })
            ),
            "an incomplete tree cover must not certify (dropped cube {})",
            dropped.index
        );
        fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn deferred_mode_is_refused() {
        let (formula, plan, records, dir) = deferred_schur_cover("mode");
        assert!(matches!(
            certify_dumped_cover(
                &formula,
                &plan,
                &records,
                &dir,
                &CoverOptions::default().proof_prefix,
                CheckMode::Deferred
            ),
            Err(SearchError::InvalidParameter { .. })
        ));
        fs::remove_dir_all(&dir).ok();
    }
}
