//! Route A: one DRAT proof of the *original* formula, composed from the
//! per-cell refutations.
//!
//! Route B (per-cell checked proofs plus a checked cover) leaves exactly one
//! step to a meta-argument: *a checked refutation of every cell of an exhaustive
//! cover implies `F` is unsatisfiable*. True, and short, but not something a
//! checker verified. Route A removes it. The composed proof is checked against
//! the original formula by [`check_drat`](axeyum_cnf::check_drat), and that
//! single acceptance discharges the whole result.
//!
//! # The transform
//!
//! Let cell `c` have literals `l_1 .. l_d` and negation clause
//! `D_c = (~l_1 | .. | ~l_d)`. The cell was refuted by solving
//! `F + {(l_1) .. (l_d)}`, yielding a proof `P_c`. Then:
//!
//! * every `Add(C)` of `P_c` is re-emitted as `Add(C | D_c)`;
//! * every `Delete` of `P_c` is dropped.
//!
//! **Soundness.** axeyum's proof-producing CDCL only ever adds a 1-UIP learned
//! clause or the empty clause, and both are RUP — never RAT-only. RUP is
//! monotone in the clause set, so dropping deletions can only make later checks
//! easier, and clauses left behind by earlier segments can only add propagation.
//! For the augmentation: the RUP check of `C | D_c` falsifies every literal of
//! `C | D_c`, which makes each `~l_i` false, i.e. sets every cell literal `l_i`
//! true — exactly the assignment the cell's unit clauses forced in the original
//! run. Under that assignment `D_c` is falsified in every companion clause
//! `C_j | D_c`, so each behaves exactly as `C_j` did, and unit propagation
//! reproduces the original conflict. The final step of `P_c` is `Add([])`, which
//! the transform turns into `Add(D_c)`: the cell's refutation lemma, derived in
//! DRAT from `F` alone.
//!
//! **The collapse.** After all segments the clause set contains `D_c` for every
//! cell. The proof then collapses the branch tree one coordinate at a time,
//! deepest first. For a prefix `p` of length `L < d`, add
//! `R(p) = (~l(p_0) | .. | ~l(p_{L-1}))`. `R(p)` is RUP: falsifying it sets each
//! `l(p_t)` true, which turns each already-present child `R(p, i)` into the unit
//! `~l_i` of group `L`; propagating all of them falsifies every literal of group
//! `L`'s at-least-one clause, which is a conflict. At `L = 0` the added clause
//! is the **empty clause**. The at-least-one clauses are original clauses of `F`
//! and are never deleted, so they are available at every collapse step — which
//! is why [`compose_cover_proof`] verifies they are present before emitting
//! anything.
//!
//! # Cost
//!
//! Route A materialises every cell proof at once. On `R_4(3(x-y)=2z)` at
//! `n = 103` that was 649,183 steps and a 40 MB proof — affordable to *build*
//! and, with backward checking, affordable to check; on a harder instance it is
//! not, and the caller should fall back to route B and say so.

use std::collections::HashSet;

use axeyum_cnf::{CnfFormula, CnfLit, DratStep};

use crate::SearchError;
use crate::cover::{BranchPlan, verify_branch_clauses};

/// Unions two clauses, dropping duplicates.
///
/// Returns `None` for a tautology: it is trivially RUP, so emitting it would be
/// noise in the proof rather than a step that carries weight.
fn union_lits(base: &[CnfLit], extra: &[CnfLit]) -> Option<Vec<CnfLit>> {
    let mut seen: HashSet<(usize, bool)> = HashSet::new();
    let mut out: Vec<CnfLit> = Vec::with_capacity(base.len() + extra.len());
    for &lit in base.iter().chain(extra.iter()) {
        let key = (lit.var().index(), lit.is_negated());
        if seen.contains(&(key.0, !key.1)) {
            return None;
        }
        if seen.insert(key) {
            out.push(lit);
        }
    }
    Some(out)
}

/// Composes one DRAT proof of `formula` from the per-cell refutations.
///
/// `proofs` is indexed by cell index and must have one entry per cell of the
/// plan. See the module docs for the transform and its soundness argument.
///
/// The result is a *candidate*: nothing here makes it valid. Run
/// [`check_drat`](axeyum_cnf::check_drat) or
/// [`check_drat_backward`](axeyum_cnf::check_drat_backward) on it against
/// `formula`; that check is the certificate.
///
/// # Errors
///
/// Returns [`SearchError::MissingAtLeastOneClause`] if a branch group's clause
/// is not in `formula` (the collapse would not be RUP),
/// [`SearchError::InvalidParameter`] if `proofs` is the wrong length,
/// [`SearchError::ComposeMissingProof`] for a cell with no retained proof, and
/// [`SearchError::ComposeNoEmptyClause`] if the composition does not end in the
/// empty clause.
pub fn compose_cover_proof(
    formula: &CnfFormula,
    plan: &BranchPlan,
    proofs: &[Option<Vec<DratStep>>],
) -> Result<Vec<DratStep>, SearchError> {
    verify_branch_clauses(formula, plan)?;
    if proofs.len() != plan.cell_count() {
        return Err(SearchError::InvalidParameter {
            what: format!(
                "compose got {} proof slots for {} cells",
                proofs.len(),
                plan.cell_count()
            ),
        });
    }

    let mut composed: Vec<DratStep> = Vec::new();
    for index in 0..plan.cell_count() {
        let cell = plan.cell(index)?;
        let proof = proofs[index]
            .as_ref()
            .ok_or(SearchError::ComposeMissingProof { index })?;
        let negation = cell.negation();
        for step in proof {
            let DratStep::Add(clause) = step else {
                continue;
            };
            if let Some(lits) = union_lits(clause, &negation) {
                composed.push(DratStep::Add(lits));
            }
        }
    }

    for level in (0..plan.depth()).rev() {
        for code in 0..plan.prefix_count(level) {
            let prefix = plan.prefix(level, code)?;
            let clause: Vec<CnfLit> = prefix
                .iter()
                .enumerate()
                .map(|(slot, &choice)| plan.groups()[slot].literals()[choice - 1].negated())
                .collect();
            composed.push(DratStep::Add(clause));
        }
    }

    match composed.last() {
        Some(DratStep::Add(clause)) if clause.is_empty() => Ok(composed),
        _ => Err(SearchError::ComposeNoEmptyClause),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cover::colour_branch_plan;
    use crate::family::{ColouringFamily, Schur};
    use axeyum_cnf::{CnfClause, ProofSolveOutcome, check_drat, solve_with_drat_proof};

    /// Solves every cell of `plan` against `formula` and retains the proofs.
    fn cell_proofs(formula: &CnfFormula, plan: &BranchPlan) -> Vec<Option<Vec<DratStep>>> {
        (0..plan.cell_count())
            .map(|index| {
                let cell = plan.cell(index).expect("cell");
                let mut augmented = formula.clone();
                for &lit in cell.literals() {
                    augmented
                        .add_clause(CnfClause::new(vec![lit]))
                        .expect("unit clause");
                }
                match solve_with_drat_proof(&augmented) {
                    ProofSolveOutcome::Unsat(proof) => Some(proof),
                    other => panic!("cell {index} was not refuted: {other:?}"),
                }
            })
            .collect()
    }

    fn schur_five() -> (CnfFormula, BranchPlan) {
        let family = Schur::new(2).expect("family");
        let problem = family.problem(5).expect("problem");
        let formula = problem.encode().expect("encode");
        let plan = colour_branch_plan(&problem, &[2, 3]).expect("plan");
        (formula, plan)
    }

    #[test]
    fn composed_proof_is_accepted_on_the_original_formula() {
        let (formula, plan) = schur_five();
        let proofs = cell_proofs(&formula, &plan);
        let composed = compose_cover_proof(&formula, &plan, &proofs).expect("compose");
        assert!(matches!(composed.last(), Some(DratStep::Add(c)) if c.is_empty()));
        assert!(check_drat(&formula, &composed).expect("check"));
    }

    #[test]
    fn a_forged_cover_of_a_satisfiable_formula_is_rejected() {
        // SOUNDNESS-NEGATIVE: fabricate every cell "refutation" as a bare,
        // unjustified `Add([])` over a formula that is genuinely SATISFIABLE
        // (S(2) = 5, so [1, 4] has a sum-free 2-colouring). No valid DRAT
        // refutation of it exists, so if the final check accepted the
        // composition it would be accepting the cover meta-argument rather
        // than checking the proof.
        //
        // Note the sharper fact this test deliberately does NOT assert: on an
        // UNSAT formula, forging one cell's proof can still compose into an
        // artifact `check_drat` accepts, because checking re-derives every
        // lifted step by RUP and the forged step may be independently
        // derivable (on `schur_five` with this plan, every cube negation is
        // one propagation cascade away, so it always is). That acceptance is
        // correct: the guarantee is that an accepted artifact is a valid
        // refutation of F, not a claim about the provenance of its steps.
        let family = Schur::new(2).expect("family");
        let problem = family.problem(4).expect("problem");
        let formula = problem.encode().expect("encode");
        let plan = colour_branch_plan(&problem, &[2, 3]).expect("plan");
        let proofs: Vec<Option<Vec<DratStep>>> =
            vec![Some(vec![DratStep::Add(Vec::new())]); plan.cell_count()];
        let composed = compose_cover_proof(&formula, &plan, &proofs).expect("compose");
        assert!(
            check_drat(&formula, &composed).is_err(),
            "check_drat accepted a forged refutation of a satisfiable formula"
        );
    }

    #[test]
    fn a_missing_cell_proof_is_refused() {
        let (formula, plan) = schur_five();
        let mut proofs = cell_proofs(&formula, &plan);
        proofs[1] = None;
        assert_eq!(
            compose_cover_proof(&formula, &plan, &proofs),
            Err(SearchError::ComposeMissingProof { index: 1 })
        );
    }

    #[test]
    fn composition_refuses_a_formula_without_the_branch_clauses() {
        let (formula, plan) = schur_five();
        let proofs = cell_proofs(&formula, &plan);
        // Drop the at-least-one clauses by rebuilding the formula without them.
        let mut stripped = CnfFormula::new(formula.variable_count());
        for clause in formula.clauses().iter().skip(5) {
            stripped.add_clause(clause.clone()).expect("clause");
        }
        assert!(matches!(
            compose_cover_proof(&stripped, &plan, &proofs),
            Err(SearchError::MissingAtLeastOneClause { .. })
        ));
    }
}
