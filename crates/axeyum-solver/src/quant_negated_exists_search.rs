//! Untrusted search for ADR-0126 negated-existential witnesses.

use std::collections::HashMap;

use axeyum_ir::{Sort, TermArena, TermId, well_founded_default};
use axeyum_rewrite::replace_subterms;

use crate::auto::check_auto;
use crate::backend::{CheckResult, SolverConfig, SolverError};
use crate::quant_negated_exists_cert::{
    NegatedExistentialWitnessCertificate, admitted_negated_existential,
    check_negated_existential_witness,
};

/// Searches for a concrete witness satisfying one top-level negated
/// existential's body. Returned evidence has already passed source replay.
pub(crate) fn find_negated_existential_witness(
    arena: &TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<Option<NegatedExistentialWitnessCertificate>, SolverError> {
    for &assertion in assertions {
        let Some((binders, body)) = admitted_negated_existential(arena, assertion) else {
            continue;
        };

        let mut search_arena = arena.clone();
        let mut replacements = HashMap::new();
        let mut fresh_binders = Vec::with_capacity(binders.len());
        let mut nonce = search_arena.symbols().count();
        for &binder in &binders {
            let sort = search_arena.symbol(binder).1;
            let fresh = declare_fresh(
                &mut search_arena,
                assertion,
                binder.index(),
                sort,
                &mut nonce,
            )?;
            replacements.insert(search_arena.var(binder), search_arena.var(fresh));
            fresh_binders.push((binder, fresh, sort));
        }

        let mut memo = HashMap::new();
        let instance = replace_subterms(&mut search_arena, body, &replacements, &mut memo)
            .map_err(|error| SolverError::Backend(error.to_string()))?;
        let result = match check_auto(&mut search_arena, &[instance], config) {
            Ok(CheckResult::Unknown(_)) | Err(SolverError::Unsupported(_)) => {
                crate::solve(&mut search_arena, &[instance], config)?
            }
            Ok(result) => result,
            Err(error) => return Err(error),
        };
        let CheckResult::Sat(model) = result else {
            continue;
        };

        let mut bindings = Vec::with_capacity(fresh_binders.len());
        for (binder, fresh, sort) in fresh_binders {
            let Some(value) = model
                .get(fresh)
                .or_else(|| well_founded_default(&search_arena, sort))
            else {
                bindings.clear();
                break;
            };
            bindings.push((binder, value));
        }
        if bindings.len() != binders.len() {
            continue;
        }

        let certificate = NegatedExistentialWitnessCertificate {
            assertion,
            bindings,
        };
        if check_negated_existential_witness(arena, assertions, &certificate) {
            return Ok(Some(certificate));
        }
    }
    Ok(None)
}

#[cfg(test)]
mod tests {
    use std::fs;

    use axeyum_smtlib::parse_script;

    use crate::quant_bv_conjunctive_cert::{
        admitted_conjunctive_universal_loose, conjunctive_universals,
    };

    #[test]
    fn psyco_107_bv_admits_relaxed_conjunctive_universal_shape() {
        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../corpus/public-curated/quantified/BV/cvc5-regress-clean/cli__regress1__quantifiers__psyco-107-bv.smt2",
        );
        let text = fs::read_to_string(path).expect("read psyco-107-bv");
        let script = parse_script(&text).expect("parse psyco-107-bv");
        let admitted = script.assertions.iter().copied().find_map(|assertion| {
            conjunctive_universals(&script.arena, assertion)
                .into_iter()
                .find_map(|universal| {
                    admitted_conjunctive_universal_loose(&script.arena, assertion, universal)
                })
        });
        assert!(
            admitted.is_some(),
            "psyco-107-bv should admit a relaxed conjunctive-universal shape"
        );
    }
}

fn declare_fresh(
    arena: &mut TermArena,
    assertion: TermId,
    binder_index: usize,
    sort: Sort,
    nonce: &mut usize,
) -> Result<axeyum_ir::SymbolId, SolverError> {
    loop {
        let name = format!(
            "!negated_exists_witness_{}_{}_{}",
            assertion.index(),
            binder_index,
            *nonce
        );
        *nonce += 1;
        if arena.find_internal_symbol(&name).is_none() {
            return arena
                .declare_internal(&name, sort)
                .map_err(|error| SolverError::Backend(error.to_string()));
        }
    }
}
