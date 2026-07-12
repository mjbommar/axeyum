//! Untrusted search below vacuous existential prefixes (ADR-0128).

use std::collections::HashMap;

use axeyum_ir::{TermArena, TermId, well_founded_default};
use axeyum_rewrite::replace_subterms;

use crate::auto::check_auto;
use crate::backend::{CheckResult, SolverConfig, SolverError};
use crate::quant_vacuous_exists_counterexample_cert::{
    VacuousExistsUniversalCounterexampleCertificate, admitted_vacuous_exists_universal,
    check_vacuous_exists_universal_counterexample,
};

/// Searches for a universal counterexample after independently recognizing a
/// syntactically vacuous leading existential block.
pub(crate) fn find_vacuous_exists_universal_counterexample(
    arena: &TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<Option<VacuousExistsUniversalCounterexampleCertificate>, SolverError> {
    for &assertion in assertions {
        let Some(admitted) = admitted_vacuous_exists_universal(arena, assertion) else {
            continue;
        };

        let mut search_arena = arena.clone();
        let mut replacements = HashMap::new();
        let mut fresh_binders = Vec::with_capacity(admitted.universal_binders.len());
        let mut nonce = search_arena.symbols().count();
        for &binder in &admitted.universal_binders {
            let sort = search_arena.symbol(binder).1;
            let fresh = loop {
                let name = format!(
                    "!vacuous_exists_counterexample_{}_{}_{}",
                    assertion.index(),
                    binder.index(),
                    nonce
                );
                nonce += 1;
                if search_arena.find_internal_symbol(&name).is_none() {
                    break search_arena
                        .declare_internal(&name, sort)
                        .map_err(|error| SolverError::Backend(error.to_string()))?;
                }
            };
            let binder_term = search_arena.var(binder);
            let fresh_term = search_arena.var(fresh);
            replacements.insert(binder_term, fresh_term);
            fresh_binders.push((binder, fresh, sort));
        }

        let mut memo = HashMap::new();
        let instance = replace_subterms(&mut search_arena, admitted.body, &replacements, &mut memo)
            .map_err(|error| SolverError::Backend(error.to_string()))?;
        let negated = search_arena
            .not(instance)
            .map_err(|error| SolverError::Backend(error.to_string()))?;
        let result = match check_auto(&mut search_arena, &[negated], config) {
            Ok(result) => result,
            Err(SolverError::Unsupported(_)) => continue,
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
        if bindings.len() != admitted.universal_binders.len() {
            continue;
        }

        let certificate = VacuousExistsUniversalCounterexampleCertificate {
            assertion,
            bindings,
        };
        if check_vacuous_exists_universal_counterexample(arena, assertions, &certificate) {
            return Ok(Some(certificate));
        }
        return Err(SolverError::Backend(
            "generated vacuous-existential counterexample failed independent replay".to_owned(),
        ));
    }
    Ok(None)
}
