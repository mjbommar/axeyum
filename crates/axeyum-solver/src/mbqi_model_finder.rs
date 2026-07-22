//! Search-side bridge from MBQI candidates to checked quantified-UF models.
//!
//! The finite-profile proof lives in [`crate::quant_uf_model_sat_cert`], not in
//! this search adapter. A candidate receives SAT credit only when that separate
//! source checker accepts every original universal and returns one certificate
//! per assertion.

use axeyum_ir::TermArena;

use crate::{Model, QuantifiedUfModelSatCertificate};

/// Returns source-bound certificates when `model` is independently proved to
/// satisfy every universal in `assertions`; otherwise declines.
pub(crate) fn certify_all_universals(
    arena: &TermArena,
    assertions: &[axeyum_ir::TermId],
    model: &Model,
) -> Option<Vec<QuantifiedUfModelSatCertificate>> {
    if assertions.is_empty() {
        return None;
    }
    assertions
        .iter()
        .map(|&assertion| {
            crate::quant_uf_model_sat_cert::certify_quantified_uf_model_sat(arena, assertion, model)
        })
        .collect()
}
