//! Untrusted witness search for ADR-0122 guarded quantified SAT certificates.

use axeyum_ir::{Op, Sort, TermArena, TermId, TermNode, Value, WideUint};

use crate::{CheckResult, Model, QuantifiedGuardSatCertificate, check_quantified_guard_sat};

/// Proposes deterministic BV witnesses and returns SAT only after certificate replay.
pub(crate) fn decide_quantified_guard_vacuity_sat(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<CheckResult> {
    let [assertion] = assertions else {
        return None;
    };
    let TermNode::App {
        op: Op::Exists(existential),
        ..
    } = arena.node(*assertion)
    else {
        return None;
    };
    let Sort::BitVec(width) = arena.symbol(*existential).1 else {
        return None;
    };

    for witness in [bv_value(width, 0), bv_value(width, 1)] {
        let cert = QuantifiedGuardSatCertificate {
            assertion: *assertion,
            existential: *existential,
            witness,
        };
        if check_quantified_guard_sat(arena, *assertion, &cert) {
            let mut model = Model::new();
            model.set_quantified_guard_sat_certificate(cert);
            return Some(CheckResult::Sat(model));
        }
    }
    None
}

fn bv_value(width: u32, value: u128) -> Value {
    if width <= 128 {
        Value::Bv { width, value }
    } else {
        Value::WideBv(WideUint::from_u128(value, width))
    }
}
