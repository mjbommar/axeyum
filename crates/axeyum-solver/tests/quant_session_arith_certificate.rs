#![cfg(feature = "full")]
//! Every `Unsat` the quantified e-graph route returns carries an instance-set
//! certificate (ADR-2130, closing the gap ADR-2124 measured and left open).
//!
//! # Why this suite is a source invariant and not a query fixture
//!
//! [ADR-2124] section 4.4 repaired the `CandidateFixpointStep::Refuted` exit,
//! which returned `unsat` with no certificate while its matched sibling — the
//! batch path, reached through the *identical* `replay_online_refutation` over
//! the *identical* ground set — collected one. Section 8 then measured what
//! covered that repair: it removed the collection and ran the whole
//! `quant_instance_set_cert::` surface against the mutant. **9 tests ran and all
//! 9 SURVIVED.** So nothing anywhere noticed the repair being taken away, and
//! its presence in a diff was the only thing keeping it there.
//!
//! The obvious fix is a query that drives that exit and inspects the
//! certificate. ADR-2124 did not write one and said why: reaching `Refuted`
//! needs the candidate-equality fixpoint to produce a session `Unsat` on a query
//! small enough to be a fixture, and the paths that get there on real files are
//! 24-second cores. This lane did not find a small one either, and says so
//! rather than shipping a fixture that passes for the wrong reason.
//!
//! What IS available is the property the repair is an instance of, and it is
//! the property that actually matters: **no exit of this function returns
//! `Unsat` without assigning the certificate first.** That is checkable over the
//! function's own source, it is what a later change would have to violate to
//! undo the repair, and — unlike the fixture that does not exist — it also
//! guards the three exits that were already right and any exit added later.
//!
//! This is the "a test named *every X* must derive its X from the authority"
//! discipline: the authority here is the source of
//! `prove_quantified_unsat_via_egraph_impl`, not a list of exits someone
//! remembered.
//!
//! [ADR-2124]: ../../../docs/research/09-decisions/adr-2124-incremental-ground-closure-for-quantifier-instances.md

/// The function whose exits are the subject.
const FN_NAME: &str = "fn prove_quantified_unsat_via_egraph_impl";

/// The source of the quantified e-graph route, read at compile time.
const SOURCE: &str = include_str!("../src/qinst_egraph.rs");

/// The body of `prove_quantified_unsat_via_egraph_impl`, by brace balance.
///
/// Brace counting is crude but it is the right crudeness here: the alternative
/// is a hand-maintained line range, which is the thing that went stale in the
/// config-registry entry this lane also had to fix.
fn function_body() -> &'static str {
    let start = SOURCE
        .find(FN_NAME)
        .unwrap_or_else(|| panic!("{FN_NAME} not found -- this suite is pointed at nothing"));
    let open = SOURCE[start..]
        .find('{')
        .expect("a function signature is followed by a body")
        + start;
    let mut depth = 0usize;
    for (offset, ch) in SOURCE[open..].char_indices() {
        match ch {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    return &SOURCE[open..=open + offset];
                }
            }
            _ => {}
        }
    }
    panic!("unbalanced braces while reading {FN_NAME}");
}

/// The control: the subject must actually have been found and be substantial.
///
/// Without this, a rename would make `function_body` panic (fine) but a
/// SHRINKING body — say, an early `return` inserted above everything — would
/// silently reduce the population every assertion below quantifies over, and
/// each of them would pass over an empty set.
#[test]
fn the_subject_function_is_present_and_substantial() {
    let body = function_body();
    assert!(
        body.len() > 10_000,
        "the body of {FN_NAME} is only {} bytes; this suite quantifies over its \
         exits, so a body this small means it is measuring almost nothing",
        body.len()
    );
    assert!(
        body.contains("CandidateFixpointStep::Refuted"),
        "the exit ADR-2124 repaired is not in the body this suite read"
    );
}

/// **The guard.** Every `Ok(CheckResult::Unsat)` in the function assigns the
/// certificate first.
///
/// The certificate is assigned through `*certificate = ...` and the exits are
/// `return Ok(CheckResult::Unsat)`. For each exit, the nearest preceding
/// certificate assignment must be closer than the nearest preceding *other*
/// unsat exit — i.e. each exit has an assignment of its own rather than
/// inheriting one that belongs to an earlier exit.
#[test]
fn every_unsat_exit_assigns_an_instance_set_certificate() {
    let body = function_body();
    const EXIT: &str = "return Ok(CheckResult::Unsat)";
    const ASSIGN: &str = "*certificate =";

    let exits: Vec<usize> = body.match_indices(EXIT).map(|(i, _)| i).collect();
    let assigns: Vec<usize> = body.match_indices(ASSIGN).map(|(i, _)| i).collect();

    assert!(
        exits.len() >= 3,
        "expected at least the three unsat exits ADR-2124 counted, found {}; a \
         suite that quantifies over zero or one exit cannot fail",
        exits.len()
    );

    let mut naked = Vec::new();
    for (index, &exit) in exits.iter().enumerate() {
        let previous_exit = if index == 0 { 0 } else { exits[index - 1] };
        let has_own_assignment = assigns.iter().any(|&a| a < exit && a >= previous_exit);
        if !has_own_assignment {
            let context_start = exit.saturating_sub(300);
            naked.push(format!(
                "exit #{index} at byte {exit} has no `{ASSIGN}` of its own; \
                 preceding context:\n...{}",
                &body[context_start..exit]
            ));
        }
    }

    assert!(
        naked.is_empty(),
        "{} of {} unsat exits return without assigning an instance-set \
         certificate. ADR-2124 repaired exactly this on the \
         `CandidateFixpointStep::Refuted` exit and measured that NOTHING \
         noticed the repair being removed; this suite is what notices.\n\n{}",
        naked.len(),
        exits.len(),
        naked.join("\n\n")
    );
}

/// The repaired exit specifically, named, so the mutation has a target whose
/// death is attributable to it rather than to the population guard above.
#[test]
fn the_candidate_fixpoint_refutation_exit_is_certified() {
    let body = function_body();
    let refuted = body
        .find("CandidateFixpointStep::Refuted =>")
        .expect("the repaired exit's match arm");
    let after = &body[refuted..];
    let exit = after
        .find("return Ok(CheckResult::Unsat)")
        .expect("the repaired exit returns Unsat");
    let arm = &after[..exit];
    assert!(
        arm.contains("*certificate ="),
        "`CandidateFixpointStep::Refuted` returns `Unsat` without assigning a \
         certificate. This is the exact regression ADR-2124 repaired: its \
         sibling exit (the batch path) collects one through the identical \
         `replay_online_refutation` over the identical ground set, so an \
         uncertified refutation here is one of a matched pair with the other \
         half missing."
    );
    assert!(
        arm.contains("collect_ground_derivations"),
        "the assignment must come from `collect_ground_derivations` over the \
         ground set -- an assignment of something else would satisfy the guard \
         above while carrying a certificate that is not about these instances"
    );
}
