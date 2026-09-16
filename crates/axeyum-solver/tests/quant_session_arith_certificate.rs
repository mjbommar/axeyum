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

/// The unsat exit this suite quantifies over.
const EXIT: &str = "return Ok(CheckResult::Unsat)";

/// The certificate assignment each instance-set exit must carry.
const ASSIGN: &str = "*certificate =";

/// How far back to look for the guard that decides an exit's kind.
const GUARD_WINDOW: usize = 200;

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

/// **The guard.** Every unsat exit that refutes BY THE INSTANCE SET assigns the
/// certificate first.
///
/// # The population, and why it is not simply "every unsat exit"
///
/// This assertion was first written over every `return Ok(CheckResult::Unsat)`
/// in the function, and its first honest run was a finding: the function has
/// **seven** such exits, not the four [ADR-2124] counted, and two of them assign
/// no certificate.
///
/// Those two are not defects. They are `if try_closed_universal_refutations(…)?`
/// and `if try_targeted_quantifier_refutations(…)?` — DELEGATED routes that run
/// before the instantiation loop and refute a quantifier directly, producing no
/// instances at all. An instance-set certificate for one of them would be empty,
/// and an empty certificate asserted as evidence is worse than no claim.
///
/// So the population is derived from the source rather than listed: an exit
/// whose guard calls a `try_…` helper is a delegated route and carries its own
/// evidence; every other exit refutes by the accumulated ground set and must
/// carry the instance-set certificate. Both counts are asserted below, so
/// neither a new delegated route nor a new loop exit can slip in unnoticed.
#[test]
fn every_instance_set_unsat_exit_assigns_a_certificate() {
    let body = function_body();
    let exits: Vec<usize> = body.match_indices(EXIT).map(|(i, _)| i).collect();
    let assigns: Vec<usize> = body.match_indices(ASSIGN).map(|(i, _)| i).collect();

    let mut delegated = Vec::new();
    let mut instance_set = Vec::new();
    for &exit in &exits {
        let window = &body[exit.saturating_sub(GUARD_WINDOW)..exit];
        if window.contains("if try_") {
            delegated.push(exit);
        } else {
            instance_set.push(exit);
        }
    }

    assert!(
        instance_set.len() >= 3,
        "only {} instance-set exits found; a suite that quantifies over fewer \
         than the three ADR-2124 counted is measuring almost nothing",
        instance_set.len()
    );
    assert!(
        !delegated.is_empty(),
        "no delegated exits found. Either the `try_…` routes were removed, or \
         the guard window no longer reaches their condition -- in which case \
         every delegated exit has silently joined the population above and this \
         suite is about to demand a certificate that would be empty"
    );

    let mut naked = Vec::new();
    for (index, &exit) in instance_set.iter().enumerate() {
        let previous = if index == 0 {
            0
        } else {
            instance_set[index - 1]
        };
        if !assigns.iter().any(|&a| a < exit && a >= previous) {
            let context = exit.saturating_sub(300);
            naked.push(format!(
                "instance-set exit #{index} at byte {exit} has no `{ASSIGN}` of \
                 its own; preceding context:\n...{}",
                &body[context..exit]
            ));
        }
    }

    assert!(
        naked.is_empty(),
        "{} of {} instance-set unsat exits return without assigning a \
         certificate ({} delegated exits excluded). ADR-2124 repaired exactly \
         this on the `CandidateFixpointStep::Refuted` exit and MEASURED that \
         nothing noticed the repair being removed; this suite is what \
         notices.\n\n{}",
        naked.len(),
        instance_set.len(),
        delegated.len(),
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
    let exit = after.find(EXIT).expect("the repaired exit returns Unsat");
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
