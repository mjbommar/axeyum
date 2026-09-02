//! **L4 phase C3 — the thin Lean adapter's protocol and grading logic.**
//!
//! `docs/plan/library-artifact-compatibility-roadmap-2026-08-30.md` section C3
//! asks for "a small Lean command/tactic adapter that receives an already
//! elaborated goal plus environment identity, calls Axeyum as a
//! sidecar/library, and returns a proof/certificate that Lean itself checks.
//! It must not trust Axeyum's verdict or add an axiom."
//!
//! This module is deliberately the ONLY new translation logic C3 adds. Every
//! actual proof-checking step is composed from what C2 (ADR-0915) already
//! built and proved sound: `Kernel::render_lean4export_ndjson_roots` for
//! export, `axeyum_lean_import::import_ndjson` for the fresh independent
//! reimport, and `scripts/lean/replay-lean4export.lean` for submission to
//! pinned Lean's own kernel. C3's job is the glue around a goal request and a
//! sidecar response that C2 never needed: environment-identity binding and a
//! typed decline/malformed-response protocol. If this file ever grows into a
//! second parser or a second closure-computation, that is the sign called out
//! in this lane's brief to stop and route through the existing artifact
//! contract instead.
//!
//! # The protocol
//!
//! A [`GoalDescriptor`] names an already-elaborated goal: a declaration name,
//! its rendered type (as `Kernel::render_lean` printed it), and the
//! environment identity the sidecar's response is expected to match. The
//! sidecar (Axeyum, called as a library) answers with a [`SidecarResponse`]:
//! either `accepted` (carrying its own claimed environment identity and a
//! path to an NDJSON stream) or `declined` (carrying a typed reason). Nothing
//! else parses — an adapter that understood more shapes than this would be
//! trusting more of the sidecar's own framing than C3 permits.
//!
//! # Grading, in two stages
//!
//! [`pre_lean_verdict`] decides everything that does NOT require asking Lean
//! anything: a malformed envelope, an unrecognized status or decline reason,
//! and an environment-identity mismatch are all decided from the response
//! bytes and the goal alone. Only a syntactically well-formed `accepted`
//! response whose environment identity matches goes on to
//! [`PreLeanStage::NeedsLeanCheck`], the signal that the caller must now
//! actually run the two independent paths and finish grading with
//! [`decide_after_lean`].
//!
//! [`decide_after_lean`] never trusts the sidecar's self-reported success.
//! It asks exactly the two questions ADR-0915 already answers for C2's
//! credited roots: did pinned Lean's kernel accept the stream at all, and —
//! if so — does pinned Lean's own `env.constants` hold a constant of the
//! goal's exact name whose independently-reimported type renders
//! byte-identically to the goal's expected type? A stream Lean's kernel
//! rejects outright is graded `mutated-proof` (the proof term itself did not
//! check); a stream Lean accepts but that does not establish the goal by
//! name and type is graded `wrong-goal` (the sidecar answered a different,
//! separately-valid question). Neither grading step adds an axiom or asks
//! the kernel to trust anything the adapter itself asserts.

use std::collections::BTreeSet;

use serde_json::Value;

/// An already-elaborated goal: the sidecar is asked to prove exactly this
/// name has exactly this rendered type, inside exactly this environment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GoalDescriptor {
    /// The declaration name the sidecar is asked to establish.
    pub name: String,
    /// The goal's type, rendered via `Kernel::render_lean` -- the
    /// already-elaborated form the sidecar must reproduce.
    pub expected_type: String,
    /// The environment identity (Lean version, commit, population) the
    /// sidecar's response must match before its stream is even read.
    pub environment_id: String,
}

/// The sidecar's response envelope. This is deliberately the ENTIRE
/// vocabulary the adapter understands -- anything that does not parse into
/// one of these two shapes is a malformed response, never a crash and never
/// a silent accept.
///
/// Parsed by hand from a [`Value`] (`parse_response`) rather than through a
/// derive: this crate already depends on `serde_json` for the NDJSON reader
/// and nothing else here needs a second serde dependency for two fields.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SidecarResponse {
    /// The sidecar claims to have established the goal.
    Accepted {
        /// The environment identity the sidecar claims to have worked in.
        environment_id: String,
        /// Path to the NDJSON closure the sidecar claims establishes the
        /// goal.
        stream_path: String,
    },
    /// The sidecar declined, carrying a typed reason.
    Declined {
        /// The decline reason string, checked against
        /// [`KNOWN_DECLINE_REASONS`] before being treated as genuine.
        reason: String,
    },
}

/// Parse the response envelope from a [`Value`]. Anything that is not an
/// object with a recognized `"status"` field and the fields that status
/// requires returns `Err` -- never a panic, and never a default variant that
/// would let an unrecognized shape read as a decision.
fn parse_response(value: &Value) -> Result<SidecarResponse, String> {
    let object = value
        .as_object()
        .ok_or_else(|| "response is not a JSON object".to_owned())?;
    let status = object
        .get("status")
        .and_then(Value::as_str)
        .ok_or_else(|| "response has no string \"status\" field".to_owned())?;
    match status {
        "accepted" => {
            let environment_id = object
                .get("environment_id")
                .and_then(Value::as_str)
                .ok_or_else(|| "accepted response has no \"environment_id\"".to_owned())?
                .to_owned();
            let stream_path = object
                .get("stream_path")
                .and_then(Value::as_str)
                .ok_or_else(|| "accepted response has no \"stream_path\"".to_owned())?
                .to_owned();
            Ok(SidecarResponse::Accepted {
                environment_id,
                stream_path,
            })
        }
        "declined" => {
            let reason = object
                .get("reason")
                .and_then(Value::as_str)
                .ok_or_else(|| "declined response has no \"reason\"".to_owned())?
                .to_owned();
            Ok(SidecarResponse::Declined { reason })
        }
        other => Err(format!("unrecognized status {other:?}")),
    }
}

/// The only decline reasons the adapter recognizes as genuine sidecar
/// declines. A `declined` response carrying anything else is treated as
/// malformed -- the adapter must not silently invent a category the sidecar
/// did not actually name.
pub const KNOWN_DECLINE_REASONS: &[&str] = &["unknown", "timeout", "unsupported"];

/// The reason string this module always uses for an envelope-level failure:
/// bytes that do not parse as JSON, JSON that does not match either
/// [`SidecarResponse`] variant, or a `declined` reason outside
/// [`KNOWN_DECLINE_REASONS`].
pub const MALFORMED_RESPONSE: &str = "malformed-response";
/// The rejection reason for an `accepted` response whose `environment_id`
/// does not match the goal's.
pub const WRONG_ENVIRONMENT: &str = "wrong-environment";
/// The rejection reason for a stream pinned Lean accepts that does not
/// establish the requested goal by name and type.
pub const WRONG_GOAL: &str = "wrong-goal";
/// The rejection reason for a stream pinned Lean's own kernel rejects
/// outright.
pub const MUTATED_PROOF: &str = "mutated-proof";

/// The adapter's final verdict on one goal request. Every variant is a
/// distinct, printable outcome -- there is no fourth "something went wrong"
/// bucket that would let an unclassified failure hide.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AdapterVerdict {
    /// Pinned Lean's own kernel admitted a constant of the goal's exact name
    /// whose independently-reimported type matches the goal's expected type
    /// byte-for-byte.
    Accepted,
    /// The sidecar declined by a recognized typed reason, or its response
    /// could not be understood at all (folded into `malformed-response`).
    Declined(String),
    /// The sidecar claimed success but the result does not actually
    /// establish the requested goal: wrong environment, wrong goal, or a
    /// proof pinned Lean's kernel itself rejected.
    Rejected(String),
}

impl AdapterVerdict {
    /// The coarse outcome tag used in the committed result artifact and in
    /// this module's own doc comments: `"accepted"`, `"declined"`, or
    /// `"rejected"`.
    #[must_use]
    pub fn tag(&self) -> &'static str {
        match self {
            AdapterVerdict::Accepted => "accepted",
            AdapterVerdict::Declined(_) => "declined",
            AdapterVerdict::Rejected(_) => "rejected",
        }
    }

    /// The typed reason, if this verdict carries one (every variant except
    /// `Accepted`).
    #[must_use]
    pub fn reason(&self) -> Option<&str> {
        match self {
            AdapterVerdict::Accepted => None,
            AdapterVerdict::Declined(reason) | AdapterVerdict::Rejected(reason) => {
                Some(reason.as_str())
            }
        }
    }
}

/// What [`pre_lean_verdict`] found before any Lean invocation: either a final
/// verdict (nothing further to check), or a signal that the caller must now
/// run the two independent paths (fresh reimport + pinned Lean replay)
/// against the named stream before grading can finish.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PreLeanStage {
    /// Nothing further to check -- the caller should report this verdict
    /// as-is, without invoking Lean.
    Final(AdapterVerdict),
    /// The response is a syntactically well-formed, environment-matching
    /// `accepted`; the caller must now replay `stream_path` through both
    /// independent paths and finish grading with [`decide_after_lean`].
    NeedsLeanCheck {
        /// Path to the NDJSON stream the caller must now replay.
        stream_path: String,
    },
}

/// Stage 1: decide everything answerable from the response bytes and the
/// goal alone, without asking Lean anything.
///
/// This function alone is a complete, Lean-free unit under test for four of
/// C3's eight required outcome categories (`unknown`, `timeout`,
/// `unsupported`, `malformed-response`) plus the environment-identity half
/// of a fifth (`wrong-environment`) -- the remaining categories all need a
/// real Lean invocation and are finished by [`decide_after_lean`].
#[must_use]
pub fn pre_lean_verdict(goal: &GoalDescriptor, raw_response: &[u8]) -> PreLeanStage {
    let value: Value = match serde_json::from_slice(raw_response) {
        Ok(value) => value,
        Err(_) => return PreLeanStage::Final(AdapterVerdict::Declined(MALFORMED_RESPONSE.into())),
    };
    let Ok(response) = parse_response(&value) else {
        return PreLeanStage::Final(AdapterVerdict::Declined(MALFORMED_RESPONSE.into()));
    };
    match response {
        SidecarResponse::Declined { reason } => {
            if KNOWN_DECLINE_REASONS.contains(&reason.as_str()) {
                PreLeanStage::Final(AdapterVerdict::Declined(reason))
            } else {
                PreLeanStage::Final(AdapterVerdict::Declined(MALFORMED_RESPONSE.into()))
            }
        }
        SidecarResponse::Accepted {
            environment_id,
            stream_path,
        } => {
            if environment_id == goal.environment_id {
                PreLeanStage::NeedsLeanCheck { stream_path }
            } else {
                PreLeanStage::Final(AdapterVerdict::Rejected(WRONG_ENVIRONMENT.into()))
            }
        }
    }
}

/// Stage 2: finish grading a stream that passed the environment-identity
/// check, using exactly the two facts ADR-0915 already established are
/// necessary and sufficient for credit -- never the sidecar's own framing.
///
/// * `lean_accepted_stream` -- did pinned Lean's kernel (via
///   `scripts/lean/replay-lean4export.lean`) accept every declaration record
///   in the stream? `false` means the proof term itself did not check:
///   graded `mutated-proof`.
/// * `admitted` -- the constant names pinned Lean's OWN `env.constants` held
///   afterward (never the transmitted stream's own claims).
/// * `reimported_type_matches` -- `Some(true)` when the goal's name is
///   present in `admitted` AND the type rebuilt by an independently
///   reimported `Kernel` renders identically to `goal.expected_type`;
///   `Some(false)` when the name is present but the type disagrees; `None`
///   when the name was never present.
#[must_use]
pub fn decide_after_lean(
    goal: &GoalDescriptor,
    lean_accepted_stream: bool,
    admitted: &BTreeSet<String>,
    reimported_type_matches: Option<bool>,
) -> AdapterVerdict {
    if !lean_accepted_stream {
        return AdapterVerdict::Rejected(MUTATED_PROOF.into());
    }
    if !admitted.contains(&goal.name) {
        return AdapterVerdict::Rejected(WRONG_GOAL.into());
    }
    match reimported_type_matches {
        Some(true) => AdapterVerdict::Accepted,
        Some(false) | None => AdapterVerdict::Rejected(WRONG_GOAL.into()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn goal() -> GoalDescriptor {
        GoalDescriptor {
            name: "Nat.add_comm".to_owned(),
            expected_type: "∀ (a b : AxNat), Eq (AxNat.add a b) (AxNat.add b a)".to_owned(),
            environment_id: "lean-4.30.0@d024af09:credited-roots-v1".to_owned(),
        }
    }

    #[test]
    fn a_declined_response_with_a_known_reason_is_final_and_untouched() {
        let raw = br#"{"status":"declined","reason":"unknown"}"#;
        assert_eq!(
            pre_lean_verdict(&goal(), raw),
            PreLeanStage::Final(AdapterVerdict::Declined("unknown".into()))
        );
    }

    #[test]
    fn a_declined_response_with_an_unrecognized_reason_is_malformed() {
        let raw = br#"{"status":"declined","reason":"bogus"}"#;
        assert_eq!(
            pre_lean_verdict(&goal(), raw),
            PreLeanStage::Final(AdapterVerdict::Declined(MALFORMED_RESPONSE.into()))
        );
    }

    #[test]
    fn bytes_that_do_not_parse_as_json_are_malformed_not_a_panic() {
        let raw = b"{not-json";
        assert_eq!(
            pre_lean_verdict(&goal(), raw),
            PreLeanStage::Final(AdapterVerdict::Declined(MALFORMED_RESPONSE.into()))
        );
    }

    #[test]
    fn an_accepted_response_with_the_wrong_environment_id_is_rejected_before_any_lean_check() {
        let raw = br#"{"status":"accepted","environment_id":"wrong","stream_path":"x.ndjson"}"#;
        assert_eq!(
            pre_lean_verdict(&goal(), raw),
            PreLeanStage::Final(AdapterVerdict::Rejected(WRONG_ENVIRONMENT.into()))
        );
    }

    #[test]
    fn an_accepted_response_with_the_right_environment_id_needs_a_lean_check() {
        let raw = br#"{"status":"accepted","environment_id":"lean-4.30.0@d024af09:credited-roots-v1","stream_path":"x.ndjson"}"#;
        assert_eq!(
            pre_lean_verdict(&goal(), raw),
            PreLeanStage::NeedsLeanCheck {
                stream_path: "x.ndjson".to_owned()
            }
        );
    }

    #[test]
    fn a_stream_lean_rejects_outright_is_a_mutated_proof() {
        let admitted = BTreeSet::new();
        assert_eq!(
            decide_after_lean(&goal(), false, &admitted, None),
            AdapterVerdict::Rejected(MUTATED_PROOF.into())
        );
    }

    #[test]
    fn a_stream_lean_accepts_but_never_names_the_goal_is_wrong_goal() {
        let mut admitted = BTreeSet::new();
        admitted.insert("Nat.le_refl".to_owned());
        assert_eq!(
            decide_after_lean(&goal(), true, &admitted, None),
            AdapterVerdict::Rejected(WRONG_GOAL.into())
        );
    }

    #[test]
    fn a_stream_that_names_the_goal_with_a_different_type_is_wrong_goal() {
        let mut admitted = BTreeSet::new();
        admitted.insert(goal().name);
        assert_eq!(
            decide_after_lean(&goal(), true, &admitted, Some(false)),
            AdapterVerdict::Rejected(WRONG_GOAL.into())
        );
    }

    #[test]
    fn a_stream_lean_accepts_that_names_the_goal_with_the_matching_type_is_accepted() {
        let mut admitted = BTreeSet::new();
        admitted.insert(goal().name);
        assert_eq!(
            decide_after_lean(&goal(), true, &admitted, Some(true)),
            AdapterVerdict::Accepted
        );
    }
}
