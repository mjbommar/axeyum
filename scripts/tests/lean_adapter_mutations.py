"""Fixtures for `scripts/tests/test-lean-adapter-mutations.sh`. One "good"
goal pack + result pair matching the real committed shape, and one "bad_*"
variant per guard in `scripts/check-lean-adapter.py` -- each bad fixture
changes ONLY what its own guard is meant to catch, keeping every other field
internally consistent, so a guard's removal cannot be rescued by an unrelated
check catching the same mutation by accident.
"""
from __future__ import annotations

import copy

REQUIRED_CATEGORIES = [
    "success",
    "unknown",
    "timeout",
    "unsupported",
    "malformed_response",
    "wrong_goal",
    "wrong_environment",
    "mutated_proof",
]


def good_goal_pack() -> dict:
    return {
        "goal_pack_id": "thin-adapter-v1",
        "required_categories": list(REQUIRED_CATEGORIES),
    }


def _outcome(category: str, verdict: str, reason, lean_invoked: bool) -> dict:
    return {
        "category": category,
        "expected_verdict": verdict,
        "observed_verdict": verdict,
        "reason": reason,
        "lean_invoked": lean_invoked,
    }


def good_result() -> dict:
    return {
        "schema_version": 1,
        "goal_pack_id": "thin-adapter-v1",
        "lean_version": "4.30.0",
        "lean_commit": "d024af099ca4bf2c86f649261ebf59565dc8c622",
        "outcomes": [
            _outcome("success", "accepted", None, True),
            _outcome("unknown", "declined", "unknown", False),
            _outcome("timeout", "declined", "timeout", False),
            _outcome("unsupported", "declined", "unsupported", False),
            _outcome("malformed_response", "declined", "malformed-response", False),
            _outcome("wrong_goal", "rejected", "wrong-goal", True),
            _outcome("wrong_environment", "rejected", "wrong-environment", False),
            _outcome("mutated_proof", "rejected", "mutated-proof", True),
        ],
    }


def good_live_identity() -> tuple[str, str]:
    return ("4.30.0", "d024af099ca4bf2c86f649261ebf59565dc8c622")


# ABSENCE: drop the wrong_goal outcome entirely.
def bad_absence_result() -> dict:
    result = copy.deepcopy(good_result())
    result["outcomes"] = [o for o in result["outcomes"] if o["category"] != "wrong_goal"]
    return result


# LEAN_ACTUALLY_RAN: every category claims lean_invoked=false, including the
# three that must actually invoke Lean.
def bad_lean_actually_ran_result() -> dict:
    result = copy.deepcopy(good_result())
    for outcome in result["outcomes"]:
        outcome["lean_invoked"] = False
    return result


# SUCCESS_ACCEPTED: success is graded (and internally consistent) as
# "declined" instead of "accepted" -- would sail past EXPECTED_MATCHES_OBSERVED
# because both fields were edited together.
def bad_success_accepted_result() -> dict:
    result = copy.deepcopy(good_result())
    for outcome in result["outcomes"]:
        if outcome["category"] == "success":
            outcome["expected_verdict"] = "declined"
            outcome["observed_verdict"] = "declined"
            outcome["reason"] = "unknown"
    return result


# MUTATIONS_REJECTED: mutated_proof is graded (internally consistently) as
# "accepted" -- the sidecar's forged proof would be credited.
def bad_mutations_rejected_result() -> dict:
    result = copy.deepcopy(good_result())
    for outcome in result["outcomes"]:
        if outcome["category"] == "mutated_proof":
            outcome["expected_verdict"] = "accepted"
            outcome["observed_verdict"] = "accepted"
            outcome["reason"] = None
    return result


# DECLINES_TYPED_NONVACUOUS: "unknown" is graded "declined" but with the
# WRONG reason string -- verdict matches, typed reason does not.
def bad_declines_typed_nonvacuous_result() -> dict:
    result = copy.deepcopy(good_result())
    for outcome in result["outcomes"]:
        if outcome["category"] == "unknown":
            outcome["reason"] = "something-else"
    return result


# EXPECTED_MATCHES_OBSERVED: wrong_environment's own expected/observed fields
# disagree with EACH OTHER (unlike the fixtures above, which keep the two in
# lockstep).
def bad_expected_matches_observed_result() -> dict:
    result = copy.deepcopy(good_result())
    for outcome in result["outcomes"]:
        if outcome["category"] == "wrong_environment":
            outcome["expected_verdict"] = "rejected"
            outcome["observed_verdict"] = "accepted"
    return result


# ENVIRONMENT_TOOLCHAIN_STALE: the result claims an older Lean commit than
# the live checked-interchange census.
def bad_environment_toolchain_stale_result() -> dict:
    result = copy.deepcopy(good_result())
    result["lean_commit"] = "0000000000000000000000000000000000000000"
    return result
