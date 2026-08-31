#!/usr/bin/env python3
"""Gate: validate `artifacts/lean-adapter/results/*.result.json` (L4 phase C3,
docs/plan/library-artifact-compatibility-roadmap-2026-08-30.md).

C3 asks for a small Lean adapter that receives an already-elaborated goal
plus environment identity, calls Axeyum as a sidecar, and returns a
proof/certificate Lean itself checks -- never trusting Axeyum's own verdict.
Its exit criterion: a preregistered goal pack covers success, unknown,
timeout, unsupported, malformed response, wrong goal, wrong environment, and
mutated proof; every success is accepted by Lean and every mutation rejects.

`crates/axeyum-lean-import/tests/thin_lean_adapter_goal_pack.rs` drives the
real pipeline (`axeyum_lean_import::thin_adapter`'s grading logic, real
pinned Lean via `scripts/lean/replay-lean4export.lean`, and a real
independent `import_ndjson` reimport) against one real goal
(`Nat.add_comm`, a C2 credited root) and writes the committed result this
script validates. This script needs NO Lean toolchain and NO cargo run,
matching `check-checked-interchange.py`'s own posture.

Seven guards, seven distinct mutation classes, each mutation-verified to be
killed by exactly one fixture
(`scripts/tests/test-lean-adapter-mutations.sh`):

  ABSENCE                the result's outcome categories do not cover every
                          category the goal pack requires -- an empty or
                          partial population is a failure, not a pass over
                          nothing
  LEAN_ACTUALLY_RAN       none of the categories the goal pack marks as
                          needing a real Lean invocation actually recorded
                          lean_invoked=true -- proves the adapter did not
                          grade everything from the envelope alone
  SUCCESS_ACCEPTED        the success category's own observed_verdict is not
                          literally "accepted" -- checked against a hardcoded
                          requirement, never merely against the artifact's
                          own expected_verdict field
  MUTATIONS_REJECTED      wrong_goal / wrong_environment / mutated_proof do
                          not each have observed_verdict=="rejected" --
                          hardcoded, not merely internally consistent
  DECLINES_TYPED_NONVACUOUS  unknown / timeout / unsupported /
                          malformed_response do not each have
                          observed_verdict=="declined" with the SPECIFIC
                          typed reason the exit criterion names -- proves
                          the decline path was actually exercised per
                          category, not read as a blanket success
  EXPECTED_MATCHES_OBSERVED  some outcome's observed_verdict disagrees with
                          its own expected_verdict field -- internal
                          consistency
  ENVIRONMENT_TOOLCHAIN_STALE  the result's lean_version/lean_commit disagree
                          with the LIVE checked-interchange census file's own
                          lean_version/lean_commit -- external authority the
                          result does not control, mirroring
                          check-checked-interchange.py's STALE_POPULATION
                          guard

Usage:
    python3 scripts/check-lean-adapter.py
    python3 scripts/check-lean-adapter.py --results-dir DIR --goal-pack-dir DIR
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_RESULTS_DIR = REPO_ROOT / "artifacts" / "lean-adapter" / "results"
DEFAULT_GOAL_PACK_DIR = REPO_ROOT / "artifacts" / "lean-adapter" / "goal-pack"
DEFAULT_CHECKED_INTERCHANGE_CENSUS_DIR = (
    REPO_ROOT / "artifacts" / "checked-interchange" / "census"
)

# Hardcoded per the exit criterion -- never read from the artifact's own
# fields, so a mutation that edits both the outcome AND its own "expected"
# label in lockstep still fails.
REQUIRED_VERDICT_BY_CATEGORY = {
    "success": "accepted",
    "unknown": "declined",
    "timeout": "declined",
    "unsupported": "declined",
    "malformed_response": "declined",
    "wrong_goal": "rejected",
    "wrong_environment": "rejected",
    "mutated_proof": "rejected",
}
REQUIRED_REASON_BY_CATEGORY = {
    "unknown": "unknown",
    "timeout": "timeout",
    "unsupported": "unsupported",
    "malformed_response": "malformed-response",
    "wrong_goal": "wrong-goal",
    "wrong_environment": "wrong-environment",
    "mutated_proof": "mutated-proof",
}
MUST_INVOKE_LEAN = ("success", "wrong_goal", "mutated_proof")


def load_json(path: Path):
    with open(path, "r", encoding="utf-8") as fh:
        return json.load(fh)


def live_checked_interchange_identity(census_dir: Path) -> tuple[str, str] | None:
    """The (lean_version, lean_commit) the LIVE checked-interchange census
    files say pinned Lean is -- never read from this gate's own snapshot.
    Returns None if no census file exists (staleness cannot be judged)."""
    for census_path in sorted(census_dir.glob("*.census.json")):
        census = load_json(census_path)
        version = census.get("lean_version")
        commit = census.get("lean_commit")
        if version and commit:
            return (version, commit)
    return None


# GUARD:ABSENCE begin
def check_absence(goal_pack: dict, result: dict) -> list[str]:
    required = set(goal_pack.get("required_categories", []))
    if not required:
        return ["ABSENCE: goal pack names zero required_categories"]
    observed = {o.get("category") for o in result.get("outcomes", [])}
    missing = required - observed
    if missing:
        return [
            f"ABSENCE: required categories {sorted(missing)} have no outcome "
            "in the result -- an absent category is a failure, not a pass "
            "over nothing"
        ]
    return []
# GUARD:ABSENCE end


# GUARD:LEAN_ACTUALLY_RAN begin
def check_lean_actually_ran(result: dict) -> list[str]:
    outcomes = {o.get("category"): o for o in result.get("outcomes", [])}
    invoked = [c for c in MUST_INVOKE_LEAN if outcomes.get(c, {}).get("lean_invoked") is True]
    if not invoked:
        return [
            "LEAN_ACTUALLY_RAN: none of "
            f"{list(MUST_INVOKE_LEAN)} recorded lean_invoked=true -- the "
            "adapter must actually submit a stream to pinned Lean for at "
            "least one of these categories, or nothing was checked"
        ]
    return []
# GUARD:LEAN_ACTUALLY_RAN end


# GUARD:SUCCESS_ACCEPTED begin
def check_success_accepted(result: dict) -> list[str]:
    for outcome in result.get("outcomes", []):
        if outcome.get("category") == "success":
            if outcome.get("observed_verdict") != "accepted":
                return [
                    "SUCCESS_ACCEPTED: the success category's observed_verdict "
                    f"is {outcome.get('observed_verdict')!r}, not 'accepted'"
                ]
            return []
    return ["SUCCESS_ACCEPTED: no 'success' category outcome present"]
# GUARD:SUCCESS_ACCEPTED end


# GUARD:MUTATIONS_REJECTED begin
def check_mutations_rejected(result: dict) -> list[str]:
    failures = []
    outcomes = {o.get("category"): o for o in result.get("outcomes", [])}
    for category in ("wrong_goal", "wrong_environment", "mutated_proof"):
        outcome = outcomes.get(category)
        if outcome is None:
            failures.append(f"MUTATIONS_REJECTED: no {category!r} category outcome present")
            continue
        if outcome.get("observed_verdict") != "rejected":
            failures.append(
                f"MUTATIONS_REJECTED: {category!r} observed_verdict is "
                f"{outcome.get('observed_verdict')!r}, not 'rejected' -- C3's exit "
                "criterion is that every mutation rejects"
            )
    return failures
# GUARD:MUTATIONS_REJECTED end


# GUARD:DECLINES_TYPED_NONVACUOUS begin
def check_declines_typed_nonvacuous(result: dict) -> list[str]:
    failures = []
    outcomes = {o.get("category"): o for o in result.get("outcomes", [])}
    for category in ("unknown", "timeout", "unsupported", "malformed_response"):
        outcome = outcomes.get(category)
        if outcome is None:
            failures.append(f"DECLINES_TYPED_NONVACUOUS: no {category!r} category outcome present")
            continue
        if outcome.get("observed_verdict") != "declined":
            failures.append(
                f"DECLINES_TYPED_NONVACUOUS: {category!r} observed_verdict is "
                f"{outcome.get('observed_verdict')!r}, not 'declined'"
            )
            continue
        expected_reason = REQUIRED_REASON_BY_CATEGORY[category]
        if outcome.get("reason") != expected_reason:
            failures.append(
                f"DECLINES_TYPED_NONVACUOUS: {category!r} reason is "
                f"{outcome.get('reason')!r}, expected {expected_reason!r} -- a "
                "decline that never shows its typed reason is not a decline "
                "path, it is a label"
            )
    return failures
# GUARD:DECLINES_TYPED_NONVACUOUS end


# GUARD:EXPECTED_MATCHES_OBSERVED begin
def check_expected_matches_observed(result: dict) -> list[str]:
    failures = []
    for outcome in result.get("outcomes", []):
        category = outcome.get("category")
        expected = REQUIRED_VERDICT_BY_CATEGORY.get(category)
        if expected is None:
            continue
        if outcome.get("expected_verdict") != outcome.get("observed_verdict"):
            failures.append(
                f"EXPECTED_MATCHES_OBSERVED: {category!r} expected_verdict="
                f"{outcome.get('expected_verdict')!r} but observed_verdict="
                f"{outcome.get('observed_verdict')!r}"
            )
    return failures
# GUARD:EXPECTED_MATCHES_OBSERVED end


# GUARD:ENVIRONMENT_TOOLCHAIN_STALE begin
def check_environment_toolchain_stale(
    result: dict, live_identity: tuple[str, str] | None
) -> list[str]:
    if live_identity is None:
        return [
            "ENVIRONMENT_TOOLCHAIN_STALE: no checked-interchange census file "
            "carries a lean_version/lean_commit -- cannot verify this "
            "result's toolchain identity against a live authority"
        ]
    live_version, live_commit = live_identity
    if (result.get("lean_version"), result.get("lean_commit")) != (live_version, live_commit):
        return [
            "ENVIRONMENT_TOOLCHAIN_STALE: this result's lean_version/"
            f"lean_commit ({result.get('lean_version')!r}, "
            f"{result.get('lean_commit')!r}) disagrees with the LIVE "
            f"checked-interchange census ({live_version!r}, {live_commit!r}) "
            "-- regenerate this artifact against the current pinned toolchain"
        ]
    return []
# GUARD:ENVIRONMENT_TOOLCHAIN_STALE end


def run_all_guards(
    goal_pack: dict, result: dict, live_identity: tuple[str, str] | None
) -> list[str]:
    failures: list[str] = []
    failures += check_absence(goal_pack, result)
    failures += check_lean_actually_ran(result)
    failures += check_success_accepted(result)
    failures += check_mutations_rejected(result)
    failures += check_declines_typed_nonvacuous(result)
    failures += check_expected_matches_observed(result)
    failures += check_environment_toolchain_stale(result, live_identity)
    return failures


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--results-dir", type=Path, default=DEFAULT_RESULTS_DIR)
    parser.add_argument("--goal-pack-dir", type=Path, default=DEFAULT_GOAL_PACK_DIR)
    parser.add_argument(
        "--checked-interchange-census-dir",
        type=Path,
        default=DEFAULT_CHECKED_INTERCHANGE_CENSUS_DIR,
    )
    args = parser.parse_args()

    result_files = sorted(args.results_dir.glob("*.result.json"))
    if not result_files:
        print(
            f"NO RESULT FILES found under {args.results_dir} -- an absent "
            "artifact is a failure, not a clean pass over nothing",
            file=sys.stderr,
        )
        return 1

    live_identity = live_checked_interchange_identity(args.checked_interchange_census_dir)

    total_failures: list[str] = []
    checked = 0
    for result_path in result_files:
        result = load_json(result_path)
        goal_pack_id = result.get("goal_pack_id")
        if not goal_pack_id:
            total_failures.append(f"{result_path}: no goal_pack_id field")
            continue
        goal_pack_path = args.goal_pack_dir / f"{goal_pack_id}.json"
        if not goal_pack_path.is_file():
            total_failures.append(
                f"{result_path}: goal pack file {goal_pack_path} does not exist"
            )
            continue
        goal_pack = load_json(goal_pack_path)
        failures = run_all_guards(goal_pack, result, live_identity)
        if failures:
            total_failures.append(f"{result_path}:")
            total_failures.extend(f"  {f}" for f in failures)
        else:
            outcomes = result.get("outcomes", [])
            accepted = sum(1 for o in outcomes if o.get("observed_verdict") == "accepted")
            declined = sum(1 for o in outcomes if o.get("observed_verdict") == "declined")
            rejected = sum(1 for o in outcomes if o.get("observed_verdict") == "rejected")
            print(
                f"OK {result_path.name}: categories={len(outcomes)} "
                f"accepted={accepted} declined={declined} rejected={rejected}"
            )
        checked += 1

    if checked == 0:
        print("ZERO result files examined -- refusing to report a pass over nothing", file=sys.stderr)
        return 1

    if total_failures:
        print("LEAN-ADAPTER GATE FAILED:", file=sys.stderr)
        for line in total_failures:
            print(line, file=sys.stderr)
        return 1

    print(f"LEAN-ADAPTER GATE PASSED -- {checked} result file(s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
