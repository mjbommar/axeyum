"""Small, fail-closed projections for parity evidence artifacts.

The historical SMT-COMP-style inventory intentionally follows competition
scoring and counts a definitive answer on a benchmark with unknown status as a
correct decision.  That is useful for scoring, but it is too coarse for a
soundness claim.  This module adds a read-only audit projection that keeps
known-status agreement and unadjudicated decisions separate.

It also computes decided-set overlap for paired benchmark artifacts.  Equal
solved counts are not decision parity when the solved sets differ.
"""

from __future__ import annotations

from collections.abc import Mapping
from typing import Any


DECISIONS = frozenset({"sat", "unsat"})
REPORTS = DECISIONS | {"unknown", None}


class ParityEvidenceError(ValueError):
    """Raised when an evidence artifact cannot support the requested audit."""


def audit_inventory_raw(
    raw: Mapping[str, Mapping[str, Mapping[str, Any]]],
    *,
    solver: str,
) -> dict[str, int]:
    """Partition one raw inventory without treating unknown status as truth.

    ``legacy_decided_correct`` is retained solely as a reconciliation field for
    the frozen inventory report.  The soundness-bearing fields are
    ``known_status_agreements`` and ``known_status_disagreements``.
    """

    counts = {
        "total": 0,
        "known_status_benchmarks": 0,
        "unknown_status_benchmarks": 0,
        "known_status_agreements": 0,
        "known_status_disagreements": 0,
        "unadjudicated_decisions": 0,
        "declines": 0,
        "no_answers": 0,
    }

    for benchmark, by_solver in raw.items():
        if solver not in by_solver:
            raise ParityEvidenceError(
                f"{benchmark}: missing requested solver result {solver!r}"
            )
        result = by_solver[solver]
        reported = result.get("reported_status")
        expected = result.get("expected_status")
        if reported not in REPORTS:
            raise ParityEvidenceError(f"{benchmark}: invalid reported status {reported!r}")
        if expected not in DECISIONS | {None, "unknown"}:
            raise ParityEvidenceError(f"{benchmark}: invalid expected status {expected!r}")

        counts["total"] += 1
        known = expected in DECISIONS
        counts["known_status_benchmarks" if known else "unknown_status_benchmarks"] += 1

        if reported is None:
            counts["no_answers"] += 1
        elif reported == "unknown":
            counts["declines"] += 1
        elif not known:
            counts["unadjudicated_decisions"] += 1
        elif reported == expected:
            counts["known_status_agreements"] += 1
        else:
            counts["known_status_disagreements"] += 1

    counts["legacy_decided_correct"] = (
        counts["known_status_agreements"] + counts["unadjudicated_decisions"]
    )
    partition = (
        counts["known_status_agreements"]
        + counts["known_status_disagreements"]
        + counts["unadjudicated_decisions"]
        + counts["declines"]
        + counts["no_answers"]
    )
    if partition != counts["total"]:
        raise ParityEvidenceError(
            f"inventory partition {partition} does not equal total {counts['total']}"
        )
    if (
        counts["known_status_benchmarks"] + counts["unknown_status_benchmarks"]
        != counts["total"]
    ):
        raise ParityEvidenceError("known/unknown-status partition does not equal total")
    return counts


def paired_decision_overlap(
    left: Mapping[str, Any],
    right: Mapping[str, Any],
) -> dict[str, int]:
    """Return exact decided-set overlap for two same-population artifacts."""

    def outcomes(artifact: Mapping[str, Any], label: str) -> dict[str, str]:
        instances = artifact.get("instances")
        if not isinstance(instances, list):
            raise ParityEvidenceError(f"{label}: instances must be a list")
        result: dict[str, str] = {}
        for instance in instances:
            benchmark = instance.get("file")
            outcome = instance.get("outcome")
            if not isinstance(benchmark, str) or not benchmark:
                raise ParityEvidenceError(f"{label}: instance has no stable file identity")
            if benchmark in result:
                raise ParityEvidenceError(f"{label}: duplicate file {benchmark}")
            if outcome not in DECISIONS | {"unknown", "unsupported", "error"}:
                raise ParityEvidenceError(
                    f"{label}: invalid outcome {outcome!r} for {benchmark}"
                )
            result[benchmark] = outcome
        return result

    left_outcomes = outcomes(left, "left")
    right_outcomes = outcomes(right, "right")
    if set(left_outcomes) != set(right_outcomes):
        missing_left = sorted(set(right_outcomes) - set(left_outcomes))
        missing_right = sorted(set(left_outcomes) - set(right_outcomes))
        raise ParityEvidenceError(
            "paired populations differ: "
            f"missing_left={missing_left[:1]} missing_right={missing_right[:1]}"
        )

    left_decided = {key for key, value in left_outcomes.items() if value in DECISIONS}
    right_decided = {key for key, value in right_outcomes.items() if value in DECISIONS}
    both = left_decided & right_decided
    disagreements = sum(left_outcomes[key] != right_outcomes[key] for key in both)
    return {
        "total": len(left_outcomes),
        "left_decided": len(left_decided),
        "right_decided": len(right_decided),
        "both_decided": len(both),
        "left_only_decided": len(left_decided - right_decided),
        "right_only_decided": len(right_decided - left_decided),
        "neither_decided": len(set(left_outcomes) - (left_decided | right_decided)),
        "both_decided_disagreements": disagreements,
    }
