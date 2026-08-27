#!/usr/bin/env python3
"""Check the first unchanged-producer measurement over exported arrow goals."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/binomial-arrow-retrieved-induction-census-v1.json"
CAPABILITY = ROOT / "artifacts/autogenesis/binomial-arrow-export-capability-v1.json"
NURSERY = ROOT / "artifacts/autogenesis/nursery-v1.json"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def check(result: dict[str, Any], capability: dict[str, Any], root: Path = ROOT) -> None:
    require(
        result.get("kind") == "axeyum-open-ranked-transport-induction-census",
        "wrong measurement kind",
    )
    require(
        result.get("state") == "train-development-measurement-held-out-excluded",
        "measurement state drifted",
    )
    strategy = result.get("strategy", {})
    require(
        strategy.get("producer") == "bounded-induction-with-retrieved-rewrites", "producer changed"
    )
    require(strategy.get("native_candidate_transport") is True, "transport is not enabled")
    require(strategy.get("retrieved_induction") is True, "retrieved induction is not enabled")
    require(
        result.get("held_out_exclusion", {}).get("identities_redacted") is True,
        "held-out exclusion is absent",
    )

    source = result.get("source", {})
    cap_source = capability.get("source", {})
    require(
        source.get("mathlib_commit") == cap_source.get("mathlib_commit"),
        "Mathlib identity disagrees with export capability",
    )
    require(
        source.get("lean_version") == cap_source.get("lean_version"),
        "Lean identity disagrees with export capability",
    )
    require(
        source.get("lean4export_format") == cap_source.get("lean4export_version"),
        "export format disagrees with export capability",
    )
    capsule_dir = Path(source.get("external_capsule_directory", ""))
    require(
        capsule_dir == Path(cap_source["external_pack"]) / "streams",
        "measurement uses a different external pack",
    )
    require(
        source.get("mapping_sha256") == cap_source.get("mapping_sha256"),
        "mapping identity disagrees with export capability",
    )
    ranking = source.get("candidate_ranking", {})
    ranking_path = Path(ranking.get("path", ""))
    if not ranking_path.is_absolute():
        ranking_path = root / ranking_path
    require(
        ranking_path.is_file() and digest(ranking_path) == ranking.get("sha256"),
        "candidate ranking is absent or changed",
    )
    require(
        source.get("nursery_sha256") == digest(root / "artifacts/autogenesis/nursery-v1.json"),
        "nursery identity changed",
    )

    capability_rows = {row["fact_id"]: row for row in capability.get("rows", [])}
    outcomes = result.get("outcomes", [])
    require(len(outcomes) == len(capability_rows) == 3, "population is not the three arrow goals")
    reasons: dict[str, int] = {}
    for row in outcomes:
        fact_id = row.get("fact_id")
        require(fact_id in capability_rows, "measurement contains an unbound fact")
        expected = capability_rows[fact_id]
        require(
            row.get("target_definition") == expected.get("target_definition"),
            f"{fact_id} target changed",
        )
        require(
            row.get("capsule_sha256") == expected.get("measurement_stream_sha256"),
            f"{fact_id} capsule changed",
        )
        require(
            row.get("capsule_bytes") == expected.get("measurement_stream_bytes"),
            f"{fact_id} capsule size changed",
        )
        require(row.get("evaluation_class") == "positive-target", f"{fact_id} class changed")
        require(row.get("result") == "declined", f"{fact_id} was not an honest decline")
        reason = row.get("reason_kind")
        require(
            reason in {"TerminalNotDefEqNoRewrite", "NotEqualityGoal"},
            f"{fact_id} decline reason changed",
        )
        reasons[reason] = reasons.get(reason, 0) + 1
        require(
            isinstance(row.get("candidate_transport"), list),
            f"{fact_id} has no transport observations",
        )
    require(
        reasons == {"TerminalNotDefEqNoRewrite": 2, "NotEqualityGoal": 1},
        "decline decomposition changed",
    )

    census = result.get("census", {})
    require(census.get("population") == 3, "census population changed")
    require(census.get("accepted") == 0, "accepted count changed without regeneration")
    require(census.get("declined") == 3, "declined count changed")
    require(census.get("import_rejected") == 0, "arrow imports regressed")
    require(census.get("decline_reasons") == reasons, "census reasons disagree with outcomes")


def main() -> int:
    try:
        result = json.loads(RESULT.read_text())
        capability = json.loads(CAPABILITY.read_text())
        check(result, capability)
    except (OSError, ValueError, json.JSONDecodeError) as error:
        print(f"BINOMIAL_ARROW_MEASUREMENT_ERROR|{error}")
        return 1
    print(
        "BINOMIAL_ARROW_MEASUREMENT|population=3|imports=3|accepted=0|"
        "missing_composition=2|not_equality=1"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
