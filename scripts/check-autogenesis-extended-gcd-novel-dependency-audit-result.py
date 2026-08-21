#!/usr/bin/env python3
"""Verify the sealed xgcd frontier and clean gcd induction interface."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/extended-gcd-novel-dependency-audit-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/extended-gcd-novel-dependency-audit-plan-v1.json"
PACK = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/reference-packs/"
    "609241d91-extended-gcd-novel-dependency-audit-v1"
)
MANIFEST = PACK / "manifest.json"
AUDIT = PACK / "audit-result.json"
RESULT_SHA256 = "15ae23fb0107b76e59905eb2c58f8988db45a406f1e8cc178fb24ec704fa1cb9"
PLAN_SHA256 = "a64cf595b6eccb6620b3e932c461ec1af7699a5efe28fcf79025e47d18b3e0b1"
MANIFEST_SHA256 = "a5ea914683ec2bcc626e721d0ec0b7f1daed22867c6814e8a1ba6aaf58d0439a"


class ExtendedGcdNovelDependencyAuditResultError(RuntimeError):
    """The measured split, clean induction seam, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise ExtendedGcdNovelDependencyAuditResultError(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    canonical = load(RESULT)
    if sha256(RESULT) != RESULT_SHA256:
        raise ExtendedGcdNovelDependencyAuditResultError("tracked result identity changed")
    result = canonical if result is None else result
    if result != canonical:
        raise ExtendedGcdNovelDependencyAuditResultError("measured novel result changed")
    if (
        result.get("kind")
        != "axeyum-autogenesis-extended-gcd-novel-dependency-audit-result"
        or result.get("state")
        != "imported-xgcd-route-closed-clean-gcd-induction-retained-for-target-owned-reconstruction"
        or sha256(PLAN) != PLAN_SHA256
        or stat.S_IMODE(PACK.stat().st_mode) != 0o555
        or stat.S_IMODE(MANIFEST.stat().st_mode) != 0o444
        or sha256(MANIFEST) != MANIFEST_SHA256
    ):
        raise ExtendedGcdNovelDependencyAuditResultError("result producer or pack changed")
    for name, size, digest in [
        ("audit-result.json", 7_358, "17f8a867e95965da37468c46f29c95b6b03770f9375b5d92081ba001e167639d"),
        ("audit.stderr", 0, "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
    ]:
        path = PACK / name
        if (
            stat.S_IMODE(path.stat().st_mode) != 0o444
            or path.stat().st_size != size
            or sha256(path) != digest
        ):
            raise ExtendedGcdNovelDependencyAuditResultError(f"{name} changed")
    audit = load(AUDIT)
    if (
        audit.get("rendered_material")
        != {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0}
        or audit.get("summary")
        != {
            "all_roots_empty": False,
            "class_counts": {
                "empty-footprint": 6,
                "other-assumption-bearing": 1,
                "propext-bearing": 10,
            },
            "population": 17,
        }
    ):
        raise ExtendedGcdNovelDependencyAuditResultError("batch measurement changed")
    expected_classes = {
        "empty_footprint": [
            row["name"] for row in audit["rows"] if row["class"] == "empty-footprint"
        ],
        "other_assumption_bearing": [
            row["name"]
            for row in audit["rows"]
            if row["class"] == "other-assumption-bearing"
        ],
        "propext_bearing": [
            row["name"] for row in audit["rows"] if row["class"] == "propext-bearing"
        ],
    }
    if result.get("classifications") != expected_classes:
        raise ExtendedGcdNovelDependencyAuditResultError("classification split changed")
    rows = {row["name"]: row for row in audit["rows"]}
    terminal = rows["Nat.xgcd.eq_1"]
    clean_induction = rows["Nat.gcd.induction"]
    if (
        result.get("terminal_projection_equation")
        != {
            "name": terminal["name"],
            "declaration_sha256": terminal["declaration_sha256"],
            "axiom_footprint": terminal["axiom_footprint"],
            "direct_theorem_dependencies": terminal["direct_theorem_dependencies"],
        }
        or terminal["axiom_footprint"] != ["propext"]
        or terminal["direct_theorem_dependencies"] != []
        or result.get("clean_induction_interface")
        != {
            "name": clean_induction["name"],
            "declaration_sha256": clean_induction["declaration_sha256"],
            "axiom_footprint": clean_induction["axiom_footprint"],
            "direct_theorem_dependencies": clean_induction[
                "direct_theorem_dependencies"
            ],
        }
        or clean_induction["axiom_footprint"] != []
        or clean_induction["direct_theorem_dependencies"]
        != ["Nat.mod_lt", "Nat.succ_pos"]
    ):
        raise ExtendedGcdNovelDependencyAuditResultError(
            "terminal projection or clean induction seam changed"
        )
    if result.get("summary") != {
        "population": 17,
        "empty_footprint": 6,
        "other_assumption_bearing": 1,
        "propext_bearing": 10,
        "imported_xgcd_route_open": False,
        "target_owned_projection_replacement_required": True,
        "clean_nat_gcd_induction_available": True,
        "target_owned_reconstruction_authorized": False,
    }:
        raise ExtendedGcdNovelDependencyAuditResultError("route decision changed")
    if result.get("budget") != {
        "exporter_invocations": 0,
        "batch_importer_runs": 1,
        "proof_bearing_stream_reads": 1,
        "retries": 0,
        "reconstruction_source_compilations": 0,
        "new_theorem_submissions": 0,
        "exact_target_submissions": 0,
        "executor_invocations": 0,
    } or result.get("authority") != {
        "proof_terms_rendered": 0,
        "theorem_types_rendered": 0,
        "theorem_values_rendered": 0,
        "support_theorem_credit": 0,
        "fact_status_changes": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }:
        raise ExtendedGcdNovelDependencyAuditResultError("no-credit authority changed")
    return result


def main() -> int:
    try:
        validate()
        print(
            "AUTOGENESIS_EXTENDED_GCD_NOVEL_DEPENDENCY_AUDIT_RESULT_OK|"
            "roots=17|empty=6|propext=10|clean=Nat.gcd.induction|"
            "imported_xgcd=closed|ledger_writes=0"
        )
        return 0
    except (
        OSError,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        ExtendedGcdNovelDependencyAuditResultError,
    ) as error:
        print(f"autogenesis-extended-gcd-novel-dependency-audit-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
