#!/usr/bin/env python3
"""Fail closed unless two retained authoritative B -> A runs reproduce."""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import sys
from typing import Any


class CompareError(RuntimeError):
    """The retained runs do not establish clean-room reproduction."""


def canonical_digest(value: Any) -> str:
    return hashlib.sha256(
        json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()


def load_run(root: pathlib.Path) -> dict[str, Any]:
    path = root / "run.json"
    value = json.loads(path.read_text(encoding="utf-8"))
    if value.get("schema_version") != 1 or value.get("kind") != "axeyum-autogenesis-authoritative-two-write-run":
        raise CompareError(f"unsupported run manifest: {path}")
    unsigned = dict(value)
    claimed = unsigned.pop("run_sha256", None)
    if claimed != canonical_digest(unsigned):
        raise CompareError(f"invalid run manifest digest: {path}")
    for relative, claimed_digest in value.get("artifacts", {}).items():
        artifact = root / relative
        if not artifact.is_file():
            raise CompareError(f"missing retained artifact: {artifact}")
        observed = hashlib.sha256(artifact.read_bytes()).hexdigest()
        if observed != claimed_digest:
            raise CompareError(f"retained artifact digest mismatch: {artifact}")
    if not value.get("checks") or not all(value["checks"].values()):
        raise CompareError(f"run contains a failed semantic check: {path}")
    return value


def comparison_identity(value: dict[str, Any]) -> dict[str, Any]:
    return {
        key: value[key]
        for key in (
            "source_commit",
            "reconstructed_prestate_commit",
            "pre_a_state_commit",
            "chain",
            "budgets",
            "intervention_audit",
            "trusted_base_audit",
            "fault_injection",
            "checks",
            "artifacts",
        )
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("first", type=pathlib.Path)
    parser.add_argument("second", type=pathlib.Path)
    parser.add_argument("--output", required=True, type=pathlib.Path)
    args = parser.parse_args()
    first_root = args.first.resolve()
    second_root = args.second.resolve()
    output = args.output.resolve()
    if first_root == second_root:
        raise CompareError("reproduction requires two distinct retained directories")
    if output.exists():
        raise CompareError("refusing to overwrite comparison output")
    first = load_run(first_root)
    second = load_run(second_root)
    first_identity = comparison_identity(first)
    second_identity = comparison_identity(second)
    if first_identity != second_identity:
        differing = sorted(
            key for key in first_identity if first_identity[key] != second_identity[key]
        )
        raise CompareError(f"deterministic run fields differ: {differing}")
    report = {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-authoritative-two-write-reproduction",
        "first_run_sha256": first["run_sha256"],
        "second_run_sha256": second["run_sha256"],
        "source_commit": first["source_commit"],
        "byte_identical_artifacts": sorted(first["artifacts"]),
        "semantic_identity_sha256": canonical_digest(first_identity),
        "checks": {
            "distinct_retained_directories": True,
            "same_exact_source": True,
            "same_prestate_commit": True,
            "same_pre_a_state_commit": True,
            "same_semantic_outcomes": True,
            "same_artifact_bytes": True,
            "zero_human_interventions_after_launch": (
                first["intervention_audit"]["human_interventions_after_launch"] == 0
            ),
            "zero_trusted_base_delta": first["trusted_base_audit"]["trusted_base_files_changed"] == [],
        },
    }
    report["reproduction_sha256"] = canonical_digest(report)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        f"AUTOGENESIS_AUTHORITATIVE_REPRODUCTION_OK|{report['reproduction_sha256']}|"
        f"output={output}"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (CompareError, OSError, KeyError, TypeError, ValueError) as error:
        print(f"AUTOGENESIS_AUTHORITATIVE_REPRODUCTION_ERROR|{error}", file=sys.stderr)
        raise SystemExit(1)
