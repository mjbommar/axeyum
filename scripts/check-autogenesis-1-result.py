#!/usr/bin/env python3
"""Validate the small committed index for the externally retained A1 result."""

from __future__ import annotations

import hashlib
import importlib.util
import json
import pathlib
import subprocess
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parent.parent
RESULT = ROOT / "artifacts/autogenesis/autogenesis-1-result.json"
COMPARE = ROOT / "scripts/compare-autogenesis-authoritative-chains.py"


class ResultError(RuntimeError):
    """The committed result index does not support its verdict."""


def digest(value: Any) -> str:
    return hashlib.sha256(
        json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()


def validate(value: dict[str, Any]) -> None:
    if value.get("schema_version") != 1 or value.get("kind") != "axeyum-autogenesis-1-result":
        raise ResultError("unsupported result schema")
    unsigned = dict(value)
    claimed = unsigned.pop("result_sha256", None)
    if claimed != digest(unsigned):
        raise ResultError("result digest is invalid")
    if value.get("verdict") != "autogenesis-1-passed":
        raise ResultError("result does not carry the passed verdict")
    if value.get("chain") != {"premise": "F:nat-zero-add", "consequent": "F:nat-mul-one"}:
        raise ResultError("result names the wrong chain")
    if value.get("budgets") != {"pre_b_a_negative": 1, "b": 2, "a": 1}:
        raise ResultError("result budgets are not the credited fixed budgets")
    assurance = value.get("assurance", {})
    expected_zero = (
        "caller_authored_checker_commands",
        "human_interventions_after_launch",
        "human_written_or_repaired_proofs",
    )
    if any(assurance.get(key) != 0 for key in expected_zero):
        raise ResultError("result contains a proof-affecting intervention")
    if any(
        assurance.get(key) != []
        for key in ("a_axiom_footprint", "b_axiom_footprint", "trusted_base_files_changed")
    ):
        raise ResultError("result grows the trusted base or carries an axiom")
    checks = value.get("reproduction", {}).get("checks", {})
    if len(checks) != 8 or not all(checks.values()):
        raise ResultError("clean-room reproduction checks are incomplete or failed")
    runs = value.get("runs", {})
    if runs.get("first_sha256") != runs.get("second_sha256"):
        raise ResultError("the two run identities differ")
    source = value.get("identities", {}).get("source_commit")
    if not isinstance(source, str) or len(source) != 40:
        raise ResultError("source commit identity is malformed")
    if subprocess.run(
        ["git", "cat-file", "-e", f"{source}^{{commit}}"], cwd=ROOT, check=False
    ).returncode != 0:
        raise ResultError("source commit is unavailable")


def verify_external(value: dict[str, Any]) -> bool:
    root = pathlib.Path(value["artifact_locator"]["external_root"])
    if not root.is_dir():
        return False
    spec = importlib.util.spec_from_file_location("compare_autogenesis_chains", COMPARE)
    if spec is None or spec.loader is None:
        raise ResultError("cannot load authoritative chain comparer")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    first = module.load_run(root / "run-1")
    second = module.load_run(root / "run-2")
    reproduction = json.loads((root / "reproduction.json").read_text(encoding="utf-8"))
    expected = value["reproduction"]
    if first["run_sha256"] != value["runs"]["first_sha256"]:
        raise ResultError("external first run differs from the committed index")
    if second["run_sha256"] != value["runs"]["second_sha256"]:
        raise ResultError("external second run differs from the committed index")
    if reproduction.get("reproduction_sha256") != expected["reproduction_sha256"]:
        raise ResultError("external reproduction differs from the committed index")
    if reproduction.get("semantic_identity_sha256") != expected["semantic_identity_sha256"]:
        raise ResultError("external semantic identity differs from the committed index")
    if len(reproduction.get("byte_identical_artifacts", [])) != expected["artifact_count"]:
        raise ResultError("external artifact count differs from the committed index")
    if reproduction.get("checks") != expected["checks"]:
        raise ResultError("external reproduction checks differ from the committed index")
    bundle_sha = first["bundle"]["sha256"]
    if bundle_sha != value["identities"]["pre_a_state_bundle_sha256"]:
        raise ResultError("external state bundle differs from the committed index")
    return True


def main() -> int:
    value = json.loads(RESULT.read_text(encoding="utf-8"))
    validate(value)
    external = verify_external(value)
    print(
        f"AUTOGENESIS_1_RESULT_OK|{value['result_sha256']}|"
        f"external={'verified' if external else 'unavailable'}"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ResultError, OSError, KeyError, TypeError, ValueError, json.JSONDecodeError) as error:
        print(f"AUTOGENESIS_1_RESULT_ERROR|{error}", file=sys.stderr)
        raise SystemExit(1)
