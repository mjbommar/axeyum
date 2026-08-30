#!/usr/bin/env python3
"""Validate the rendered Exists.rec minor type mismatch and localization."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import subprocess
import sys


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-nat-fib-gcd-exists-rec-minor-type-result-v1.json"


class ResultError(RuntimeError):
    """The minor-type evidence, localization, or zero authority changed."""


def sha(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def implementation_exists(path: str, expected: str) -> bool:
    current = ROOT / path
    if current.exists() and sha(current) == expected:
        return True
    rows = subprocess.check_output(["git", "rev-list", "--objects", "--all", "--", path], cwd=ROOT, text=True)
    for row in rows.splitlines():
        object_id = row.split(" ", 1)[0]
        if subprocess.check_output(["git", "cat-file", "-t", object_id], cwd=ROOT, text=True).strip() != "blob":
            continue
        value = subprocess.check_output(["git", "cat-file", "blob", object_id], cwd=ROOT)
        if hashlib.sha256(value).hexdigest() == expected:
            return True
    return False


def validate() -> dict:
    result = json.loads(RESULT.read_text())
    plan = result.get("plan") or {}
    implementation = result.get("implementation") or {}
    pack = result.get("evidence_pack") or {}
    observation = result.get("observation") or {}
    pack_path = pathlib.Path(pack["path"])
    recorded = json.loads((pack_path / "observation.json").read_text())
    if (
        result.get("state") != "minor-types-rendered-left-gcd-recursion-transport-missing"
        or sha(ROOT / plan["path"]) != plan.get("sha256")
        or not implementation_exists(implementation["path"], implementation["sha256"])
        or sha(pack_path / "SHA256SUMS") != pack.get("index_sha256")
        or sha(pack_path / "observation.json") != pack.get("observation_sha256")
        or sha(pack_path / "stderr.txt") != pack.get("stderr_sha256")
        or stat.S_IMODE(pack_path.stat().st_mode) != 0o555
        or any(stat.S_IMODE(path.stat().st_mode) != 0o444 for path in pack_path.iterdir())
        or recorded.get("expected", {}).get("sha256") != observation.get("expected_type_sha256")
        or recorded.get("actual", {}).get("sha256") != observation.get("actual_type_sha256")
        or recorded.get("definitionally_equal") is not False
        or observation.get("definitionally_equal") is not False
        or observation.get("localized_missing_transport")
        != "explicit positive-divisor gcd recursion equality before the induction-hypothesis equality chain"
        or observation.get("target_submitted") is not False
        or result.get("execution") != recorded.get("execution")
        or any(value != 0 for value in result.get("authority", {}).values())
    ):
        raise ResultError("minor type identity, evidence, localization, or authority changed")
    return result


def main() -> int:
    try:
        validate()
    except (OSError, ValueError, KeyError, TypeError, ResultError) as error:
        print(f"autogenesis-nat-fib-gcd-exists-rec-minor-type-result: FAIL: {error}", file=sys.stderr)
        return 1
    print("AUTOGENESIS_NAT_FIB_GCD_EXISTS_REC_MINOR_TYPE_RESULT_OK|defeq=0|missing=gcd-recursion-transport|target=0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
