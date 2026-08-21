#!/usr/bin/env python3
"""Fail closed over the V2 clean divisibility-antisymmetry decline."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/nat-gcd-fib-add-self-clean-dvd-antisymm-result-v2.json"
PLAN = ROOT / "artifacts/autogenesis/nat-gcd-fib-add-self-clean-dvd-antisymm-plan-v2.json"
PACK = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/fa993f97a-clean-dvd-antisymm-v2")
MANIFEST = PACK / "manifest.json"
EXPECTED_PLAN_SHA256 = "d12313b9839e30e02109e92717e7f450c0fd70201afc7cd63ee9630e1ed3609f"
EXPECTED_MANIFEST_SHA256 = "d4af64d38832b1d884ae9b6a1cf8bb8467d7b0a4ca959af9bc61facce478e0d8"
EXPECTED_STDERR_SHA256 = "305508811dc80df570f2ebf78afcfc5ed2ba1a629e07e7b5229e2283fa64ab6f"


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check() -> None:
    result = json.loads(RESULT.read_text())
    manifest = json.loads(MANIFEST.read_text())
    assert sha256(PLAN) == EXPECTED_PLAN_SHA256
    assert sha256(MANIFEST) == EXPECTED_MANIFEST_SHA256
    assert result["state"] == manifest["state"] == "first-invocation-aborted-at-missing-native-zero-divisibility-leaf-no-retry"
    assert result["evidence_pack"]["sha256"] == EXPECTED_MANIFEST_SHA256
    assert result["decline"] == manifest["decline"]
    assert result["authority"] == manifest["authority"] == {
        "support_credit": 0,
        "exact_target_submissions": 0,
        "target_credit": 0,
        "fact_status_changes": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }
    execution = manifest["execution"]
    assert execution["complete_invocations"] == execution["input_stream_reads"] == 1
    assert execution["clean_le_of_dvd_native_submissions"] == 1
    assert execution["clean_dvd_antisymm_submissions"] == execution["composition_operations"] == 0
    assert execution["published_support_theorems"] == execution["exact_target_submissions"] == execution["retries"] == 0
    assert execution["second_invocation_skipped"] is True
    assert (PACK / "run-1.exit").read_text() == "101\n"
    assert (PACK / "run-2.exit").read_text() == "skipped\n"
    assert not (PACK / "run-1.json").read_bytes()
    assert sha256(PACK / "run-1.stderr") == EXPECTED_STDERR_SHA256
    assert stat.S_IMODE(PACK.stat().st_mode) == 0o555
    for path in PACK.iterdir():
        assert stat.S_IMODE(path.stat().st_mode) == 0o444
    files = {entry["path"]: entry for entry in manifest["files"]}
    for name in ("run-1.json", "run-1.stderr"):
        path = PACK / name
        assert files[name] == {"path": name, "bytes": path.stat().st_size, "sha256": sha256(path)}


def main() -> int:
    try:
        check()
    except (AssertionError, KeyError, OSError, json.JSONDecodeError) as error:
        print(f"autogenesis-clean-dvd-antisymm-result-v2: {error}", file=sys.stderr)
        return 1
    print("autogenesis-clean-dvd-antisymm-result-v2: ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
