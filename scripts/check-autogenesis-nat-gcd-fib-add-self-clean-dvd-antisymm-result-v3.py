#!/usr/bin/env python3
"""Fail closed over the V3 missing-successor-positivity decline."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/nat-gcd-fib-add-self-clean-dvd-antisymm-result-v3.json"
PLAN = ROOT / "artifacts/autogenesis/nat-gcd-fib-add-self-clean-dvd-antisymm-plan-v3.json"
PACK = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/dda5d54a0-clean-dvd-antisymm-v3")
MANIFEST = PACK / "manifest.json"
PLAN_SHA = "120863fbb5bc2d8ecd16b8c8f6e9043d3da176f796239f62151a55b3481cc79c"
MANIFEST_SHA = "4b3bd8c88a709ede2cab0853778107d50ebaf645e2bcd9bf4fa5625df4d45b1c"


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check() -> None:
    result = json.loads(RESULT.read_text())
    manifest = json.loads(MANIFEST.read_text())
    assert sha256(PLAN) == PLAN_SHA and sha256(MANIFEST) == MANIFEST_SHA
    assert result["state"] == manifest["state"] == "first-invocation-aborted-at-missing-native-successor-positivity-leaf-no-retry"
    assert result["evidence_pack"]["sha256"] == MANIFEST_SHA
    assert result["decline"] == manifest["decline"]
    assert result["decline"]["diagnostic"] == "declaration is absent: Nat.succ_pos"
    assert result["authority"] == manifest["authority"]
    assert all(value == 0 for value in result["authority"].values())
    execution = manifest["execution"]
    assert execution["complete_invocations"] == execution["input_stream_reads"] == 1
    assert execution["clean_zero_dvd_native_submissions"] == execution["clean_le_of_dvd_native_submissions"] == 1
    assert execution["clean_dvd_antisymm_submissions"] == execution["composition_operations"] == 0
    assert execution["second_invocation_skipped"] is True
    assert (PACK / "run-1.exit").read_text() == "101\n"
    assert (PACK / "run-2.exit").read_text() == "skipped\n"
    assert not (PACK / "run-1.json").read_bytes()
    assert sha256(PACK / "run-1.stderr") == "3d7dd3a702db5cecbb7c4cdda7640b35e0b0272cad1e67539a757083826c9602"
    assert stat.S_IMODE(PACK.stat().st_mode) == 0o555
    assert all(stat.S_IMODE(path.stat().st_mode) == 0o444 for path in PACK.iterdir())


def main() -> int:
    try:
        check()
    except (AssertionError, KeyError, OSError, json.JSONDecodeError) as error:
        print(f"autogenesis-clean-dvd-antisymm-result-v3: {error}", file=sys.stderr)
        return 1
    print("autogenesis-clean-dvd-antisymm-result-v3: ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
