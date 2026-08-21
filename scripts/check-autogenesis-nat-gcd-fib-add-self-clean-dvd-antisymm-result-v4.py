#!/usr/bin/env python3
"""Fail closed over the V4 dependent-induction decline."""
from __future__ import annotations
import hashlib, json, pathlib, stat, sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/nat-gcd-fib-add-self-clean-dvd-antisymm-result-v4.json"
PLAN = ROOT / "artifacts/autogenesis/nat-gcd-fib-add-self-clean-dvd-antisymm-plan-v4.json"
PACK = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/3e17cc2ed-clean-dvd-antisymm-v4")
MANIFEST = PACK / "manifest.json"
PLAN_SHA = "2516af20087cd869da440f4c36268a00629439132b919e778ff27373773fb974"
MANIFEST_SHA = "228771c31dfa802cda9f98dc9918eb3fc18e5fde2023aaecc80d6b227fd165f6"

def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def check() -> None:
    result, manifest = json.loads(RESULT.read_text()), json.loads(MANIFEST.read_text())
    assert sha256(PLAN) == PLAN_SHA and sha256(MANIFEST) == MANIFEST_SHA
    assert result["state"] == manifest["state"] == "first-invocation-declined-at-unspecialized-inner-induction-hypothesis-no-retry"
    assert result["evidence_pack"]["sha256"] == MANIFEST_SHA
    assert result["decline"] == manifest["decline"]
    assert result["decline"]["class"] == "TypeMismatch"
    assert result["authority"] == manifest["authority"] and all(value == 0 for value in result["authority"].values())
    execution = manifest["execution"]
    assert execution["complete_invocations"] == execution["input_stream_reads"] == 1
    assert execution["clean_dvd_antisymm_rejected_submissions"] == 1
    assert execution["composition_operations"] == execution["published_support_theorems"] == 0
    assert execution["second_invocation_skipped"] is True
    assert (PACK / "run-1.exit").read_text() == "1\n" and (PACK / "run-2.exit").read_text() == "skipped\n"
    assert not (PACK / "run-1.json").read_bytes()
    assert sha256(PACK / "run-1.stderr") == "7f2baa1a214973d1253cbad69fcf8daf180738d268b7e6bdd1db16e676cf80af"
    assert stat.S_IMODE(PACK.stat().st_mode) == 0o555
    assert all(stat.S_IMODE(path.stat().st_mode) == 0o444 for path in PACK.iterdir())

def main() -> int:
    try: check()
    except (AssertionError, KeyError, OSError, json.JSONDecodeError) as error:
        print(f"autogenesis-clean-dvd-antisymm-result-v4: {error}", file=sys.stderr); return 1
    print("autogenesis-clean-dvd-antisymm-result-v4: ok"); return 0

if __name__ == "__main__": raise SystemExit(main())
