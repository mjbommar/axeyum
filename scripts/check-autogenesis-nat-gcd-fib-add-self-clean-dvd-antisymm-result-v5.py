#!/usr/bin/env python3
"""Fail closed over the accepted V5 clean order support pack."""
from __future__ import annotations
import hashlib, json, pathlib, stat, sys
ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/nat-gcd-fib-add-self-clean-dvd-antisymm-result-v5.json"
PLAN = ROOT / "artifacts/autogenesis/nat-gcd-fib-add-self-clean-dvd-antisymm-plan-v5.json"
PACK = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/7da31933f-clean-dvd-antisymm-v5")
MANIFEST = PACK / "manifest.json"
PLAN_SHA = "4e18a295d042e114b66a744ded7858777ddc43330de68c5b4823e033d8521bd1"
MANIFEST_SHA = "5b35fda424057206b6d94afcead81c3581383e8ed463ba3d5d8c7af11ee1fb6c"
OUTPUT_SHA = "3a9651d264e239f01db87a3acc904d5dae4a62544d1a35b11103b035eded069d"

def sha256(path: pathlib.Path) -> str: return hashlib.sha256(path.read_bytes()).hexdigest()

def check() -> None:
    result, manifest = json.loads(RESULT.read_text()), json.loads(MANIFEST.read_text())
    assert sha256(PLAN) == PLAN_SHA and sha256(MANIFEST) == MANIFEST_SHA
    assert result["state"] == manifest["state"] == "three-clean-supports-transported-twice-byte-identically-empty-footprint"
    assert result["evidence_pack"]["sha256"] == MANIFEST_SHA
    assert sha256(PACK / "run-1.json") == sha256(PACK / "run-2.json") == OUTPUT_SHA
    assert not (PACK / "run-1.stderr").read_bytes() and not (PACK / "run-2.stderr").read_bytes()
    assert (PACK / "run-1.exit").read_text() == (PACK / "run-2.exit").read_text() == "0\n"
    run = json.loads((PACK / "run-1.json").read_text())
    assert run["transport_receipt_sha256"] == manifest["result"]["transport_receipt_sha256"]
    assert run["source_theorems"] == run["target_theorems"] == manifest["result"]["theorems"]
    assert all(not theorem["axiom_footprint"] for theorem in run["source_theorems"])
    assert run["rendered_material"] == {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0}
    assert run["exact_target_submissions"] == run["target_credit"] == run["fact_status_changes"] == run["evaluation_credit"] == run["ledger_writes"] == 0
    assert manifest["execution"] == {"complete_invocations": 2, "input_stream_reads": 2, "new_support_theorem_submissions": 6, "composition_operations": 2, "checked_composition_replays": 2, "published_support_theorems_per_invocation": 3, "exact_target_submissions": 0, "retries": 0}
    assert result["authority"] == manifest["authority"] == {"support_credit": 3, "exact_target_submissions": 0, "target_credit": 0, "fact_status_changes": 0, "evaluation_credit": 0, "ledger_writes": 0}
    assert stat.S_IMODE(PACK.stat().st_mode) == 0o555 and all(stat.S_IMODE(path.stat().st_mode) == 0o444 for path in PACK.iterdir())

def main() -> int:
    try: check()
    except (AssertionError, KeyError, OSError, json.JSONDecodeError) as error:
        print(f"autogenesis-clean-dvd-antisymm-result-v5: {error}", file=sys.stderr); return 1
    print("autogenesis-clean-dvd-antisymm-result-v5: ok"); return 0
if __name__ == "__main__": raise SystemExit(main())
