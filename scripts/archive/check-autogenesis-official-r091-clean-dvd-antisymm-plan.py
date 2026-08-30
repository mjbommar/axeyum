#!/usr/bin/env python3
"""Verify the official-r091 clean divisibility-order reconstruction plan."""
from __future__ import annotations
import hashlib, json, pathlib, sys
ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/official-r091-clean-dvd-antisymm-plan-v1.json"
def sha256(path: pathlib.Path) -> str: return hashlib.sha256(path.read_bytes()).hexdigest()
def check() -> None:
    plan = json.loads(PLAN.read_text())
    predecessor = plan["predecessor"]
    assert sha256(ROOT / predecessor["path"]) == predecessor["sha256"]
    for row in plan["inputs"].values(): assert sha256(pathlib.Path(row["path"])) == row["sha256"]
    assert [row["name"] for row in plan["construction"]["theorems"]] == ["Axeyum.Autogenesis.eqZeroOfZeroDvdOfficialV1", "Axeyum.Autogenesis.leOfDvdOfficialV1", "Axeyum.Autogenesis.dvdAntisymmOfficialV1"]
    assert "without TypeShapeMismatch" in plan["construction"]["compatibility_gate"]
    forbidden = " ".join(plan["forbidden"])
    assert "assumption-bearing Nat.le_of_dvd" in forbidden and "assumption-bearing Nat.dvd_antisymm" in forbidden
    assert plan["acceptance"]["all_three_axiom_footprints"] == [] and plan["acceptance"]["exact_target_submissions"] == 0
    assert plan["budget"]["max_exact_target_submissions"] == plan["budget"]["max_retries"] == 0
    assert all(value == 0 for value in plan["authority"].values())
def main() -> int:
    try: check()
    except (AssertionError, KeyError, OSError, json.JSONDecodeError) as error:
        print(f"autogenesis-official-r091-clean-dvd-antisymm-plan: {error}", file=sys.stderr); return 1
    print("AUTOGENESIS_OFFICIAL_R091_CLEAN_DVD_ANTISYMM_PLAN_OK|supports=3|runs=2|target=0"); return 0
if __name__ == "__main__": raise SystemExit(main())
