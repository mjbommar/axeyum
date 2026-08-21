#!/usr/bin/env python3
"""Fail closed over the four portable Fibonacci/GCD support capsules plan."""
from __future__ import annotations
import hashlib, json, pathlib, sys
ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/nat-gcd-fib-add-self-portable-support-capsules-plan-v1.json"

def sha256(path: pathlib.Path) -> str: return hashlib.sha256(path.read_bytes()).hexdigest()

def check() -> None:
    plan = json.loads(PLAN.read_text())
    assert plan["state"] == "preregistered-four-root-selected-roundtrip-checked-capsules-before-code-or-export"
    accepted = plan["accepted_inputs"]
    assert len(accepted) == 4 and len({row["root"] for row in accepted.values()}) == 4
    for row in accepted.values():
        assert sha256(ROOT / row["path"]) == row["sha256"]
    assert "proof-bearing NDJSON remains in the sealed external pack" in plan["storage"]["git_policy"]
    construction = plan["construction"]
    assert construction["roots_per_capsule"] == 1 and construction["exports_per_root"] == 2
    assert "complete axiom footprint empty" in construction["required_properties"]
    assert plan["acceptance"] == {"capsules": 4, "fresh_exports_per_capsule": 2, "outputs_per_capsule_must_be_byte_identical": True, "each_capsule_must_import_twice": True, "each_root_declaration_sha256_must_match_accepted_result": True, "each_root_axiom_footprint": [], "rendered_material": {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0}}
    assert plan["budget"]["max_exact_target_submissions"] == plan["budget"]["max_retries"] == 0
    assert all(value == 0 for value in plan["authority"].values())

def main() -> int:
    try: check()
    except (AssertionError, KeyError, OSError, json.JSONDecodeError) as error:
        print(f"autogenesis-portable-support-capsules-plan: {error}", file=sys.stderr); return 1
    print("autogenesis-portable-support-capsules-plan: ok"); return 0
if __name__ == "__main__": raise SystemExit(main())
