#!/usr/bin/env python3
"""Verify the reproduced but assumption-bearing Int.fib_natCast construction."""

import hashlib
import json
import pathlib
import stat
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-int-fib-natcast-rooted-construction-result-v2.json"
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-natcast-rooted-construction-plan-v2.json"
PACK = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/int-fib-natcast-rooted-v2")


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def main() -> int:
    try:
        result = json.loads(RESULT.read_text())
        first = json.loads((PACK / "import-1.json").read_text())
        second = json.loads((PACK / "import-2.json").read_text())
        row = first["rows"][0]
        if result["state"] != "rfl-proof-reproduces-but-official-int-fib-definition-carries-assumptions" or sha256(PLAN) != result["plan_sha256"] or stat.S_IMODE(PACK.stat().st_mode) != 0o555 or sha256(PACK / "manifest.json") != result["pack_manifest_sha256"] or first != second or row["direct_theorem_dependencies"] != [] or row["axiom_footprint"] != result["theorem"]["axiom_footprint"] or result["conclusion"] != {"proof_term_source": "rfl", "proof_dependency_contamination": False, "official_definition_or_representation_contamination": True, "fact_admission_authorized": False, "next": "preregister a nonrendering Int.fib declaration/definition closure audit and select a target-owned representation reconstruction"} or result["authority"]["ledger_writes"] != 0:
            raise RuntimeError("reproduction, footprint, conclusion, or authority changed")
        print("AUTOGENESIS_INT_FIB_NATCAST_ROOTED_CONSTRUCTION_RESULT_OK|imports=2|identical=true|footprint=9|credit=0|next=definition-audit")
        return 0
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError, RuntimeError) as error:
        print(f"autogenesis-int-fib-natcast-rooted-construction-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
