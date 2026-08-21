#!/usr/bin/env python3
"""Verify clean target-owned Int.fib and exact Int.fib_natCast construction."""

import hashlib
import json
import pathlib
import stat
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-int-fib-clean-definition-construction-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-clean-definition-construction-plan-v1.json"
PACK = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/int-fib-clean-definition-v1")


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
        if result["state"] != "target-owned-int-fib-and-exact-natcast-reconstruct-axiom-free" or sha256(PLAN) != result["plan_sha256"] or stat.S_IMODE(PACK.stat().st_mode) != 0o555 or sha256(PACK / "manifest.json") != result["pack_manifest_sha256"] or first != second or row["name"] != "Int.fib_natCast" or row["axiom_footprint"] != [] or row["direct_theorem_dependencies"] != [] or result["theorem"] != {"name": "Int.fib_natCast", "declaration_sha256": row["declaration_sha256"], "axiom_footprint": [], "direct_theorem_dependencies": []} or result["conclusion"]["fact_admission_authorized"] is not False or result["authority"]["ledger_writes"] != 0:
            raise RuntimeError("construction evidence, footprint, or authority changed")
        print("AUTOGENESIS_INT_FIB_CLEAN_DEFINITION_CONSTRUCTION_RESULT_OK|definition=Int.fib|theorem=Int.fib_natCast|imports=2|footprint=0|ledger_writes=0")
        return 0
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError, RuntimeError) as error:
        print(f"autogenesis-int-fib-clean-definition-construction-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
