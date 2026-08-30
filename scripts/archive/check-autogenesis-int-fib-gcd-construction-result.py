#!/usr/bin/env python3
"""Validate the sealed exact Int.fib_gcd theorem construction."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-int-fib-gcd-construction-result-v1.json"
PACK = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/int-fib-gcd-exact-v1")


class ResultError(RuntimeError):
    """The sealed construction evidence changed."""


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def mode(path: pathlib.Path) -> str:
    return f"{stat.S_IMODE(path.stat().st_mode):04o}"


def validate() -> None:
    result = json.loads(RESULT.read_text())
    target = result["target"]
    capsule = result["capsule"]
    execution = result["execution"]
    authority = result["authority"]
    capsule_path = pathlib.Path(capsule["path"])
    dependencies = ["Eq.symm", "Eq.trans", "Int.fib_natCast", "Int.gcd_fib"]
    if (
        result.get("schema_version") != 1
        or result.get("kind")
        != "axeyum-autogenesis-mathlib-int-fib-gcd-construction-result-v1"
        or result.get("state")
        != "exact-int-fib-gcd-constructed-exported-and-twice-reimported-empty-footprint"
        or sha256(ROOT / result["plan"]["path"]) != result["plan"].get("sha256")
        or sha256(ROOT / result["producer"]["path"])
        != result["producer"].get("sha256")
        or sha256(ROOT / result["producer"]["shared_path"])
        != result["producer"].get("shared_sha256")
        or target.get("name") != "Int.fib_gcd"
        or target.get("declaration_sha256")
        != "d269d9ef0763dd923c7825c77c0a3a3dd05ebbe4fbad4d84f3ce93482386a0bf"
        or target.get("axiom_footprint") != []
        or target.get("direct_theorem_dependencies") != dependencies
        or sha256(capsule_path) != capsule.get("sha256")
        or capsule_path.stat().st_size != capsule.get("bytes")
        or mode(capsule_path) != capsule.get("mode")
        or mode(PACK) != capsule.get("directory_mode")
        or sha256(PACK / "manifest.json") != capsule.get("manifest_sha256")
        or capsule.get("fresh_imports") != 2
        or execution
        != {
            "complete_invocations": 1,
            "input_stream_reads": 1,
            "target_theorem_submissions": 1,
            "target_exports": 1,
            "fresh_target_imports": 2,
            "retries": 0,
            "ledger_writes": 0,
        }
        or authority
        != {
            "fact_status_changes": 0,
            "proof_terms_types_or_values_rendered": 0,
            "official_target_proof_body_inspected": False,
            "same_name_declaration_transported": False,
        }
    ):
        raise ResultError("exact Int.fib_gcd evidence changed")


def main() -> int:
    try:
        validate()
    except (ResultError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-fib-gcd-construction-result: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "autogenesis-int-fib-gcd-construction-result: PASS: "
        "target=Int.fib_gcd|axioms=0|dependencies=4|fresh_imports=2|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
