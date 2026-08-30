#!/usr/bin/env python3
"""Validate the sealed exact integer Fibonacci natAbs bridge."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-int-gcd-fib-construction-result-v9.json"
PACK = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/int-fib-natabs-exact-v1")


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def mode(path: pathlib.Path) -> str:
    return f"{stat.S_IMODE(path.stat().st_mode):04o}"


def validate() -> None:
    result = json.loads(RESULT.read_text())
    plan = ROOT / result["plan"]["path"]
    producer = ROOT / result["producer"]["path"]
    capsule = pathlib.Path(result["capsule"]["path"])
    manifest = PACK / "manifest.json"
    target = result["target"]
    expected_dependencies = [
        "Axeyum.Autogenesis.intFibNatAbsResidualV2",
        "Axeyum.Autogenesis.intFibNegativeEvenV1",
        "Axeyum.Autogenesis.intFibNegativeOddV1",
        "Axeyum.Autogenesis.intNatAbsOfNatV1",
        "Axeyum.IntFib.modCases",
        "Int.fib_natCast",
        "Int.natAbs_neg",
    ]
    if (
        result.get("state")
        != "exact-int-fib-natabs-specialized-exported-and-twice-reimported-empty-footprint"
        or sha256(plan) != result["plan"].get("sha256")
        or sha256(producer) != result["producer"].get("sha256")
        or target.get("name") != "Axeyum.Autogenesis.intFibNatAbsV1"
        or target.get("axiom_footprint") != []
        or target.get("direct_theorem_dependencies") != expected_dependencies
        or len(result.get("composition_receipt_sha256", [])) != 4
        or result["support"].get("axiom_footprint") != []
        or result["support"].get("direct_theorem_dependencies") != []
        or capsule != PACK / "root.ndjson"
        or sha256(capsule) != result["capsule"].get("sha256")
        or capsule.stat().st_size != result["capsule"].get("bytes")
        or mode(capsule) != result["capsule"].get("mode")
        or sha256(manifest) != result["capsule"].get("manifest_sha256")
        or mode(PACK) != result["capsule"].get("directory_mode")
        or result["execution"].get("complete_invocations") != 1
        or result["execution"].get("input_stream_reads") != 5
        or result["execution"].get("composition_operations") != 4
        or result["execution"].get("composition_replays") != 4
        or result["execution"].get("fresh_target_imports") != 2
        or result["execution"].get("retries") != 0
        or result["execution"].get("ledger_writes") != 0
        or result["authority"].get("rendered_proof_terms") != 0
        or result["authority"].get("fact_status_changes") != 0
    ):
        raise ValueError("exact integer Fibonacci natAbs evidence changed")


def main() -> int:
    try:
        validate()
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-gcd-fib-construction-result-v9: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "autogenesis-int-gcd-fib-construction-result-v9: PASS: "
        "target=Axeyum.Autogenesis.intFibNatAbsV1|axioms=0|dependencies=7|"
        "compositions=4|fresh_imports=2|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
