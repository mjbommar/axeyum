#!/usr/bin/env python3
"""Validate the fail-closed V5 direct multiplication export result."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-int-fib-dvd-direct-natabs-mul-export-result-v5.json"


class ResultError(RuntimeError):
    """The V5 export result changed."""


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    result = json.loads(RESULT.read_text())
    evidence = result["evidence"]
    root = result["root"]
    execution = result["execution"]
    pack = pathlib.Path(evidence["pack"])
    expected_dependencies = [
        "Eq.symm",
        "_private.AxeyumIntNatAbsMulDirectV1.0.Axeyum.Autogenesis.intNatAbsNegOfNatDirectV1",
    ]
    if (
        result.get("schema_version") != 1
        or result.get("kind")
        != "axeyum-autogenesis-mathlib-int-fib-dvd-direct-natabs-mul-export-result-v5"
        or result.get("state")
        != "declined-at-nonempty-direct-dependency-set-before-sealing"
        or sha256(ROOT / result["plan"]["path"]) != result["plan"].get("sha256")
        or sha256(pack / "root.ndjson") != evidence.get("root_sha256")
        or sha256(pack / "replay.ndjson") != evidence.get("replay_sha256")
        or evidence.get("root_sha256") != evidence.get("replay_sha256")
        or root.get("axiom_footprint") != []
        or root.get("observed_direct_theorem_dependencies") != expected_dependencies
        or root.get("preregistered_direct_theorem_dependencies") != []
        or execution.get("exporter_invocations") != 2
        or execution.get("importer_runs") != 2
        or execution.get("staging_paths_removed") is not True
        or execution.get("target_fib_dvd_submissions") != 0
        or execution.get("ledger_writes") != 0
        or result["decision"].get("accepted_under_v5") is not False
    ):
        raise ResultError("stream identity, observed dependency mismatch, or budget changed")


def main() -> int:
    try:
        validate()
    except (ResultError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-fib-dvd-direct-natabs-mul-export-result: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "autogenesis-int-fib-dvd-direct-natabs-mul-export-result: PASS: "
        "axioms=0|observed_dependencies=2|accepted=false|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
