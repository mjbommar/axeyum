#!/usr/bin/env python3
"""Validate the compiling direct witness transport source."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-int-fib-dvd-witness-transport-result-v8.json"


class ResultError(RuntimeError):
    """The compiling witness transport result changed."""


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    result = json.loads(RESULT.read_text())
    source = result["source"]
    execution = result["execution"]
    source_text = (ROOT / source["path"]).read_text()
    forbidden = [
        "Int.natAbs_dvd_natAbs",
        "Int.dvd_natAbs_self",
        "Int.dvd_trans",
        "Int.ofNat_dvd_left",
        "Int.natAbs_mul",
        "propext",
    ]
    if (
        result.get("schema_version") != 1
        or result.get("kind")
        != "axeyum-autogenesis-mathlib-int-fib-dvd-witness-transport-result-v8"
        or result.get("state") != "both-direct-witness-transports-compile"
        or sha256(ROOT / result["plan"]["path"]) != result["plan"].get("sha256")
        or sha256(ROOT / source["path"]) != source.get("sha256")
        or any(name in source_text for name in forbidden)
        or source.get("roots")
        != [
            "Axeyum.Autogenesis.intNatAbsDvdForwardResidualV1",
            "Axeyum.Autogenesis.intDvdOfNatAbsDvdDirectV1",
        ]
        or execution
        != {
            "source_rewrites": 1,
            "compile_invocations": 1,
            "compiler_exit_status": 0,
            "exporter_invocations": 0,
            "importer_runs": 0,
            "retries": 0,
            "target_fib_dvd_submissions": 0,
            "ledger_writes": 0,
        }
    ):
        raise ResultError("source identity, forbidden dependency, roots, or budget changed")


def main() -> int:
    try:
        validate()
    except (ResultError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-fib-dvd-witness-transport-result-v8: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "autogenesis-int-fib-dvd-witness-transport-result-v8: PASS: "
        "roots=2|compile=1|exit=0|exports=0|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
