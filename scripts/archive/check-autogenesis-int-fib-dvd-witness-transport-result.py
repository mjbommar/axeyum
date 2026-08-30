#!/usr/bin/env python3
"""Validate the first direct divisibility witness transport result."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-int-fib-dvd-witness-transport-result-v7.json"


class ResultError(RuntimeError):
    """The witness transport diagnostic changed."""


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    result = json.loads(RESULT.read_text())
    source = result["source"]
    diagnostic = result["diagnostic"]
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
        != "axeyum-autogenesis-mathlib-int-fib-dvd-witness-transport-result-v7"
        or result.get("state")
        != "declined-at-two-opposite-sign-zero-quotient-representations"
        or sha256(ROOT / result["plan"]["path"]) != result["plan"].get("sha256")
        or sha256(ROOT / source["path"]) != source.get("sha256")
        or any(name in source_text for name in forbidden)
        or diagnostic.get("forward_residual") != "accepted"
        or diagnostic.get("reverse_accepted_branches")
        != ["ofNat.ofNat", "negSucc.negSucc"]
        or diagnostic.get("reverse_rejected_branches")
        != ["ofNat.negSucc", "negSucc.ofNat"]
        or execution.get("compile_invocations") != 1
        or execution.get("exporter_invocations") != 0
        or execution.get("target_fib_dvd_submissions") != 0
        or execution.get("ledger_writes") != 0
    ):
        raise ResultError("source identity, localized branches, or budget changed")


def main() -> int:
    try:
        validate()
    except (ResultError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-fib-dvd-witness-transport-result: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "autogenesis-int-fib-dvd-witness-transport-result: PASS: "
        "forward=accepted|reverse_branches=2/4|exports=0|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
