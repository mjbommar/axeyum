#!/usr/bin/env python3
"""Validate the first direct natAbs multiplication compile result."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-int-fib-dvd-direct-natabs-mul-result-v3.json"


class ResultError(RuntimeError):
    """The direct multiplication diagnostic changed."""


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    result = json.loads(RESULT.read_text())
    source = result["source"]
    diagnostic = result["diagnostic"]
    execution = result["execution"]
    source_text = (ROOT / source["path"]).read_text()
    forbidden = [
        "Int.natAbs_mul",
        "Int.natAbs_dvd_natAbs",
        "Int.dvd_natAbs_self",
        "Int.dvd_trans",
        "Int.ofNat_dvd_left",
        "propext",
    ]
    if (
        result.get("schema_version") != 1
        or result.get("kind")
        != "axeyum-autogenesis-mathlib-int-fib-dvd-direct-natabs-mul-result-v3"
        or result.get("state")
        != "declined-at-two-cross-sign-definitional-equality-branches"
        or sha256(ROOT / result["plan"]["path"]) != result["plan"].get("sha256")
        or sha256(ROOT / source["path"]) != source.get("sha256")
        or any(name in source_text for name in forbidden)
        or diagnostic.get("accepted_branches") != ["ofNat.ofNat", "negSucc.negSucc"]
        or diagnostic.get("rejected_branches") != ["ofNat.negSucc", "negSucc.ofNat"]
        or diagnostic.get("compiler_exit_status") != 1
        or execution.get("compile_invocations") != 1
        or execution.get("exporter_invocations") != 0
        or execution.get("importer_runs") != 0
        or execution.get("target_fib_dvd_submissions") != 0
        or execution.get("ledger_writes") != 0
    ):
        raise ResultError("source identity, branches, or execution budget changed")


def main() -> int:
    try:
        validate()
    except (ResultError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-fib-dvd-direct-natabs-mul-result: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "autogenesis-int-fib-dvd-direct-natabs-mul-result: PASS: "
        "accepted=2|rejected=2|exports=0|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
