#!/usr/bin/env python3
"""Validate sealed direct Int divisibility witness transports."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-int-fib-dvd-witness-transport-export-result-v9.json"


class ResultError(RuntimeError):
    """The sealed transport evidence changed."""


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    result = json.loads(RESULT.read_text())
    evidence = result["evidence"]
    execution = result["execution"]
    roots = result["roots"]
    pack = pathlib.Path(evidence["pack"])
    forbidden = {
        "Int.natAbs_dvd_natAbs",
        "Int.dvd_natAbs_self",
        "Int.dvd_trans",
        "Int.ofNat_dvd_left",
        "Int.natAbs_mul",
    }
    dependencies = {name for root in roots for name in root["direct_theorem_dependencies"]}
    if (
        result.get("schema_version") != 1
        or result.get("kind")
        != "axeyum-autogenesis-mathlib-int-fib-dvd-witness-transport-export-result-v9"
        or result.get("state")
        != "two-direct-witness-transports-reproduced-empty-footprint-and-sealed"
        or sha256(ROOT / result["plan"]["path"]) != result["plan"].get("sha256")
        or sha256(pack / "manifest.json") != evidence.get("manifest_sha256")
        or sha256(pack / "root.ndjson") != evidence.get("root_sha256")
        or sha256(pack / "replay.ndjson") != evidence.get("replay_sha256")
        or evidence.get("root_sha256") != evidence.get("replay_sha256")
        or stat.S_IMODE(pack.stat().st_mode) != 0o555
        or any(stat.S_IMODE(path.stat().st_mode) != 0o444 for path in pack.iterdir())
        or [root["name"] for root in roots]
        != [
            "Axeyum.Autogenesis.intNatAbsDvdForwardResidualV1",
            "Axeyum.Autogenesis.intDvdOfNatAbsDvdDirectV1",
        ]
        or any(root.get("axiom_footprint") != [] for root in roots)
        or not dependencies.isdisjoint(forbidden)
        or execution.get("exporter_invocations") != 2
        or execution.get("importer_runs") != 2
        or execution.get("staging_paths_removed") is not True
        or execution.get("target_fib_dvd_submissions") != 0
        or execution.get("ledger_writes") != 0
        or result["authority"].get("transport_theorem_credit") != 2
    ):
        raise ResultError("sealed streams, roots, forbidden dependencies, or budget changed")


def main() -> int:
    try:
        validate()
    except (ResultError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-fib-dvd-witness-transport-export-result: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "autogenesis-int-fib-dvd-witness-transport-export-result: PASS: "
        "roots=2|axioms=0|forbidden_dependencies=0|sealed=true|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
