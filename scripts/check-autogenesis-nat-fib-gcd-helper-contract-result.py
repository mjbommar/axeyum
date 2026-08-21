#!/usr/bin/env python3
"""Validate the exact type-only Nat.fib_gcd helper contracts."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-nat-fib-gcd-helper-contract-result-v1.json"


class ResultError(RuntimeError):
    """The helper contracts or zero-authority result changed."""


def sha(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> dict:
    result = json.loads(RESULT.read_text())
    plan = result.get("plan") or {}
    implementation = result.get("implementation") or {}
    pack = result.get("evidence_pack") or {}
    root = pathlib.Path(pack.get("path", ""))
    observation_path = root / "observation.json"
    observation = json.loads(observation_path.read_text())
    contracts = result.get("contracts")
    observed = observation.get("contracts")
    if (
        result.get("schema_version") != 1
        or result.get("kind")
        != "axeyum-autogenesis-mathlib-nat-fib-gcd-helper-contract-result-v1"
        or result.get("state")
        != "exact-euclidean-contracts-bound-zero-proof-values-or-submissions"
        or sha(ROOT / plan["path"]) != plan.get("sha256")
        or sha(ROOT / implementation["path"]) != implementation.get("sha256")
        or sha(root / "SHA256SUMS") != pack.get("index_sha256")
        or sha(observation_path) != pack.get("observation_sha256")
        or stat.S_IMODE(root.stat().st_mode) != 0o555
        or stat.S_IMODE(observation_path.stat().st_mode) != 0o444
        or not isinstance(contracts, list)
        or not isinstance(observed, list)
        or len(contracts) != 4
        or len(observed) != 4
    ):
        raise ResultError("result envelope, source, or immutable observation changed")
    for expected, actual in zip(contracts, observed, strict=True):
        for key in (
            "name",
            "type_sha256",
            "declaration_sha256",
            "top_level_binders",
            "binder_info",
        ):
            if actual.get(key) != expected.get(key):
                raise ResultError(f"contract changed for {expected.get('name')}: {key}")
        if actual.get("axiom_footprint") != [] or actual.get("proof_value_rendered") is not False:
            raise ResultError(f"contract authority changed for {expected.get('name')}")
    if (
        observation.get("execution", {}).get("rendered_theorem_values") != 0
        or observation.get("execution", {}).get("theorem_submissions") != 0
        or result.get("execution")
        != {
            "complete_audits": 1,
            "rendered_theorem_types": 4,
            "rendered_theorem_values": 0,
            "theorem_submissions": 0,
            "ledger_writes": 0,
        }
    ):
        raise ResultError("execution or zero-authority boundary changed")
    return result


def main() -> int:
    try:
        result = validate()
    except (OSError, ValueError, KeyError, TypeError, ResultError) as error:
        print(f"autogenesis-nat-fib-gcd-helper-contract-result: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "AUTOGENESIS_NAT_FIB_GCD_HELPER_CONTRACT_RESULT_OK|"
        f"contracts={len(result['contracts'])}|footprint=0|types=4|values=0|submissions=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
