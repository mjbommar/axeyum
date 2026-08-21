#!/usr/bin/env python3
"""Fail closed over the exact Fibonacci GCD-shift construction plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/nat-gcd-fib-add-self-exact-plan-v1.json"
PACK = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/9b21389e9-nat-gcd-fib-add-self-portable-support-capsules-v1")
EXPECTED_ROOTS = {
    "Axeyum.Autogenesis.NatFibSuccessorAddition",
    "Nat.fib_coprime_fib_succ",
    "Axeyum.Autogenesis.officialCoprimeFactorDivisibilityCancellationV1",
    "Axeyum.Autogenesis.dvdAntisymmCleanV5",
}


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check() -> None:
    plan = json.loads(PLAN.read_text())
    assert plan["state"] == "preregistered-exact-r091-construction-over-four-sealed-capsules-before-code-or-submission"
    assert plan["target"]["source_name"] == "Nat.gcd_fib_add_self"
    for name in ("qualification", "portable_support_result"):
        row = plan["inputs"][name]
        assert sha256(ROOT / row["path"]) == row["sha256"]
    stream = plan["inputs"]["target_stream"]
    assert sha256(pathlib.Path(stream["path"])) == stream["sha256"]
    capsule_pack = plan["inputs"]["capsule_pack"]
    assert sha256(PACK / "manifest.json") == capsule_pack["manifest_sha256"]
    assert stat.S_IMODE(PACK.stat().st_mode) == 0o555
    assert all(stat.S_IMODE(path.stat().st_mode) == 0o444 for path in PACK.iterdir() if path.is_file())
    assert set(capsule_pack["required_roots"]) == EXPECTED_ROOTS
    shortcuts = " ".join(plan["proof_route"]["forbidden_shortcuts"])
    assert "Nat.gcd_comm" in shortcuts and "Nat.dvd_antisymm" in shortcuts and "propext" in shortcuts
    assert plan["construction"]["target_must_be_submitted_only_after_all_support_checks"] is True
    acceptance = plan["acceptance"]
    assert acceptance["fresh_complete_invocations"] == acceptance["target_submissions_per_invocation"] * 2
    assert acceptance["target_axiom_footprint"] == []
    assert acceptance["proof_terms_types_or_values_may_be_rendered"] is False
    budget = plan["budget"]
    assert budget["max_complete_invocations"] == budget["max_exact_target_submissions"] == 2
    assert budget["max_retries"] == 0
    assert all(value == 0 for value in plan["authority"].values())


def main() -> int:
    try:
        check()
    except (AssertionError, KeyError, OSError, json.JSONDecodeError) as error:
        print(f"autogenesis-nat-gcd-fib-add-self-exact-plan: {error}", file=sys.stderr)
        return 1
    print("AUTOGENESIS_NAT_GCD_FIB_ADD_SELF_EXACT_PLAN_OK|runs=2|submissions=2|retries=0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
