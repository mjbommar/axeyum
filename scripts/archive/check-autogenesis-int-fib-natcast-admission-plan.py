#!/usr/bin/env python3
"""Verify the exact Int.fib_natCast sealed-capsule admission plan."""

import hashlib
import importlib.util
import json
import pathlib
import stat
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-natcast-admission-plan-v1.json"
RESULT_CHECKER = ROOT / "scripts/check-autogenesis-int-fib-natcast-goal-identity-result.py"


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load_checker():
    spec = importlib.util.spec_from_file_location("int_fib_natcast_identity", RESULT_CHECKER)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load identity checker")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main() -> int:
    try:
        plan = json.loads(PLAN.read_text())
        target = plan["target"]
        evidence = plan["evidence"]
        fact_path = ROOT / f"artifacts/facts/{target['fact_id'].replace('F:', 'F-')}.json"
        fact = json.loads(fact_path.read_text())
        capsule = pathlib.Path(evidence["capsule_path"])
        if load_checker().main() != 0:
            raise RuntimeError("identity result checker failed")
        if (
            plan["state"] != "preregistered-sealed-capsule-admission-before-operation-code-or-ledger-write"
            or fact["id"] != target["fact_id"]
            or fact["epistemic_status"] != "open"
            or sha256(fact_path) != target["fact_sha256"]
            or sha256(ROOT / evidence["construction_result"])
            != evidence["construction_result_sha256"]
            or sha256(ROOT / evidence["identity_result"])
            != evidence["identity_result_sha256"]
            or capsule.stat().st_size != 374550
            or stat.S_IMODE(capsule.stat().st_mode) != 0o444
            or sha256(capsule) != evidence["capsule_sha256"]
            or evidence["axiom_footprint"] != []
            or evidence["direct_theorem_dependencies"] != []
            or plan["protocol"]["authoritative_ledger_writes"] != 1
            or plan["budget"]["max_authoritative_ledger_writes"] != 1
            or plan["budget"]["max_search_invocations"] != 0
            or plan["expected_newly_ready"] != ["F:ml430-int-fib-add-two-739358dd"]
        ):
            raise RuntimeError("fact, evidence, protocol, budget, or unlock changed")
        print("AUTOGENESIS_INT_FIB_NATCAST_ADMISSION_PLAN_OK|operation=0/1|writes=0/1|expected_ready=1")
        return 0
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError, RuntimeError) as error:
        print(f"autogenesis-int-fib-natcast-admission-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
