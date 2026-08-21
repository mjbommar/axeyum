#!/usr/bin/env python3
"""Verify the first bounded support result for Nat.gcd_fib_add_self."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import subprocess
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-nat-gcd-fib-add-self-support-result-v1.json"

EXPECTED_DEPENDENCIES = [
    "Axeyum.Autogenesis.fibAddTwo",
    "Nat.add_assoc",
    "Nat.add_comm",
    "Nat.add_right_comm",
    "Nat.add_zero",
    "Nat.left_distrib",
    "Nat.mul_one",
    "Nat.mul_zero",
    "Nat.succ_add",
    "Nat.zero_add",
]
EXPECTED_SUPPORT = {
    "id": "fibonacci-successor-addition-v1",
    "target": "Axeyum.Autogenesis.NatFibSuccessorAddition",
    "goal_sha256": "297c9f4af4d63eff354223f9548ab1d4dd3d7e52aa701e88802d58b7929a1451",
    "proof_sha256": "b8b1d301a7e4bd7595c809c83d62ce943d2d0152dbf124484f1de254fd3ab3d3",
    "declaration_sha256": "049535cf7f432f14a0c93b4c7e9ecdcbd21feca4274b87be4a93e8838d6426ca",
    "axiom_footprint": [],
    "direct_theorem_dependencies": EXPECTED_DEPENDENCIES,
    "fresh_reconstructions": 2,
    "kernel_submissions": 2,
}
EXPECTED_AUTHORITY = {
    "proof_search_invocations": 0,
    "executor_invocations": 0,
    "semantic_theorem_receipts_issued": 0,
    "evaluation_credit": 0,
    "ledger_writes": 0,
}
EXPECTED_IMPLEMENTATION = [
    {
        "path": "crates/axeyum-lean-import/examples/nat_gcd_succ_specialization.rs",
        "sha256": "27841f21574d3d7bb5e751e5bfe2701831d28c62a2cbaad9752f1d4174088c40",
    },
    {
        "path": "crates/axeyum-lean-import/examples/support/fib_gcd_shift.rs",
        "sha256": "a151b87eade8ef5e94bea1adac8f200bd88bc439f4d13a57d132671185af30e2",
    },
]
EXPECTED_INPUTS = [
    {
        "name": "nat-mod-invariant.ndjson",
        "path": "/nas3/data/axeyum/autogenesis/reference-packs/667201932-lean430-nat-mod-invariant-v1/nat-mod-invariant.ndjson",
        "sha256": "5d945b100f3e2939d6ea3ffa67e10b4d78ff9efb7782a56f3d67468aa167ebf9",
    },
    {
        "name": "r091.ndjson",
        "path": "/nas3/data/axeyum/autogenesis/coverage/26fcc2c2f-mathlib-v4.30.0-reflexivity-train-development-v1/streams/r091.ndjson",
        "sha256": "fc1117679c743009e8548a25d1f73f71f6cd42555ea77b3efce07844673670b2",
    },
    {
        "name": "nat-gcd-bridge.ndjson",
        "path": "/nas3/data/axeyum/autogenesis/reference-packs/f94489c74-lean430-nat-gcd-succ-bridge-v1/nat-gcd-bridge.ndjson",
        "sha256": "6e99d4ae83b3916f8ee36c541bac18fc91b9f922252ca0af1cf658578b4e20db",
    },
    {
        "name": "fib-recurrence.ndjson",
        "path": "/nas3/data/axeyum/autogenesis/reference-packs/d12736b63-lean430-exact-fibonacci-coprimality-v1/fib-recurrence.ndjson",
        "sha256": "5220ace53dcbf0b89121ba72c8e63cc7dcb2a2d7836b313bc597607859d78674",
    },
]


class SupportResultError(RuntimeError):
    """The support identity, archive, budget, or no-credit boundary changed."""


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise SupportResultError(f"{path} is not an object")
    return value


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate_observation(observation: dict[str, Any]) -> None:
    if (
        observation.get("schema_version") != 1
        or observation.get("kind")
        != "axeyum-nat-gcd-fib-add-self-support-control"
        or observation.get("state")
        != "first-support-reconstructed-no-target-or-ledger-credit"
        or observation.get("target_stream_sha256")
        != "fc1117679c743009e8548a25d1f73f71f6cd42555ea77b3efce07844673670b2"
        or observation.get("supports") != [EXPECTED_SUPPORT]
        or observation.get("support_theorems_reconstructed") != 1
        or observation.get("kernel_submissions") != 2
        or observation.get("exact_source_target_submissions") != 0
        or observation.get("proof_search_invocations") != 0
        or observation.get("executor_invocations") != 0
        or observation.get("evaluation_credit") != 0
        or observation.get("ledger_writes") != 0
    ):
        raise SupportResultError("observation contract changed")
    receipts = {
        "support_composition_receipt_sha256": "ac8babcdbc897d258884ddec13958794477305aa8d99d222bf850970574103d8",
        "native_recurrence_composition_receipt_sha256": "19c7ff401412febfb8d9dae825eca50b1d8d287450dcdf1dc711fdae72a703f5",
        "target_recurrence_composition_receipt_sha256": "63183a214d54f03b4b176a6ebc64fa8f68b373de0e94061c8cc13c28f9acb380",
        "addition_composition_receipt_sha256": "3cd6871942719adf324064e0ffbe455dcf40d1a08c812cbf31834ed3906dc086",
    }
    if any(observation.get(key) != value for key, value in receipts.items()):
        raise SupportResultError("composition receipt changed")


def validate_manifest(manifest: dict[str, Any]) -> None:
    expected_theorem = dict(EXPECTED_SUPPORT)
    expected_theorem["name"] = expected_theorem.pop("target")
    expected_theorem["statement"] = (
        "forall n k, fib (n + (k + 1)) = fib (k + 1) * fib (n + 1) + fib k * fib n"
    )
    if (
        manifest.get("schema_version") != 1
        or manifest.get("kind") != "axeyum-nat-fib-successor-addition-reference-pack"
        or manifest.get("tooling_commit")
        != "f8c7febc631d6820ac8a8e827a6434bdcdc0cd8e"
        or manifest.get("lean")
        != {
            "version": "4.30.0",
            "githash": "d024af099ca4bf2c86f649261ebf59565dc8c622",
        }
        or manifest.get("frozen_plan")
        != {
            "path": "artifacts/autogenesis/mathlib-nat-gcd-fib-add-self-support-plan-v1.json",
            "sha256": "6b4c3243ef2053b7743f028268b21d436e181b9b2835d56880c860284dd08f46",
        }
        or manifest.get("inputs") != EXPECTED_INPUTS
        or manifest.get("implementation") != EXPECTED_IMPLEMENTATION
        or manifest.get("support_theorem") != expected_theorem
    ):
        raise SupportResultError("reference manifest identity changed")
    for source in EXPECTED_INPUTS:
        source_path = pathlib.Path(source["path"])
        if (
            stat.S_IMODE(source_path.stat().st_mode) != 0o444
            or sha256(source_path) != source["sha256"]
        ):
            raise SupportResultError("reference input changed or is mutable")
    # The observation spells the theorem field as `target`; the pack spells it
    # as `name`, so compare the common proof identity explicitly.
    theorem = manifest["support_theorem"]
    if "target" in theorem or theorem.get("name") != EXPECTED_SUPPORT["target"]:
        raise SupportResultError("reference theorem naming changed")
    if manifest.get("composition_receipts") != {
        "support_surface": "ac8babcdbc897d258884ddec13958794477305aa8d99d222bf850970574103d8",
        "native_recurrence": "19c7ff401412febfb8d9dae825eca50b1d8d287450dcdf1dc711fdae72a703f5",
        "target_recurrence": "63183a214d54f03b4b176a6ebc64fa8f68b373de0e94061c8cc13c28f9acb380",
        "target_addition": "3cd6871942719adf324064e0ffbe455dcf40d1a08c812cbf31834ed3906dc086",
    }:
        raise SupportResultError("manifest composition receipts changed")
    if manifest.get("target_boundary") != {
        "fact_id": "F:ml430-nat-gcd-fib-add-self-5a92d5e3",
        "definition": "Axeyum.Autogenesis.Coverage.r091",
        "epistemic_status": "open",
        "support_theorems_reconstructed": 1,
        "support_theorems_planned": 2,
        "exact_source_target_submissions": 0,
    }:
        raise SupportResultError("target boundary changed")
    if manifest.get("authority") != EXPECTED_AUTHORITY:
        raise SupportResultError("manifest authority changed")


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    result = load(RESULT) if result is None else result
    if (
        result.get("schema_version") != 1
        or result.get("kind")
        != "axeyum-autogenesis-mathlib-nat-gcd-fib-add-self-support-result"
        or result.get("state")
        != "first-support-reconstructed-no-target-or-ledger-credit"
        or result.get("tooling_commit")
        != "f8c7febc631d6820ac8a8e827a6434bdcdc0cd8e"
    ):
        raise SupportResultError("result identity changed")

    plan = result["frozen_plan"]
    if sha256(ROOT / plan["path"]) != plan["sha256"]:
        raise SupportResultError("frozen plan changed")
    if result.get("implementation") != EXPECTED_IMPLEMENTATION:
        raise SupportResultError("implementation inventory changed")
    for implementation in result["implementation"]:
        completed = subprocess.run(
            ["git", "show", f"{result['tooling_commit']}:{implementation['path']}"],
            cwd=ROOT,
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        if (
            completed.returncode
            or hashlib.sha256(completed.stdout).hexdigest()
            != implementation["sha256"]
        ):
            raise SupportResultError("historical implementation changed")

    expected_result = {
        "fact_id": "F:ml430-nat-gcd-fib-add-self-5a92d5e3",
        "target_definition": "Axeyum.Autogenesis.Coverage.r091",
        "support_id": "fibonacci-successor-addition-v1",
        "support_theorem": "Axeyum.Autogenesis.NatFibSuccessorAddition",
        "support_theorems_reconstructed": 1,
        "support_theorems_planned": 2,
        "goal_sha256": EXPECTED_SUPPORT["goal_sha256"],
        "proof_sha256": EXPECTED_SUPPORT["proof_sha256"],
        "declaration_sha256": EXPECTED_SUPPORT["declaration_sha256"],
        "axiom_footprint": [],
        "fresh_reconstructions": 2,
        "kernel_submissions": 2,
        "exact_source_target_submissions": 0,
        "executor_invocations": 0,
        "retries": 0,
        "semantic_theorem_receipts_issued": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }
    if result.get("result") != expected_result:
        raise SupportResultError("bounded result changed")

    archive = result["reference_pack"]
    root = pathlib.Path(archive["root"])
    manifest_path = root / archive["manifest"]
    if (
        archive.get("mode") != "0555"
        or
        stat.S_IMODE(root.stat().st_mode) != 0o555
        or stat.S_IMODE(manifest_path.stat().st_mode) != 0o444
        or manifest_path.stat().st_size != archive["manifest_bytes"]
        or sha256(manifest_path) != archive["manifest_sha256"]
    ):
        raise SupportResultError("reference pack changed or is mutable")
    manifest = load(manifest_path)
    validate_manifest(manifest)
    observation_row = manifest["observations"]
    if len(observation_row) != 1 or observation_row[0].get("mode") != "0444":
        raise SupportResultError("observation inventory changed")
    observation_path = root / observation_row[0]["file"]
    if (
        stat.S_IMODE(observation_path.stat().st_mode) != 0o444
        or observation_path.stat().st_size != observation_row[0]["bytes"]
        or sha256(observation_path) != observation_row[0]["sha256"]
    ):
        raise SupportResultError("observation changed or is mutable")
    validate_observation(load(observation_path))
    return result


def main() -> int:
    try:
        result = validate()
        print(
            "AUTOGENESIS_NAT_GCD_FIB_ADD_SELF_SUPPORT_RESULT_OK|"
            f"commit={result['tooling_commit'][:12]}|supports=1/2|"
            "reconstructions=2|kernel_submissions=2/6|target_submissions=0/2|"
            "executions=0/1|retries=0|receipts=0|evaluation=0|ledger_writes=0"
        )
        return 0
    except (
        OSError,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        SupportResultError,
    ) as error:
        print(f"autogenesis-nat-gcd-fib-add-self-support-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
