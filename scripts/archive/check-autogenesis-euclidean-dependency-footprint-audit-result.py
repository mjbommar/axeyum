#!/usr/bin/env python3
"""Verify the one-pass Euclidean dependency-footprint audit result."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / (
    "artifacts/autogenesis/"
    "euclidean-joint-div-mod-dependency-footprint-audit-plan-v1.json"
)
RESULT = ROOT / (
    "artifacts/autogenesis/"
    "euclidean-joint-div-mod-dependency-footprint-audit-result-v1.json"
)
TOOL = ROOT / (
    "crates/axeyum-lean-import/examples/"
    "euclidean_dependency_footprint_audit.rs"
)
STREAM = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/reference-packs/"
    "2387f116f-proof-isolated-div-mod-go-decline-v1/"
    "div-mod-go-reconstruct.ndjson"
)
RECEIPT_DIR = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/reference-packs/"
    "ef209e897-euclidean-dependency-audit-v1"
)
RECEIPT = RECEIPT_DIR / "manifest.json"

PLAN_SHA256 = "20f43cb36a1b8dc8ccf54810cb65fd6ab80daeca047209c81cc0f7bdcb036957"
TOOL_SHA256 = "40b7d3e773d64530a7ca43345bbcc323bcf31aa9dc53617015dcd64253137a40"
PRODUCER_SHA256 = "ef209e897dc16195204646d2aed69e97bb774cf6abe741ed2887dd610d1fc6b9"
RESULT_SHA256 = "9a27f06239e54fdd4979901c377f8f4675f6ff580d043244360d144aee7b29de"
RECEIPT_SHA256 = "fc6cffc7baec14790cc4f23461389c5ef229ccb5281ffea5c317efc91b7031f5"
STREAM_SHA256 = "b4793d50d2ef0d69786d28d044012f74d5f5f2279bf5d5a55e39acf0ffb1af7a"
IDENTITIES = {
    "Eq.symm": "fb271ec2ea3431e3c34737664fb7b6e308edb40ce00c7f038724eb0e4a08245f",
    "Nat.add_assoc": "ad242b76c1ef7474e7511fab52189f8c0143857c23ab6be1fb5d28fe972bc145",
    "Nat.add_comm": "4457a492f836549124e6f854cbde6f7687252088e361dfe961023803fc24cb22",
    "Nat.div.go.eq_1": "c31f2e764891ad2ce5d2d1e59638636302c236096f8fefd91dfaa9f289155763",
    "Nat.div_rec_fuel_lemma": "afd6d5a686da6d205d992c270ea2ccc640e70af612cab5bc13cee598cb28d6af",
    "Nat.modCore.go.eq_1": "aaf85a61edef7f6416bfccd8d817ca53c88cf7fe3d5b34bfbf166287e485448d",
    "Nat.mul_add": "2210e36afc0c895a118db1fb5ff490606c3a08c499757818629cde2abe020fb5",
    "Nat.mul_one": "3a41ec1862904a8bc915b1083a94bb3072c625c051388c7fcd740792004942c0",
    "Nat.not_lt_zero": "d748b3a556453ca019dbe6a575621d46676b0b26a6ab3e25f371c298e38c5dd3",
    "Nat.sub_add_cancel": "756d178b67958fe684cb9e64c8d0b40ff557a375ed14ba122c070bfa7b3616a5",
    "congr": "4a78e7643ebdd35c471d6dfa43410bd070d2c5cf6a2eb595cdedd1b56891f31d",
    "congrArg": "d39a34eb11556f4a80414b3cbda6ae21118baba14aa37ba6bff92265bf3a853b",
    "congrFun'": "8e56cb8737c7c3c5b3314918f833cb7ff7885cc45a2f0e89ccd94d327e69f2db",
    "dif_neg": "61f9d69746f9ff2f47b37d79060fb33e40fea47ce211fa393430ecc19d887993",
    "dif_pos": "11837796f69d2bcd08be7c90987cf0af8db1cecd39ff1b50910782b4613d89d6",
}


class AuditResultError(RuntimeError):
    """The measured carriers, population coverage, or no-credit state changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise AuditResultError(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    result = load(RESULT) if result is None else result
    if (
        result.get("schema_version") != 1
        or result.get("kind")
        != "axeyum-autogenesis-euclidean-dependency-footprint-audit-result"
        or result.get("state")
        != "direct-dependencies-classified-no-revised-proof-authority"
    ):
        raise AuditResultError("audit result identity changed")
    if sha256(PLAN) != PLAN_SHA256 or sha256(TOOL) != TOOL_SHA256:
        raise AuditResultError("plan or audit tool identity changed")
    if (
        stat.S_IMODE(RECEIPT_DIR.stat().st_mode) != 0o555
        or stat.S_IMODE(RECEIPT.stat().st_mode) != 0o444
        or sha256(RECEIPT) != RECEIPT_SHA256
    ):
        raise AuditResultError("audit receipt identity or mode changed")
    receipt = load(RECEIPT)
    if (
        receipt.get("measured_producer", {}).get("sha256") != PRODUCER_SHA256
        or sha256(RECEIPT_DIR / "producer.rs") != PRODUCER_SHA256
        or receipt.get("measured_output", {}).get("sha256") != RESULT_SHA256
        or sha256(RECEIPT_DIR / "result.json") != RESULT_SHA256
        or sha256(RESULT) != RESULT_SHA256
        or receipt.get("tracked_reusable_tool", {}).get("sha256_after_lint_only_cleanup")
        != TOOL_SHA256
        or receipt.get("tracked_reusable_tool", {}).get("audit_rerun_after_cleanup") is not False
    ):
        raise AuditResultError("measured producer/output receipt changed")
    if (
        stat.S_IMODE(STREAM.stat().st_mode) != 0o444
        or STREAM.stat().st_size != 460363
        or sha256(STREAM) != STREAM_SHA256
    ):
        raise AuditResultError("proof-bearing stream identity or mode changed")
    if result.get("plan") != {
        "path": "artifacts/autogenesis/euclidean-joint-div-mod-dependency-footprint-audit-plan-v1.json",
        "sha256": PLAN_SHA256,
    }:
        raise AuditResultError("result plan binding changed")
    rows = result.get("rows")
    if not isinstance(rows, list) or len(rows) != 15:
        raise AuditResultError("audit population coverage changed")
    by_name = {row.get("name"): row for row in rows if isinstance(row, dict)}
    if len(by_name) != 15 or list(by_name) != list(IDENTITIES):
        raise AuditResultError("audit population order or identity changed")
    for name, identity in IDENTITIES.items():
        row = by_name[name]
        expected_footprint = ["propext"] if name == "Nat.sub_add_cancel" else []
        expected_class = "propext-bearing" if expected_footprint else "empty-footprint"
        if (
            set(row) != {
                "name",
                "declaration_sha256",
                "axiom_footprint",
                "direct_theorem_dependencies",
                "class",
            }
            or row.get("declaration_sha256") != identity
            or row.get("axiom_footprint") != expected_footprint
            or row.get("class") != expected_class
            or not isinstance(row.get("direct_theorem_dependencies"), list)
            or row["direct_theorem_dependencies"]
            != sorted(row["direct_theorem_dependencies"])
        ):
            raise AuditResultError(f"audit row changed for {name}")
    if result.get("summary") != {
        "population": 15,
        "class_counts": {
            "empty-footprint": 14,
            "other-assumption-bearing": 0,
            "propext-bearing": 1,
        },
    }:
        raise AuditResultError("audit aggregate changed")
    if result.get("authority") != {
        "importer_runs": 1,
        "proof_bearing_stream_reads": 1,
        "proof_terms_rendered": 0,
        "theorem_values_rendered": 0,
        "revised_proof_compilations": 0,
        "new_authored_theorem_submissions": 0,
        "exact_target_submissions": 0,
        "executor_invocations": 0,
        "support_theorem_credit": 0,
        "fact_status_changes": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
        "retries": 0,
    }:
        raise AuditResultError("audit no-credit authority changed")
    return result


def main() -> int:
    try:
        validate()
        print(
            "AUTOGENESIS_EUCLIDEAN_DEPENDENCY_AUDIT_OK|population=15|empty=14|"
            "propext=1|carrier=Nat.sub_add_cancel|revised_proofs=0|evaluation=0|ledger_writes=0"
        )
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, AuditResultError) as error:
        print(f"autogenesis-euclidean-dependency-audit-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
