#!/usr/bin/env python3
"""Verify the fail-closed integer Fibonacci support audit result."""

import hashlib
import json
import pathlib
import stat
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-int-fib-recurrence-support-audit-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-recurrence-support-audit-plan-v1.json"
PACK = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/int-fib-recurrence-support-audit-failure-v1")


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def main() -> int:
    try:
        result = json.loads(RESULT.read_text())
        if result != {
            "schema_version": 1,
            "kind": "axeyum-autogenesis-int-fib-recurrence-support-audit-result",
            "state": "sealed-parent-stream-does-not-yield-complete-two-root-audit-fresh-root-export-required",
            "plan_sha256": "fa4b2548e77317132b4cbbc8da230f314789ed1415c9ac94ef5b16646f142aeb",
            "failure_pack_manifest_sha256": "0b7e995479dd4df6d0705c451c29e5a07a415816a714ffcbf2b9e5b88a2a14a8",
            "requested_roots": ["Int.fib_natCast", "Int.fib_add_two"],
            "execution": {"batch_importer_runs": 1, "proof_bearing_stream_reads": 1, "completed_audit_documents": 0, "stdout_bytes": 0, "retries": 0},
            "conclusion": {"support_footprints_measured": False, "fresh_root_selected_export_required": True, "first_bottom_up_target": "Int.fib_natCast"},
            "authority": {"proof_terms_rendered": 0, "theorem_types_rendered": 0, "theorem_values_rendered": 0, "support_theorem_credit": 0, "fact_status_changes": 0, "ledger_writes": 0},
            "limitations": "The process runner did not retain child stderr after the nonzero exit, so this result records only the authoritative absence of a completed audit and does not claim which requested root was absent."
        } or sha256(PLAN) != result["plan_sha256"] or stat.S_IMODE(PACK.stat().st_mode) != 0o555 or sha256(PACK / "manifest.json") != result["failure_pack_manifest_sha256"] or (PACK / "audit.stdout").stat().st_size != 0:
            raise RuntimeError("failure evidence or fail-closed conclusion changed")
        print("AUTOGENESIS_INT_FIB_RECURRENCE_SUPPORT_AUDIT_RESULT_OK|completed=0|retries=0|next=fresh-root-export|ledger_writes=0")
        return 0
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError, RuntimeError) as error:
        print(f"autogenesis-int-fib-recurrence-support-audit-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
