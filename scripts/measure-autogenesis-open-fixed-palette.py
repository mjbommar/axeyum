#!/usr/bin/env python3
"""Measure bounded application over proof-free open-goal capsules.

The NDJSON capsules and their fact-to-definition map are external inputs.  This
script records their hashes and replays the same fixed, target-independent
candidate palette for every goal.  It never changes fact status or registers
an operation.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from collections import Counter
from pathlib import Path
from typing import Any

from axeyum import producers
from axeyum.kernel import Declaration

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "artifacts/autogenesis/open-fixed-palette-census-v1.json"
CANDIDATES = tuple(
    sorted(
        (
            "Eq.refl",
            "Eq.symm",
            "Eq.trans",
            "congrArg",
            "Nat.zero_add",
            "Nat.add_zero",
            "Nat.mul_one",
            "Nat.one_mul",
            "Nat.le_refl",
            "Nat.le_trans",
            "Nat.succ_le_succ",
            "Nat.zero_le",
            "Nat.not_succ_le_zero",
        )
    )
)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def capsule_path(directory: Path, fact_id: str) -> Path:
    return directory / f"{fact_id.replace(':', '-', 1)}.ndjson"


def measure(mapping_path: Path, capsule_directory: Path) -> dict[str, Any]:
    mapping_bytes = mapping_path.read_bytes()
    mapping: dict[str, str] = json.loads(mapping_bytes)
    outcomes = []
    for fact_id, target_definition in sorted(mapping.items()):
        path = capsule_path(capsule_directory, fact_id)
        data = path.read_bytes()
        row: dict[str, Any] = {
            "fact_id": fact_id,
            "target_definition": target_definition,
            "capsule_bytes": len(data),
            "capsule_sha256": digest(data),
        }
        try:
            imported = producers.import_candidate_statement_ndjson(
                data, None, target_definition, list(CANDIDATES)
            )
            kernel = imported.kernel()
            candidate = producers.propose_bounded_application(
                kernel,
                imported.goal(),
                [kernel.name(name, must_exist=True) for name in CANDIDATES],
            )
            admitted = kernel.name("Axeyum.OpenCensus.Verified", must_exist=False)
            kernel.add_declaration(
                Declaration.theorem(admitted, [], imported.goal(), candidate.proof)
            )
            row.update(
                result="accepted",
                axiom_footprint=kernel.axiom_footprint(admitted),
                theorem_dependencies=kernel.theorem_dependencies(admitted),
                binders_used=candidate.binders_used,
                application_depth=candidate.application_depth,
                terms_considered=candidate.terms_considered,
            )
        except producers.Declined as decline:
            row.update(result="declined", reason_kind=decline.reason.kind)
        except producers.StatementImportError as error:
            message = str(error)
            trusted = re.search(
                r'trusted declaration "([^"]+)" \(([^)]+)\)', message
            )
            row.update(
                result="import_rejected",
                reason_kind="TrustedDeclarationInStatementClosure",
                trusted_declaration=(trusted.group(1) if trusted else None),
                trusted_declaration_kind=(trusted.group(2) if trusted else None),
            )
        outcomes.append(row)

    counts = Counter(row["result"] for row in outcomes)
    decline_reasons = Counter(
        row["reason_kind"] for row in outcomes if row["result"] == "declined"
    )
    rejection_declarations = Counter(
        row["trusted_declaration"]
        for row in outcomes
        if row["result"] == "import_rejected"
    )
    return {
        "schema_version": 1,
        "kind": "axeyum-open-fixed-palette-census",
        "authority": "measurement only; no operation registration or fact admission",
        "source": {
            "mathlib_commit": "c5ea00351c28e24afc9f0f84379aa41082b1188f",
            "lean_version": "4.30.0",
            "lean4export_format": "3.1.0",
            "mapping_sha256": digest(mapping_bytes),
            "external_capsule_directory": str(capsule_directory),
        },
        "strategy": {
            "producer": "bounded-application",
            "candidate_rule": "one fixed target-independent palette for every goal",
            "candidate_declarations": list(CANDIDATES),
            "forbidden_inputs": [
                "target theorem proof",
                "per-target candidate selection",
                "name or statement similarity",
                "transitive declaration closure as search candidates",
            ],
        },
        "census": {
            "population": len(outcomes),
            "accepted": counts["accepted"],
            "declined": counts["declined"],
            "import_rejected": counts["import_rejected"],
            "conversion_percent": round(
                100 * counts["accepted"] / len(outcomes), 1
            ),
            "decline_reasons": dict(sorted(decline_reasons.items())),
            "rejection_declarations": dict(sorted(rejection_declarations.items())),
        },
        "outcomes": outcomes,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--mapping", type=Path, required=True)
    parser.add_argument("--capsule-directory", type=Path, required=True)
    parser.add_argument("--output", type=Path, default=OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    rendered = json.dumps(
        measure(args.mapping, args.capsule_directory), indent=2, sort_keys=True
    ) + "\n"
    if args.check:
        if not args.output.is_file() or args.output.read_text() != rendered:
            print("OPEN_FIXED_PALETTE_CENSUS_ERROR|artifact is stale")
            return 1
    else:
        args.output.write_text(rendered)
    census = json.loads(rendered)["census"]
    print(
        "OPEN_FIXED_PALETTE_CENSUS|"
        f"population={census['population']}|accepted={census['accepted']}|"
        f"declined={census['declined']}|import_rejected={census['import_rejected']}|"
        f"conversion_percent={census['conversion_percent']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
