#!/usr/bin/env python3
"""Index exact imported theorem candidates with footprint-aware routing."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
AUTO = ROOT / "artifacts/autogenesis"
OUTPUT = AUTO / "imported-candidate-search-index-v1.json"
KIND = "axeyum-autogenesis-imported-candidate-audit"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def build(entries: list[tuple[Path, dict[str, Any]]]) -> dict[str, Any]:
    rows = []
    sources = []
    seen: set[tuple[str, str]] = set()
    for path, data in sorted(entries, key=lambda item: str(item[0])):
        if data.get("kind") != KIND:
            raise ValueError(f"{path} is not an imported candidate audit")
        candidate = data["candidate"]
        kernel = data["kernel_import"]
        key = candidate["name"], candidate["declaration_content_sha256"]
        if key in seen:
            raise ValueError(f"duplicate imported candidate identity: {key[0]}")
        seen.add(key)
        footprint = kernel["axiom_footprint"]
        axiom_free = kernel["axiom_free"]
        if axiom_free != (len(footprint) == 0):
            raise ValueError(f"{key[0]} axiom-free flag disagrees with footprint")
        disposition = "candidate-executable" if axiom_free else "reconstruct-required"
        rows.append(
            {
                "name": candidate["name"],
                "canonical_type": candidate["canonical_type"],
                "type_expression_sha256": candidate["type_expression_sha256"],
                "alpha_type_expression_sha256": candidate["alpha_type_expression_sha256"],
                "declaration_content_sha256": candidate["declaration_content_sha256"],
                "direct_dependency_sha256": candidate["direct_dependency_sha256"],
                "direct_theorem_dependencies": candidate["direct_theorem_dependencies"],
                "direct_theorem_dependency_count": len(candidate["direct_theorem_dependencies"]),
                "axiom_footprint": footprint,
                "axiom_footprint_size": len(footprint),
                "retrieval_disposition": disposition,
                "external_stream": data["external_stream"],
                "audit_artifact_path": str(path.relative_to(ROOT)),
                "audit_artifact_sha256": digest(path),
                "strategy_eligible": True,
                "execution_eligible": axiom_free,
            }
        )
        sources.append({"path": str(path.relative_to(ROOT)), "sha256": digest(path)})
    rows.sort(key=lambda row: (row["name"], row["declaration_content_sha256"]))
    return {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-imported-candidate-search-index",
        "state": "footprint-aware-candidate-routing",
        "authority": "search context only; index membership grants no semantic contract, proof, operation, applicability, transport, axiom-free, or fact-transition authority",
        "source": {"audit_artifacts": sources},
        "census": {
            "candidates": len(rows),
            "candidate_executable": sum(row["execution_eligible"] for row in rows),
            "reconstruct_required": sum(
                row["retrieval_disposition"] == "reconstruct-required" for row in rows
            ),
        },
        "candidates": rows,
        "limitations": "The current index contains only explicitly audited root-selected candidates. It is not a census of Lean or Mathlib theorem declarations.",
    }


def audit_entries() -> list[tuple[Path, dict[str, Any]]]:
    entries = []
    for path in sorted(AUTO.glob("*.json")):
        if path == OUTPUT:
            continue
        raw = path.read_bytes()
        if KIND.encode() not in raw:
            continue
        data = json.loads(raw)
        if data.get("kind") == KIND:
            entries.append((path, data))
    return entries


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--output", type=Path, default=OUTPUT)
    args = parser.parse_args()
    rendered = json.dumps(build(audit_entries()), indent=2, sort_keys=True) + "\n"
    if args.check:
        if not args.output.is_file() or args.output.read_text() != rendered:
            print("IMPORTED_CANDIDATE_INDEX_ERROR|artifact is stale")
            return 1
    else:
        args.output.write_text(rendered)
    census = json.loads(rendered)["census"]
    print(
        "IMPORTED_CANDIDATE_INDEX|"
        f"candidates={census['candidates']}|executable={census['candidate_executable']}|"
        f"reconstruct_required={census['reconstruct_required']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
