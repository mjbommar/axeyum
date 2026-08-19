#!/usr/bin/env python3
"""Create or verify the internal typed evidence handoff for generated premise B."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import pathlib
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
CATALOG_SCRIPT = ROOT / "scripts/create-autogenesis-proposer-catalog.py"
PROPOSAL_VERIFIER = ROOT / "scripts/verify-autogenesis-induction-proposals.py"
OPERATION_VALIDATOR = ROOT / "scripts/validate-autogenesis-operations.py"
OPERATION_REGISTRY = ROOT / "artifacts/autogenesis/operations.json"


class EvidenceError(RuntimeError):
    """The handoff is malformed, stale, or makes an unsupported claim."""


def load_module(name: str, path: pathlib.Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise EvidenceError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode()).hexdigest()


def byte_digest(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def registered_operation(fact_id: str) -> tuple[dict[str, Any], str]:
    module = load_module(
        "validate_autogenesis_operations_for_evidence", OPERATION_VALIDATOR
    )
    try:
        registry = module.load_registry(OPERATION_REGISTRY, ROOT)
    except (OSError, json.JSONDecodeError, module.RegistryError) as error:
        raise EvidenceError(f"operation registry validation failed: {error}") from error
    matches = [
        operation
        for operation in registry["operations"]
        if operation["scope"] == "counterfactual-fixture-only"
        and fact_id in operation["applicability"]["fact_ids"]
    ]
    if len(matches) != 1:
        raise EvidenceError(
            f"fact {fact_id!r} has {len(matches)} fixture operations; expected exactly one"
        )
    return matches[0], module.digest(registry)


KERNEL_FIELDS = {
    "candidate",
    "canonical_type",
    "bundle_sha256",
    "catalog_sha256",
    "attempted",
    "budget",
    "accepted_plan_rank",
    "axiom_footprint",
    "retained_answer_dependencies",
}


def parse_kernel_evidence(text: str) -> dict[str, str]:
    lines = text.splitlines()
    if not lines or lines[0] != "AXEYUM_AUTOGENESIS_KERNEL_EVIDENCE_V1":
        raise EvidenceError("kernel evidence has the wrong or missing version header")
    fields: dict[str, str] = {}
    for index, line in enumerate(lines[1:], start=2):
        parts = line.split("\t")
        if len(parts) != 2 or not parts[0]:
            raise EvidenceError(f"kernel evidence line {index} is not key<TAB>value")
        key, value = parts
        if key in fields:
            raise EvidenceError(f"kernel evidence repeats field {key!r}")
        fields[key] = value
    missing = sorted(KERNEL_FIELDS.difference(fields))
    extra = sorted(set(fields).difference(KERNEL_FIELDS))
    if missing or extra:
        raise EvidenceError(f"kernel evidence field mismatch: missing={missing}, extra={extra}")
    return fields


def positive_int(fields: dict[str, str], key: str) -> int:
    try:
        value = int(fields[key])
    except ValueError as error:
        raise EvidenceError(f"kernel evidence {key} is not an integer") from error
    if value < 1 or str(value) != fields[key]:
        raise EvidenceError(f"kernel evidence {key} is not a canonical positive integer")
    return value


def build_evidence(
    *,
    snapshot: dict[str, Any],
    catalog: dict[str, Any],
    bundle: dict[str, Any],
    plans_bytes: bytes,
    kernel_fields: dict[str, str],
) -> dict[str, Any]:
    if snapshot.get("episode_id") != catalog.get("episode_id"):
        raise EvidenceError("catalog episode does not match snapshot")
    if catalog.get("phase") != "pre_b" or bundle.get("phase") != "pre_b":
        raise EvidenceError("premise evidence requires pre_b catalog and proposals")
    if kernel_fields["candidate"] != catalog["target"]["name"]:
        raise EvidenceError("kernel candidate does not match catalog target")
    if kernel_fields["canonical_type"] != catalog["target"]["canonical_type"]:
        raise EvidenceError("kernel candidate type does not match catalog target type")
    if kernel_fields["catalog_sha256"] != catalog["catalog_sha256"]:
        raise EvidenceError("kernel evidence names the wrong catalog")
    if kernel_fields["bundle_sha256"] != bundle["bundle_sha256"]:
        raise EvidenceError("kernel evidence names the wrong proposal bundle")
    if kernel_fields["axiom_footprint"] or kernel_fields["retained_answer_dependencies"]:
        raise EvidenceError("premise candidate is not axiom-free and isolated from retained answers")
    attempted = positive_int(kernel_fields, "attempted")
    budget = positive_int(kernel_fields, "budget")
    rank = positive_int(kernel_fields, "accepted_plan_rank")
    if attempted > budget or rank > attempted:
        raise EvidenceError("kernel search rank/attempt count exceeds its budget")
    matching = [plan for plan in bundle["plans"] if plan.get("rank") == rank]
    if len(matching) != 1:
        raise EvidenceError("accepted plan rank is absent or duplicated in proposal bundle")
    fact_id = snapshot["chain"]["premise"]["fact_id"]
    operation, registry_sha = registered_operation(fact_id)
    if operation["checker"]["operation"] != "axeyum-lean-kernel/autogenesis-induction-plan-check-v1":
        raise EvidenceError("registered operation names an unsupported kernel checker")
    evidence: dict[str, Any] = {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-kernel-premise-evidence",
        "identity": {
            "episode_id": snapshot["episode_id"],
            "snapshot_sha256": snapshot["snapshot_sha256"],
            "fact_id": fact_id,
            "formal_statement_sha256": byte_digest(
                catalog["target"]["canonical_type"].encode()
            ),
        },
        "route": {
            "kind": operation["producer"]["operation"],
            "operation_id": operation["id"],
            "operation_registry_sha256": registry_sha,
            "checker_operation": operation["checker"]["operation"],
            "catalog_sha256": catalog["catalog_sha256"],
            "proposal_bundle_sha256": bundle["bundle_sha256"],
            "plan_projection_sha256": byte_digest(plans_bytes),
            "accepted_plan": matching[0],
            "attempted": attempted,
            "budget": budget,
        },
        "result": {
            "outcome": "proved",
            "declaration": kernel_fields["candidate"],
            "canonical_type": kernel_fields["canonical_type"],
        },
        "acceptance": {
            "independent_kernel_checked": True,
            "axiom_footprint": [],
            "retained_answer_dependencies": [],
        },
    }
    evidence["evidence_sha256"] = digest(evidence)
    return evidence


def derive(args: argparse.Namespace) -> dict[str, Any]:
    catalog_module = load_module("autogenesis_catalog_for_evidence", CATALOG_SCRIPT)
    proposal_verifier = load_module(
        "autogenesis_induction_verifier_for_evidence", PROPOSAL_VERIFIER
    )
    snapshot = json.loads(args.snapshot.read_text())
    catalog = json.loads(args.catalog.read_text())
    expected_catalog = catalog_module.derive(args.snapshot.resolve(), "pre_b")
    if catalog != expected_catalog:
        raise EvidenceError("catalog is not the current derived pre_b catalog")
    bundle = json.loads(args.bundle.read_text())
    plans_bytes = args.plans.read_bytes()
    try:
        proposal_verifier.verify(catalog, bundle, plans_bytes.decode())
    except proposal_verifier.ProposalError as error:
        raise EvidenceError(f"proposal verification failed: {error}") from error
    kernel_fields = parse_kernel_evidence(args.kernel_evidence.read_text())
    return build_evidence(
        snapshot=snapshot,
        catalog=catalog,
        bundle=bundle,
        plans_bytes=plans_bytes,
        kernel_fields=kernel_fields,
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--snapshot", required=True, type=pathlib.Path)
    parser.add_argument("--catalog", required=True, type=pathlib.Path)
    parser.add_argument("--bundle", required=True, type=pathlib.Path)
    parser.add_argument("--plans", required=True, type=pathlib.Path)
    parser.add_argument("--kernel-evidence", required=True, type=pathlib.Path)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--output", type=pathlib.Path)
    action.add_argument("--verify", type=pathlib.Path)
    args = parser.parse_args()
    try:
        expected = derive(args)
        if args.verify is not None:
            actual = json.loads(args.verify.read_text())
            if actual != expected:
                raise EvidenceError("typed evidence is stale or mutated")
            print(f"AUTOGENESIS_PREMISE_EVIDENCE_OK|{expected['evidence_sha256']}")
        else:
            output = args.output.resolve()
            if output.exists():
                raise EvidenceError(f"refusing to overwrite {output}")
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_text(json.dumps(expected, indent=2, sort_keys=True) + "\n")
            print(f"AUTOGENESIS_PREMISE_EVIDENCE|{expected['evidence_sha256']}|{output}")
        return 0
    except (
        OSError,
        UnicodeDecodeError,
        json.JSONDecodeError,
        KeyError,
        TypeError,
        EvidenceError,
    ) as error:
        print(f"AUTOGENESIS_PREMISE_EVIDENCE_ERROR|{error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
