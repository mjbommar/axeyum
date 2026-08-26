#!/usr/bin/env python3
"""Materialize and verify a proof-isolated native Nat candidate capsule."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from axeyum import producers
from axeyum.kernel import Declaration, Kernel


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def materialize(
    target: str,
    target_definition: str,
    candidates: list[str],
) -> tuple[bytes, dict[str, object]]:
    if not candidates or candidates != sorted(set(candidates)):
        raise ValueError("candidate names must be a nonempty sorted unique list")
    source = Kernel()
    source.build_nat_prelude()
    target_declaration = source.get_declaration(target)
    if target_declaration is None or target_declaration.kind != "theorem":
        raise ValueError(f"target is not a constructed Nat theorem: {target}")
    target_name = source.name(target_definition, must_exist=False)
    source.add_declaration(
        Declaration.definition(
            target_name, [], source.sort_zero(), target_declaration.ty
        )
    )
    candidate_ids = [source.name(name, must_exist=True) for name in candidates]
    roots = [target_name, *candidate_ids]
    capsule = source.render_lean4export_ndjson_roots("4.30.0", roots).encode()
    if target.encode() in capsule:
        raise RuntimeError("root-selected capsule leaked the target theorem declaration")

    imported = producers.import_candidate_statement_ndjson(
        capsule, None, target_definition, candidates
    )
    kernel = imported.kernel()
    proposal = producers.propose_bounded_application(
        kernel,
        imported.goal(),
        [kernel.name(name, must_exist=True) for name in candidates],
    )
    admitted_name = kernel.name("Axeyum.Capsule.Verified", must_exist=False)
    kernel.add_declaration(
        Declaration.theorem(admitted_name, [], imported.goal(), proposal.proof)
    )
    proof_text = kernel.render_lean(proposal.proof)
    report = {
        "schema_version": 1,
        "kind": "axeyum-proof-isolated-candidate-capsule-receipt",
        "target": target,
        "target_definition": target_definition,
        "candidate_declarations": candidates,
        "capsule_bytes": len(capsule),
        "capsule_sha256": digest(capsule),
        "proof_sha256": digest(proof_text.encode()),
        "binders_used": proposal.binders_used,
        "application_depth": proposal.application_depth,
        "terms_considered": proposal.terms_considered,
        "axiom_footprint": kernel.axiom_footprint(admitted_name),
        "theorem_dependencies": kernel.theorem_dependencies(admitted_name),
        "target_theorem_bytes_present": False,
        "authority": "candidate and receipt only; no fact admission or autonomous-production credit",
    }
    return capsule, report


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--target", required=True)
    parser.add_argument("--target-definition", required=True)
    parser.add_argument("--candidate", action="append", dest="candidates", default=[])
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--receipt", type=Path, required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    candidates = sorted(args.candidates)
    capsule, report = materialize(args.target, args.target_definition, candidates)
    report = {**report, "external_artifact": {"path": str(args.output)}}
    rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.check:
        if not args.output.is_file() or args.output.read_bytes() != capsule:
            print("CANDIDATE_CAPSULE_ERROR|external capsule is absent or stale")
            return 1
        if not args.receipt.is_file() or args.receipt.read_text() != rendered:
            print("CANDIDATE_CAPSULE_ERROR|receipt is absent or stale")
            return 1
    else:
        if args.output.exists() or args.receipt.exists():
            raise FileExistsError("refusing to overwrite an existing capsule or receipt")
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_bytes(capsule)
        args.receipt.write_text(rendered)
    print(
        "CANDIDATE_CAPSULE|"
        f"target={args.target}|bytes={len(capsule)}|sha256={report['capsule_sha256']}|"
        f"dependencies={','.join(report['theorem_dependencies'])}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
