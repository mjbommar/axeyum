#!/usr/bin/env python3
"""Verify the exact Int.gcd bounded source-delta control."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import subprocess
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "artifacts/autogenesis/mathlib-int-gcd-source-delta-v1.json"
EXPECTED_RESULT = {
    "source": "Int.gcd",
    "source_content_sha256": "1b4460e69780e5080a107bc178b77ffe064585b9712c5f7468a80c02cdee0655",
    "selected_delta_steps": 1,
    "consulted_declarations": ["Int.gcd"],
    "residual_constants_left_opaque": ["Nat.gcd"],
    "recursive_delta_steps": 0,
    "theorem_dependency_walks": 0,
    "proof_free_template": True,
    "specialization_verified": True,
    "trace_eligible": True,
    "receipt_eligible": False,
}


class SourceDeltaError(RuntimeError):
    """The source-delta control changed, weakened, or overclaimed."""


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise SourceDeltaError(f"{path} is not an object")
    return value


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def canonical_digest(value: Any) -> str:
    return hashlib.sha256(
        json.dumps(value, ensure_ascii=False, separators=(",", ":")).encode()
    ).hexdigest()


def validate_observation(observation: dict[str, Any]) -> None:
    unsigned = dict(observation)
    claimed = unsigned.pop("observation_sha256", None)
    if claimed != canonical_digest(unsigned):
        raise SourceDeltaError("inner observation identity changed")
    expected_authority = {
        "partitions_inspected": ["train"],
        "held_out_inspected": False,
        "proof_bodies_inspected": False,
        "producer_target_attempts": 0,
        "contracts_admitted": 0,
        "ledger_writes": 0,
    }
    source = observation.get("source")
    template = observation.get("proof_free_template")
    trace = observation.get("bounded_delta_trace")
    if (
        observation.get("schema_version") != 1
        or observation.get("kind") != "axeyum-autogenesis-int-gcd-source-delta-control"
        or observation.get("state")
        != "mechanism-control-no-contract-proof-or-ledger-credit"
        or observation.get("authority") != expected_authority
        or not isinstance(source, dict)
        or not isinstance(template, dict)
        or not isinstance(trace, dict)
    ):
        raise SourceDeltaError("observation authority changed")
    if (
        source.get("artifact_file") != "r018.ndjson"
        or source.get("lean_version") != "4.30.0"
        or source.get("lean_githash") != "d024af099ca4bf2c86f649261ebf59565dc8c622"
        or source.get("definition") != "Int.gcd"
        or source.get("definition_content_sha256")
        != EXPECTED_RESULT["source_content_sha256"]
    ):
        raise SourceDeltaError("source identity changed")
    if (
        template.get("binders") != ["Int.gcd", "Nat.gcd"]
        or template.get("source_and_residual_absent_from_direct_constants") is not True
        or template.get("direct_constants") != ["Eq", "Int", "Int.natAbs", "Nat"]
        or template.get("specialization_verified") is not True
        or not isinstance(template.get("generalized_contract_sha256"), str)
        or len(template["generalized_contract_sha256"]) != 64
    ):
        raise SourceDeltaError("proof-free template changed")
    if (
        trace.get("rule") != "selected-transparent-definition-delta-v1"
        or trace.get("selected_source") != "Int.gcd"
        or trace.get("consulted_declarations") != ["Int.gcd"]
        or trace.get("universe_arguments") != 0
        or trace.get("term_arguments") != 0
        or trace.get("after_direct_constants") != ["Int", "Int.natAbs", "Nat.gcd"]
        or trace.get("residual_constants_left_opaque") != ["Nat.gcd"]
        or trace.get("recursive_delta_steps") != 0
        or trace.get("theorem_dependency_walks") != 0
        or not isinstance(trace.get("before_sha256"), str)
        or len(trace["before_sha256"]) != 64
        or not isinstance(trace.get("after_sha256"), str)
        or len(trace["after_sha256"]) != 64
    ):
        raise SourceDeltaError("bounded delta trace changed")


def validate() -> dict[str, Any]:
    manifest = load(MANIFEST)
    if (
        manifest.get("schema_version") != 1
        or manifest.get("kind") != "axeyum-autogenesis-mathlib-int-gcd-source-delta"
        or manifest.get("state") != "mechanism-control-no-contract-proof-or-ledger-credit"
        or manifest.get("result") != EXPECTED_RESULT
    ):
        raise SourceDeltaError("manifest contract changed")
    tooling = manifest["tooling_file"]
    result = subprocess.run(
        ["git", "show", f"{manifest['tooling_commit']}:{tooling['path']}"],
        cwd=ROOT,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if result.returncode or hashlib.sha256(result.stdout).hexdigest() != tooling["sha256"]:
        raise SourceDeltaError("tooling identity changed")
    archive = manifest["observation_archive"]
    root = pathlib.Path(archive["root"])
    path = root / archive["file"]
    if (
        sha256(path) != archive["file_sha256"]
        or path.stat().st_size != archive["bytes"]
        or stat.S_IMODE(path.stat().st_mode) != 0o444
        or stat.S_IMODE(root.stat().st_mode) != 0o555
    ):
        raise SourceDeltaError("external observation changed or is mutable")
    observation = load(path)
    if observation.get("observation_sha256") != archive["observation_sha256"]:
        raise SourceDeltaError("external semantic identity changed")
    validate_observation(observation)
    return manifest


def main() -> int:
    try:
        manifest = validate()
        print(
            "AUTOGENESIS_INT_GCD_SOURCE_DELTA_OK|"
            f"{manifest['observation_archive']['observation_sha256']}|"
            "source=Int.gcd|consulted=1|residual_opaque=Nat.gcd|"
            "trace_eligible=1|receipt_eligible=0|held_out=0|ledger_writes=0"
        )
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, SourceDeltaError) as error:
        print(f"autogenesis-int-gcd-source-delta: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
