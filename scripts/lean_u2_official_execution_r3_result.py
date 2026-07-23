#!/usr/bin/env python3
"""Publish the amended offline result for the frozen TL0.6.3 R3 execution."""

from __future__ import annotations

import sys
from pathlib import Path


REPOSITORY_ROOT = Path(__file__).resolve().parents[1]
if str(REPOSITORY_ROOT) not in sys.path:
    sys.path.insert(0, str(REPOSITORY_ROOT))

import argparse
import copy
import json
from typing import Any

from scripts import lean_u2_official_execution as BASE
from scripts import lean_u2_official_execution_r3 as R3


ROOT = BASE.ROOT
AMENDMENT = (
    ROOT
    / "docs/plan/lean-u2-official-execution-tl0.6.3-m0-r3-result-amendment-2026-07-22.md"
)
AMENDMENT_COMMIT = "7fc8755f8f948eb9a8f8ee48b0a24be23e7c6256"
AMENDMENT_SHA256 = "1aa0a0f83922f88238feec710e73f6de19a6e6d60a9888d4e876a98507fefdc2"
EXECUTION_IMPLEMENTATION = "d0390561a3044ccd6785cb1fdb0a3be2fb41d0bb"
R3_RUNNER_SHA256 = "061a7eca2e54f274c7289de4217d80db9a02f8e6f611f31667f7f01f059d835d"
R3_TEST_SHA256 = "73d7aa1f3facb2572c632a1804cbfdc24a7dc6f5c53d3e6e34314dc1e660cb90"
EVIDENCE_FILE_COUNT = 24
EVIDENCE_BYTES = 8_953_979
EVIDENCE_MANIFEST_SHA256 = (
    "982c0481784bf487995d76b6caf5c27e24d7c170115a114dccfa53d054327c78"
)
TERMINAL_SHA256 = "f3d04115b62a582122fb3fa5dee1f9818cf5e44791e928475bcd2a10a4874607"
JUNIT_SHA256 = "1cb384c6b4fd9655e79387a2d1aaa7845535fd621b2922f8a3ecf2c6a66dde0d"
CASE_SHA256 = "64fbf989ec5e458f6e8b69bad71c4c6532cd73e4be70baa998ffae4f702289eb"
COMPLETION_SHA256 = "a997934b49ef1fbb2be6322b49279dc3f183c22c2436e6fe05e211f722dcd240"
RESULT_SCHEMA = "axeyum-lean-u2-official-execution-r3-result-v2"
SUMMARY_SCHEMA = "axeyum-lean-u2-official-execution-r3-summary-v2"
RESULT_CLAIMS = {
    "official_lean_case_observed": True,
    "local_shard_complete": True,
    "parent_profile_complete": False,
    "official_provider_reproduced": False,
    "axeyum_observed": False,
    "matched_pair_formed": False,
    "performance_measured": False,
    "lean_parity_established": False,
}


def validate_frozen_inputs(
    root: Path,
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    if not AMENDMENT.is_file() or BASE.sha256_file(AMENDMENT) != AMENDMENT_SHA256:
        raise BASE.U2ExecutionError("R3 result amendment drift")
    runner = Path(R3.__file__).resolve()
    test = ROOT / "scripts/tests/test_lean_u2_official_execution_r3.py"
    if (
        BASE.sha256_file(runner) != R3_RUNNER_SHA256
        or BASE.sha256_file(test) != R3_TEST_SHA256
    ):
        raise BASE.U2ExecutionError("frozen R3 execution implementation drift")
    completion, evidence = R3.validate_evidence_root(root)
    if (
        len(evidence) != EVIDENCE_FILE_COUNT
        or sum(row["bytes"] for row in evidence) != EVIDENCE_BYTES
        or BASE.domain_digest(
            "axeyum-lean-u2-official-execution-evidence-files-v1", evidence
        )
        != EVIDENCE_MANIFEST_SHA256
        or BASE.load_canonical(root / "terminal.json").get("record_sha256")
        != TERMINAL_SHA256
        or BASE.load_canonical(root / "junit.json").get("record_sha256")
        != JUNIT_SHA256
        or BASE.load_canonical(root / "case.json").get("record_sha256")
        != CASE_SHA256
        or completion.get("record_sha256") != COMPLETION_SHA256
        or completion.get("projection", {}).get("case_outcome") != "passed"
    ):
        raise BASE.U2ExecutionError("frozen R3 evidence or outcome drift")
    return completion, evidence


def build_result_authority(root: Path) -> dict[str, Any]:
    validate_frozen_inputs(root)
    authority = R3.build_result_authority(
        root, implementation_revision=EXECUTION_IMPLEMENTATION
    )
    additions = [
        AMENDMENT,
        Path(__file__).resolve(),
        ROOT / "scripts/tests/test_lean_u2_official_execution_r3_result.py",
    ]
    source_by_path = {row["path"]: row for row in authority["source_inputs"]}
    for path in additions:
        relative = path.relative_to(ROOT).as_posix()
        source_by_path[relative] = {"path": relative, "sha256": BASE.sha256_file(path)}
    authority |= {
        "schema": RESULT_SCHEMA,
        "result_amendment_commit": AMENDMENT_COMMIT,
        "result_amendment_sha256": AMENDMENT_SHA256,
        "frozen_r3_runner_sha256": R3_RUNNER_SHA256,
        "frozen_r3_test_sha256": R3_TEST_SHA256,
        "source_inputs": [source_by_path[path] for path in sorted(source_by_path)],
        "record_sha256": "",
    }
    return BASE.seal(authority, RESULT_SCHEMA)


def validate_result_authority(authority: Any) -> list[str]:
    if not BASE.valid_seal(authority, RESULT_SCHEMA):
        return ["amended R3 result authority identity drift"]
    failures: list[str] = []
    if (
        authority.get("status") != "complete-local-official-case-history"
        or authority.get("implementation_revision") != EXECUTION_IMPLEMENTATION
        or authority.get("result_amendment_commit") != AMENDMENT_COMMIT
        or authority.get("result_amendment_sha256") != AMENDMENT_SHA256
        or authority.get("frozen_r3_runner_sha256") != R3_RUNNER_SHA256
        or authority.get("frozen_r3_test_sha256") != R3_TEST_SHA256
        or authority.get("r3_preregistration_commit")
        != R3.R3_PREREGISTRATION_COMMIT
        or authority.get("r3_plan_sha256") != R3.R3_PLAN_SHA256
    ):
        failures.append("amended R3 result source or preregistration drift")
    attempts = authority.get("attempts", [])
    if (
        not isinstance(attempts, list)
        or len(attempts) != 4
        or [row.get("id") for row in attempts if isinstance(row, dict)]
        != ["attempt-001", "attempt-002", "attempt-003", "attempt-004"]
        or [row.get("sequence") for row in attempts if isinstance(row, dict)]
        != [1, 2, 3, 4]
        or [row.get("official_outcomes") for row in attempts]
        != [0, 1, 0, 1]
        or attempts[1].get("outcome") != "failed"
        or attempts[2].get("status") != "failed-before-runner-import"
        or attempts[3].get("outcome") != "passed"
    ):
        failures.append("amended R3 result attempt history drift")
    summary = authority.get("summary", {})
    if (
        summary.get("process_attempts") != 4
        or summary.get("incomplete_process_attempts") != 2
        or summary.get("completed_process_attempts") != 2
        or summary.get("parent_selected_cases") != 3678
        or summary.get("local_shard_completed_cases") != 1
        or summary.get("official_outcomes") != 2
        or summary.get("official_passes") != 1
        or summary.get("official_failures") != 1
        or summary.get("parent_profiles_completed") != 0
        or summary.get("axeyum_outcomes") != 0
        or summary.get("paired_cells") != 0
        or summary.get("performance_rows") != 0
    ):
        failures.append("amended R3 result summary drift")
    if (
        authority.get("case", {}).get("outcome") != "passed"
        or authority.get("claims") != RESULT_CLAIMS
        or authority.get("credits") != R3.aggregate_credits("passed")
        or authority.get("failed_attempt")
        != R3.failed_attempt_dependency(
            live_readonly_validated=True, git_index_validated=True
        )
    ):
        failures.append("amended R3 result claim or credit drift")
    evidence = authority.get("evidence_files")
    if (
        not isinstance(evidence, list)
        or len(evidence) != EVIDENCE_FILE_COUNT
        or sum(row.get("bytes", 0) for row in evidence if isinstance(row, dict))
        != EVIDENCE_BYTES
        or authority.get("evidence_manifest_sha256")
        != EVIDENCE_MANIFEST_SHA256
    ):
        failures.append("amended R3 result evidence manifest drift")
    required_sources = {
        AMENDMENT.relative_to(ROOT).as_posix(): AMENDMENT_SHA256,
        "scripts/lean_u2_official_execution_r3.py": R3_RUNNER_SHA256,
        "scripts/tests/test_lean_u2_official_execution_r3.py": R3_TEST_SHA256,
        Path(__file__).resolve().relative_to(ROOT).as_posix(): BASE.sha256_file(
            Path(__file__).resolve()
        ),
        "scripts/tests/test_lean_u2_official_execution_r3_result.py": BASE.sha256_file(
            ROOT / "scripts/tests/test_lean_u2_official_execution_r3_result.py"
        ),
    }
    source_inputs = authority.get("source_inputs", [])
    source_by_path = {
        row.get("path"): row.get("sha256")
        for row in source_inputs
        if isinstance(row, dict)
    }
    if any(source_by_path.get(path) != digest for path, digest in required_sources.items()):
        failures.append("amended R3 result source-input drift")
    return failures


def result_summary(authority: dict[str, Any]) -> dict[str, Any]:
    return {
        "schema": SUMMARY_SCHEMA,
        "status": authority["status"],
        "implementation_revision": authority["implementation_revision"],
        "attempts": authority["attempts"],
        "case": authority["case"],
        "summary": authority["summary"],
        "claims": authority["claims"],
        "credits": authority["credits"],
        "authority_sha256": authority["record_sha256"],
    }


def render_markdown(authority: dict[str, Any]) -> str:
    summary = authority["summary"]
    evidence_bytes = sum(row["bytes"] for row in authority["evidence_files"])
    return f"""# TL0.6.3 M0 R3 official Lean execution summary

Generated from [the amended R3 authority](../lean-u2-official-execution-tl0.6.3-m0-r3-v1.json).

- Status: **complete local official-case history**
- Execution implementation: `{authority['implementation_revision']}`
- Attempt 002 retained outcome: **failed**
- Attempt 003 retained state: **failed before runner import**
- Attempt 004 outcome: **passed**
- Process attempts / decided official outcomes: **4 / {summary['official_outcomes']}**
- Official passes / failures: **1 / 1**
- Unique parent selection coverage: **1 / {BASE.PARENT_SELECTED_COUNT:,}** cases
- Attempt-004 evidence: **{len(authority['evidence_files'])} files / {evidence_bytes:,} bytes**
- Parent/provider completions, Axeyum outcomes, pairs, performance rows: **0**
- Complete populations / axes / gates / Lean parity credit: **0 / 0 / 0 / 0**

The two bounded positive claims mean only that one local official case was
observed and its singleton shard completed. They do not complete the parent,
reproduce an official provider, observe Axeyum, form a semantic pair, measure
performance, or establish Lean 4 parity.
"""


def generate_result(*, root: Path, check: bool) -> None:
    if check:
        if not R3.RESULT_AUTHORITY.is_file():
            raise BASE.U2ExecutionError("missing committed amended R3 authority")
        authority = BASE.load_json(R3.RESULT_AUTHORITY)
        failures = validate_result_authority(authority)
        if failures:
            raise BASE.U2ExecutionError("; ".join(failures))
        if authority != build_result_authority(root):
            raise BASE.U2ExecutionError("committed amended R3 authority is stale")
    else:
        authority = build_result_authority(root)
        failures = validate_result_authority(authority)
        if failures:
            raise BASE.U2ExecutionError("; ".join(failures))
    outputs = {
        R3.RESULT_AUTHORITY: json.dumps(authority, indent=2) + "\n",
        R3.RESULT_JSON: json.dumps(result_summary(authority), indent=2) + "\n",
        R3.RESULT_MARKDOWN: render_markdown(authority),
    }
    if check:
        stale = [
            path
            for path, content in outputs.items()
            if not path.is_file() or path.read_text(encoding="utf-8") != content
        ]
        if stale:
            raise BASE.U2ExecutionError("stale amended R3 generated result")
    else:
        for path, content in outputs.items():
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content, encoding="utf-8")
    print(
        f"LEAN_U2_OFFICIAL_R3_AMENDED_RESULT|case={BASE.CASE_ID}|outcome=passed|"
        "official_outcomes=2|parent_complete=false|axeyum=0|pairs=0|parity_credit=0"
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command_name", required=True)
    validate = commands.add_parser("validate")
    validate.add_argument("--evidence-root", type=Path, default=R3.DEFAULT_EVIDENCE_ROOT)
    result = commands.add_parser("result")
    result.add_argument("--evidence-root", type=Path, default=R3.DEFAULT_EVIDENCE_ROOT)
    result.add_argument("--check", action="store_true")
    args = parser.parse_args()
    try:
        if args.command_name == "validate":
            validate_frozen_inputs(args.evidence_root)
            print("LEAN_U2_OFFICIAL_R3_AMENDED_EVIDENCE_VALID|outcome=passed|parity_credit=0")
        elif args.command_name == "result":
            generate_result(root=args.evidence_root, check=args.check)
        else:  # pragma: no cover
            raise AssertionError(args.command_name)
    except (
        BASE.U2ExecutionError,
        BASE.STORE.CheckpointConflict,
        BASE.STORE.StoreEvidenceError,
    ) as exc:
        print(f"LEAN_U2_OFFICIAL_R3_AMENDED_ERROR|{exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
