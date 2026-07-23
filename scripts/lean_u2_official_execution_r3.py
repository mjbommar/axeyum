#!/usr/bin/env python3
"""Run and validate TL0.6.3 M0 attempt-004 with a direct-file entry contract."""

from __future__ import annotations

import sys
from pathlib import Path


REPOSITORY_ROOT = Path(__file__).resolve().parents[1]
if str(REPOSITORY_ROOT) not in sys.path:
    sys.path.insert(0, str(REPOSITORY_ROOT))

import argparse
import base64
import copy
import hashlib
import json
from contextlib import contextmanager
from typing import Any, Iterator

from scripts import lean_u2_official_execution as BASE
from scripts import lean_u2_official_execution_r2 as R2


ROOT = BASE.ROOT
R3_PLAN = ROOT / "docs/plan/lean-u2-official-execution-tl0.6.3-m0-r3-plan-2026-07-22.md"
R3_PREREGISTRATION_COMMIT = "40f0a9220eea8ec8c09376ed7b9b8cbaecac8520"
R3_PLAN_SHA256 = "594d0edb8b1536e229afdcded6213b9a1d9cb1ab77d5a3db949015f0a9bda406"
R2_INVOCATION = (
    ROOT
    / "docs/plan/lean-u2-official-execution-tl0.6.3-m0-r2-invocation-v1.json"
)
R2_INVOCATION_BYTES_SHA256 = (
    "662f9e399660c0cca676988e7b4a7f9ba3a0f2dd3469e0b6313e09c56d6a18fc"
)
R2_INVOCATION_RECORD_SHA256 = (
    "efcf5236090d712923ac083c470f407d56cb26b7a67a83724ba89ba02b5194ed"
)
R2_RUNNER_SHA256 = "c9fa1a2b54decb03486c43514c632713337768b471971a9e2359c5c1d8dca03b"

LANE_ID = "official-ctest-local-8g-lean-j1-bundled-cc-v4"
ATTEMPT_ID = "attempt-004"
SEQUENCE = 4
DEFAULT_EVIDENCE_ROOT = (
    ROOT / "docs/plan/evidence/lean-u2-official-execution-tl0.6.3-m0-r3"
)
RESULT_AUTHORITY = ROOT / "docs/plan/lean-u2-official-execution-tl0.6.3-m0-r3-v1.json"
RESULT_JSON = ROOT / "docs/plan/generated/lean-u2-official-execution-tl0.6.3-m0-r3.json"
RESULT_MARKDOWN = ROOT / "docs/plan/generated/lean-u2-official-execution-tl0.6.3-m0-r3.md"
RESULT_SCHEMA = "axeyum-lean-u2-official-execution-r3-result-v1"
SUMMARY_SCHEMA = "axeyum-lean-u2-official-execution-r3-summary-v1"
PRIOR_ATTEMPTS_DOMAIN = "axeyum-lean-u2-r3-prior-attempts-v1"
ZERO_CLAIMS = {
    "parent_profile_complete": False,
    "official_provider_reproduced": False,
    "axeyum_observed": False,
    "matched_pair_formed": False,
    "performance_measured": False,
    "lean_parity_established": False,
}

ORIG_R2_VALIDATE_REPOSITORY_INPUTS = R2.validate_repository_inputs


def _decode_stream(stream: Any, label: str) -> bytes:
    if not isinstance(stream, dict):
        raise BASE.U2ExecutionError(f"R2 invocation {label} stream is missing")
    try:
        raw = base64.b64decode(stream.get("base64", ""), validate=True)
    except (TypeError, ValueError) as exc:
        raise BASE.U2ExecutionError(
            f"R2 invocation {label} base64 is invalid"
        ) from exc
    if (
        stream.get("bytes") != len(raw)
        or stream.get("sha256") != hashlib.sha256(raw).hexdigest()
    ):
        raise BASE.U2ExecutionError(f"R2 invocation {label} identity drift")
    return raw


def _validate_git_regular_file(path: Path) -> None:
    relative = path.relative_to(ROOT).as_posix()
    row = BASE._git(ROOT, "ls-files", "--stage", "--", relative)
    metadata, separator, indexed_path = row.partition("\t")
    fields = metadata.split()
    if (
        not separator
        or indexed_path != relative
        or len(fields) != 3
        or fields[0] != "100644"
    ):
        raise BASE.U2ExecutionError("R2 invocation Git index mode drift")


def validate_r2_invocation(*, require_git_index: bool) -> dict[str, Any]:
    if (
        not R2_INVOCATION.is_file()
        or R2_INVOCATION.is_symlink()
        or BASE.sha256_file(R2_INVOCATION) != R2_INVOCATION_BYTES_SHA256
    ):
        raise BASE.U2ExecutionError("R2 invocation authority physical drift")
    record = BASE.load_json(R2_INVOCATION)
    if (
        not BASE.valid_seal(record, record.get("schema", ""))
        or record.get("schema")
        != "axeyum-lean-u2-official-execution-r2-invocation-v1"
        or record.get("record_sha256") != R2_INVOCATION_RECORD_SHA256
        or record.get("status") != "failed-before-runner-import"
        or record.get("implementation_revision")
        != "660915572968435f68b7a08fd95e737db6ef7762"
        or record.get("attempt_id") != "attempt-003"
        or record.get("sequence") != 3
        or record.get("environment") != {"state": "not-recorded", "value": None}
    ):
        raise BASE.U2ExecutionError("R2 invocation authority identity drift")
    stdout = _decode_stream(record.get("terminal", {}).get("stdout"), "stdout")
    stderr = _decode_stream(record.get("terminal", {}).get("stderr"), "stderr")
    terminal = record.get("terminal", {})
    if (
        stdout != b""
        or len(stderr) != 265
        or hashlib.sha256(stderr).hexdigest()
        != "743f4e81513ab9f004ccab1115da538340a490b805d783e285f26ddcbafb8ca2"
        or terminal.get("class") != "exited"
        or terminal.get("exit_code") != 1
        or terminal.get("signal") is not None
        or terminal.get("runner_import_completed") is not False
        or terminal.get("harness_prepared") is not False
        or terminal.get("ctest_launched") is not False
        or record.get("postconditions")
        != {
            "private_work_root_absent": True,
            "evidence_root_absent": True,
            "official_outcome_created": False,
            "completion_created": False,
        }
        or record.get("summary", {}).get("process_attempts") != 3
        or record.get("summary", {}).get("official_outcomes") != 1
        or record.get("credits", {}).get("parity_credit") != 0
        or record.get("claims") != ZERO_CLAIMS
    ):
        raise BASE.U2ExecutionError("R2 invocation terminal or credit drift")
    if require_git_index:
        _validate_git_regular_file(R2_INVOCATION)
    return record


def r2_invocation_dependency(*, git_index_validated: bool) -> dict[str, Any]:
    return {
        "path": R2_INVOCATION.relative_to(ROOT).as_posix(),
        "implementation_revision": "660915572968435f68b7a08fd95e737db6ef7762",
        "attempt_id": "attempt-003",
        "sequence": 3,
        "status": "failed-before-runner-import",
        "authority_bytes_sha256": R2_INVOCATION_BYTES_SHA256,
        "authority_record_sha256": R2_INVOCATION_RECORD_SHA256,
        "terminal_class": "exited",
        "exit_code": 1,
        "runner_import_completed": False,
        "harness_prepared": False,
        "ctest_launched": False,
        "private_work_root_absent": True,
        "evidence_root_absent": True,
        "official_outcomes": 0,
        "parity_credit": 0,
        "git_index_mode": {
            "validated": git_index_validated,
            "mode": "100644" if git_index_validated else None,
        },
    }


def failed_attempt_dependency(
    *, live_readonly_validated: bool, git_index_validated: bool
) -> dict[str, Any]:
    attempts = [
        R2.ORIG_FAILED_DEPENDENCY(
            live_readonly_validated=live_readonly_validated,
            git_index_validated=git_index_validated,
        ),
        R2.r1_attempt_dependency(
            live_readonly_validated=live_readonly_validated,
            git_index_validated=git_index_validated,
        ),
        r2_invocation_dependency(git_index_validated=git_index_validated),
    ]
    payload = {
        "attempts": attempts,
        "process_attempts": 3,
        "incomplete_process_attempts": 2,
        "completed_process_attempts": 1,
        "official_outcomes": 1,
        "official_passes": 0,
        "official_failures": 1,
        "parity_credit": 0,
    }
    return payload | {
        "identity_sha256": BASE.domain_digest(PRIOR_ATTEMPTS_DOMAIN, payload)
    }


def validate_failed_attempt(
    root: Path = BASE.FAILED_EVIDENCE_ROOT,
    *,
    require_live_readonly: bool,
    require_git_index: bool,
) -> dict[str, Any]:
    if root != BASE.FAILED_EVIDENCE_ROOT:
        raise BASE.U2ExecutionError("R3 prior-attempt root substitution")
    R2.ORIG_VALIDATE_FAILED_ATTEMPT(
        root,
        require_live_readonly=require_live_readonly,
        require_git_index=require_git_index,
    )
    R2.validate_r1_attempt(
        require_live_readonly=require_live_readonly,
        require_git_index=require_git_index,
    )
    validate_r2_invocation(require_git_index=require_git_index)
    return failed_attempt_dependency(
        live_readonly_validated=require_live_readonly,
        git_index_validated=require_git_index,
    )


def validate_repository_inputs() -> list[str]:
    failures = ORIG_R2_VALIDATE_REPOSITORY_INPUTS()
    if not R3_PLAN.is_file() or BASE.sha256_file(R3_PLAN) != R3_PLAN_SHA256:
        failures.append("R3 preregistration plan drift")
    if BASE.sha256_file(Path(R2.__file__).resolve()) != R2_RUNNER_SHA256:
        failures.append("frozen R2 runner drift")
    try:
        validate_r2_invocation(require_git_index=True)
    except BASE.U2ExecutionError as exc:
        failures.append(str(exc))
    return failures


def build_spec(**kwargs: Any) -> dict[str, Any]:
    spec = R2.ORIG_BUILD_SPEC(**kwargs)
    spec |= {
        "r2_preregistration_commit": R2.R2_PREREGISTRATION_COMMIT,
        "r2_plan_sha256": R2.R2_PLAN_SHA256,
        "r1_authority_bytes_sha256": R2.R1_AUTHORITY_BYTES_SHA256,
        "r1_authority_record_sha256": R2.R1_AUTHORITY_RECORD_SHA256,
        "r3_preregistration_commit": R3_PREREGISTRATION_COMMIT,
        "r3_plan_sha256": R3_PLAN_SHA256,
        "r2_invocation_bytes_sha256": R2_INVOCATION_BYTES_SHA256,
        "r2_invocation_record_sha256": R2_INVOCATION_RECORD_SHA256,
        "prior_attempts_sha256": failed_attempt_dependency(
            live_readonly_validated=True, git_index_validated=True
        )["identity_sha256"],
    }
    return BASE.seal(spec, BASE.SPEC_SCHEMA)


def validate_spec(spec: Any) -> list[str]:
    if not BASE.valid_seal(spec, BASE.SPEC_SCHEMA):
        return ["R3 spec identity drift"]
    expected = {
        "r2_preregistration_commit": R2.R2_PREREGISTRATION_COMMIT,
        "r2_plan_sha256": R2.R2_PLAN_SHA256,
        "r1_authority_bytes_sha256": R2.R1_AUTHORITY_BYTES_SHA256,
        "r1_authority_record_sha256": R2.R1_AUTHORITY_RECORD_SHA256,
        "r3_preregistration_commit": R3_PREREGISTRATION_COMMIT,
        "r3_plan_sha256": R3_PLAN_SHA256,
        "r2_invocation_bytes_sha256": R2_INVOCATION_BYTES_SHA256,
        "r2_invocation_record_sha256": R2_INVOCATION_RECORD_SHA256,
        "prior_attempts_sha256": failed_attempt_dependency(
            live_readonly_validated=True, git_index_validated=True
        )["identity_sha256"],
    }
    failures: list[str] = []
    if any(spec.get(key) != value for key, value in expected.items()):
        failures.append("R3 preregistration or attempt-history drift")
    environment = spec.get("environment", {})
    if "LEAN_CC" in environment or "PYTHONPATH" in environment:
        failures.append("R3 spec environment contains a forbidden override")
    probe = copy.deepcopy(spec)
    for key in expected:
        probe.pop(key, None)
    probe = BASE.seal(probe, BASE.SPEC_SCHEMA)
    failures.extend(R2.ORIG_VALIDATE_SPEC(probe))
    return failures


@contextmanager
def r2_r3_configuration() -> Iterator[None]:
    replacements = {
        "LANE_ID": LANE_ID,
        "ATTEMPT_ID": ATTEMPT_ID,
        "SEQUENCE": SEQUENCE,
        "build_spec": build_spec,
        "validate_spec": validate_spec,
        "validate_repository_inputs": validate_repository_inputs,
        "failed_attempt_dependency": failed_attempt_dependency,
        "validate_failed_attempt": validate_failed_attempt,
    }
    original = {name: getattr(R2, name) for name in replacements}
    for name, value in replacements.items():
        setattr(R2, name, value)
    try:
        yield
    finally:
        for name, value in original.items():
            setattr(R2, name, value)


def validate_evidence_root(
    root: Path, *, require_live_readonly: bool = False
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    with r2_r3_configuration():
        return R2.validate_evidence_root(
            root, require_live_readonly=require_live_readonly
        )


def aggregate_credits(outcome: str) -> dict[str, int]:
    return R2.aggregate_credits(outcome)


def build_result_authority(
    root: Path, *, implementation_revision: str
) -> dict[str, Any]:
    with r2_r3_configuration(), R2.base_r2_configuration():
        authority = R2.ORIG_BUILD_RESULT(
            root, implementation_revision=implementation_revision
        )
    outcome = authority["case"]["outcome"]
    current = authority["attempts"][1]
    additions = [
        R3_PLAN,
        R2_INVOCATION,
        Path(R2.__file__).resolve(),
        ROOT / "scripts/tests/test_lean_u2_official_execution_r2.py",
        Path(__file__).resolve(),
        ROOT / "scripts/tests/test_lean_u2_official_execution_r3.py",
    ]
    source_by_path = {row["path"]: row for row in authority["source_inputs"]}
    for path in additions:
        relative = path.relative_to(ROOT).as_posix()
        source_by_path[relative] = {"path": relative, "sha256": BASE.sha256_file(path)}
    credits = aggregate_credits(outcome)
    authority |= {
        "schema": RESULT_SCHEMA,
        "status": "complete-local-official-case-history",
        "r3_preregistration_commit": R3_PREREGISTRATION_COMMIT,
        "r3_plan_sha256": R3_PLAN_SHA256,
        "r2_invocation_bytes_sha256": R2_INVOCATION_BYTES_SHA256,
        "r2_invocation_record_sha256": R2_INVOCATION_RECORD_SHA256,
        "source_inputs": [source_by_path[path] for path in sorted(source_by_path)],
        "failed_attempt": failed_attempt_dependency(
            live_readonly_validated=True, git_index_validated=True
        ),
        "attempts": [
            {
                "id": "attempt-001",
                "sequence": 1,
                "status": "incomplete-process-failure",
                "terminal_sha256": BASE.FAILED_TERMINAL_SHA256,
                "junit_sha256": BASE.FAILED_JUNIT_SHA256,
                "evidence_manifest_sha256": BASE.FAILED_EVIDENCE_MANIFEST_SHA256,
                "official_outcomes": 0,
                "parity_credit": 0,
            },
            {
                "id": "attempt-002",
                "sequence": 2,
                "status": "complete-local-official-case-outcome",
                "outcome": "failed",
                "terminal_sha256": R2.R1_TERMINAL_SHA256,
                "junit_sha256": R2.R1_JUNIT_SHA256,
                "completion_sha256": R2.R1_COMPLETION_SHA256,
                "evidence_manifest_sha256": R2.R1_EVIDENCE_MANIFEST_SHA256,
                "official_outcomes": 1,
                "parity_credit": 0,
            },
            {
                "id": "attempt-003",
                "sequence": 3,
                "status": "failed-before-runner-import",
                "authority_sha256": R2_INVOCATION_RECORD_SHA256,
                "terminal_class": "exited",
                "exit_code": 1,
                "official_outcomes": 0,
                "parity_credit": 0,
            },
            current | {"outcome": outcome},
        ],
        "summary": authority["summary"]
        | {
            "process_attempts": 4,
            "incomplete_process_attempts": 2,
            "completed_process_attempts": 2,
            "official_outcomes": 2,
            "official_passes": credits["official_passes"],
            "official_failures": credits["official_failures"],
        },
        "credits": credits,
        "record_sha256": "",
    }
    return BASE.seal(authority, RESULT_SCHEMA)


def validate_result_authority(authority: Any) -> list[str]:
    if not BASE.valid_seal(authority, RESULT_SCHEMA):
        return ["R3 result authority identity drift"]
    failures: list[str] = []
    if (
        authority.get("status") != "complete-local-official-case-history"
        or authority.get("r3_preregistration_commit") != R3_PREREGISTRATION_COMMIT
        or authority.get("r3_plan_sha256") != R3_PLAN_SHA256
        or authority.get("r2_invocation_bytes_sha256")
        != R2_INVOCATION_BYTES_SHA256
        or authority.get("r2_invocation_record_sha256")
        != R2_INVOCATION_RECORD_SHA256
        or not BASE.HEX40.fullmatch(authority.get("implementation_revision", ""))
    ):
        failures.append("R3 result preregistration or implementation drift")
    attempts = authority.get("attempts", [])
    if (
        not isinstance(attempts, list)
        or len(attempts) != 4
        or [row.get("id") for row in attempts if isinstance(row, dict)]
        != ["attempt-001", "attempt-002", "attempt-003", ATTEMPT_ID]
        or [row.get("sequence") for row in attempts if isinstance(row, dict)]
        != [1, 2, 3, SEQUENCE]
        or attempts[0].get("official_outcomes") != 0
        or attempts[1].get("outcome") != "failed"
        or attempts[1].get("official_outcomes") != 1
        or attempts[2].get("status") != "failed-before-runner-import"
        or attempts[2].get("official_outcomes") != 0
        or attempts[3].get("outcome") not in {"passed", "failed"}
        or attempts[3].get("official_outcomes") != 1
    ):
        failures.append("R3 result attempt history drift")
    outcome = authority.get("case", {}).get("outcome")
    if outcome not in {"passed", "failed"} or authority.get(
        "credits"
    ) != aggregate_credits(outcome):
        failures.append("R3 result case or aggregate credit drift")
    summary = authority.get("summary", {})
    if (
        summary.get("process_attempts") != 4
        or summary.get("incomplete_process_attempts") != 2
        or summary.get("completed_process_attempts") != 2
        or summary.get("official_outcomes") != 2
        or summary.get("official_passes") != int(outcome == "passed")
        or summary.get("official_failures") != 1 + int(outcome == "failed")
        or summary.get("parent_profiles_completed") != 0
        or summary.get("axeyum_outcomes") != 0
        or summary.get("paired_cells") != 0
        or summary.get("performance_rows") != 0
    ):
        failures.append("R3 result summary drift")
    if authority.get("failed_attempt") != failed_attempt_dependency(
        live_readonly_validated=True, git_index_validated=True
    ):
        failures.append("R3 result prior-attempt dependency drift")
    evidence = authority.get("evidence_files")
    if (
        not isinstance(evidence, list)
        or authority.get("evidence_manifest_sha256")
        != BASE.domain_digest(
            "axeyum-lean-u2-official-execution-evidence-files-v1", evidence
        )
        or authority.get("claims") != ZERO_CLAIMS
    ):
        failures.append("R3 result evidence or claim drift")
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

Generated from
[the R3 authority](../lean-u2-official-execution-tl0.6.3-m0-r3-v1.json).

- Status: **complete local official-case history**
- Implementation revision: `{authority['implementation_revision']}`
- Attempt 002 retained outcome: **failed**
- Attempt 003 retained state: **failed before runner import**
- Attempt 004 outcome: **{authority['case']['outcome']}**
- Process attempts / decided official outcomes: **4 / {summary['official_outcomes']}**
- Official passes / failures: **{summary['official_passes']} / {summary['official_failures']}**
- Parent selection coverage: **1 / {BASE.PARENT_SELECTED_COUNT:,}** unique cases
- Attempt-004 evidence: **{len(authority['evidence_files'])} files / {evidence_bytes:,} bytes**
- Parent/provider completions, Axeyum outcomes, pairs, performance rows: **0**
- Complete populations / axes / gates / Lean parity credit: **0 / 0 / 0 / 0**

This history preserves both incomplete adapter attempts and the earlier local
official failure. It does not complete the parent profile, reproduce an
official provider, observe Axeyum, form a semantic pair, measure performance,
or establish Lean 4 parity.
"""


def generate_result(
    *, root: Path, implementation_revision: str | None, check: bool
) -> None:
    if check:
        if not RESULT_AUTHORITY.is_file():
            raise BASE.U2ExecutionError("missing committed R3 result authority")
        authority = BASE.load_json(RESULT_AUTHORITY)
        failures = validate_result_authority(authority)
        if failures:
            raise BASE.U2ExecutionError("; ".join(failures))
        rebuilt = build_result_authority(
            root, implementation_revision=authority["implementation_revision"]
        )
        if rebuilt != authority:
            raise BASE.U2ExecutionError("committed R3 result authority is stale")
    else:
        if implementation_revision is None:
            raise BASE.U2ExecutionError(
                "R3 result generation requires implementation revision"
            )
        authority = build_result_authority(
            root, implementation_revision=implementation_revision
        )
        failures = validate_result_authority(authority)
        if failures:
            raise BASE.U2ExecutionError("; ".join(failures))
    outputs = {
        RESULT_AUTHORITY: json.dumps(authority, indent=2) + "\n",
        RESULT_JSON: json.dumps(result_summary(authority), indent=2) + "\n",
        RESULT_MARKDOWN: render_markdown(authority),
    }
    if check:
        stale = [
            path
            for path, content in outputs.items()
            if not path.is_file() or path.read_text(encoding="utf-8") != content
        ]
        if stale:
            raise BASE.U2ExecutionError("stale R3 generated result")
    else:
        for path, content in outputs.items():
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content, encoding="utf-8")
    print(
        f"LEAN_U2_OFFICIAL_R3_RESULT|case={BASE.CASE_ID}|"
        f"outcome={authority['case']['outcome']}|official_outcomes=2|"
        "parent_complete=false|axeyum=0|pairs=0|parity_credit=0"
    )


def run_m0(args: argparse.Namespace) -> None:
    with r2_r3_configuration():
        R2.run_m0(args)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command_name", required=True)
    run = commands.add_parser("run-m0")
    run.add_argument("--implementation-revision", required=True)
    run.add_argument("--source-repo", type=Path, required=True)
    run.add_argument("--toolchain-root", type=Path, required=True)
    run.add_argument("--work-root", type=Path, required=True)
    run.add_argument("--evidence-root", type=Path, default=DEFAULT_EVIDENCE_ROOT)
    validate = commands.add_parser("validate")
    validate.add_argument("--evidence-root", type=Path, default=DEFAULT_EVIDENCE_ROOT)
    result = commands.add_parser("result")
    result.add_argument("--evidence-root", type=Path, default=DEFAULT_EVIDENCE_ROOT)
    result.add_argument("--implementation-revision")
    result.add_argument("--check", action="store_true")
    args = parser.parse_args()
    try:
        if args.command_name == "run-m0":
            run_m0(args)
        elif args.command_name == "validate":
            completion, _ = validate_evidence_root(args.evidence_root)
            print(
                f"LEAN_U2_OFFICIAL_R3_EVIDENCE_VALID|case={BASE.CASE_ID}|"
                f"outcome={completion['projection']['case_outcome']}|parity_credit=0"
            )
        elif args.command_name == "result":
            generate_result(
                root=args.evidence_root,
                implementation_revision=args.implementation_revision,
                check=args.check,
            )
        else:  # pragma: no cover
            raise AssertionError(args.command_name)
    except (
        BASE.U2ExecutionError,
        BASE.STORE.CheckpointConflict,
        BASE.STORE.StoreEvidenceError,
    ) as exc:
        print(f"LEAN_U2_OFFICIAL_R3_ERROR|{exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
