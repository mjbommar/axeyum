#!/usr/bin/env python3
"""Validate M2 completion-last evidence-store semantics without running Lean."""

from __future__ import annotations

import argparse
import os
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import lean_u2_official_execution as BASE  # noqa: E402
from scripts import lean_u2_official_execution_m2 as M2  # noqa: E402


COMPLETION_SCHEMA = "axeyum-lean-u2-official-execution-m2-completion-v1"
RECORD_SET_DOMAIN = "axeyum-lean-u2-official-execution-m2-record-set-v1"

FIXED_JSON_PATHS = (
    "source.json",
    "toolchain.json",
    "tools.json",
    "platform.json",
    "lane.json",
    "run.json",
    "shard.json",
    "harness.json",
    "discovery.json",
    "spec.json",
    "prelaunch.json",
    "terminal.json",
    "junit.json",
    "post.json",
    "projection.json",
)
FIXED_RAW_PATHS = (
    "raw/discovery.json",
    "raw/stdout.bin",
    "raw/stderr.bin",
    "raw/junit.xml",
)
FIXED_ARTIFACT_PATHS = (
    "artifacts/with_stage1_test_env.sh",
    "artifacts/CTestTestfile.cmake",
)
ALLOWED_TOP = {
    *FIXED_JSON_PATHS,
    "raw",
    "artifacts",
    "generated",
    "cases",
    "quarantine",
    "completion.json",
}


class M2StoreError(ValueError):
    """The M2 evidence store is incomplete, mutable, or inconsistent."""


def case_path(ordinal: int) -> str:
    if not 0 <= ordinal < M2.SHARD_CASE_COUNT:
        raise M2StoreError("M2 case ordinal is outside the frozen shard")
    return f"cases/{ordinal:04d}.json"


def generated_path(source_path: str) -> str:
    path = Path(source_path)
    if path.is_absolute() or ".." in path.parts or not path.parts:
        raise M2StoreError("unsafe M2 generated artifact path")
    return (Path("generated") / path).as_posix()


def _load(path: Path) -> Any:
    try:
        return BASE.load_canonical(path)
    except BASE.U2ExecutionError as error:
        raise M2StoreError(f"cannot load M2 evidence record: {path}") from error


def _descriptor(path: str, payload: bytes) -> dict[str, Any]:
    return {
        "path": path,
        "bytes": len(payload),
        "sha256": BASE.sha256_bytes(payload),
    }


def _validate_descriptor(root: Path, descriptor: Any, expected_path: str) -> None:
    try:
        payload = (root / expected_path).read_bytes()
    except OSError as error:
        raise M2StoreError(f"missing M2 retained payload: {expected_path}") from error
    if (
        not isinstance(descriptor, dict)
        or descriptor != _descriptor(expected_path, payload)
    ):
        raise M2StoreError(f"M2 retained payload descriptor drift: {expected_path}")


def _clean_tracked_checkout_files(root: Path) -> set[str]:
    """Return non-executable tracked files when Git reproduces retained bytes.

    Git stores only the executable bit, so the creation-time 0444 permission is
    not portable to a fresh worktree.  A normal writable checkout is equivalent
    only when the file is a clean, tracked 100644 entry under this evidence root.
    """
    try:
        relative_root = root.resolve().relative_to(ROOT).as_posix()
    except ValueError:
        return set()
    git = shutil.which("git")
    if git is None:
        return set()
    git = os.path.realpath(git)
    clean = subprocess.run(
        [git, "diff", "--quiet", "--no-ext-diff", "--", relative_root],
        cwd=ROOT,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if clean.returncode != 0:
        return set()
    listed = subprocess.run(
        [git, "ls-files", "--stage", "-z", "--", relative_root],
        cwd=ROOT,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if listed.returncode != 0:
        return set()
    tracked = set()
    prefix = relative_root.rstrip("/") + "/"
    for raw_record in listed.stdout.split(b"\0"):
        if not raw_record:
            continue
        try:
            metadata, raw_path = raw_record.split(b"\t", 1)
            mode = metadata.split(b" ", 1)[0]
            repository_path = os.fsdecode(raw_path)
        except ValueError:
            return set()
        if mode == b"100644" and repository_path.startswith(prefix):
            tracked.add(repository_path[len(prefix) :])
    return tracked


def accepted_inventory(root: Path, *, include_completion: bool) -> list[dict[str, Any]]:
    if not root.is_dir() or root.is_symlink():
        raise M2StoreError("M2 evidence root must be a real directory")
    extras = sorted(path.name for path in root.iterdir() if path.name not in ALLOWED_TOP)
    if extras:
        raise M2StoreError(f"unexpected M2 evidence entry: {extras[0]}")
    rows = []
    clean_tracked_files: set[str] | None = None
    for path in sorted(root.rglob("*"), key=lambda item: item.relative_to(root).as_posix()):
        relative = path.relative_to(root)
        if relative.parts[0] == "quarantine":
            continue
        if relative.as_posix() == "completion.json" and not include_completion:
            continue
        if path.is_symlink():
            raise M2StoreError(f"symlinked M2 evidence path: {relative.as_posix()}")
        if path.is_dir():
            continue
        if not path.is_file():
            raise M2StoreError(f"non-regular M2 evidence path: {relative.as_posix()}")
        permissions = path.stat().st_mode & 0o777
        if permissions != 0o444:
            if clean_tracked_files is None:
                clean_tracked_files = _clean_tracked_checkout_files(root)
            if permissions & 0o111 or relative.as_posix() not in clean_tracked_files:
                raise M2StoreError(
                    f"mutable M2 evidence file: {relative.as_posix()}"
                )
        rows.append(BASE.file_record(relative.as_posix(), path))
    return rows


def _require_paths(root: Path, paths: set[str]) -> None:
    missing = sorted(path for path in paths if not (root / path).is_file())
    if missing:
        raise M2StoreError(f"missing M2 evidence dependency: {missing[0]}")


def _validate_generic_seals(root: Path) -> None:
    for relative in FIXED_JSON_PATHS:
        value = _load(root / relative)
        schema = value.get("schema") if isinstance(value, dict) else None
        if not isinstance(schema, str) or not BASE.valid_seal(value, schema):
            raise M2StoreError(f"M2 evidence record seal drift: {relative}")


def validate_dependencies(
    root: Path, *, allow_completion: bool = False
) -> dict[str, Any]:
    completion = root / "completion.json"
    if not allow_completion and (completion.exists() or completion.is_symlink()):
        raise M2StoreError("M2 completion exists before dependency validation")
    required = {*FIXED_JSON_PATHS, *FIXED_RAW_PATHS, *FIXED_ARTIFACT_PATHS}
    required.update(case_path(index) for index in range(M2.SHARD_CASE_COUNT))
    _require_paths(root, required)
    accepted_inventory(root, include_completion=False)
    _validate_generic_seals(root)

    spec = _load(root / "spec.json")
    terminal = _load(root / "terminal.json")
    junit = _load(root / "junit.json")
    post = _load(root / "post.json")
    projection = _load(root / "projection.json")
    harness = _load(root / "harness.json")
    if M2.validate_spec(spec):
        raise M2StoreError("M2 retained spec drift")
    if not BASE.valid_seal(harness, M2.HARNESS_SCHEMA):
        raise M2StoreError("M2 retained harness drift")
    junit_failures = M2.validate_junit_projection(junit)
    if junit_failures:
        raise M2StoreError("; ".join(junit_failures))
    expected_projection = M2.result_projection(junit, post)
    if projection != expected_projection:
        raise M2StoreError("M2 retained result projection drift")
    records = [_load(root / case_path(index)) for index in range(M2.SHARD_CASE_COUNT)]
    case_failures = M2.validate_case_records(
        records,
        spec=spec,
        terminal=terminal,
        junit=junit,
    )
    if case_failures:
        raise M2StoreError("; ".join(case_failures))

    discovery = _load(root / "discovery.json")
    _validate_descriptor(root, discovery.get("raw"), "raw/discovery.json")
    if discovery.get("normalized") != harness.get("discovery"):
        raise M2StoreError("M2 discovery/harness projection drift")
    _validate_descriptor(root, junit.get("raw"), "raw/junit.xml")
    raw_outputs = terminal.get("raw_outputs", [])
    expected_raw = [
        _descriptor(path, (root / path).read_bytes())
        for path in ("raw/stderr.bin", "raw/stdout.bin")
    ]
    if raw_outputs != expected_raw:
        raise M2StoreError("M2 terminal raw-output closure drift")

    wrapper_payload = (root / FIXED_ARTIFACT_PATHS[0]).read_bytes()
    ctest_payload = (root / FIXED_ARTIFACT_PATHS[1]).read_bytes()
    if harness.get("wrapper") != {
        "bytes": len(wrapper_payload),
        "sha256": BASE.sha256_bytes(wrapper_payload),
        "mode": 0o755,
    } or harness.get("ctest_file") != {
        "bytes": len(ctest_payload),
        "sha256": BASE.sha256_bytes(ctest_payload),
    }:
        raise M2StoreError("M2 retained harness artifact closure drift")

    generated_rows = post.get("generated_files", [])
    generated_evidence_paths = set()
    for row in generated_rows:
        relative = generated_path(row["path"])
        generated_evidence_paths.add(relative)
        payload = (root / relative).read_bytes()
        if (
            row.get("kind") != "file"
            or row.get("target") is not None
            or row.get("bytes") != len(payload)
            or row.get("sha256") != BASE.sha256_bytes(payload)
        ):
            raise M2StoreError(f"M2 generated artifact payload drift: {row['path']}")
    _require_paths(root, generated_evidence_paths)
    retained_wrapper = root / generated_path("tests/with_stage1_test_env.sh")
    if not retained_wrapper.is_file() or retained_wrapper.read_bytes() != wrapper_payload:
        raise M2StoreError("M2 generated wrapper differs from retained harness artifact")
    inventory_paths = {row["path"] for row in accepted_inventory(root, include_completion=False)}
    observed_generated = {path for path in inventory_paths if path.startswith("generated/")}
    if observed_generated != generated_evidence_paths:
        raise M2StoreError("M2 generated artifact evidence closure drift")
    expected_inventory = {
        *FIXED_JSON_PATHS,
        *FIXED_RAW_PATHS,
        *FIXED_ARTIFACT_PATHS,
        *generated_evidence_paths,
        *(case_path(index) for index in range(M2.SHARD_CASE_COUNT)),
    }
    if inventory_paths != expected_inventory:
        raise M2StoreError("M2 evidence namespace closure drift")
    return {
        "spec": spec,
        "terminal": terminal,
        "junit": junit,
        "post": post,
        "projection": projection,
        "cases": records,
    }


def build_completion(root: Path) -> dict[str, Any]:
    bundle = validate_dependencies(root)
    dependencies = accepted_inventory(root, include_completion=False)
    case_records = [
        {
            "ordinal": index,
            "case_id": record["case_id"],
            "path": case_path(index),
            "record_sha256": record["record_sha256"],
        }
        for index, record in enumerate(bundle["cases"])
    ]
    projection = bundle["projection"]
    return BASE.seal(
        {
            "schema": COMPLETION_SCHEMA,
            "run_id": M2.RUN_ID,
            "attempt_id": M2.ATTEMPT_ID,
            "shard_id": M2.SHARD_ID,
            "state": "complete-local-official-shard-outcomes",
            "completion_installed_last": True,
            "dependencies": dependencies,
            "record_set_sha256": BASE.domain_digest(RECORD_SET_DOMAIN, dependencies),
            "case_records": case_records,
            "projection_sha256": projection["record_sha256"],
            "credits": projection["credits"],
            "record_sha256": "",
        },
        COMPLETION_SCHEMA,
    )


def install_completion(root: Path) -> dict[str, Any]:
    completion = build_completion(root)
    BASE.install_json(root, "completion.json", completion)
    return completion


def validate_complete_store(root: Path) -> dict[str, Any]:
    completion_path = root / "completion.json"
    if not completion_path.is_file() or completion_path.is_symlink():
        raise M2StoreError("missing real M2 completion record")
    if completion_path.stat().st_mode & 0o777 != 0o444:
        raise M2StoreError("mutable M2 completion record")
    completion = _load(completion_path)
    if not BASE.valid_seal(completion, COMPLETION_SCHEMA):
        raise M2StoreError("M2 completion identity drift")
    dependencies = accepted_inventory(root, include_completion=False)
    if (
        completion.get("run_id") != M2.RUN_ID
        or completion.get("attempt_id") != M2.ATTEMPT_ID
        or completion.get("shard_id") != M2.SHARD_ID
        or completion.get("state") != "complete-local-official-shard-outcomes"
        or completion.get("completion_installed_last") is not True
        or completion.get("dependencies") != dependencies
        or completion.get("record_set_sha256")
        != BASE.domain_digest(RECORD_SET_DOMAIN, dependencies)
    ):
        raise M2StoreError("M2 completion dependency closure drift")
    bundle = validate_dependencies(root, allow_completion=True)
    expected_cases = [
        {
            "ordinal": index,
            "case_id": record["case_id"],
            "path": case_path(index),
            "record_sha256": record["record_sha256"],
        }
        for index, record in enumerate(bundle["cases"])
    ]
    if (
        completion.get("case_records") != expected_cases
        or completion.get("projection_sha256")
        != bundle["projection"]["record_sha256"]
        or completion.get("credits") != bundle["projection"]["credits"]
    ):
        raise M2StoreError("M2 completion case or projection closure drift")
    return completion


def validate_offline_contract() -> dict[str, int]:
    M2.validate_offline_contract()
    if len(FIXED_JSON_PATHS) != len(set(FIXED_JSON_PATHS)):
        raise M2StoreError("duplicate M2 fixed JSON path")
    if len(FIXED_RAW_PATHS) != len(set(FIXED_RAW_PATHS)):
        raise M2StoreError("duplicate M2 raw path")
    if len(FIXED_ARTIFACT_PATHS) != len(set(FIXED_ARTIFACT_PATHS)):
        raise M2StoreError("duplicate M2 harness artifact path")
    return {
        "fixed_json": len(FIXED_JSON_PATHS),
        "fixed_raw": len(FIXED_RAW_PATHS),
        "fixed_artifacts": len(FIXED_ARTIFACT_PATHS),
        "case_records": M2.SHARD_CASE_COUNT,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if not args.check:
        parser.error("only the offline --check operation is implemented")
    try:
        summary = validate_offline_contract()
    except (M2.M2ContractError, M2StoreError) as error:
        print(f"LEAN_U2_M2_STORE_ERROR|{error}")
        return 1
    print(
        "LEAN_U2_M2_STORE|"
        f"json={summary['fixed_json']}|raw={summary['fixed_raw']}|"
        f"artifacts={summary['fixed_artifacts']}|cases={summary['case_records']}|"
        "live_execution=false|outcomes=0|parity=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
