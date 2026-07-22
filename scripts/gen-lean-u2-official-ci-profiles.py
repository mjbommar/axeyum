#!/usr/bin/env python3
"""Capture, validate, and render pinned Lean official CI test profiles.

TL0.6.1 records the CTest registrations.  This TL0.6.2 tool evaluates only the
isolated matrix-construction JavaScript from pinned Lean CI, resolves its
event predicates, and maps each enabled test job to an exact registered-case
selection.  It never executes a workflow step or a test and therefore cannot
record outcome or parity credit.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import re
import shlex
import subprocess
import sys
import tempfile
from collections import Counter
from pathlib import Path
from types import ModuleType
from typing import Any


ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "docs" / "plan" / "lean-u2-official-ci-profiles-v1.json"
OUT_JSON = ROOT / "docs" / "plan" / "generated" / "lean-u2-official-ci-profiles.json"
OUT_MD = ROOT / "docs" / "plan" / "generated" / "lean-u2-official-ci-profiles.md"
U2_MANIFEST = ROOT / "docs" / "plan" / "lean-u2-test-authority-v1.json"

SCHEMA = "axeyum-lean-u2-official-ci-profiles-v1"
LEAN_COMMIT = "d024af099ca4bf2c86f649261ebf59565dc8c622"
HEX = set("0123456789abcdef")

UPSTREAM_INPUTS = (
    (
        ".github/workflows/ci.yml",
        "e90ce40c73a73481b61651e1c10762dedabc72f963fd164d395ba9f2eecd1cad",
    ),
    (
        ".github/workflows/build-template.yml",
        "c5db66bb5612c767f3c9b6b45f95e59d0d01f9f25f110cf2f6e462b41ffe6226",
    ),
    (
        "CMakePresets.json",
        "31400a143d5bb683395a1f5b9eff09293f974b92764111b92be172833aa45466",
    ),
    (
        "tests/CMakeLists.txt",
        "1bc3c6f21b661104361936648823e5f357081d7026a9487f0b4b614d9aa1bca5",
    ),
    (
        "src/stdlib_flags.h",
        "4b69268baa96fb217ad805b15fc33410639809fb21b7df2f93371f1004acd5a4",
    ),
    (
        "stage0/src/stdlib_flags.h",
        "4b69268baa96fb217ad805b15fc33410639809fb21b7df2f93371f1004acd5a4",
    ),
)
U2_MANIFEST_SHA256 = "d7446e7965bac100ac6b5c607cbb7c87b5b80063fc23b3ec998fff2736d5d18e"

CONTEXT_SPECS: tuple[dict[str, Any], ...] = (
    {
        "id": "pr-l0",
        "event": "pull_request",
        "level": 0,
        "fast": False,
        "lake_ci": False,
        "is_pr": True,
        "is_push_to_master": False,
        "version_mode": "development",
    },
    {
        "id": "pr-l0-fast",
        "event": "pull_request",
        "level": 0,
        "fast": True,
        "lake_ci": False,
        "is_pr": True,
        "is_push_to_master": False,
        "version_mode": "development",
    },
    {
        "id": "pr-l0-lake",
        "event": "pull_request",
        "level": 0,
        "fast": False,
        "lake_ci": True,
        "is_pr": True,
        "is_push_to_master": False,
        "version_mode": "development",
    },
    {
        "id": "pr-l0-lake-fast",
        "event": "pull_request",
        "level": 0,
        "fast": True,
        "lake_ci": True,
        "is_pr": True,
        "is_push_to_master": False,
        "version_mode": "development",
    },
    {
        "id": "pr-l1",
        "event": "pull_request",
        "level": 1,
        "fast": False,
        "lake_ci": False,
        "is_pr": True,
        "is_push_to_master": False,
        "version_mode": "development",
    },
    {
        "id": "pr-l1-fast",
        "event": "pull_request",
        "level": 1,
        "fast": True,
        "lake_ci": False,
        "is_pr": True,
        "is_push_to_master": False,
        "version_mode": "development",
    },
    {
        "id": "pr-l1-lake",
        "event": "pull_request",
        "level": 1,
        "fast": False,
        "lake_ci": True,
        "is_pr": True,
        "is_push_to_master": False,
        "version_mode": "development",
    },
    {
        "id": "pr-l1-lake-fast",
        "event": "pull_request",
        "level": 1,
        "fast": True,
        "lake_ci": True,
        "is_pr": True,
        "is_push_to_master": False,
        "version_mode": "development",
    },
    {
        "id": "pr-l3",
        "event": "pull_request",
        "level": 3,
        "fast": False,
        "lake_ci": False,
        "is_pr": True,
        "is_push_to_master": False,
        "version_mode": "development",
    },
    {
        "id": "pr-l3-fast",
        "event": "pull_request",
        "level": 3,
        "fast": True,
        "lake_ci": False,
        "is_pr": True,
        "is_push_to_master": False,
        "version_mode": "development",
    },
    {
        "id": "pr-l3-lake",
        "event": "pull_request",
        "level": 3,
        "fast": False,
        "lake_ci": True,
        "is_pr": True,
        "is_push_to_master": False,
        "version_mode": "development",
    },
    {
        "id": "pr-l3-lake-fast",
        "event": "pull_request",
        "level": 3,
        "fast": True,
        "lake_ci": True,
        "is_pr": True,
        "is_push_to_master": False,
        "version_mode": "development",
    },
    {
        "id": "merge-group-l1",
        "event": "merge_group",
        "level": 1,
        "fast": False,
        "lake_ci": False,
        "is_pr": False,
        "is_push_to_master": False,
        "version_mode": "development",
    },
    {
        "id": "push-master-l1",
        "event": "push",
        "level": 1,
        "fast": False,
        "lake_ci": False,
        "is_pr": False,
        "is_push_to_master": True,
        "version_mode": "development",
    },
    {
        "id": "nightly-l2",
        "event": "schedule",
        "level": 2,
        "fast": False,
        "lake_ci": False,
        "is_pr": False,
        "is_push_to_master": False,
        "version_mode": "normalized-nightly",
    },
    {
        "id": "manual-nightly-l2",
        "event": "workflow_dispatch",
        "level": 2,
        "fast": False,
        "lake_ci": False,
        "is_pr": False,
        "is_push_to_master": False,
        "version_mode": "normalized-nightly",
    },
    {
        "id": "release-tag-l3",
        "event": "push-tag-v4.30.0",
        "level": 3,
        "fast": False,
        "lake_ci": False,
        "is_pr": False,
        "is_push_to_master": False,
        "version_mode": "release-v4.30.0",
    },
)

JOB_SPECS: tuple[tuple[str, str], ...] = (
    ("linux-release", "Linux release"),
    ("linux-lake", "Linux Lake"),
    ("linux-lake-cached", "Linux Lake (Cached)"),
    ("linux-reldebug", "Linux Reldebug"),
    ("linux-fsanitize", "Linux fsanitize"),
    ("macos-x86-64", "macOS"),
    ("macos-aarch64", "macOS aarch64"),
    ("windows-x86-64", "Windows"),
    ("linux-aarch64", "Linux aarch64"),
)

COMMENTED_JOB_NAMES = ("Linux LLVM", "Linux 32bit", "Web Assembly")
PORTABLE_FILTER = re.compile(r"^[A-Za-z0-9_./|\\-]+$")

CELL_FIELDS = {
    "id",
    "context_id",
    "job_id",
    "job_name",
    "job_order",
    "enabled",
    "secondary",
    "test",
    "state",
    "runner",
    "release",
    "shell",
    "preset",
    "cmake_options",
    "ctest_options",
    "selection_profile",
    "target_stage",
    "check_rebootstrap",
    "check_stage3",
    "test_bench",
    "cross",
    "post_test_binary_check",
    "sha256",
}
ATTEMPT_FIELDS = {
    "id",
    "cell_id",
    "phase",
    "target_stage",
    "preset",
    "ctest_options",
    "selection_set_id",
    "command",
    "junit_path",
    "outcome",
    "sha256",
}
SELECTION_FIELDS = {
    "id",
    "profile",
    "include_regex",
    "exclude_regex",
    "registered_count",
    "registered_ids_sha256",
    "selected_count",
    "selected_ids_sha256",
    "selected_case_ids",
    "excluded_count",
    "excluded_ids_sha256",
    "excluded_case_ids",
    "sha256",
}


class ProfileError(RuntimeError):
    """A fail-closed profile capture or validation failure."""


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(
        value, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def is_sha256(value: Any) -> bool:
    return (
        isinstance(value, str)
        and len(value) == 64
        and all(char in HEX for char in value)
    )


def json_text(value: Any) -> str:
    return json.dumps(value, indent=2, ensure_ascii=False) + "\n"


def load_json(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as handle:
        return json.load(handle)


def load_script(name: str, path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise ProfileError(f"cannot import {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def run(
    argv: list[str], *, cwd: Path | None = None
) -> subprocess.CompletedProcess[bytes]:
    try:
        return subprocess.run(
            argv,
            cwd=cwd,
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
    except (OSError, subprocess.CalledProcessError) as error:
        stderr = getattr(error, "stderr", b"") or b""
        detail = stderr.decode("utf-8", errors="replace").strip()
        raise ProfileError(f"command failed: {' '.join(argv)}\n{detail}") from error


def git(repo: Path, *args: str) -> bytes:
    return run(["git", "-C", str(repo), *args]).stdout


def git_blob(repo: Path, revision: str, path: str) -> bytes:
    return git(repo, "show", f"{revision}:{path}")


def context_records() -> list[dict[str, Any]]:
    records = []
    for spec in CONTEXT_SPECS:
        record = {**spec, "official_repository": True}
        record["sha256"] = digest(record)
        records.append(record)
    return records


def extract_matrix_fragment(workflow: str) -> str:
    start_marker = "            let matrix = ["
    end_marker = "            console.log(`matrix:"
    start = workflow.find(start_marker)
    end = workflow.find(end_marker, start)
    if start < 0 or end < 0:
        raise ProfileError("cannot isolate pinned matrix-construction fragment")
    lines = workflow[start:end].splitlines()
    fragment_lines = []
    for line in lines:
        if line.startswith("            "):
            fragment_lines.append(line[12:])
        elif line.strip():
            raise ProfileError("matrix fragment indentation drift")
    fragment = "\n".join(fragment_lines).rstrip() + "\n"
    if "core.setOutput" in fragment or "uses:" in fragment or "run:" in fragment:
        raise ProfileError("isolated matrix fragment crossed a workflow-step boundary")
    return fragment


def evaluate_matrix(fragment: str, contexts: list[dict[str, Any]]) -> dict[str, list[dict[str, Any]]]:
    clean_contexts = [
        {key: value for key, value in context.items() if key != "sha256"}
        for context in contexts
    ]
    source = f"""
function derive(ctx) {{
  const level = ctx.level;
  const fast = ctx.fast;
  const lakeCi = ctx.lake_ci;
  const large = true;
  const isPr = ctx.is_pr;
  const isPushToMaster = ctx.is_push_to_master;
{fragment}
  return matrix;
}}
const contexts = {json.dumps(clean_contexts)};
const result = {{}};
for (const ctx of contexts) result[ctx.id] = derive(ctx);
process.stdout.write(JSON.stringify(result));
"""
    payload = run(["node", "-e", source]).stdout
    result = json.loads(payload)
    if set(result) != {context["id"] for context in contexts}:
        raise ProfileError("Node matrix result context set drift")
    return result


def parse_ctest_options(options: str) -> tuple[str | None, str | None, list[str]]:
    tokens = shlex.split(options)
    include: str | None = None
    exclude: str | None = None
    index = 0
    while index < len(tokens):
        token = tokens[index]
        if token not in {"-R", "--tests-regex", "-E", "--exclude-regex"}:
            raise ProfileError(f"unsupported CTest option {token!r}")
        if index + 1 >= len(tokens):
            raise ProfileError(f"missing regular expression after {token}")
        pattern = tokens[index + 1]
        if not PORTABLE_FILTER.fullmatch(pattern):
            raise ProfileError(f"unsupported CTest regular-expression syntax {pattern!r}")
        if token in {"-R", "--tests-regex"}:
            if include is not None:
                raise ProfileError("multiple include regexes are not supported by this schema")
            include = pattern
        else:
            if exclude is not None:
                raise ProfileError("multiple exclude regexes are not supported by this schema")
            exclude = pattern
        index += 2
    return include, exclude, tokens


def selection_set_id(profile: str, include: str | None, exclude: str | None) -> str:
    if include is None and exclude is None:
        return f"{profile}-all"
    identity = digest({"profile": profile, "include": include, "exclude": exclude})
    return f"{profile}-filtered-{identity[:12]}"


def selection_key(profile: str, options: str) -> tuple[str, str | None, str | None]:
    include, exclude, _ = parse_ctest_options(options)
    return profile, include, exclude


def registered_case_ids(u2: dict[str, Any], profile: str) -> list[str]:
    return [case["id"] for case in u2["cases"] if profile in case["profiles"]]


def make_selection_set(
    u2: dict[str, Any], profile: str, options: str
) -> dict[str, Any]:
    include, exclude, _ = parse_ctest_options(options)
    registered = registered_case_ids(u2, profile)
    include_re = re.compile(include) if include else None
    exclude_re = re.compile(exclude) if exclude else None
    selected = [
        case_id
        for case_id in registered
        if (include_re is None or include_re.search(case_id))
        and (exclude_re is None or not exclude_re.search(case_id))
    ]
    selected_set = set(selected)
    excluded = [case_id for case_id in registered if case_id not in selected_set]
    record: dict[str, Any] = {
        "id": selection_set_id(profile, include, exclude),
        "profile": profile,
        "include_regex": include,
        "exclude_regex": exclude,
        "registered_count": len(registered),
        "registered_ids_sha256": digest(registered),
        "selected_count": len(selected),
        "selected_ids_sha256": digest(selected),
        "selected_case_ids": selected,
        "excluded_count": len(excluded),
        "excluded_ids_sha256": digest(excluded),
        "excluded_case_ids": excluded,
    }
    record["sha256"] = digest(record)
    return record


def cell_digest(cell: dict[str, Any]) -> str:
    return digest({key: value for key, value in cell.items() if key != "sha256"})


def attempt_digest(attempt: dict[str, Any]) -> str:
    return digest({key: value for key, value in attempt.items() if key != "sha256"})


def selection_digest(selection: dict[str, Any]) -> str:
    return digest({key: value for key, value in selection.items() if key != "sha256"})


def make_cell(
    context: dict[str, Any], job_id: str, job_order: int, job: dict[str, Any], target_stage: str
) -> dict[str, Any]:
    enabled = bool(job.get("enabled", False))
    test = bool(job.get("test", False))
    if not enabled:
        state = "disabled"
    elif test:
        state = "ctest"
    else:
        state = "packaging-only"
    cross = bool(job.get("cross", False))
    cell: dict[str, Any] = {
        "id": f"{context['id']}--{job_id}",
        "context_id": context["id"],
        "job_id": job_id,
        "job_name": job["name"],
        "job_order": job_order,
        "enabled": enabled,
        "secondary": bool(job.get("secondary", False)),
        "test": test,
        "state": state,
        "runner": job["os"],
        "release": bool(job.get("release", False)),
        "shell": job.get("shell"),
        "preset": job.get("CMAKE_PRESET", "release"),
        "cmake_options": job.get("CMAKE_OPTIONS", ""),
        "ctest_options": job.get("CTEST_OPTIONS", ""),
        "selection_profile": "full-lake" if context["lake_ci"] else "default",
        "target_stage": target_stage,
        "check_rebootstrap": bool(job.get("check-rebootstrap", False)),
        "check_stage3": bool(job.get("check-stage3", False)),
        "test_bench": bool(job.get("test-bench", False)),
        "cross": cross,
        "post_test_binary_check": enabled and test and not cross,
    }
    parse_ctest_options(cell["ctest_options"])
    cell["sha256"] = cell_digest(cell)
    return cell


def attempt_command(
    *, preset: str, target_stage: str, options: str, junit: str | None
) -> list[str]:
    command = [
        "ctest",
        "--preset",
        preset,
        "--test-dir",
        f"build/{target_stage}",
        "-j$NPROC",
    ]
    if junit is not None:
        command.extend(["--output-junit", junit])
    command.extend(shlex.split(options))
    return command


def make_attempt(
    cell: dict[str, Any], phase: str, selection_id: str
) -> dict[str, Any]:
    if phase == "primary":
        target_stage = cell["target_stage"]
        options = cell["ctest_options"]
        junit = "test-results.xml"
    elif phase == "rebootstrap":
        target_stage = "stage1"
        options = ""
        junit = None
    else:
        raise ProfileError(f"unknown attempt phase {phase}")
    attempt: dict[str, Any] = {
        "id": f"{cell['id']}--{phase}",
        "cell_id": cell["id"],
        "phase": phase,
        "target_stage": target_stage,
        "preset": cell["preset"],
        "ctest_options": options,
        "selection_set_id": selection_id,
        "command": attempt_command(
            preset=cell["preset"],
            target_stage=target_stage,
            options=options,
            junit=junit,
        ),
        "junit_path": junit,
        "outcome": "not-run",
    }
    attempt["sha256"] = attempt_digest(attempt)
    return attempt


def capture(repo: Path) -> dict[str, Any]:
    repo = repo.resolve()
    head = git(repo, "rev-parse", "HEAD").decode("ascii").strip()
    if head != LEAN_COMMIT:
        raise ProfileError(f"expected Lean {LEAN_COMMIT}, got {head}")
    if git(repo, "status", "--porcelain", "--untracked-files=no").strip():
        raise ProfileError("pinned Lean checkout has tracked modifications")

    source_inputs = []
    source_bytes: dict[str, bytes] = {}
    for path, expected_sha in UPSTREAM_INPUTS:
        contents = git_blob(repo, head, path)
        observed_sha = sha256_bytes(contents)
        if observed_sha != expected_sha:
            raise ProfileError(f"pinned input digest drift at {path}")
        tree_row = git(repo, "ls-tree", "--full-tree", head, "--", path).decode().strip()
        metadata, observed_path = tree_row.split("\t", 1)
        mode, object_type, object_id = metadata.split()
        if object_type != "blob" or observed_path != path:
            raise ProfileError(f"bad Git tree identity for {path}")
        source_inputs.append(
            {
                "path": path,
                "mode": mode,
                "git_blob": object_id,
                "bytes": len(contents),
                "sha256": observed_sha,
            }
        )
        source_bytes[path] = contents

    observed_u2_sha = sha256_bytes(U2_MANIFEST.read_bytes())
    if observed_u2_sha != U2_MANIFEST_SHA256:
        raise ProfileError("TL0.6.1 authority digest drift")
    u2 = load_json(U2_MANIFEST)
    u2_checker = load_script(
        "lean_u2_authority_for_ci_profiles",
        ROOT / "scripts" / "gen-lean-u2-test-authority.py",
    )
    u2_failures = u2_checker.validate_manifest(u2)
    if u2_failures:
        raise ProfileError("invalid TL0.6.1 authority: " + "; ".join(u2_failures))

    stdlib_equal = (
        source_bytes["src/stdlib_flags.h"]
        == source_bytes["stage0/src/stdlib_flags.h"]
    )
    target_stage = "stage1" if stdlib_equal else "stage2"
    contexts = context_records()
    fragment = extract_matrix_fragment(
        source_bytes[".github/workflows/ci.yml"].decode("utf-8")
    )
    evaluated = evaluate_matrix(fragment, contexts)

    expected_names = [name for _, name in JOB_SPECS]
    jobs = [
        {"id": job_id, "name": name, "order": order}
        for order, (job_id, name) in enumerate(JOB_SPECS)
    ]
    cells = []
    context_by_id = {context["id"]: context for context in contexts}
    for context in contexts:
        context_jobs = evaluated[context["id"]]
        names = [job.get("name") for job in context_jobs]
        if names != expected_names:
            raise ProfileError(
                f"active matrix job names/order drift in {context['id']}: {names}"
            )
        if any(name in names for name in COMMENTED_JOB_NAMES):
            raise ProfileError("commented matrix job became active")
        for order, ((job_id, _), job) in enumerate(zip(JOB_SPECS, context_jobs)):
            cells.append(make_cell(context, job_id, order, job, target_stage))

    selection_keys: dict[tuple[str, str | None, str | None], dict[str, Any]] = {}
    for cell in cells:
        if cell["state"] != "ctest":
            continue
        primary_key = selection_key(cell["selection_profile"], cell["ctest_options"])
        selection_keys.setdefault(
            primary_key,
            make_selection_set(
                u2, cell["selection_profile"], cell["ctest_options"]
            ),
        )
        if cell["check_rebootstrap"]:
            rebootstrap_key = selection_key(cell["selection_profile"], "")
            selection_keys.setdefault(
                rebootstrap_key,
                make_selection_set(u2, cell["selection_profile"], ""),
            )
    selection_sets = sorted(selection_keys.values(), key=lambda item: item["id"])
    selection_id_by_key = {
        (item["profile"], item["include_regex"], item["exclude_regex"]): item["id"]
        for item in selection_sets
    }

    attempts = []
    for cell in cells:
        if cell["state"] != "ctest":
            continue
        primary_id = selection_id_by_key[
            selection_key(cell["selection_profile"], cell["ctest_options"])
        ]
        attempts.append(make_attempt(cell, "primary", primary_id))
        if cell["check_rebootstrap"]:
            rebootstrap_id = selection_id_by_key[
                selection_key(cell["selection_profile"], "")
            ]
            attempts.append(make_attempt(cell, "rebootstrap", rebootstrap_id))
    attempts.sort(key=lambda item: item["id"])

    cell_counts = Counter(cell["state"] for cell in cells)
    phase_counts = Counter(attempt["phase"] for attempt in attempts)
    return {
        "schema": SCHEMA,
        "as_of": "2026-07-22",
        "scope": "official-ci-profile-derivation-not-execution-or-parity",
        "target": {
            "repository": "https://github.com/leanprover/lean4.git",
            "official_repository": "leanprover/lean4",
            "version": "4.30.0",
            "tag": "v4.30.0",
            "commit": LEAN_COMMIT,
        },
        "source_inputs": source_inputs,
        "registration_authority": {
            "path": "docs/plan/lean-u2-test-authority-v1.json",
            "sha256": observed_u2_sha,
            "cases_sha256": u2["cases_sha256"],
            "default_registered": next(
                item["registered"]
                for item in u2["capture"]["profiles"]
                if item["id"] == "default"
            ),
            "full_lake_registered": next(
                item["registered"]
                for item in u2["capture"]["profiles"]
                if item["id"] == "full-lake"
            ),
        },
        "derivation": {
            "method": "isolated pinned JavaScript matrix evaluation plus exact CTest-name filtering",
            "matrix_fragment_sha256": sha256_bytes(fragment.encode("utf-8")),
            "official_repository_large": True,
            "stdlib_flags_equal": stdlib_equal,
            "target_stage": target_stage,
            "contexts": len(contexts),
            "active_job_literals": len(jobs),
            "candidate_cells": len(cells),
            "cell_state_counts": dict(sorted(cell_counts.items())),
            "ctest_attempts": len(attempts),
            "attempt_phase_counts": dict(sorted(phase_counts.items())),
            "selection_sets": len(selection_sets),
            "outcomes_observed": 0,
        },
        "contexts_sha256": digest(contexts),
        "contexts": contexts,
        "jobs": jobs,
        "cells_sha256": digest(cells),
        "cells": cells,
        "selection_sets_sha256": digest(selection_sets),
        "selection_sets": selection_sets,
        "attempts_sha256": digest(attempts),
        "attempts": attempts,
        "outcomes": {
            "official_executed_attempts": 0,
            "official_completed_cases": 0,
            "axeyum_executed_attempts": 0,
            "paired_registered": 0,
            "state": "not-run",
        },
        "residual": [
            "Retain official executable, configuration, environment, resource, attempt, completion, JUnit, log, and artifact identities for every declared execution profile.",
            "Classify and implement the native Axeyum surface required by every selected case.",
            "Execute matched native cases and register terminal paired cells only from completed both-system evidence.",
        ],
    }


def normalize_options(selection: dict[str, Any]) -> str:
    tokens = []
    if selection["include_regex"] is not None:
        tokens.extend(["-R", shlex.quote(selection["include_regex"])])
    if selection["exclude_regex"] is not None:
        tokens.extend(["-E", shlex.quote(selection["exclude_regex"])])
    return " ".join(tokens)


def expected_contexts() -> list[dict[str, Any]]:
    return context_records()


def validate_selection_set(
    selection: dict[str, Any], u2: dict[str, Any], failures: list[str]
) -> None:
    selection_id = str(selection.get("id", "<unknown>"))
    if set(selection) != SELECTION_FIELDS:
        failures.append(f"{selection_id}: selection fields must be exact")
        return
    profile = selection["profile"]
    if profile not in {"default", "full-lake"}:
        failures.append(f"{selection_id}: invalid registration profile")
        return
    try:
        expected = make_selection_set(u2, profile, normalize_options(selection))
    except ProfileError as error:
        failures.append(f"{selection_id}: {error}")
        return
    if selection != expected:
        failures.append(f"{selection_id}: exact selection membership or identity drift")


def validate_manifest(data: dict[str, Any]) -> list[str]:
    failures: list[str] = []
    if data.get("schema") != SCHEMA:
        failures.append(f"schema must be {SCHEMA}")
    if data.get("as_of") != "2026-07-22":
        failures.append("as_of must remain 2026-07-22")
    if data.get("scope") != "official-ci-profile-derivation-not-execution-or-parity":
        failures.append("scope must remain derivation-only and non-terminal")
    if data.get("target") != {
        "repository": "https://github.com/leanprover/lean4.git",
        "official_repository": "leanprover/lean4",
        "version": "4.30.0",
        "tag": "v4.30.0",
        "commit": LEAN_COMMIT,
    }:
        failures.append("target must match the exact official Lean v4.30.0 pin")

    inputs = data.get("source_inputs")
    if not isinstance(inputs, list):
        failures.append("source_inputs must be a list")
        inputs = []
    observed_input_pairs = [
        (item.get("path"), item.get("sha256"))
        for item in inputs
        if isinstance(item, dict)
    ]
    if observed_input_pairs != list(UPSTREAM_INPUTS):
        failures.append("source input paths/digests/order drift")
    for index, item in enumerate(inputs):
        if not isinstance(item, dict) or set(item) != {
            "path",
            "mode",
            "git_blob",
            "bytes",
            "sha256",
        }:
            failures.append(f"source_inputs[{index}]: malformed Git identity")
            continue
        if item["mode"] not in {"100644", "100755"}:
            failures.append(f"source_inputs[{index}]: unsupported mode")
        if not isinstance(item["git_blob"], str) or len(item["git_blob"]) != 40:
            failures.append(f"source_inputs[{index}]: bad Git blob identity")
        if not isinstance(item["bytes"], int) or item["bytes"] < 0:
            failures.append(f"source_inputs[{index}]: bad byte count")

    observed_u2_sha = sha256_bytes(U2_MANIFEST.read_bytes())
    u2 = load_json(U2_MANIFEST)
    registration = data.get("registration_authority")
    expected_registration = {
        "path": "docs/plan/lean-u2-test-authority-v1.json",
        "sha256": observed_u2_sha,
        "cases_sha256": u2["cases_sha256"],
        "default_registered": 3678,
        "full_lake_registered": 3723,
    }
    if observed_u2_sha != U2_MANIFEST_SHA256:
        failures.append("committed TL0.6.1 authority drifted from preregistration")
    if registration != expected_registration:
        failures.append("registration authority identity/count drift")

    contexts = data.get("contexts")
    if contexts != expected_contexts():
        failures.append("context closure, order, fields, or digest drift")
        contexts = contexts if isinstance(contexts, list) else []
    if data.get("contexts_sha256") != digest(contexts):
        failures.append("contexts_sha256 disagrees with contexts")
    context_by_id = {
        context["id"]: context
        for context in contexts
        if isinstance(context, dict) and isinstance(context.get("id"), str)
    }

    expected_jobs = [
        {"id": job_id, "name": name, "order": order}
        for order, (job_id, name) in enumerate(JOB_SPECS)
    ]
    jobs = data.get("jobs")
    if jobs != expected_jobs:
        failures.append("active matrix job literals/order drift")
        jobs = jobs if isinstance(jobs, list) else []
    if any(job.get("name") in COMMENTED_JOB_NAMES for job in jobs if isinstance(job, dict)):
        failures.append("commented matrix job cannot be active")
    job_by_id = {
        job["id"]: job
        for job in jobs
        if isinstance(job, dict) and isinstance(job.get("id"), str)
    }

    cells = data.get("cells")
    if not isinstance(cells, list):
        failures.append("cells must be a list")
        cells = []
    expected_cell_ids = [
        f"{context['id']}--{job['id']}"
        for context in expected_contexts()
        for job in expected_jobs
    ]
    cell_ids = [cell.get("id") for cell in cells if isinstance(cell, dict)]
    if cell_ids != expected_cell_ids:
        failures.append("candidate cell closure/order must be 17 contexts x 9 jobs")
    cell_by_id = {}
    for cell in cells:
        if not isinstance(cell, dict):
            failures.append("every cell must be an object")
            continue
        cell_id = str(cell.get("id", "<unknown>"))
        if set(cell) != CELL_FIELDS:
            failures.append(f"{cell_id}: cell fields must be exact")
            continue
        context = context_by_id.get(cell["context_id"])
        job = job_by_id.get(cell["job_id"])
        if context is None or job is None:
            failures.append(f"{cell_id}: unknown context or job")
        else:
            if cell_id != f"{context['id']}--{job['id']}":
                failures.append(f"{cell_id}: context/job id mismatch")
            if cell["job_name"] != job["name"] or cell["job_order"] != job["order"]:
                failures.append(f"{cell_id}: job name/order drift")
            expected_profile = "full-lake" if context["lake_ci"] else "default"
            if cell["selection_profile"] != expected_profile:
                failures.append(f"{cell_id}: registration profile/context mismatch")
        expected_state = (
            "disabled"
            if not cell["enabled"]
            else "ctest"
            if cell["test"]
            else "packaging-only"
        )
        if cell["state"] != expected_state:
            failures.append(f"{cell_id}: cell state disagrees with enabled/test")
        if cell["target_stage"] != "stage1":
            failures.append(f"{cell_id}: target stage must follow equal bootstrap flags")
        if cell["post_test_binary_check"] != (
            cell["enabled"] and cell["test"] and not cell["cross"]
        ):
            failures.append(f"{cell_id}: post-test binary-check predicate drift")
        try:
            parse_ctest_options(cell["ctest_options"])
        except ProfileError as error:
            failures.append(f"{cell_id}: {error}")
        if cell["sha256"] != cell_digest(cell):
            failures.append(f"{cell_id}: cell digest drift")
        cell_by_id[cell_id] = cell
    if data.get("cells_sha256") != digest(cells):
        failures.append("cells_sha256 disagrees with cells")

    selections = data.get("selection_sets")
    if not isinstance(selections, list):
        failures.append("selection_sets must be a list")
        selections = []
    selection_ids = [
        selection.get("id") for selection in selections if isinstance(selection, dict)
    ]
    if selection_ids != sorted(selection_ids) or len(selection_ids) != len(set(selection_ids)):
        failures.append("selection set ids must be unique and sorted")
    for selection in selections:
        if not isinstance(selection, dict):
            failures.append("every selection set must be an object")
            continue
        validate_selection_set(selection, u2, failures)
    if data.get("selection_sets_sha256") != digest(selections):
        failures.append("selection_sets_sha256 disagrees with selection_sets")
    selection_by_id = {
        selection["id"]: selection
        for selection in selections
        if isinstance(selection, dict) and isinstance(selection.get("id"), str)
    }

    attempts = data.get("attempts")
    if not isinstance(attempts, list):
        failures.append("attempts must be a list")
        attempts = []
    attempt_ids = [attempt.get("id") for attempt in attempts if isinstance(attempt, dict)]
    if attempt_ids != sorted(attempt_ids) or len(attempt_ids) != len(set(attempt_ids)):
        failures.append("attempt ids must be unique and sorted")
    attempts_by_cell: dict[str, list[dict[str, Any]]] = {}
    for attempt in attempts:
        if not isinstance(attempt, dict):
            failures.append("every attempt must be an object")
            continue
        attempt_id = str(attempt.get("id", "<unknown>"))
        if set(attempt) != ATTEMPT_FIELDS:
            failures.append(f"{attempt_id}: attempt fields must be exact")
            continue
        cell = cell_by_id.get(attempt["cell_id"])
        if cell is None:
            failures.append(f"{attempt_id}: unknown cell")
            continue
        attempts_by_cell.setdefault(cell["id"], []).append(attempt)
        phase = attempt["phase"]
        if phase == "primary":
            expected_options = cell["ctest_options"]
            expected_stage = cell["target_stage"]
            expected_junit = "test-results.xml"
        elif phase == "rebootstrap":
            expected_options = ""
            expected_stage = "stage1"
            expected_junit = None
            if not cell["check_rebootstrap"]:
                failures.append(f"{attempt_id}: unregistered rebootstrap attempt")
        else:
            failures.append(f"{attempt_id}: invalid phase")
            continue
        expected_attempt_id = f"{cell['id']}--{phase}"
        if attempt_id != expected_attempt_id:
            failures.append(f"{attempt_id}: attempt id/cell/phase mismatch")
        if cell["state"] != "ctest":
            failures.append(f"{attempt_id}: disabled/packaging cell cannot own attempt")
        if (
            attempt["ctest_options"] != expected_options
            or attempt["target_stage"] != expected_stage
            or attempt["preset"] != cell["preset"]
            or attempt["junit_path"] != expected_junit
        ):
            failures.append(f"{attempt_id}: command configuration drift")
        selection = selection_by_id.get(attempt["selection_set_id"])
        if selection is None:
            failures.append(f"{attempt_id}: unknown selection set")
        else:
            try:
                include, exclude, _ = parse_ctest_options(expected_options)
            except ProfileError as error:
                failures.append(f"{attempt_id}: {error}")
            else:
                expected_selection_id = selection_set_id(
                    cell["selection_profile"], include, exclude
                )
                if attempt["selection_set_id"] != expected_selection_id:
                    failures.append(f"{attempt_id}: attempt/selection mismatch")
        expected_command = attempt_command(
            preset=cell["preset"],
            target_stage=expected_stage,
            options=expected_options,
            junit=expected_junit,
        )
        if attempt["command"] != expected_command:
            failures.append(f"{attempt_id}: normalized command drift")
        if attempt["outcome"] != "not-run":
            failures.append(f"{attempt_id}: profile derivation cannot claim outcome")
        if attempt["sha256"] != attempt_digest(attempt):
            failures.append(f"{attempt_id}: attempt digest drift")
    for cell_id, cell in cell_by_id.items():
        phases = sorted(attempt["phase"] for attempt in attempts_by_cell.get(cell_id, []))
        expected_phases = []
        if cell["state"] == "ctest":
            expected_phases.append("primary")
            if cell["check_rebootstrap"]:
                expected_phases.append("rebootstrap")
        if phases != sorted(expected_phases):
            failures.append(f"{cell_id}: attempt phase closure drift")
    if data.get("attempts_sha256") != digest(attempts):
        failures.append("attempts_sha256 disagrees with attempts")

    referenced_selections = sorted(
        {attempt["selection_set_id"] for attempt in attempts if isinstance(attempt, dict)}
    )
    if referenced_selections != sorted(selection_by_id):
        failures.append("selection sets must be exactly those referenced by attempts")

    derivation = data.get("derivation")
    if not isinstance(derivation, dict):
        failures.append("derivation must be an object")
    else:
        state_counts = Counter(cell.get("state") for cell in cells if isinstance(cell, dict))
        phase_counts = Counter(
            attempt.get("phase") for attempt in attempts if isinstance(attempt, dict)
        )
        expected_dynamic = {
            "contexts": len(contexts),
            "active_job_literals": len(jobs),
            "candidate_cells": len(cells),
            "cell_state_counts": dict(sorted(state_counts.items())),
            "ctest_attempts": len(attempts),
            "attempt_phase_counts": dict(sorted(phase_counts.items())),
            "selection_sets": len(selections),
            "outcomes_observed": 0,
        }
        for field, expected in expected_dynamic.items():
            if derivation.get(field) != expected:
                failures.append(f"derivation {field} aggregate drift")
        if (
            derivation.get("method")
            != "isolated pinned JavaScript matrix evaluation plus exact CTest-name filtering"
            or derivation.get("official_repository_large") is not True
            or derivation.get("stdlib_flags_equal") is not True
            or derivation.get("target_stage") != "stage1"
            or not is_sha256(derivation.get("matrix_fragment_sha256"))
        ):
            failures.append("derivation method/bootstrap identity drift")

    if data.get("outcomes") != {
        "official_executed_attempts": 0,
        "official_completed_cases": 0,
        "axeyum_executed_attempts": 0,
        "paired_registered": 0,
        "state": "not-run",
    }:
        failures.append("profile derivation cannot claim execution or parity outcomes")
    residual = data.get("residual")
    if not isinstance(residual, list) or len(residual) != 3 or not all(residual):
        failures.append("TL0.6.3/TL0.6.4/TL0.6.5 residual must remain explicit")
    return failures


def ctest_selected_ids(selection: dict[str, Any]) -> list[str]:
    with tempfile.TemporaryDirectory(prefix="axeyum-u2-ctest-filter-") as raw_temp:
        temp = Path(raw_temp)
        lines = []
        for case_id in selection["selected_case_ids"] + selection["excluded_case_ids"]:
            escaped = case_id.replace("\\", "\\\\").replace('"', '\\"')
            lines.append(f'add_test("{escaped}" "/usr/bin/true")')
        (temp / "CTestTestfile.cmake").write_text("\n".join(lines) + "\n", encoding="utf-8")
        command = ["ctest", "--test-dir", str(temp), "--show-only=json-v1"]
        if selection["include_regex"] is not None:
            command.extend(["-R", selection["include_regex"]])
        if selection["exclude_regex"] is not None:
            command.extend(["-E", selection["exclude_regex"]])
        payload = json.loads(run(command).stdout)
        return [test["name"] for test in payload["tests"]]


def verify_ctest_filters(data: dict[str, Any]) -> list[str]:
    failures = []
    for selection in data["selection_sets"]:
        observed = ctest_selected_ids(selection)
        if observed != selection["selected_case_ids"]:
            failures.append(
                f"{selection['id']}: CTest and manifest selection membership/order differ"
            )
    return failures


def summarize(data: dict[str, Any]) -> dict[str, Any]:
    cells = data["cells"]
    attempts = data["attempts"]
    cell_by_id = {cell["id"]: cell for cell in cells}
    selection_by_id = {item["id"]: item for item in data["selection_sets"]}
    context_rows = []
    for context in data["contexts"]:
        context_cells = [cell for cell in cells if cell["context_id"] == context["id"]]
        context_attempts = [
            attempt
            for attempt in attempts
            if cell_by_id[attempt["cell_id"]]["context_id"] == context["id"]
        ]
        context_rows.append(
            {
                "id": context["id"],
                "event": context["event"],
                "level": context["level"],
                "lake_ci": context["lake_ci"],
                "fast": context["fast"],
                "enabled_jobs": sum(cell["enabled"] for cell in context_cells),
                "primary_jobs": sum(
                    cell["enabled"] and not cell["secondary"] for cell in context_cells
                ),
                "secondary_jobs": sum(
                    cell["enabled"] and cell["secondary"] for cell in context_cells
                ),
                "packaging_only_jobs": sum(
                    cell["state"] == "packaging-only" for cell in context_cells
                ),
                "ctest_attempts": len(context_attempts),
                "selected_case_occurrences": sum(
                    selection_by_id[attempt["selection_set_id"]]["selected_count"]
                    for attempt in context_attempts
                ),
                "selection_set_ids": sorted(
                    {attempt["selection_set_id"] for attempt in context_attempts}
                ),
            }
        )
    source_sha = sha256_bytes(MANIFEST.read_bytes())
    return {
        "schema": "axeyum-lean-u2-official-ci-profiles-report-v1",
        "generated_from": "docs/plan/lean-u2-official-ci-profiles-v1.json",
        "generated_from_sha256": source_sha,
        "target": data["target"],
        "scope": data["scope"],
        "derivation": data["derivation"],
        "contexts": context_rows,
        "jobs": data["jobs"],
        "selection_sets": [
            {
                key: selection[key]
                for key in (
                    "id",
                    "profile",
                    "include_regex",
                    "exclude_regex",
                    "registered_count",
                    "selected_count",
                    "excluded_count",
                    "selected_ids_sha256",
                )
            }
            for selection in data["selection_sets"]
        ],
        "outcomes": data["outcomes"],
        "residual": data["residual"],
        "verdict": "official CI profiles derived; no execution or parity outcome established",
    }


def render_markdown(report: dict[str, Any]) -> str:
    derivation = report["derivation"]
    lines = [
        "# Lean U2 official CI execution profiles",
        "",
        "> **Generated; do not edit by hand.** Regenerate with `python3 "
        "scripts/gen-lean-u2-official-ci-profiles.py`; validate with `--check`.",
        "",
        "> **Verdict: official CI profiles derived; no execution or parity outcome "
        "established.** Every attempt below remains `not-run`.",
        "",
        f"Pinned Lean `v4.30.0` at `{report['target']['commit']}`. The authority "
        "evaluates only the isolated matrix-construction fragment and maps its "
        "CTest options onto the TL0.6.1 registered names.",
        "",
        "## Derivation closure",
        "",
        f"- {derivation['contexts']} official-repository event contexts.",
        f"- {derivation['active_job_literals']} active matrix job literals and "
        f"{derivation['candidate_cells']} candidate context/job cells.",
        "- Cell states: "
        + ", ".join(
            f"`{key}`={value}"
            for key, value in derivation["cell_state_counts"].items()
        )
        + ".",
        f"- {derivation['ctest_attempts']} CTest attempts: "
        + ", ".join(
            f"`{key}`={value}"
            for key, value in derivation["attempt_phase_counts"].items()
        )
        + ".",
        f"- {derivation['selection_sets']} unique factored case-selection sets.",
        f"- Equal bootstrap flag inputs select `{derivation['target_stage']}`.",
        "- Commented Linux LLVM, Linux 32-bit, and WebAssembly jobs receive no "
        "active-cell or attempt credit.",
        "",
        "## Context matrix",
        "",
        "`Selected occurrences` intentionally counts repeated attempts; it is not a "
        "unique-case denominator or pass count.",
        "",
        "| Context | Event | Level | Lake | Fast | Enabled jobs | Primary | "
        "Secondary | Packaging only | CTest attempts | Selected occurrences |",
        "|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for row in report["contexts"]:
        lines.append(
            f"| `{row['id']}` | `{row['event']}` | {row['level']} | "
            f"{'yes' if row['lake_ci'] else 'no'} | "
            f"{'yes' if row['fast'] else 'no'} | {row['enabled_jobs']} | "
            f"{row['primary_jobs']} | {row['secondary_jobs']} | "
            f"{row['packaging_only_jobs']} | {row['ctest_attempts']} | "
            f"{row['selected_case_occurrences']:,} |"
        )
    lines.extend(
        [
            "",
            "## Exact selection sets",
            "",
            "| Selection | Registration | Include | Exclude | Registered | Selected | Excluded | Selected digest |",
            "|---|---|---|---|---:|---:|---:|---|",
        ]
    )
    for selection in report["selection_sets"]:
        include = selection["include_regex"] or "-"
        exclude = selection["exclude_regex"] or "-"
        lines.append(
            f"| `{selection['id']}` | `{selection['profile']}` | `{include}` | "
            f"`{exclude}` | {selection['registered_count']:,} | "
            f"{selection['selected_count']:,} | {selection['excluded_count']:,} | "
            f"`{selection['selected_ids_sha256']}` |"
        )
    lines.extend(
        [
            "",
            "## Assurance boundary",
            "",
            "- The machine-readable authority retains every resolved cell, normalized "
            "command, selection-set membership, stage, preset, primary/secondary "
            "classification, and non-CTest action flag.",
            "- Primary attempts retain matrix filters and JUnit shape. Rebootstrap "
            "attempts are separate, fixed to stage 1, and deliberately unfiltered.",
            "- Disabled and packaging-only cells own no CTest attempt.",
            "- Stage-3 and benchmark actions remain flags, not invented CTest cases.",
            "- Official executions, completed cases, Axeyum executions, and paired "
            "cells all remain zero.",
            "",
            "## Remaining work",
            "",
        ]
    )
    lines.extend(f"- {item}" for item in report["residual"])
    lines.append("")
    return "\n".join(lines)


def write_outputs(data: dict[str, Any]) -> None:
    report = summarize(data)
    OUT_JSON.write_text(json_text(report), encoding="utf-8")
    OUT_MD.write_text(render_markdown(report), encoding="utf-8")


def check_outputs(data: dict[str, Any]) -> list[str]:
    report = summarize(data)
    expected = {
        OUT_JSON: json_text(report),
        OUT_MD: render_markdown(report),
    }
    failures = []
    for path, text in expected.items():
        if not path.is_file():
            failures.append(f"missing generated output {path.relative_to(ROOT)}")
        elif path.read_text(encoding="utf-8") != text:
            failures.append(f"stale generated output {path.relative_to(ROOT)}")
    return failures


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--capture-upstream", type=Path, metavar="LEAN_REPO")
    parser.add_argument("--verify-upstream", type=Path, metavar="LEAN_REPO")
    parser.add_argument("--verify-ctest", action="store_true")
    args = parser.parse_args()
    if args.capture_upstream and args.verify_upstream:
        parser.error("choose at most one upstream mode")

    if args.capture_upstream:
        data = capture(args.capture_upstream)
        MANIFEST.write_text(json_text(data), encoding="utf-8")
    else:
        data = load_json(MANIFEST)

    failures = validate_manifest(data)
    if args.verify_upstream:
        observed = capture(args.verify_upstream)
        if observed != data:
            failures.append("fresh pinned-upstream profile capture differs from authority")
    if args.verify_ctest or args.verify_upstream:
        failures.extend(verify_ctest_filters(data))
    if args.check:
        failures.extend(check_outputs(data))
    if failures:
        for failure in failures:
            print(f"lean-u2-official-ci-profiles: {failure}", file=sys.stderr)
        return 1
    if not args.check and not args.verify_upstream and not args.verify_ctest:
        write_outputs(data)
    derivation = data["derivation"]
    print(
        "lean-u2-official-ci-profiles: ok "
        f"({derivation['contexts']} contexts; "
        f"{derivation['candidate_cells']} cells; "
        f"{derivation['ctest_attempts']} not-run attempts; "
        f"{derivation['selection_sets']} exact selection sets)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
