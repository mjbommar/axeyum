#!/usr/bin/env python3
"""Capture, validate, and render the pinned Lean U2 test registration authority.

This is deliberately a *registration* authority, not a parity result.  Capture
executes pinned Lean's own CMake registration twice (the default selection and
``LAKE_CI=ON``), normalizes host paths, and binds every selected primary file,
sidecar, command, property, and over-approximating support subtree.  Normal CI
validates the committed capture without cloning Lean; ``--verify-upstream`` is
the slower source-to-capture reproduction gate.
"""

from __future__ import annotations

import argparse
import fnmatch
import hashlib
import json
import os
import subprocess
import sys
import tarfile
import tempfile
from collections import Counter
from pathlib import Path
from typing import Any, Iterable


ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "docs" / "plan" / "lean-u2-test-authority-v1.json"
OUT_JSON = ROOT / "docs" / "plan" / "generated" / "lean-u2-test-authority.json"
OUT_MD = ROOT / "docs" / "plan" / "generated" / "lean-u2-test-authority.md"

LEAN_VERSION = "4.30.0"
LEAN_TAG = "v4.30.0"
LEAN_COMMIT = "d024af099ca4bf2c86f649261ebf59565dc8c622"
SCHEMA = "axeyum-lean-u2-test-authority-v1"
PROFILE_IDS = ("default", "full-lake")
OUTPUT_POLICIES = ("empty", "exact", "ignored", "script-defined")
KINDS = ("pile", "directory", "lake-directory", "lint")
HEX40 = set("0123456789abcdef")
CASE_FIELDS = {
    "id",
    "profiles",
    "kind",
    "family",
    "source_path",
    "source_sha256",
    "sidecars",
    "support_scope",
    "output_policy",
    "expected_path",
    "ctest_success",
    "registration",
    "sha256",
}

REGISTRATION_INPUTS = (
    ".github/workflows/build-template.yml",
    ".github/workflows/ci.yml",
    "CMakePresets.json",
    "tests/CMakeLists.txt",
    "tests/README.md",
    "tests/with_env.sh.in",
)
CONTENT_ROOTS = ("doc/examples", "tests")
PILE_SPECS = (
    ("doc/examples", "*.lean"),
    ("tests/compile", "*.lean"),
    ("tests/compile_bench", "*.lean"),
    ("tests/docparse", "*.txt"),
    ("tests/elab", "*.lean"),
    ("tests/elab_bench", "*.lean"),
    ("tests/elab_fail", "*.lean"),
    ("tests/misc", "*.sh"),
    ("tests/misc_bench", "*.sh"),
    ("tests/server", "*.lean"),
    ("tests/server_interactive", "*.lean"),
)


class AuthorityError(RuntimeError):
    """A fail-closed authority capture or validation failure."""


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(
        value, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def run(
    argv: list[str],
    *,
    cwd: Path | None = None,
    stdout: Any = subprocess.PIPE,
) -> subprocess.CompletedProcess[bytes]:
    try:
        return subprocess.run(
            argv,
            cwd=cwd,
            check=True,
            stdout=stdout,
            stderr=subprocess.PIPE,
        )
    except (OSError, subprocess.CalledProcessError) as error:
        stderr = getattr(error, "stderr", b"") or b""
        detail = stderr.decode("utf-8", errors="replace").strip()
        raise AuthorityError(f"command failed: {' '.join(argv)}\n{detail}") from error


def git(repo: Path, *args: str) -> bytes:
    return run(["git", "-C", str(repo), *args]).stdout


def git_blob(repo: Path, revision: str, path: str) -> bytes:
    return git(repo, "show", f"{revision}:{path}")


def read_manifest() -> dict[str, Any]:
    with MANIFEST.open(encoding="utf-8") as handle:
        return json.load(handle)


def json_text(value: Any) -> str:
    return json.dumps(value, indent=2, ensure_ascii=False) + "\n"


def file_identity(path: str, mode: str, git_blob_id: str, contents: bytes) -> dict[str, Any]:
    return {
        "path": path,
        "mode": mode,
        "git_blob": git_blob_id,
        "bytes": len(contents),
        "sha256": sha256_bytes(contents),
    }


def parse_tree(repo: Path, revision: str) -> list[tuple[str, str, str]]:
    raw = git(
        repo,
        "ls-tree",
        "-r",
        "-z",
        "--full-tree",
        revision,
        "--",
        *CONTENT_ROOTS,
    )
    rows: list[tuple[str, str, str]] = []
    for record in raw.split(b"\0"):
        if not record:
            continue
        metadata, raw_path = record.split(b"\t", 1)
        mode, object_type, object_id = metadata.decode("ascii").split()
        if object_type != "blob":
            raise AuthorityError(f"non-blob content entry: {raw_path!r}")
        rows.append((raw_path.decode("utf-8"), mode, object_id))
    rows.sort()
    return rows


def extract_content(repo: Path, revision: str, destination: Path) -> None:
    archive = destination.parent / "lean-u2-content.tar"
    with archive.open("wb") as output:
        run(
            [
                "git",
                "-C",
                str(repo),
                "archive",
                "--format=tar",
                revision,
                *CONTENT_ROOTS,
            ],
            stdout=output,
        )
    destination.mkdir(parents=True, exist_ok=True)
    with tarfile.open(archive) as bundle:
        for member in bundle.getmembers():
            member_path = Path(member.name)
            if member_path.is_absolute() or ".." in member_path.parts:
                raise AuthorityError(f"unsafe archive member {member.name!r}")
        bundle.extractall(destination, filter="data")


def content_bytes(root: Path, path: str, mode: str) -> bytes:
    item = root / path
    if mode == "120000":
        if not item.is_symlink():
            raise AuthorityError(f"expected symlink at {path}")
        return os.readlink(item).encode("utf-8")
    if not item.is_file():
        raise AuthorityError(f"expected file at {path}")
    return item.read_bytes()


def normalize_text(
    text: str, *, lean_root: Path, harness_root: Path, build_root: Path
) -> str:
    replacements = (
        (str(build_root), "$BUILD_ROOT"),
        (str(lean_root), "$LEAN_ROOT"),
        (str(harness_root), "$HARNESS_ROOT"),
    )
    result = text
    for old, new in replacements:
        result = result.replace(old, new)
    return result


def normalize_command(
    command: list[str], *, lean_root: Path, harness_root: Path, build_root: Path
) -> list[str]:
    normalized = [
        normalize_text(
            item, lean_root=lean_root, harness_root=harness_root, build_root=build_root
        )
        for item in command
    ]
    if normalized and Path(normalized[0]).name == "bash":
        normalized[0] = "$BASH"
    if normalized and Path(normalized[0]).name.startswith("python3"):
        normalized[0] = "$PYTHON3"
    return normalized


def configure_profile(
    harness_root: Path, lean_root: Path, profile_id: str
) -> tuple[list[dict[str, Any]], str]:
    build_root = harness_root / f"build-{profile_id}"
    lake_ci = "ON" if profile_id == "full-lake" else "OFF"
    run(
        [
            "cmake",
            "-S",
            str(harness_root),
            "-B",
            str(build_root),
            f"-DLAKE_CI={lake_ci}",
        ]
    )
    raw = run(
        ["ctest", "--test-dir", str(build_root), "--show-only=json-v1"]
    ).stdout
    payload = json.loads(raw)
    normalized: list[dict[str, Any]] = []
    for test in payload["tests"]:
        properties = []
        for prop in test.get("properties", []):
            value = prop["value"]
            if isinstance(value, str):
                value = normalize_text(
                    value,
                    lean_root=lean_root,
                    harness_root=harness_root,
                    build_root=build_root,
                )
            properties.append({"name": prop["name"], "value": value})
        properties.sort(key=lambda item: item["name"])
        normalized.append(
            {
                "id": test["name"],
                "command": normalize_command(
                    test["command"],
                    lean_root=lean_root,
                    harness_root=harness_root,
                    build_root=build_root,
                ),
                "properties": properties,
            }
        )
    normalized.sort(key=lambda item: item["id"])
    wrapper = lean_root / "tests" / "with_stage1_test_env.sh"
    wrapper_text = normalize_text(
        wrapper.read_text(encoding="utf-8"),
        lean_root=lean_root,
        harness_root=harness_root,
        build_root=build_root,
    )
    return normalized, sha256_bytes(wrapper_text.encode("utf-8"))


def relative_source_path(case_id: str, kind: str) -> str:
    if kind == "lint":
        return "tests/lint.py"
    if kind == "lake-directory":
        return case_id
    if kind == "pile":
        if case_id.startswith("../"):
            return case_id[3:]
        return f"tests/{case_id}"
    if case_id.startswith("../"):
        return f"{case_id[3:]}/run_test.sh"
    return f"tests/{case_id}/run_test.sh"


def case_kind(case_id: str) -> str:
    if case_id == "lint.py":
        return "lint"
    if case_id.startswith("tests/lake/") and case_id.endswith("/test.sh"):
        return "lake-directory"
    for scope, pattern in PILE_SPECS:
        prefix = "../doc/examples/" if scope == "doc/examples" else scope[6:] + "/"
        if case_id.startswith(prefix) and fnmatch.fnmatch(case_id[len(prefix) :], pattern):
            return "pile"
    return "directory"


def case_family(case_id: str) -> str:
    if case_id.startswith("../doc/examples/"):
        return "doc-examples"
    if case_id.startswith("tests/lake/"):
        return "lake"
    if case_id == "lint.py":
        return "lint"
    return case_id.split("/", 1)[0]


def scope_digest(entries: Iterable[dict[str, Any]]) -> str:
    return digest(
        [
            {
                "path": item["path"],
                "mode": item["mode"],
                "bytes": item["bytes"],
                "sha256": item["sha256"],
            }
            for item in entries
        ]
    )


def build_support_scopes(
    source_paths: Iterable[str], files: list[dict[str, Any]]
) -> tuple[list[dict[str, Any]], dict[str, dict[str, Any]]]:
    prefixes = sorted({Path(path).parent.as_posix() for path in source_paths})
    scopes: list[dict[str, Any]] = []
    by_prefix: dict[str, dict[str, Any]] = {}
    for prefix in prefixes:
        prefix_with_slash = prefix + "/"
        members = [item for item in files if item["path"].startswith(prefix_with_slash)]
        if not members:
            raise AuthorityError(f"empty support scope {prefix}")
        scope = {
            "path": prefix,
            "files": len(members),
            "bytes": sum(item["bytes"] for item in members),
            "sha256": scope_digest(members),
        }
        scopes.append(scope)
        by_prefix[prefix] = scope
    return scopes, by_prefix


def selection_accounting(
    file_rows: list[dict[str, Any]], registered_pile_ids: set[str]
) -> dict[str, Any]:
    paths = {item["path"] for item in file_rows}
    candidates: list[dict[str, str]] = []
    selected: list[str] = []
    for scope, pattern in PILE_SPECS:
        prefix = scope + "/"
        scope_candidates = sorted(
            path
            for path in paths
            if path.startswith(prefix)
            and "/" not in path[len(prefix) :]
            and fnmatch.fnmatch(path[len(prefix) :], pattern)
        )
        has_runner = f"{scope}/run_test.sh" in paths
        for path in scope_candidates:
            basename = path[len(prefix) :]
            if basename.startswith("run_test") or basename.startswith("run_bench"):
                candidates.append({"path": path, "reason": "runner-name"})
            elif f"{path}.no_test" in paths:
                candidates.append({"path": path, "reason": "no-test-sidecar"})
            elif not has_runner:
                candidates.append({"path": path, "reason": "no-test-runner"})
            else:
                selected.append(path)
    selected_ids = {
        "../" + path if path.startswith("doc/examples/") else path[6:]
        for path in selected
    }
    if selected_ids != registered_pile_ids:
        missing = sorted(selected_ids - registered_pile_ids)[:5]
        extra = sorted(registered_pile_ids - selected_ids)[:5]
        raise AuthorityError(
            f"pile accounting disagrees with CTest; missing={missing}, extra={extra}"
        )
    reasons = Counter(item["reason"] for item in candidates)
    return {
        "declared_piles": len(PILE_SPECS),
        "glob_candidates": len(selected) + len(candidates),
        "registered": len(selected),
        "excluded": len(candidates),
        "excluded_by_reason": dict(sorted(reasons.items())),
        "excluded_cases": candidates,
    }


def case_digest(case: dict[str, Any]) -> str:
    return digest({key: value for key, value in case.items() if key != "sha256"})


def capture(repo: Path) -> dict[str, Any]:
    repo = repo.resolve()
    head = git(repo, "rev-parse", "HEAD").decode("ascii").strip()
    if head != LEAN_COMMIT:
        raise AuthorityError(f"expected Lean {LEAN_COMMIT}, got {head}")
    if git(repo, "status", "--porcelain", "--untracked-files=no").strip():
        raise AuthorityError("pinned Lean checkout has tracked modifications")

    tree = parse_tree(repo, head)
    with tempfile.TemporaryDirectory(prefix="axeyum-lean-u2-") as raw_temp:
        temp = Path(raw_temp)
        lean_root = temp / "lean"
        extract_content(repo, head, lean_root)
        (lean_root / "src").mkdir()
        harness_root = temp / "harness"
        harness_root.mkdir()
        (harness_root / "CMakeLists.txt").write_text(
            "\n".join(
                (
                    "cmake_minimum_required(VERSION 3.20)",
                    "project(axeyum_lean_u2_registration NONE)",
                    "enable_testing()",
                    "set(STAGE 1)",
                    f'set(LEAN_SOURCE_DIR "{lean_root.as_posix()}/src")',
                    f'add_subdirectory("{lean_root.as_posix()}/tests" lean-tests)',
                    "",
                )
            ),
            encoding="utf-8",
        )

        files: list[dict[str, Any]] = []
        for path, mode, object_id in tree:
            files.append(
                file_identity(
                    path, mode, object_id, content_bytes(lean_root, path, mode)
                )
            )

        profile_rows: dict[str, list[dict[str, Any]]] = {}
        wrapper_digests: dict[str, str] = {}
        for profile_id in PROFILE_IDS:
            rows, wrapper_digest = configure_profile(harness_root, lean_root, profile_id)
            profile_rows[profile_id] = rows
            wrapper_digests[profile_id] = wrapper_digest

    if wrapper_digests["default"] != wrapper_digests["full-lake"]:
        raise AuthorityError("normalized generated test environment differs by profile")

    rows_by_profile = {
        profile_id: {row["id"]: row for row in rows}
        for profile_id, rows in profile_rows.items()
    }
    default_ids = set(rows_by_profile["default"])
    full_ids = set(rows_by_profile["full-lake"])
    if not default_ids < full_ids:
        raise AuthorityError("expected default CTest selection to be a strict full-lake subset")

    file_by_path = {item["path"]: item for item in files}
    source_paths = []
    for case_id in sorted(full_ids):
        source_paths.append(relative_source_path(case_id, case_kind(case_id)))
    support_scopes, _ = build_support_scopes(source_paths, files)

    cases: list[dict[str, Any]] = []
    for case_id in sorted(full_ids):
        kind = case_kind(case_id)
        source_path = relative_source_path(case_id, kind)
        source = file_by_path.get(source_path)
        if source is None:
            raise AuthorityError(f"registered case {case_id} has no primary {source_path}")
        registration = rows_by_profile["full-lake"][case_id]
        if case_id in default_ids and rows_by_profile["default"][case_id] != registration:
            raise AuthorityError(f"normalized registration differs by profile: {case_id}")
        sidecars = sorted(
            path for path in file_by_path if path.startswith(source_path + ".")
        )
        exact_path = source_path + ".out.expected"
        ignored_path = source_path + ".out.ignored"
        if kind != "pile":
            output_policy = "script-defined"
            expected_path = None
        elif ignored_path in file_by_path:
            output_policy = "ignored"
            expected_path = ignored_path
        elif exact_path in file_by_path:
            output_policy = "exact"
            expected_path = exact_path
        else:
            output_policy = "empty"
            expected_path = None
        case: dict[str, Any] = {
            "id": case_id,
            "profiles": [
                profile_id for profile_id in PROFILE_IDS if case_id in rows_by_profile[profile_id]
            ],
            "kind": kind,
            "family": case_family(case_id),
            "source_path": source_path,
            "source_sha256": source["sha256"],
            "sidecars": sidecars,
            "support_scope": str(Path(source_path).parent),
            "output_policy": output_policy,
            "expected_path": expected_path,
            "ctest_success": "process-exit-0",
            "registration": {
                "command": registration["command"],
                "properties": registration["properties"],
            },
        }
        case["sha256"] = case_digest(case)
        cases.append(case)

    profiles = []
    for profile_id in PROFILE_IDS:
        profile_cases = [case for case in cases if profile_id in case["profiles"]]
        profiles.append(
            {
                "id": profile_id,
                "lake_ci": profile_id == "full-lake",
                "registered": len(profile_cases),
                "registration_sha256": digest(
                    [
                        {"id": case["id"], "registration": case["registration"]}
                        for case in profile_cases
                    ]
                ),
            }
        )

    content_roots = []
    for root in CONTENT_ROOTS:
        prefix = root + "/"
        members = [item for item in files if item["path"].startswith(prefix)]
        content_roots.append(
            {
                "path": root,
                "files": len(members),
                "bytes": sum(item["bytes"] for item in members),
                "sha256": scope_digest(members),
            }
        )

    registration_inputs = []
    tree_by_path = {path: (mode, object_id) for path, mode, object_id in tree}
    for path in REGISTRATION_INPUTS:
        contents = git_blob(repo, head, path)
        if path in tree_by_path:
            mode, object_id = tree_by_path[path]
        else:
            row = git(repo, "ls-tree", "--full-tree", head, "--", path).decode().strip()
            metadata, observed_path = row.split("\t", 1)
            mode, object_type, object_id = metadata.split()
            if object_type != "blob" or observed_path != path:
                raise AuthorityError(f"bad registration input tree row for {path}")
        registration_inputs.append(file_identity(path, mode, object_id, contents))

    pile_ids = {case["id"] for case in cases if case["kind"] == "pile"}
    return {
        "schema": SCHEMA,
        "as_of": "2026-07-22",
        "scope": "bounded-registration-authority-not-complete-u2",
        "target": {
            "repository": "https://github.com/leanprover/lean4.git",
            "version": LEAN_VERSION,
            "tag": LEAN_TAG,
            "commit": LEAN_COMMIT,
        },
        "capture": {
            "method": "pinned CMake registration plus CTest JSON v1",
            "stage": 1,
            "profiles": profiles,
            "default_is_full_lake_subset": True,
            "default_only": 0,
            "full_lake_only": len(full_ids - default_ids),
            "generated_test_environment_sha256": wrapper_digests["default"],
            "path_tokens": ["$BASH", "$BUILD_ROOT", "$HARNESS_ROOT", "$LEAN_ROOT", "$PYTHON3"],
        },
        "selection_accounting": selection_accounting(files, pile_ids),
        "registration_inputs": registration_inputs,
        "content_roots": content_roots,
        "content_files_sha256": scope_digest(files),
        "content_files": files,
        "support_scopes": support_scopes,
        "cases_sha256": digest(cases),
        "cases": cases,
        "outcomes": {
            "official_executed": 0,
            "axeyum_executed": 0,
            "paired_registered": 0,
            "state": "not-run",
        },
        "residual": [
            "Derive every official CI platform, build preset, CTEST_OPTIONS filter, shard, retry, resource, and completion identity.",
            "Execute and retain official Lean outcomes for the complete declared profile matrix.",
            "Implement native Axeyum source/workflow/runtime surfaces and retain matched per-case outcomes.",
            "Register U2 terminal paired cells only after both executions use the same normalized case identity.",
        ],
    }


def validate_file_identity(owner: str, item: Any, failures: list[str]) -> None:
    if not isinstance(item, dict) or set(item) != {
        "path",
        "mode",
        "git_blob",
        "bytes",
        "sha256",
    }:
        failures.append(f"{owner}: malformed file identity")
        return
    if not isinstance(item["path"], str) or not item["path"]:
        failures.append(f"{owner}: file path is required")
    if item["mode"] not in {"100644", "100755", "120000"}:
        failures.append(f"{owner}: unsupported file mode")
    if (
        not isinstance(item["git_blob"], str)
        or len(item["git_blob"]) != 40
        or any(char not in HEX40 for char in item["git_blob"])
    ):
        failures.append(f"{owner}: git blob must be lowercase 40-hex")
    if not isinstance(item["bytes"], int) or isinstance(item["bytes"], bool) or item["bytes"] < 0:
        failures.append(f"{owner}: byte count must be non-negative")
    if not is_sha256(item["sha256"]):
        failures.append(f"{owner}: sha256 must be lowercase 64-hex")


def is_file_identity(item: Any) -> bool:
    return (
        isinstance(item, dict)
        and set(item) == {"path", "mode", "git_blob", "bytes", "sha256"}
        and isinstance(item["path"], str)
        and bool(item["path"])
        and item["mode"] in {"100644", "100755", "120000"}
        and isinstance(item["git_blob"], str)
        and len(item["git_blob"]) == 40
        and all(char in HEX40 for char in item["git_blob"])
        and isinstance(item["bytes"], int)
        and not isinstance(item["bytes"], bool)
        and item["bytes"] >= 0
        and is_sha256(item["sha256"])
    )


def is_sha256(value: Any) -> bool:
    return (
        isinstance(value, str)
        and len(value) == 64
        and all(char in HEX40 for char in value)
    )


def validate_manifest(data: dict[str, Any]) -> list[str]:
    failures: list[str] = []
    if data.get("schema") != SCHEMA:
        failures.append(f"schema must be {SCHEMA}")
    if data.get("scope") != "bounded-registration-authority-not-complete-u2":
        failures.append("scope must remain bounded and non-terminal")
    if data.get("as_of") != "2026-07-22":
        failures.append("as_of must remain the capture date 2026-07-22")
    if data.get("target") != {
        "repository": "https://github.com/leanprover/lean4.git",
        "version": LEAN_VERSION,
        "tag": LEAN_TAG,
        "commit": LEAN_COMMIT,
    }:
        failures.append("target must match the exact Lean v4.30.0 pin")

    files = data.get("content_files")
    if not isinstance(files, list):
        failures.append("content_files must be a list")
        files = []
    paths = [item.get("path") for item in files if isinstance(item, dict)]
    if (
        not all(isinstance(path, str) for path in paths)
        or paths != sorted(path for path in paths if isinstance(path, str))
        or len(paths) != len(set(paths))
    ):
        failures.append("content file paths must be unique and sorted")
    for index, item in enumerate(files):
        validate_file_identity(f"content_files[{index}]", item, failures)
    valid_files = [item for item in files if is_file_identity(item)]
    if len(valid_files) == len(files) and data.get("content_files_sha256") != scope_digest(files):
        failures.append("content_files_sha256 disagrees with content_files")
    file_by_path = {
        item["path"]: item
        for item in valid_files
    }

    inputs = data.get("registration_inputs")
    if not isinstance(inputs, list):
        failures.append("registration_inputs must be a list")
        inputs = []
    if [item.get("path") for item in inputs if isinstance(item, dict)] != list(REGISTRATION_INPUTS):
        failures.append("registration input paths/order drift")
    for index, item in enumerate(inputs):
        validate_file_identity(f"registration_inputs[{index}]", item, failures)

    roots = data.get("content_roots")
    if not isinstance(roots, list):
        failures.append("content_roots must be a list")
        roots = []
    if [item.get("path") for item in roots if isinstance(item, dict)] != list(CONTENT_ROOTS):
        failures.append("content root paths/order drift")
    for root in roots:
        if not isinstance(root, dict):
            failures.append("malformed content root")
            continue
        members = [
            item
            for item in valid_files
            if item["path"].startswith(str(root.get("path")) + "/")
        ]
        expected = {
            "path": root.get("path"),
            "files": len(members),
            "bytes": sum(item.get("bytes", 0) for item in members),
            "sha256": scope_digest(members),
        }
        if root != expected:
            failures.append(f"content root {root.get('path')}: aggregate drift")

    scopes = data.get("support_scopes")
    if not isinstance(scopes, list):
        failures.append("support_scopes must be a list")
        scopes = []
    scope_paths = [item.get("path") for item in scopes if isinstance(item, dict)]
    if (
        not all(isinstance(path, str) for path in scope_paths)
        or scope_paths != sorted(path for path in scope_paths if isinstance(path, str))
        or len(scope_paths) != len(set(scope_paths))
    ):
        failures.append("support scope paths must be unique and sorted")
    scope_by_path = {}
    for scope in scopes:
        if not isinstance(scope, dict):
            failures.append("malformed support scope")
            continue
        path = scope.get("path")
        members = [
            item for item in valid_files if item["path"].startswith(str(path) + "/")
        ]
        expected = {
            "path": path,
            "files": len(members),
            "bytes": sum(item.get("bytes", 0) for item in members),
            "sha256": scope_digest(members),
        }
        if scope != expected:
            failures.append(f"support scope {path}: aggregate drift")
        scope_by_path[path] = scope

    cases = data.get("cases")
    if not isinstance(cases, list):
        failures.append("cases must be a list")
        cases = []
    case_ids = [case.get("id") for case in cases if isinstance(case, dict)]
    if (
        not all(isinstance(case_id, str) for case_id in case_ids)
        or case_ids != sorted(case_id for case_id in case_ids if isinstance(case_id, str))
        or len(case_ids) != len(set(case_ids))
    ):
        failures.append("case ids must be unique and sorted")
    for case in cases:
        if not isinstance(case, dict):
            failures.append("every case must be an object")
            continue
        case_id = case.get("id")
        if set(case) != CASE_FIELDS:
            failures.append(f"{case_id}: case fields must be exact")
        if not isinstance(case_id, str) or not case_id:
            failures.append("every case needs a non-empty string id")
            continue
        if case.get("profiles") not in (["full-lake"], ["default", "full-lake"]):
            failures.append(f"{case_id}: invalid profile membership")
        expected_kind = case_kind(case_id)
        if case.get("kind") != expected_kind:
            failures.append(f"{case_id}: kind disagrees with registration id")
        if case.get("family") != case_family(case_id):
            failures.append(f"{case_id}: family disagrees with registration id")
        expected_source_path = relative_source_path(case_id, expected_kind)
        source_path = case.get("source_path")
        if source_path != expected_source_path:
            failures.append(f"{case_id}: primary source path drift")
        source = file_by_path.get(source_path)
        if source is None:
            failures.append(f"{case_id}: missing primary source")
        elif case.get("source_sha256") != source["sha256"]:
            failures.append(f"{case_id}: primary source digest drift")
        sidecars = case.get("sidecars")
        if not isinstance(sidecars, list) or sidecars != sorted(sidecars):
            failures.append(f"{case_id}: sidecars must be sorted")
            sidecars = []
        if any(path not in file_by_path for path in sidecars):
            failures.append(f"{case_id}: missing sidecar")
        derived_sidecars = sorted(
            path for path in file_by_path if path.startswith(str(source_path) + ".")
        )
        if sidecars != derived_sidecars:
            failures.append(f"{case_id}: sidecar set drift")
        expected = case.get("expected_path")
        policy = case.get("output_policy")
        exact_path = str(source_path) + ".out.expected"
        ignored_path = str(source_path) + ".out.ignored"
        if expected_kind != "pile":
            derived_policy = "script-defined"
        elif ignored_path in file_by_path:
            derived_policy = "ignored"
        elif exact_path in file_by_path:
            derived_policy = "exact"
        else:
            derived_policy = "empty"
        if policy != derived_policy:
            failures.append(f"{case_id}: output policy drift")
        if policy in {"exact", "ignored"}:
            suffix = ".out.expected" if policy == "exact" else ".out.ignored"
            if expected != str(source_path) + suffix or expected not in sidecars:
                failures.append(f"{case_id}: expected-output identity drift")
        elif expected is not None:
            failures.append(f"{case_id}: unexpected expected-output path")
        expected_scope = Path(str(source_path)).parent.as_posix()
        if case.get("support_scope") != expected_scope:
            failures.append(f"{case_id}: support scope path drift")
        if case.get("support_scope") not in scope_by_path:
            failures.append(f"{case_id}: missing support scope")
        registration = case.get("registration")
        if not isinstance(registration, dict) or set(registration) != {"command", "properties"}:
            failures.append(f"{case_id}: malformed registration")
        elif not isinstance(registration["command"], list) or not registration["command"]:
            failures.append(f"{case_id}: registration command is required")
        elif any(
            isinstance(value, str) and ("/tmp/" in value or "/home/" in value)
            for value in registration["command"]
        ):
            failures.append(f"{case_id}: registration command contains a host path")
        if case.get("ctest_success") != "process-exit-0":
            failures.append(f"{case_id}: CTest success contract drift")
        if case.get("sha256") != case_digest(case):
            failures.append(f"{case_id}: case digest drift")
    if data.get("cases_sha256") != digest(cases):
        failures.append("cases_sha256 disagrees with cases")

    capture_data = data.get("capture")
    profiles = capture_data.get("profiles", []) if isinstance(capture_data, dict) else []
    expected_capture_fields = {
        "method",
        "stage",
        "profiles",
        "default_is_full_lake_subset",
        "default_only",
        "full_lake_only",
        "generated_test_environment_sha256",
        "path_tokens",
    }
    if not isinstance(capture_data, dict) or set(capture_data) != expected_capture_fields:
        failures.append("capture fields must be exact")
    elif (
        capture_data.get("method") != "pinned CMake registration plus CTest JSON v1"
        or capture_data.get("stage") != 1
        or capture_data.get("path_tokens")
        != ["$BASH", "$BUILD_ROOT", "$HARNESS_ROOT", "$LEAN_ROOT", "$PYTHON3"]
    ):
        failures.append("capture method, stage, or path-token contract drift")
    if [profile.get("id") for profile in profiles if isinstance(profile, dict)] != list(PROFILE_IDS):
        failures.append("capture profile ids/order drift")
    for profile in profiles:
        if not isinstance(profile, dict):
            failures.append("every capture profile must be an object")
            continue
        profile_id = profile.get("id")
        members = [
            case
            for case in cases
            if isinstance(case, dict)
            and set(case) == CASE_FIELDS
            and profile_id in case.get("profiles", [])
        ]
        expected = {
            "id": profile_id,
            "lake_ci": profile_id == "full-lake",
            "registered": len(members),
            "registration_sha256": digest(
                [
                    {"id": case["id"], "registration": case["registration"]}
                    for case in members
                ]
            ),
        }
        if profile != expected:
            failures.append(f"capture profile {profile_id}: aggregate drift")
    if isinstance(capture_data, dict):
        default_ids = {
            case["id"]
            for case in cases
            if isinstance(case, dict)
            and isinstance(case.get("id"), str)
            and "default" in case.get("profiles", [])
        }
        full_ids = {
            case["id"]
            for case in cases
            if isinstance(case, dict)
            and isinstance(case.get("id"), str)
            and "full-lake" in case.get("profiles", [])
        }
        if capture_data.get("default_is_full_lake_subset") is not True or not default_ids < full_ids:
            failures.append("default selection must be a strict full-lake subset")
        if capture_data.get("default_only") != len(default_ids - full_ids):
            failures.append("default-only count drift")
        if capture_data.get("full_lake_only") != len(full_ids - default_ids):
            failures.append("full-lake-only count drift")
        if not is_sha256(capture_data.get("generated_test_environment_sha256")):
            failures.append("generated test environment digest is required")

    accounting = data.get("selection_accounting")
    pile_cases = {
        case["id"]
        for case in cases
        if isinstance(case, dict)
        and isinstance(case.get("id"), str)
        and case.get("kind") == "pile"
    }
    pile_count = len(pile_cases)
    if not isinstance(accounting, dict) or accounting.get("registered") != pile_count:
        failures.append("pile selection accounting disagrees with cases")
    elif accounting.get("glob_candidates") != accounting.get("registered") + accounting.get("excluded"):
        failures.append("pile glob accounting does not close")
    if len(valid_files) == len(files):
        try:
            expected_accounting = selection_accounting(valid_files, pile_cases)
        except AuthorityError as error:
            failures.append(str(error))
        else:
            if accounting != expected_accounting:
                failures.append("pile selection accounting content drift")

    if data.get("outcomes") != {
        "official_executed": 0,
        "axeyum_executed": 0,
        "paired_registered": 0,
        "state": "not-run",
    }:
        failures.append("registration authority cannot claim execution or paired outcomes")
    residual = data.get("residual")
    if not isinstance(residual, list) or len(residual) < 4 or not all(residual):
        failures.append("open U2 residual must remain explicit")
    return failures


def summarize(data: dict[str, Any]) -> dict[str, Any]:
    cases = data["cases"]
    kind_counts = Counter(case["kind"] for case in cases)
    family_counts = Counter(case["family"] for case in cases)
    output_counts = Counter(case["output_policy"] for case in cases)
    sidecar_counts = Counter()
    for case in cases:
        for sidecar in case["sidecars"]:
            suffix = sidecar[len(case["source_path"]) :]
            sidecar_counts[suffix] += 1
    source = MANIFEST.read_bytes()
    return {
        "schema": "axeyum-lean-u2-test-authority-report-v1",
        "generated_from": "docs/plan/lean-u2-test-authority-v1.json",
        "generated_from_sha256": sha256_bytes(source),
        "target": data["target"],
        "scope": data["scope"],
        "profiles": data["capture"]["profiles"],
        "selection_relation": {
            "default_only": data["capture"]["default_only"],
            "full_lake_only": data["capture"]["full_lake_only"],
        },
        "content": {
            "roots": data["content_roots"],
            "files": len(data["content_files"]),
            "files_sha256": data["content_files_sha256"],
            "support_scopes": len(data["support_scopes"]),
            "cases": len(cases),
            "cases_sha256": data["cases_sha256"],
        },
        "selection_accounting": data["selection_accounting"],
        "kind_counts": dict(sorted(kind_counts.items())),
        "family_counts": dict(sorted(family_counts.items())),
        "output_policy_counts": dict(sorted(output_counts.items())),
        "sidecar_counts": dict(sorted(sidecar_counts.items())),
        "outcomes": data["outcomes"],
        "residual": data["residual"],
        "verdict": "registration bounded; complete U2 parity authority not established",
    }


def render_markdown(report: dict[str, Any]) -> str:
    target = report["target"]
    lines = [
        "# Lean U2 official-test registration authority",
        "",
        "> **Generated; do not edit by hand.** Regenerate with `python3 "
        "scripts/gen-lean-u2-test-authority.py`; validate with `--check`.",
        "",
        "> **Verdict: registration bounded; complete U2 parity authority not "
        "established.** No official execution, Axeyum execution, or paired-result "
        "credit is recorded here.",
        "",
        f"Pinned Lean `{target['tag']}` at `{target['commit']}`. The capture runs "
        "Lean's CMake test registration and reads CTest JSON v1; it does not count "
        "raw files as tests.",
        "",
        "## Registered profiles",
        "",
        "| Profile | `LAKE_CI` | Registered cases | Registration digest |",
        "|---|---:|---:|---|",
    ]
    for profile in report["profiles"]:
        lines.append(
            f"| `{profile['id']}` | `{'ON' if profile['lake_ci'] else 'OFF'}` | "
            f"{profile['registered']:,} | `{profile['registration_sha256']}` |"
        )
    lines.extend(
        [
            "",
            f"The default selection is a strict subset of the full-Lake selection: "
            f"{report['selection_relation']['default_only']} default-only and "
            f"{report['selection_relation']['full_lake_only']} full-Lake-only cases.",
            "",
            "## Selection composition",
            "",
            "| Kind | Cases |",
            "|---|---:|",
        ]
    )
    for kind, count in report["kind_counts"].items():
        lines.append(f"| `{kind}` | {count:,} |")
    lines.extend(["", "| Output contract | Cases |", "|---|---:|"])
    for policy, count in report["output_policy_counts"].items():
        lines.append(f"| `{policy}` | {count:,} |")
    lines.extend(["", "| Family | Cases |", "|---|---:|"])
    for family, count in report["family_counts"].items():
        lines.append(f"| `{family}` | {count:,} |")

    content = report["content"]
    accounting = report["selection_accounting"]
    lines.extend(
        [
            "",
            "## Content and derivation closure",
            "",
            f"- {content['cases']:,} full-Lake case records, digest "
            f"`{content['cases_sha256']}`.",
            f"- {content['files']:,} Git-tracked support files across "
            f"{content['support_scopes']:,} over-approximating per-case support "
            f"subtrees, digest `{content['files_sha256']}`.",
            f"- Pile selection closes exactly: {accounting['glob_candidates']:,} "
            f"glob candidates = {accounting['registered']:,} registered + "
            f"{accounting['excluded']:,} excluded.",
            "- Every case retains its normalized command and CTest properties, "
            "primary content digest, sidecar paths, output policy, support scope, "
            "profile membership, and case digest in the "
            "[machine-readable authority](../lean-u2-test-authority-v1.json).",
            "- Upstream CI and preset sources are content-bound, but their platform "
            "filters, sharding, retries, and resource envelopes remain deliberately "
            "unpromoted pending a separate executable profile derivation.",
            "",
            "## Why U2 remains incomplete",
            "",
        ]
    )
    lines.extend(f"- {item}" for item in report["residual"])
    lines.extend(
        [
            "",
            "This is therefore a reproducible selection denominator for two bounded "
            "registration profiles, not evidence that Lean ran them successfully and "
            "not evidence that Axeyum can run or match them.",
            "",
        ]
    )
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
    parser.add_argument("--check", action="store_true", help="validate committed inputs and outputs")
    parser.add_argument("--capture-upstream", type=Path, metavar="LEAN_REPO")
    parser.add_argument("--verify-upstream", type=Path, metavar="LEAN_REPO")
    args = parser.parse_args()
    if args.capture_upstream and args.verify_upstream:
        parser.error("choose at most one upstream mode")

    if args.capture_upstream:
        data = capture(args.capture_upstream)
        MANIFEST.write_text(json_text(data), encoding="utf-8")
    else:
        data = read_manifest()

    failures = validate_manifest(data)
    if args.verify_upstream:
        observed = capture(args.verify_upstream)
        if observed != data:
            failures.append("fresh pinned-upstream capture differs from committed authority")
    if args.check:
        failures.extend(check_outputs(data))
    if failures:
        for failure in failures:
            print(f"lean-u2-test-authority: {failure}", file=sys.stderr)
        return 1
    if not args.check and not args.verify_upstream:
        write_outputs(data)
    print(
        "lean-u2-test-authority: ok "
        f"({len(data['cases'])} full-Lake cases; "
        f"{data['capture']['profiles'][0]['registered']} default cases; "
        "outcomes not run)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
