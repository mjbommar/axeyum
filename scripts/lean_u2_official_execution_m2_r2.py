#!/usr/bin/env python3
"""Validate or append M2 R2's zero-process diagnostic artifact closure."""

from __future__ import annotations

import argparse
import json
import stat
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import lean_u2_official_execution as BASE  # noqa: E402
from scripts import lean_u2_official_execution_m2 as M2  # noqa: E402


PLAN = ROOT / (
    "docs/plan/lean-u2-official-execution-tl0.6.3-m2-r2-"
    "diagnostic-closure-plan-2026-07-22.md"
)
PLAN_COMMIT = "e776ea73251e3346952e9f5a55749a982f3506ed"
PLAN_SHA256 = "91f1d6d42f55a5717fef731df301bb7f2d49eb00eef5689c5bc7f7e17f7aff67"
R1_AUTHORITY = ROOT / (
    "docs/plan/lean-u2-official-execution-tl0.6.3-m2-r1-result-v1.json"
)
R1_AUTHORITY_SHA256 = "df5f95b9ee4f96e576119e7225eac98f0329a1eadbfd901703287627af852dd6"
R1_AUTHORITY_RECORD = "0df3ed527d28b12b17cd5a3c0db3970f01a98e7886452feefda3f02068edb9fe"
EVIDENCE_ROOT = ROOT / (
    "docs/plan/evidence/lean-u2-official-execution-tl0.6.3-m2-shard-0001"
)
WORK_SOURCE = Path(
    "/home/mjbommar/.cache/axeyum-tl063-m2-r1-59108766/source"
)

R1_FILES = 83
R1_BYTES = 5_148_026
R1_DOMAIN = "axeyum-lean-u2-official-execution-m2-r1-incomplete-evidence-v1"
R1_MANIFEST = "8692f3184dba764e0904f1db2d2283a56a71cccced0c371ddd634807cc0b2961"
FULL_DOMAIN = "axeyum-lean-u2-official-execution-m2-generated-files-v1"
FULL_COUNT = 124
FULL_BYTES = 950_327_258
FULL_DIGEST = "0b9e462afd9a281b5fba7aabdd2399ca5a628a7e85e82989f576b32b28c8c66c"
RETAINED_DOMAIN = (
    "axeyum-lean-u2-official-execution-m2-r2-retained-generated-files-v1"
)
RETAINED_COUNT = 67
RETAINED_BYTES = 106_610
RETAINED_DIGEST = "786be409fe673843e43eaba5f665f69577ef5c9e141ec7420707dadd89e65c66"
METADATA_DOMAIN = (
    "axeyum-lean-u2-official-execution-m2-r2-manifest-only-generated-files-v1"
)
METADATA_COUNT = 56
METADATA_BYTES = 950_219_754
METADATA_DIGEST = "f242f5daf87babf747a1881966ba4e3db4ac974e57adbf6ad336a385910f2c54"
WRAPPER_DOMAIN = "axeyum-lean-u2-official-execution-m2-r2-existing-wrapper-v1"
WRAPPER_DIGEST = "58d3013ae4787e5127e1b5fbc7d60537aee99738047fc60ce800506cdd9b347a"
POST_SCHEMA = "axeyum-lean-u2-official-execution-m2-r2-diagnostic-post-v1"
COMPLETION_SCHEMA = (
    "axeyum-lean-u2-official-execution-m2-r2-diagnostic-completion-v1"
)
INVENTORY_DOMAIN = (
    "axeyum-lean-u2-official-execution-m2-r2-diagnostic-inventory-v1"
)


class R2DiagnosticError(ValueError):
    """R2's frozen evidence or append-only diagnostic closure drifted."""


def portable_manifest(root: Path, *, exclude_completion: bool = False) -> list[dict[str, Any]]:
    if not root.is_dir() or root.is_symlink():
        raise R2DiagnosticError("R2 evidence root is not a real directory")
    rows = []
    for path in sorted(root.rglob("*"), key=lambda item: item.relative_to(root).as_posix()):
        relative = path.relative_to(root).as_posix()
        if exclude_completion and relative == "diagnostic/completion.json":
            continue
        info = path.lstat()
        if stat.S_ISLNK(info.st_mode):
            raise R2DiagnosticError(f"symlinked R2 evidence path: {relative}")
        if stat.S_ISREG(info.st_mode):
            rows.append(
                {
                    "path": relative,
                    "kind": "file",
                    "mode": 0o444,
                    "bytes": info.st_size,
                    "sha256": BASE.sha256_file(path),
                    "target": None,
                }
            )
        elif not stat.S_ISDIR(info.st_mode):
            raise R2DiagnosticError(f"non-regular R2 evidence path: {relative}")
    return rows


def validate_r1_evidence(root: Path, *, require_readonly: bool) -> dict[str, Any]:
    if not PLAN.is_file() or BASE.sha256_file(PLAN) != PLAN_SHA256:
        raise R2DiagnosticError("R2 preregistration plan drift")
    if (
        not R1_AUTHORITY.is_file()
        or BASE.sha256_file(R1_AUTHORITY) != R1_AUTHORITY_SHA256
    ):
        raise R2DiagnosticError("R1 result authority physical drift")
    authority = BASE.load_json(R1_AUTHORITY)
    if (
        not BASE.valid_seal(authority, authority.get("schema", ""))
        or authority.get("record_sha256") != R1_AUTHORITY_RECORD
    ):
        raise R2DiagnosticError("R1 result authority seal drift")
    if (root / "diagnostic").exists() or (root / "diagnostic").is_symlink():
        raise R2DiagnosticError("R2 diagnostic namespace already exists")
    rows = portable_manifest(root)
    if (
        len(rows) != R1_FILES
        or sum(row["bytes"] for row in rows) != R1_BYTES
        or BASE.domain_digest(R1_DOMAIN, rows) != R1_MANIFEST
    ):
        raise R2DiagnosticError("R1 incomplete evidence manifest drift")
    if require_readonly:
        for row in rows:
            if stat.S_IMODE((root / row["path"]).stat().st_mode) != 0o444:
                raise R2DiagnosticError(f"mutable R1 evidence: {row['path']}")
    for forbidden in ("post.json", "projection.json", "completion.json"):
        if (root / forbidden).exists() or (root / forbidden).is_symlink():
            raise R2DiagnosticError(f"R1 invalid attempt gained {forbidden}")
    return authority


def case_generated_paths(case: dict[str, Any]) -> list[str]:
    source = case["source_path"]
    if case["family"] == "docparse":
        return [source + ".out.produced"]
    if case["family"] not in {"compile", "compile_bench"}:
        raise R2DiagnosticError(f"unregistered M2 family: {case['family']}")
    sidecars = set(case["sidecars"])
    no_compile = any(
        source + suffix in sidecars for suffix in (".no_compile_test", ".no_compile")
    )
    paths = [source + ".out.produced"]
    if not no_compile:
        paths.extend((source + ".c", source + ".out"))
    return sorted(paths)


def expected_generated_paths() -> list[str]:
    paths = {"tests/with_stage1_test_env.sh", *BASE.CTEST_SOURCE_PATHS}
    for case in M2.selected_contract()["cases"]:
        paths.update(case_generated_paths(case))
    return sorted(paths)


def capture_work_projection(work_source: Path, evidence_root: Path) -> dict[str, Any]:
    if work_source != WORK_SOURCE:
        raise R2DiagnosticError("R2 work-source substitution")
    source = BASE.load_canonical(evidence_root / "source.json")
    before = {row["path"]: row for row in source["files"]}
    after = {row["path"]: row for row in BASE.manifest_tree(work_source)}
    changed = [path for path, row in before.items() if after.get(path) != row]
    if changed or set(before) - set(after):
        raise R2DiagnosticError("R2 original source manifest drift")
    new_paths = sorted(set(after) - set(before))
    if new_paths != expected_generated_paths():
        raise R2DiagnosticError("R2 generated path closure drift")
    full = [after[path] for path in new_paths]
    retained = [
        row
        for row in full
        if row["path"].endswith(".out.produced")
        or row["path"].startswith("build/release/Testing/Temporary/")
    ]
    metadata = [
        row for row in full if row["path"].endswith(".c") or row["path"].endswith(".out")
    ]
    wrapper = [row for row in full if row["path"] == "tests/with_stage1_test_env.sh"]
    checks = (
        (full, FULL_COUNT, FULL_BYTES, FULL_DOMAIN, FULL_DIGEST),
        (retained, RETAINED_COUNT, RETAINED_BYTES, RETAINED_DOMAIN, RETAINED_DIGEST),
        (metadata, METADATA_COUNT, METADATA_BYTES, METADATA_DOMAIN, METADATA_DIGEST),
        (wrapper, 1, 894, WRAPPER_DOMAIN, WRAPPER_DIGEST),
    )
    for rows, count, size, domain, digest in checks:
        if (
            len(rows) != count
            or sum(row["bytes"] for row in rows) != size
            or BASE.domain_digest(domain, rows) != digest
        ):
            raise R2DiagnosticError(f"R2 frozen generated split drift: {domain}")
    return {"full": full, "retained": retained, "metadata": metadata, "wrapper": wrapper}


def diagnostic_path(source_path: str) -> str:
    path = Path(source_path)
    if path.is_absolute() or ".." in path.parts or not path.parts:
        raise R2DiagnosticError("unsafe R2 diagnostic artifact path")
    return (Path("diagnostic/generated") / path).as_posix()


def build_post(projection: dict[str, Any]) -> dict[str, Any]:
    retained = [
        row | {"evidence_path": diagnostic_path(row["path"])}
        for row in projection["retained"]
    ]
    return BASE.seal(
        {
            "schema": POST_SCHEMA,
            "plan_commit": PLAN_COMMIT,
            "plan_sha256": PLAN_SHA256,
            "r1_authority_sha256": R1_AUTHORITY_SHA256,
            "r1_authority_record_sha256": R1_AUTHORITY_RECORD,
            "r1_evidence_manifest_sha256": R1_MANIFEST,
            "terminal_sha256": "a4152e8ef82c2b5fe7388b5f661f655095696ea3a60fb5b5c03defadc70a0798",
            "junit_sha256": "5ffa07e7b51f331a4941384b0a479df917bb8ee1efbe2ab90e14e6ea9ab6e51f",
            "original_files_unchanged": True,
            "generated_files": projection["full"],
            "generated_files_sha256": FULL_DIGEST,
            "retained_generated": retained,
            "retained_generated_sha256": RETAINED_DIGEST,
            "manifest_only_generated": projection["metadata"],
            "manifest_only_generated_sha256": METADATA_DIGEST,
            "existing_wrapper": projection["wrapper"],
            "process_attempts_added": 0,
            "credits": M2.ZERO_TERMINAL_CREDITS
            | {
                "official_cases": 0,
                "official_outcomes": 0,
                "official_passes": 0,
                "official_failures": 0,
                "unique_new_official_cases": 0,
                "local_physical_shards_completed": 0,
            },
            "record_sha256": "",
        },
        POST_SCHEMA,
    )


def append_diagnostic(root: Path, work_source: Path) -> dict[str, Any]:
    validate_r1_evidence(root, require_readonly=True)
    projection = capture_work_projection(work_source, root)
    post = build_post(projection)
    for row in projection["retained"]:
        payload = (work_source / row["path"]).read_bytes()
        if len(payload) != row["bytes"] or BASE.sha256_bytes(payload) != row["sha256"]:
            raise R2DiagnosticError(f"R2 retained payload drift: {row['path']}")
        BASE.install_bytes(root, diagnostic_path(row["path"]), payload)
    BASE.install_json(root, "diagnostic/post.json", post)
    inventory = portable_manifest(root)
    completion = BASE.seal(
        {
            "schema": COMPLETION_SCHEMA,
            "post_sha256": post["record_sha256"],
            "r1_evidence_manifest_sha256": R1_MANIFEST,
            "dependency_files": len(inventory),
            "dependency_bytes": sum(row["bytes"] for row in inventory),
            "dependency_manifest_sha256": BASE.domain_digest(INVENTORY_DOMAIN, inventory),
            "r1_attempt_state": "invalid-post-artifact-closure",
            "process_attempts_added": 0,
            "official_outcomes": 0,
            "parity_credit": 0,
            "record_sha256": "",
        },
        COMPLETION_SCHEMA,
    )
    BASE.install_json(root, "diagnostic/completion.json", completion)
    validate_completed(root)
    return completion


def validate_completed(root: Path) -> dict[str, Any]:
    completion_path = root / "diagnostic/completion.json"
    if not completion_path.is_file() or completion_path.is_symlink():
        raise R2DiagnosticError("R2 diagnostic completion missing")
    post = BASE.load_canonical(root / "diagnostic/post.json")
    completion = BASE.load_canonical(completion_path)
    if not BASE.valid_seal(post, POST_SCHEMA) or not BASE.valid_seal(
        completion, COMPLETION_SCHEMA
    ):
        raise R2DiagnosticError("R2 diagnostic record seal drift")
    if post != build_post(
        {
            "full": post["generated_files"],
            "retained": [
                {key: value for key, value in row.items() if key != "evidence_path"}
                for row in post["retained_generated"]
            ],
            "metadata": post["manifest_only_generated"],
            "wrapper": post["existing_wrapper"],
        }
    ):
        raise R2DiagnosticError("R2 diagnostic post semantic drift")
    for row in post["retained_generated"]:
        path = root / row["evidence_path"]
        if (
            not path.is_file()
            or path.is_symlink()
            or path.stat().st_size != row["bytes"]
            or BASE.sha256_file(path) != row["sha256"]
        ):
            raise R2DiagnosticError(f"R2 diagnostic payload drift: {row['path']}")
    inventory = portable_manifest(root, exclude_completion=True)
    expected = BASE.seal(
        {
            "schema": COMPLETION_SCHEMA,
            "post_sha256": post["record_sha256"],
            "r1_evidence_manifest_sha256": R1_MANIFEST,
            "dependency_files": len(inventory),
            "dependency_bytes": sum(row["bytes"] for row in inventory),
            "dependency_manifest_sha256": BASE.domain_digest(INVENTORY_DOMAIN, inventory),
            "r1_attempt_state": "invalid-post-artifact-closure",
            "process_attempts_added": 0,
            "official_outcomes": 0,
            "parity_credit": 0,
            "record_sha256": "",
        },
        COMPLETION_SCHEMA,
    )
    if completion != expected:
        raise R2DiagnosticError("R2 diagnostic completion dependency drift")
    return completion


def offline_check() -> None:
    if not M2.HEX40.fullmatch(PLAN_COMMIT):
        raise R2DiagnosticError("R2 plan commit drift")
    if (EVIDENCE_ROOT / "diagnostic/completion.json").is_file():
        validate_completed(EVIDENCE_ROOT)
    else:
        validate_r1_evidence(EVIDENCE_ROOT, require_readonly=False)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("offline-check")
    append = sub.add_parser("append-diagnostic")
    append.add_argument("--work-source", type=Path, default=WORK_SOURCE)
    args = parser.parse_args()
    try:
        if args.command == "offline-check":
            offline_check()
            print("LEAN_U2_M2_R2|processes=0|outcomes=0|retained=67|metadata_only=56|parity=0")
        else:
            completion = append_diagnostic(EVIDENCE_ROOT, args.work_source)
            print(f"LEAN_U2_M2_R2_APPEND|completion={completion['record_sha256']}|processes=0|outcomes=0|parity=0")
    except (BASE.U2ExecutionError, R2DiagnosticError) as error:
        print(f"LEAN_U2_M2_R2_ERROR|{error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
