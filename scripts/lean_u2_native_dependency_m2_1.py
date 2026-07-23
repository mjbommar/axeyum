#!/usr/bin/env python3
"""Freeze and later execute TL0.6.4 M2.1 header-import evidence."""

from __future__ import annotations

import argparse
import copy
import functools
import hashlib
import importlib.util
import json
import os
import platform
import resource
import signal
import stat
import subprocess
import sys
import time
from pathlib import Path
from types import ModuleType
from typing import Any


ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

CONTRACT = ROOT / "docs/plan/lean-u2-native-header-contract-m2.1-v1.json"
OUT_JSON = ROOT / "docs/plan/generated/lean-u2-native-header-contract-m2.1.json"
OUT_MD = ROOT / "docs/plan/generated/lean-u2-native-header-contract-m2.1.md"
M1_PATH = ROOT / "docs/plan/lean-u2-native-surface-content-v1.json"
M1_VALIDATOR_PATH = ROOT / "scripts/gen-lean-u2-native-surface-content.py"
M20_PATH = ROOT / "docs/plan/lean-u2-native-dependency-v1.json"
M20_VALIDATOR_PATH = ROOT / "scripts/gen-lean-u2-native-dependency.py"
HELPER_PATH = ROOT / "scripts/lean_u2_header_full_parser.lean"
PLAN_PATH = (
    ROOT / "docs/plan/lean-u2-native-dependency-tl0.6.4-m2.1-plan-2026-07-23.md"
)

SCHEMA = "axeyum-lean-u2-native-header-contract-m2.1-v1"
REPORT_SCHEMA = "axeyum-lean-u2-native-header-contract-m2.1-report-v1"
AS_OF = "2026-07-23"
TARGET = {
    "lean_version": "4.30.0",
    "lean_commit": "d024af099ca4bf2c86f649261ebf59565dc8c622",
}
SOURCE_HASHES = {
    "docs/plan/lean-u2-native-surface-content-v1.json": (
        "c83d10ce0f0619d4327dbbd7544bd584360cb080d35778ca7798a5f7da17560f"
    ),
    "scripts/gen-lean-u2-native-surface-content.py": (
        "107d699e3ab372ee78e686affcb7cbd940d6ff4ae3446dc29f90d1cd6927fb05"
    ),
    "docs/plan/lean-u2-native-dependency-v1.json": (
        "46d2c17363bf8e4097d12df20f8ee9ffb86acf647642068d3eacc72e711dd4d6"
    ),
    "scripts/gen-lean-u2-native-dependency.py": (
        "e5f835bf4a0dbd4e59e82068b1e57b073f484153333962d1c85e0c308de90b19"
    ),
    "docs/plan/lean-u2-native-dependency-tl0.6.4-m2.1-plan-2026-07-23.md": (
        "7daa62ae0342c8fa64872604f880343fe9498866676675b61e911d034e3b999f"
    ),
    "scripts/lean_u2_header_full_parser.lean": (
        "12812e7956e5f6c5914247e7523b32559328febbeb319083652c458b3b9e4af2"
    ),
}
PINNED_PARSER_SOURCES = (
    {
        "path": "src/Lean/Elab/ParseImportsFast.lean",
        "sha256": "119ddfbd5e6b7dbe1847bfe5094c87c65e330669966b3a76de02dc12087abcb3",
        "role": "fast-header-parser-and-json-printer",
    },
    {
        "path": "src/Lean/Shell.lean",
        "sha256": "0de8cdbadedf418ccfb051ec8cb2c7bcd3bb6fef524c16962c72e4acfbf64d54",
        "role": "deps-json-stdin-command-dispatch",
    },
    {
        "path": "src/Lean/Setup.lean",
        "sha256": "452c19cab80687c56fbf90c3b9ee2627d66c40a49c15bab710d507dd4453df5a",
        "role": "import-and-module-header-json-schema",
    },
)
M1_RECORD_SHA256 = "d10f350d2c01d116538c9b52dcef71f38c473c81a36b3b41f75da4f39b889887"
M1_FILE_ROWS_SHA256 = "c52e4c465adbbbcd56577647be14c01bd3364779240661c0dbcfa138a17de13c"
M20_RECORD_SHA256 = "250b662691af5d71e375f3643454f94585bc51ff6f28aff69091b0f3956fdc86"

LEAN_BIN = Path(
    "/tmp/axeyum-codex-lean-20260722/elan-home/toolchains/"
    "leanprover--lean4---v4.30.0/bin/lean"
)
SOURCE_ROOT = Path("/tmp/axeyum-lean430-classify.MnJt9E/lean4")
EVIDENCE_ROOT = ROOT / "docs/plan/evidence/lean-u2-native-header-m2.1-attempt-001"
BATCH_SIZE = 128
PROCESS_COUNT = 39
CORPUS_ROWS = 4092
CORPUS_BYTES = 9_697_571
CASE_ROWS = 3723
CONTRACT_PHYSICAL_SHA256 = (
    "8447cf92349467962363baea30973f0cb4b0d95c1527b6544fd50e4e09100b5b"
)
CONTRACT_RECORD_SHA256 = (
    "f0c8f7a0725c78d5659eda52c1bee29ae08548a9e1bfe8043a369ca772381466"
)
RUNNER_PATH = ROOT / "scripts/lean_u2_native_dependency_m2_1.py"
PROCESS_DOMAIN = "axeyum-lean-u2-native-header-process-m2.1-v1"
COMPLETION_DOMAIN = "axeyum-lean-u2-native-header-completion-m2.1-v1"
AUTHORIZATION_DOMAIN = "axeyum-lean-u2-native-header-authorization-m2.1-v1"
PROCESS_DIR = "processes"

CORPUS_DOMAIN = "axeyum-lean-u2-native-header-corpus-row-m2.1-v1"
BATCH_DOMAIN = "axeyum-lean-u2-native-header-batch-m2.1-v1"
CONTROL_DOMAIN = "axeyum-lean-u2-native-header-control-m2.1-v1"

ZERO_CREDITS = {
    "resolved_source_edges": 0,
    "resolved_olean_edges": 0,
    "transitive_import_edges": 0,
    "configured_edges": 0,
    "runtime_edges": 0,
    "official_outcomes": 0,
    "axeyum_outcomes": 0,
    "paired_cells": 0,
    "performance_rows": 0,
    "complete_populations": 0,
    "complete_axes": 0,
    "satisfied_gates": 0,
    "parity_credit": 0,
}


class HeaderContractError(RuntimeError):
    """Fail-closed M2.1 input/control-contract error."""


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(
        value,
        allow_nan=False,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        while block := handle.read(1024 * 1024):
            digest.update(block)
    return digest.hexdigest()


def domain_digest(domain: str, value: Any) -> str:
    return sha256_bytes(domain.encode("ascii") + b"\0" + canonical_bytes(value))


def seal(record: dict[str, Any], domain: str) -> dict[str, Any]:
    result = copy.deepcopy(record)
    result["record_sha256"] = domain_digest(
        domain, {key: value for key, value in result.items() if key != "record_sha256"}
    )
    return result


def json_text(value: Any) -> str:
    return json.dumps(value, indent=2, ensure_ascii=False) + "\n"


def load_json(path: Path) -> dict[str, Any]:
    try:
        with path.open(encoding="utf-8") as handle:
            value = json.load(handle)
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise HeaderContractError(f"cannot read canonical JSON {path}: {error}") from error
    if not isinstance(value, dict):
        raise HeaderContractError(f"top-level JSON must be an object: {path}")
    return value


def load_script(name: str, path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise HeaderContractError(f"cannot import validator {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


@functools.lru_cache(maxsize=1)
def _validated_parents() -> tuple[dict[str, Any], dict[str, Any]]:
    for relative, expected in SOURCE_HASHES.items():
        path = ROOT / relative
        if not path.is_file() or sha256_file(path) != expected:
            raise HeaderContractError(f"frozen source/helper/plan drift: {relative}")
    m1 = load_json(M1_PATH)
    m1_validator = load_script("lean_u2_header_m1_validator", M1_VALIDATOR_PATH)
    failures = m1_validator.validate_authority(m1)
    if failures:
        raise HeaderContractError("invalid M1 parent: " + "; ".join(failures))
    m20 = load_json(M20_PATH)
    m20_validator = load_script("lean_u2_header_m20_validator", M20_VALIDATOR_PATH)
    failures = m20_validator.validate_authority(m20)
    if failures:
        raise HeaderContractError("invalid M2.0 parent: " + "; ".join(failures))
    if m1.get("record_sha256") != M1_RECORD_SHA256:
        raise HeaderContractError("M1 record seal drift")
    if m1.get("file_rows_sha256") != M1_FILE_ROWS_SHA256:
        raise HeaderContractError("M1 file-row seal drift")
    if m20.get("record_sha256") != M20_RECORD_SHA256:
        raise HeaderContractError("M2.0 record seal drift")
    return m1, m20


def validated_parents() -> tuple[dict[str, Any], dict[str, Any]]:
    m1, m20 = _validated_parents()
    return copy.deepcopy(m1), copy.deepcopy(m20)


def import_row(
    module: str,
    *,
    exported: bool,
    meta: bool = False,
    import_all: bool = False,
    origin: str = "explicit",
) -> dict[str, Any]:
    return {
        "module": module,
        "import_all": import_all,
        "is_exported": exported,
        "is_meta": meta,
        "origin": origin,
    }


def implicit_init() -> list[dict[str, Any]]:
    return [
        import_row("Init", exported=True, origin="implicit-default-prelude"),
        import_row(
            "Init", exported=True, meta=True, origin="implicit-default-prelude"
        ),
    ]


def control_specs() -> tuple[dict[str, Any], ...]:
    init = implicit_init()
    return (
        {
            "id": "legacy-default-init",
            "relative_path": "controls/01-legacy-default-init.lean",
            "source": "import Lean\n",
            "fast_state": "success",
            "full_state": "success",
            "comparison": "equal",
            "is_module": False,
            "imports": init + [import_row("Lean", exported=True)],
            "error_tokens": [],
        },
        {
            "id": "explicit-prelude",
            "relative_path": "controls/02-explicit-prelude.lean",
            "source": "prelude\nimport Init\n",
            "fast_state": "success",
            "full_state": "success",
            "comparison": "equal",
            "is_module": False,
            "imports": [import_row("Init", exported=True)],
            "error_tokens": [],
        },
        {
            "id": "module-private",
            "relative_path": "controls/03-module-private.lean",
            "source": "module\nimport Lean\n",
            "fast_state": "success",
            "full_state": "success",
            "comparison": "equal",
            "is_module": True,
            "imports": init + [import_row("Lean", exported=False)],
            "error_tokens": [],
        },
        {
            "id": "module-public",
            "relative_path": "controls/04-module-public.lean",
            "source": "module\npublic import Lean\n",
            "fast_state": "success",
            "full_state": "success",
            "comparison": "equal",
            "is_module": True,
            "imports": init + [import_row("Lean", exported=True)],
            "error_tokens": [],
        },
        {
            "id": "module-meta",
            "relative_path": "controls/05-module-meta.lean",
            "source": "module\nmeta import Lean\n",
            "fast_state": "success",
            "full_state": "success",
            "comparison": "equal",
            "is_module": True,
            "imports": init + [import_row("Lean", exported=False, meta=True)],
            "error_tokens": [],
        },
        {
            "id": "module-all",
            "relative_path": "controls/06-module-all.lean",
            "source": "module\nimport all Lean\n",
            "fast_state": "success",
            "full_state": "success",
            "comparison": "equal",
            "is_module": True,
            "imports": init
            + [import_row("Lean", exported=False, import_all=True)],
            "error_tokens": [],
        },
        {
            "id": "module-mixed-modifiers",
            "relative_path": "controls/07-module-mixed-modifiers.lean",
            "source": "module\npublic meta import Lean\nimport all Init\n",
            "fast_state": "success",
            "full_state": "success",
            "comparison": "equal",
            "is_module": True,
            "imports": init
            + [
                import_row("Lean", exported=True, meta=True),
                import_row("Init", exported=False, import_all=True),
            ],
            "error_tokens": [],
        },
        {
            "id": "duplicate-imports",
            "relative_path": "controls/08-duplicate-imports.lean",
            "source": "module\nimport Lean\nimport Lean\n",
            "fast_state": "success",
            "full_state": "success",
            "comparison": "equal",
            "is_module": True,
            "imports": init
            + [import_row("Lean", exported=False), import_row("Lean", exported=False)],
            "error_tokens": [],
        },
        {
            "id": "escaped-dotted-module",
            "relative_path": "controls/09-escaped-dotted-module.lean",
            "source": "module\nimport «weird-name».Sub\n",
            "fast_state": "success",
            "full_state": "success",
            "comparison": "equal",
            "is_module": True,
            "imports": init + [import_row("weird-name.Sub", exported=False)],
            "error_tokens": [],
        },
        {
            "id": "nested-and-line-comments",
            "relative_path": "controls/10-comments.lean",
            "source": "/- outer /- inner -/ end -/\n-- line\nimport Lean\n",
            "fast_state": "success",
            "full_state": "success",
            "comparison": "equal",
            "is_module": False,
            "imports": init + [import_row("Lean", exported=True)],
            "error_tokens": [],
        },
        {
            "id": "legacy-invalid-public",
            "relative_path": "controls/11-legacy-invalid-public.lean",
            "source": "public import Lean\n",
            "fast_state": "error",
            "full_state": "diagnostic",
            "comparison": "expected-fast-reject-full-diagnostic",
            "is_module": False,
            "imports": [],
            "error_tokens": ["cannot use", "without 'module'"],
        },
        {
            "id": "tab-header-whitespace",
            "relative_path": "controls/12-tab-header.lean",
            "source": "\timport Lean\n",
            "fast_state": "error",
            "full_state": "success-or-diagnostic",
            "comparison": "expected-fast-tab-rejection",
            "is_module": None,
            "imports": [],
            "error_tokens": ["tabs are not allowed"],
        },
        {
            "id": "unterminated-comment",
            "relative_path": "controls/13-unterminated-comment.lean",
            "source": "/- never closed\n",
            "fast_state": "error",
            "full_state": "diagnostic",
            "comparison": "expected-both-reject",
            "is_module": None,
            "imports": [],
            "error_tokens": ["unterminated comment"],
        },
        {
            "id": "missing-input",
            "relative_path": "controls/14-intentionally-missing.lean",
            "source": None,
            "fast_state": "error",
            "full_state": "error",
            "comparison": "expected-both-read-error",
            "is_module": None,
            "imports": [],
            "error_tokens": ["No such file"],
        },
    )


def build_corpus_rows(m1: dict[str, Any]) -> list[dict[str, Any]]:
    source_rows = [row for row in m1["file_rows"] if row["media_class"] == "lean"]
    rows = []
    for ordinal, source in enumerate(source_rows):
        rows.append(
            seal(
                {
                    "ordinal": ordinal,
                    "path": source["path"],
                    "mode": source["mode"],
                    "git_blob": source["git_blob"],
                    "bytes": source["bytes"],
                    "sha256": source["sha256"],
                    "m1_file_record_sha256": source["record_sha256"],
                    "m1_signal_hits_sha256": source["signal_hits_sha256"],
                },
                CORPUS_DOMAIN,
            )
        )
    return rows


def build_batches(corpus_rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    batches = []
    for batch_ordinal, start in enumerate(range(0, len(corpus_rows), BATCH_SIZE)):
        batch_rows = corpus_rows[start : start + BATCH_SIZE]
        batches.append(
            seal(
                {
                    "batch_ordinal": batch_ordinal,
                    "batch_id": f"corpus-{batch_ordinal + 1:04d}",
                    "start_ordinal": start,
                    "stop_ordinal_exclusive": start + len(batch_rows),
                    "input_count": len(batch_rows),
                    "input_bytes": sum(row["bytes"] for row in batch_rows),
                    "first_path": batch_rows[0]["path"],
                    "last_path": batch_rows[-1]["path"],
                    "input_rows_sha256": domain_digest(
                        "axeyum-lean-u2-native-header-batch-inputs-m2.1-v1",
                        [row["record_sha256"] for row in batch_rows],
                    ),
                    "stdin_sha256": sha256_bytes(
                        ("\n".join(row["path"] for row in batch_rows) + "\n").encode(
                            "utf-8"
                        )
                    ),
                },
                BATCH_DOMAIN,
            )
        )
    return batches


def build_controls() -> list[dict[str, Any]]:
    rows = []
    for ordinal, spec in enumerate(control_specs()):
        source = spec["source"]
        row = copy.deepcopy(spec)
        row["ordinal"] = ordinal
        row["exists"] = source is not None
        row["bytes"] = None if source is None else len(source.encode("utf-8"))
        row["sha256"] = None if source is None else sha256_bytes(source.encode("utf-8"))
        rows.append(seal(row, CONTROL_DOMAIN))
    return rows


def build_contract() -> dict[str, Any]:
    m1, m20 = validated_parents()
    corpus_rows = build_corpus_rows(m1)
    batches = build_batches(corpus_rows)
    controls = build_controls()
    mode_counts: dict[str, int] = {}
    for row in corpus_rows:
        mode_counts[row["mode"]] = mode_counts.get(row["mode"], 0) + 1
    contract: dict[str, Any] = {
        "schema": SCHEMA,
        "as_of": AS_OF,
        "status": "preregistered-no-m2.1-corpus-or-control-process",
        "scope": "full-u2-tracked-lean-header-input-and-control-contract",
        "target": TARGET,
        "policy": {
            "source_first": True,
            "implementation_push_required_before_process": True,
            "user_authorization_required": True,
            "external_processes_observed": 0,
            "attempt_process_budget": PROCESS_COUNT,
            "parser_process_budget": 35,
            "preflight_process_budget": 4,
            "retry_budget": 0,
            "parallel_processes": 1,
            "batch_size": BATCH_SIZE,
            "fast_parser_edge_assurance": "declared-static",
            "declared_module_resolution_state": "declared-only",
            "official_provider_state": "unbound",
            "canonical_json": "UTF-8; sorted keys; compact separators; no NaN/infinity",
            "digest_construction": "ASCII domain + NUL + canonical JSON bytes",
        },
        "source_authorities": [
            {"path": path, "physical_sha256": digest}
            for path, digest in SOURCE_HASHES.items()
        ],
        "parent_logical_seals": {
            "m1_record_sha256": m1["record_sha256"],
            "m1_file_rows_sha256": m1["file_rows_sha256"],
            "m20_record_sha256": m20["record_sha256"],
            "m20_case_rows_sha256": m20["case_rows_sha256"],
            "m20_provider_variants_sha256": m20["provider_variants_sha256"],
        },
        "pinned_parser_sources": list(PINNED_PARSER_SOURCES),
        "provider_floor": {
            "lean_binary_path": str(LEAN_BIN),
            "lean_binary_bytes": 9024,
            "lean_binary_mode": "0755",
            "lean_binary_sha256": (
                "3e0d0d3d801675359f2d4cf9815bfdb417b20b92fdd9d48b3b14c95bbae28bbf"
            ),
            "source_root": str(SOURCE_ROOT),
            "source_commit": TARGET["lean_commit"],
            "platform": {"os": "Linux", "arch": "x86_64", "glibc": "2.43"},
            "toolchain_libraries": [
                {
                    "name": "libInit_shared.so",
                    "bytes": 6232,
                    "sha256": "6ce912e300ad305bb38a362404544602e2229d072b78d75b1dd71c637e453c2c",
                },
                {
                    "name": "libleanshared.so",
                    "bytes": 144109624,
                    "sha256": "86c5222603b164cd1c0dee1aeea9624a1ece9ce724ee2ed36e427a4259f8834b",
                },
                {
                    "name": "libleanshared_1.so",
                    "bytes": 6232,
                    "sha256": "6ce912e300ad305bb38a362404544602e2229d072b78d75b1dd71c637e453c2c",
                },
                {
                    "name": "libleanshared_2.so",
                    "bytes": 6232,
                    "sha256": "6ce912e300ad305bb38a362404544602e2229d072b78d75b1dd71c637e453c2c",
                },
            ],
            "git": {
                "path": "/usr/bin/git",
                "bytes": 4547768,
                "sha256": "5516c9f362c29376ab9a499a33082f9f611941d8c75930c880e30ad109e39c9a",
            },
            "readelf": {
                "path": "/usr/bin/readelf",
                "realpath": "/usr/bin/x86_64-linux-gnu-readelf",
                "bytes": 818312,
                "sha256": "c857339616bbbfa5eba32733e22365048903fbaf6ed2126b897dd138bcb741fc",
            },
        },
        "evidence_root": str(EVIDENCE_ROOT.relative_to(ROOT)),
        "corpus_rows_sha256": domain_digest(
            "axeyum-lean-u2-native-header-corpus-rows-m2.1-v1", corpus_rows
        ),
        "corpus_rows": corpus_rows,
        "batches_sha256": domain_digest(
            "axeyum-lean-u2-native-header-batches-m2.1-v1", batches
        ),
        "batches": batches,
        "controls_sha256": domain_digest(
            "axeyum-lean-u2-native-header-controls-m2.1-v1", controls
        ),
        "controls": controls,
        "summary": {
            "case_rows": CASE_ROWS,
            "corpus_rows": len(corpus_rows),
            "corpus_bytes": sum(row["bytes"] for row in corpus_rows),
            "mode_counts": dict(sorted(mode_counts.items())),
            "max_path_utf8_bytes": max(
                len(row["path"].encode("utf-8")) for row in corpus_rows
            ),
            "newline_or_cr_paths": sum(
                "\n" in row["path"] or "\r" in row["path"] for row in corpus_rows
            ),
            "first_path": corpus_rows[0]["path"],
            "last_path": corpus_rows[-1]["path"],
            "batches": len(batches),
            "full_batches": sum(row["input_count"] == BATCH_SIZE for row in batches),
            "final_batch_rows": batches[-1]["input_count"],
            "controls": len(controls),
            "planned_processes": PROCESS_COUNT,
            "observed_processes": 0,
            "declared_header_edges": 0,
            "resolved_nodes": 0,
            "resolved_edges": 0,
            "native_outcomes": 0,
            "paired_cells": 0,
        },
        "claims": {
            "input_population_frozen": True,
            "batch_partition_frozen": True,
            "control_matrix_frozen": True,
            "provider_identity_observed": False,
            "fast_parser_observed": False,
            "full_parser_observed": False,
            "header_declarations_complete": False,
            "source_or_artifact_resolution_complete": False,
            "native_support_observed": False,
            "tl0_6_4_complete": False,
            "lean_parity_established": False,
        },
        "credits": ZERO_CREDITS,
        "residual": [
            "Commit, test, push, and ref-equal the process/evidence implementation.",
            "Obtain explicit user authorization for the one-shot 39-process attempt.",
            "Retain and compare all 4,092 fast/full parser rows and exact controls.",
            "Keep all M2.2-M2.7 source/artifact/runtime/native closure not run.",
        ],
        "record_sha256": "",
    }
    contract["record_sha256"] = domain_digest(
        SCHEMA, {key: value for key, value in contract.items() if key != "record_sha256"}
    )
    return contract


def validate_record_seals(rows: Any, domain: str, label: str) -> list[str]:
    failures: list[str] = []
    if not isinstance(rows, list):
        return [f"{label} must be a list"]
    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            failures.append(f"{label} {index} must be an object")
            continue
        expected = domain_digest(
            domain, {key: value for key, value in row.items() if key != "record_sha256"}
        )
        if row.get("record_sha256") != expected:
            failures.append(f"{label} {index} record seal drift")
    return failures


def validate_contract(data: dict[str, Any]) -> list[str]:
    failures: list[str] = []
    try:
        expected = build_contract()
    except HeaderContractError as error:
        return [str(error)]
    fixed = (
        "schema",
        "as_of",
        "status",
        "scope",
        "target",
        "policy",
        "source_authorities",
        "parent_logical_seals",
        "pinned_parser_sources",
        "provider_floor",
        "evidence_root",
        "summary",
        "claims",
        "credits",
        "residual",
    )
    for field in fixed:
        if data.get(field) != expected[field]:
            failures.append(f"{field} drift")
    list_fields = (
        (
            "corpus_rows",
            CORPUS_DOMAIN,
            "axeyum-lean-u2-native-header-corpus-rows-m2.1-v1",
        ),
        ("batches", BATCH_DOMAIN, "axeyum-lean-u2-native-header-batches-m2.1-v1"),
        (
            "controls",
            CONTROL_DOMAIN,
            "axeyum-lean-u2-native-header-controls-m2.1-v1",
        ),
    )
    for field, row_domain, list_domain in list_fields:
        rows = data.get(field)
        failures.extend(validate_record_seals(rows, row_domain, field))
        if rows != expected[field]:
            failures.append(f"{field} semantic or order drift")
        if data.get(f"{field}_sha256") != domain_digest(list_domain, rows):
            failures.append(f"{field} list seal drift")
    if data.get("record_sha256") != domain_digest(
        SCHEMA, {key: value for key, value in data.items() if key != "record_sha256"}
    ):
        failures.append("top-level record seal drift")
    return failures


def summarize(data: dict[str, Any]) -> dict[str, Any]:
    return {
        "schema": REPORT_SCHEMA,
        "as_of": data["as_of"],
        "target": data["target"],
        "verdict": (
            "M2.1 input, batch, provider-floor, and control contract frozen; "
            "no header parser process or dependency edge observed"
        ),
        "summary": data["summary"],
        "claims": data["claims"],
        "credits": data["credits"],
        "residual": data["residual"],
        "authority_record_sha256": data["record_sha256"],
    }


def render_markdown(report: dict[str, Any]) -> str:
    summary = report["summary"]
    lines = [
        "# Generated Lean U2 M2.1 header contract",
        "",
        "> Generated by `scripts/lean_u2_native_dependency_m2_1.py`; do not edit by hand.",
        "",
        f"- Verdict: **{report['verdict']}**.",
        f"- Frozen corpus: **{summary['corpus_rows']:,} files / {summary['corpus_bytes']:,} bytes**.",
        f"- Fast-parser batches: **{summary['batches']}** at a maximum of 128 files.",
        f"- Frozen controls: **{summary['controls']}**.",
        f"- Planned / observed processes: **{summary['planned_processes']} / {summary['observed_processes']}**.",
        f"- Declared header edges / resolved nodes / resolved edges: **{summary['declared_header_edges']} / {summary['resolved_nodes']} / {summary['resolved_edges']}**.",
        f"- Native outcomes / paired cells / parity credit: **{summary['native_outcomes']} / {summary['paired_cells']} / {report['credits']['parity_credit']}**.",
        "",
        "## Boundary",
        "",
        "The exact ordered inputs, batches, control bytes, process budget, provider floor, and zero-credit schema are preregistered. No corpus or control file has been passed to Lean under M2.1 and no dependency declaration has been observed.",
        "",
        "## Required continuation",
        "",
    ]
    lines.extend(f"- {item}" for item in report["residual"])
    return "\n".join(lines) + "\n"


def write_contract(contract: dict[str, Any]) -> None:
    CONTRACT.write_text(json_text(contract), encoding="utf-8")
    report = summarize(contract)
    OUT_JSON.write_text(json_text(report), encoding="utf-8")
    OUT_MD.write_text(render_markdown(report), encoding="utf-8")


def check_contract() -> None:
    if not CONTRACT.is_file():
        raise HeaderContractError(
            f"missing committed contract: {CONTRACT.relative_to(ROOT)}"
        )
    data = load_json(CONTRACT)
    failures = validate_contract(data)
    if failures:
        raise HeaderContractError("invalid M2.1 contract: " + "; ".join(failures))
    report = summarize(data)
    if not OUT_JSON.is_file() or OUT_JSON.read_text(encoding="utf-8") != json_text(
        report
    ):
        raise HeaderContractError(f"stale generated report: {OUT_JSON.relative_to(ROOT)}")
    if not OUT_MD.is_file() or OUT_MD.read_text(encoding="utf-8") != render_markdown(
        report
    ):
        raise HeaderContractError(f"stale generated report: {OUT_MD.relative_to(ROOT)}")
    print(
        "LEAN_U2_NATIVE_HEADER_CONTRACT|"
        f"files={data['summary']['corpus_rows']}|"
        f"batches={data['summary']['batches']}|"
        f"controls={data['summary']['controls']}|"
        f"planned_processes={data['summary']['planned_processes']}|"
        "observed_processes=0|header_edges=0|resolved=0|native=0|paired=0|parity=0"
    )


def load_valid_contract() -> dict[str, Any]:
    if not CONTRACT.is_file() or sha256_file(CONTRACT) != CONTRACT_PHYSICAL_SHA256:
        raise HeaderContractError("committed M2.1 contract physical identity drift")
    data = load_json(CONTRACT)
    failures = validate_contract(data)
    if failures:
        raise HeaderContractError("invalid committed M2.1 contract: " + "; ".join(failures))
    if data.get("record_sha256") != CONTRACT_RECORD_SHA256:
        raise HeaderContractError("committed M2.1 contract logical identity drift")
    return data


def process_limits(*, full_corpus: bool = False) -> dict[str, int]:
    return {
        "address_space_bytes": 4 * 1024**3,
        "cpu_seconds": 60,
        "wall_seconds": 300 if full_corpus else 120,
        "stdout_bytes": 64 * 1024**2 if full_corpus else 16 * 1024**2,
        "stderr_bytes": 2 * 1024**2,
        "file_size_bytes": 256 * 1024**2,
    }


def process_environment() -> dict[str, str]:
    return {"LANG": "C", "LC_ALL": "C"}


def lines_bytes(values: list[str]) -> bytes:
    return ("\n".join(values) + "\n").encode("utf-8")


def build_process_specs(contract: dict[str, Any]) -> list[dict[str, Any]]:
    specs: list[dict[str, Any]] = []

    def add(
        process_id: str,
        category: str,
        argv: list[str],
        stdin: bytes = b"",
        *,
        full_corpus: bool = False,
    ) -> None:
        specs.append(
            {
                "ordinal": len(specs),
                "process_id": process_id,
                "category": category,
                "argv": argv,
                "cwd": str(SOURCE_ROOT),
                "environment": process_environment(),
                "stdin_bytes": len(stdin),
                "stdin_sha256": sha256_bytes(stdin),
                "stdin": stdin,
                "limits": process_limits(full_corpus=full_corpus),
            }
        )

    add(
        "preflight-git-head",
        "preflight",
        ["/usr/bin/git", "rev-parse", "HEAD"],
    )
    add(
        "preflight-git-clean",
        "preflight",
        ["/usr/bin/git", "status", "--porcelain=v1", "--untracked-files=all"],
    )
    add(
        "preflight-lean-elf",
        "preflight",
        ["/usr/bin/readelf", "-d", str(LEAN_BIN)],
    )
    add("preflight-lean-version", "preflight", [str(LEAN_BIN), "--version"])

    corpus = contract["corpus_rows"]
    for batch in contract["batches"]:
        rows = corpus[batch["start_ordinal"] : batch["stop_ordinal_exclusive"]]
        stdin = lines_bytes([row["path"] for row in rows])
        if sha256_bytes(stdin) != batch["stdin_sha256"]:
            raise HeaderContractError(f"batch stdin drift: {batch['batch_id']}")
        add(
            f"fast-{batch['batch_id']}",
            "fast-corpus",
            [str(LEAN_BIN), "-j1", "--deps-json", "--stdin"],
            stdin,
        )

    control_paths = [
        str(EVIDENCE_ROOT / row["relative_path"]) for row in contract["controls"]
    ]
    add(
        "fast-controls",
        "fast-controls",
        [str(LEAN_BIN), "-j1", "--deps-json", "--stdin"],
        lines_bytes(control_paths),
    )
    add(
        "full-corpus",
        "full-corpus",
        [str(LEAN_BIN), "-j1", "--run", str(HELPER_PATH)],
        lines_bytes([row["path"] for row in corpus]),
        full_corpus=True,
    )
    add(
        "full-controls",
        "full-controls",
        [str(LEAN_BIN), "-j1", "--run", str(HELPER_PATH)],
        lines_bytes(control_paths),
    )
    if len(specs) != PROCESS_COUNT:
        raise HeaderContractError(
            f"process closure drift: expected {PROCESS_COUNT}, got {len(specs)}"
        )
    return specs


def public_process_spec(spec: dict[str, Any]) -> dict[str, Any]:
    return {key: value for key, value in spec.items() if key != "stdin"}


def authorization_payload(contract: dict[str, Any]) -> dict[str, Any]:
    specs = build_process_specs(contract)
    return {
        "contract_physical_sha256": CONTRACT_PHYSICAL_SHA256,
        "contract_record_sha256": CONTRACT_RECORD_SHA256,
        "runner_sha256": sha256_file(RUNNER_PATH),
        "helper_sha256": sha256_file(HELPER_PATH),
        "source_root": str(SOURCE_ROOT),
        "evidence_root": str(EVIDENCE_ROOT),
        "process_specs_sha256": domain_digest(
            "axeyum-lean-u2-native-header-process-specs-m2.1-v1",
            [public_process_spec(spec) for spec in specs],
        ),
        "process_count": len(specs),
        "retry_budget": 0,
    }


def authorization_digest(contract: dict[str, Any]) -> str:
    return domain_digest(AUTHORIZATION_DOMAIN, authorization_payload(contract))


def verify_file_identity(
    path: Path, *, bytes_expected: int, sha256_expected: str, mode_expected: int | None = None
) -> None:
    if not path.is_file() or path.is_symlink():
        raise HeaderContractError(f"provider file missing or not regular: {path}")
    metadata = path.stat()
    if metadata.st_size != bytes_expected or sha256_file(path) != sha256_expected:
        raise HeaderContractError(f"provider file physical identity drift: {path}")
    if mode_expected is not None and stat.S_IMODE(metadata.st_mode) != mode_expected:
        raise HeaderContractError(f"provider file mode drift: {path}")


def verify_provider_files(contract: dict[str, Any]) -> None:
    floor = contract["provider_floor"]
    verify_file_identity(
        LEAN_BIN,
        bytes_expected=floor["lean_binary_bytes"],
        sha256_expected=floor["lean_binary_sha256"],
        mode_expected=int(floor["lean_binary_mode"], 8),
    )
    verify_file_identity(
        Path(floor["git"]["path"]),
        bytes_expected=floor["git"]["bytes"],
        sha256_expected=floor["git"]["sha256"],
    )
    readelf = Path(floor["readelf"]["path"])
    if str(readelf.resolve()) != floor["readelf"]["realpath"]:
        raise HeaderContractError("readelf realpath drift")
    verify_file_identity(
        readelf.resolve(),
        bytes_expected=floor["readelf"]["bytes"],
        sha256_expected=floor["readelf"]["sha256"],
    )
    lib_root = LEAN_BIN.parent.parent / "lib/lean"
    for library in floor["toolchain_libraries"]:
        verify_file_identity(
            lib_root / library["name"],
            bytes_expected=library["bytes"],
            sha256_expected=library["sha256"],
        )
    if not SOURCE_ROOT.is_dir() or SOURCE_ROOT.is_symlink():
        raise HeaderContractError("pinned source root missing or symlinked")
    uname = os.uname()
    libc_name, libc_version = platform.libc_ver()
    expected_platform = floor["platform"]
    if (
        uname.sysname != expected_platform["os"]
        or uname.machine != expected_platform["arch"]
        or libc_name != "glibc"
        or libc_version != expected_platform["glibc"]
    ):
        raise HeaderContractError(
            "provider platform drift: "
            f"{uname.sysname}/{uname.machine}/{libc_name}/{libc_version}"
        )


def render_run_command() -> None:
    contract = load_valid_contract()
    verify_provider_files(contract)
    digest = authorization_digest(contract)
    print(
        "LEAN_U2_NATIVE_HEADER_RUN|"
        f"authorization={digest}|processes={PROCESS_COUNT}|files={CORPUS_ROWS}|"
        f"evidence_root={EVIDENCE_ROOT.relative_to(ROOT)}"
    )
    print(
        "python3 scripts/lean_u2_native_dependency_m2_1.py run "
        f"--authorization {digest}"
    )


def materialize_controls(contract: dict[str, Any]) -> None:
    for row in contract["controls"]:
        path = EVIDENCE_ROOT / row["relative_path"]
        if row["source"] is None:
            if path.exists() or path.is_symlink():
                raise HeaderContractError(f"missing control unexpectedly exists: {path}")
            continue
        path.parent.mkdir(parents=True, exist_ok=True)
        data = row["source"].encode("utf-8")
        if len(data) != row["bytes"] or sha256_bytes(data) != row["sha256"]:
            raise HeaderContractError(f"control bytes drift before materialization: {row['id']}")
        path.write_bytes(data)


def set_child_limits(limits: dict[str, int]) -> None:
    resource.setrlimit(
        resource.RLIMIT_AS,
        (limits["address_space_bytes"], limits["address_space_bytes"]),
    )
    resource.setrlimit(
        resource.RLIMIT_CPU, (limits["cpu_seconds"], limits["cpu_seconds"])
    )
    resource.setrlimit(
        resource.RLIMIT_FSIZE,
        (limits["file_size_bytes"], limits["file_size_bytes"]),
    )


def process_directory(spec: dict[str, Any]) -> Path:
    return EVIDENCE_ROOT / PROCESS_DIR / f"{spec['ordinal']:04d}-{spec['process_id']}"


def run_process(spec: dict[str, Any]) -> dict[str, Any]:
    directory = process_directory(spec)
    directory.mkdir(parents=True, exist_ok=False)
    stdin_path = directory / "stdin.bin"
    stdout_path = directory / "stdout.bin"
    stderr_path = directory / "stderr.bin"
    record_path = directory / "record.json"
    stdin_path.write_bytes(spec["stdin"])
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    start_ns = time.time_ns()
    start_monotonic_ns = time.monotonic_ns()
    process: subprocess.Popen[bytes] | None = None
    limit_fired: str | None = None
    launch_error: BaseException | None = None
    with (
        stdin_path.open("rb") as stdin_handle,
        stdout_path.open("xb") as stdout_handle,
        stderr_path.open("xb") as stderr_handle,
    ):
        try:
            process = subprocess.Popen(
                spec["argv"],
                cwd=spec["cwd"],
                env=spec["environment"],
                stdin=stdin_handle,
                stdout=stdout_handle,
                stderr=stderr_handle,
                start_new_session=True,
                preexec_fn=lambda: set_child_limits(spec["limits"]),
            )
        except (OSError, subprocess.SubprocessError) as error:
            launch_error = error
        if process is not None:
            wall_limit_ns = spec["limits"]["wall_seconds"] * 1_000_000_000
            while True:
                returncode = process.poll()
                elapsed_ns = time.monotonic_ns() - start_monotonic_ns
                stdout_bytes = stdout_path.stat().st_size
                stderr_bytes = stderr_path.stat().st_size
                if elapsed_ns > wall_limit_ns:
                    limit_fired = "wall"
                elif stdout_bytes > spec["limits"]["stdout_bytes"]:
                    limit_fired = "stdout"
                elif stderr_bytes > spec["limits"]["stderr_bytes"]:
                    limit_fired = "stderr"
                if limit_fired is not None:
                    if returncode is None:
                        try:
                            os.killpg(process.pid, signal.SIGKILL)
                        except ProcessLookupError:
                            pass
                    process.wait()
                    break
                if returncode is not None:
                    break
                time.sleep(0.005)

    end_ns = time.time_ns()
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    stdout_bytes = stdout_path.stat().st_size
    stderr_bytes = stderr_path.stat().st_size
    if limit_fired is None and stdout_bytes > spec["limits"]["stdout_bytes"]:
        limit_fired = "stdout"
    if limit_fired is None and stderr_bytes > spec["limits"]["stderr_bytes"]:
        limit_fired = "stderr"
    wall_limit_fired = limit_fired == "wall"
    stdout_limit_fired = limit_fired == "stdout"
    stderr_limit_fired = limit_fired == "stderr"
    output_within_limits = (
        stdout_bytes <= spec["limits"]["stdout_bytes"]
        and stderr_bytes <= spec["limits"]["stderr_bytes"]
    )
    returncode = process.returncode if process is not None else None
    if launch_error is not None:
        status = "failed-launch"
    elif wall_limit_fired:
        status = "failed-wall-limit"
    elif stdout_limit_fired:
        status = "failed-stdout-limit"
    elif stderr_limit_fired:
        status = "failed-stderr-limit"
    elif returncode == 0:
        status = "complete"
    else:
        status = "failed-exit"
    record = seal(
        {
            **public_process_spec(spec),
            "status": status,
            "started_unix_ns": start_ns,
            "ended_unix_ns": end_ns,
            "wall_duration_ns": end_ns - start_ns,
            "timed_out": wall_limit_fired,
            "wall_limit_fired": wall_limit_fired,
            "stdout_limit_fired": stdout_limit_fired,
            "stderr_limit_fired": stderr_limit_fired,
            "returncode": returncode,
            "launch_error_type": (
                type(launch_error).__name__ if launch_error is not None else None
            ),
            "launch_error_message": (
                str(launch_error) if launch_error is not None else None
            ),
            "stdout_bytes": stdout_bytes,
            "stdout_sha256": sha256_file(stdout_path),
            "stderr_bytes": stderr_bytes,
            "stderr_sha256": sha256_file(stderr_path),
            "output_within_limits": output_within_limits,
            "user_cpu_seconds": after.ru_utime - before.ru_utime,
            "system_cpu_seconds": after.ru_stime - before.ru_stime,
            "max_rss_kib_children_cumulative": after.ru_maxrss,
            "files": {
                "stdin": str(stdin_path.relative_to(EVIDENCE_ROOT)),
                "stdout": str(stdout_path.relative_to(EVIDENCE_ROOT)),
                "stderr": str(stderr_path.relative_to(EVIDENCE_ROOT)),
            },
        },
        PROCESS_DOMAIN,
    )
    record_path.write_text(json_text(record), encoding="utf-8")
    if status != "complete":
        raise HeaderContractError(
            f"process {spec['process_id']} stopped without retry: "
            f"status={status} returncode={returncode}"
        )
    return record


def inventory(root: Path, *, exclude_completion: bool) -> list[dict[str, Any]]:
    rows = []
    for path in sorted((item for item in root.rglob("*") if item.is_file())):
        relative = str(path.relative_to(root))
        if exclude_completion and relative == "completion.json":
            continue
        rows.append(
            {
                "path": relative,
                "bytes": path.stat().st_size,
                "sha256": sha256_file(path),
            }
        )
    return rows


def write_completion(
    contract: dict[str, Any], authorization: str, records: list[dict[str, Any]]
) -> None:
    rows = inventory(EVIDENCE_ROOT, exclude_completion=True)
    completion = seal(
        {
            "schema": "axeyum-lean-u2-native-header-completion-m2.1-v1",
            "contract_record_sha256": contract["record_sha256"],
            "authorization": authorization,
            "process_count": len(records),
            "process_record_sha256s": [row["record_sha256"] for row in records],
            "inventory_count": len(rows),
            "inventory_sha256": domain_digest(
                "axeyum-lean-u2-native-header-evidence-inventory-m2.1-v1", rows
            ),
            "inventory": rows,
            "state": "complete-unvalidated-parser-evidence",
            "credit": 0,
        },
        COMPLETION_DOMAIN,
    )
    (EVIDENCE_ROOT / "completion.json").write_text(
        json_text(completion), encoding="utf-8"
    )


def run_attempt(authorization: str) -> None:
    contract = load_valid_contract()
    verify_provider_files(contract)
    expected = authorization_digest(contract)
    if authorization != expected:
        raise HeaderContractError(
            f"authorization digest mismatch: expected {expected}, got {authorization}"
        )
    if EVIDENCE_ROOT.exists() or EVIDENCE_ROOT.is_symlink():
        raise HeaderContractError(f"evidence root already exists: {EVIDENCE_ROOT}")
    EVIDENCE_ROOT.mkdir(parents=True)
    materialize_controls(contract)
    (EVIDENCE_ROOT / PROCESS_DIR).mkdir()
    (EVIDENCE_ROOT / "authorization.json").write_text(
        json_text(
            {
                "authorization": authorization,
                "payload": authorization_payload(contract),
            }
        ),
        encoding="utf-8",
    )
    records = []
    for spec in build_process_specs(contract):
        records.append(run_process(spec))
    write_completion(contract, authorization, records)
    print(
        f"lean-u2-native-header: completed {len(records)} process records; "
        "parser normalization and authority promotion remain unrun"
    )


def load_process_record(path: Path) -> dict[str, Any]:
    data = load_json(path)
    expected = domain_digest(
        PROCESS_DOMAIN,
        {key: value for key, value in data.items() if key != "record_sha256"},
    )
    if data.get("record_sha256") != expected:
        raise HeaderContractError(f"process record seal drift: {path}")
    return data


def parse_json_output(data: bytes, label: str) -> dict[str, Any]:
    try:
        value = json.loads(data)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise HeaderContractError(f"invalid UTF-8 JSON from {label}: {error}") from error
    if not isinstance(value, dict):
        raise HeaderContractError(f"non-object JSON from {label}")
    return value


def normalize_import(value: Any, label: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise HeaderContractError(f"non-object import row in {label}")
    expected_keys = {"module", "importAll", "isExported", "isMeta"}
    if set(value) != expected_keys:
        raise HeaderContractError(f"import schema drift in {label}: {sorted(value)}")
    if not isinstance(value["module"], str) or not all(
        isinstance(value[key], bool) for key in expected_keys - {"module"}
    ):
        raise HeaderContractError(f"import value type drift in {label}")
    return {
        "module": value["module"],
        "import_all": value["importAll"],
        "is_exported": value["isExported"],
        "is_meta": value["isMeta"],
    }


def optional_result(row: dict[str, Any]) -> Any:
    if "result" in row:
        return row["result"]
    return row.get("result?")


def normalize_fast_output(data: bytes, expected_count: int, label: str) -> list[dict[str, Any]]:
    value = parse_json_output(data, label)
    rows = value.get("imports")
    if not isinstance(rows, list) or len(rows) != expected_count:
        raise HeaderContractError(
            f"fast row-count drift in {label}: expected {expected_count}, "
            f"got {None if not isinstance(rows, list) else len(rows)}"
        )
    normalized = []
    for index, row in enumerate(rows):
        row_label = f"{label}[{index}]"
        if not isinstance(row, dict) or not isinstance(row.get("errors"), list):
            raise HeaderContractError(f"fast result schema drift in {row_label}")
        errors = row["errors"]
        if not all(isinstance(error, str) for error in errors):
            raise HeaderContractError(f"fast error type drift in {row_label}")
        result = optional_result(row)
        if result is None:
            if not errors:
                raise HeaderContractError(f"fast row has neither result nor error: {row_label}")
            normalized.append({"state": "error", "errors": errors, "result": None})
            continue
        if errors or not isinstance(result, dict):
            raise HeaderContractError(f"fast row mixes result/error in {row_label}")
        imports = result.get("imports")
        if not isinstance(imports, list) or not isinstance(result.get("isModule"), bool):
            raise HeaderContractError(f"fast module-header schema drift in {row_label}")
        normalized.append(
            {
                "state": "success",
                "errors": [],
                "result": {
                    "imports": [normalize_import(item, row_label) for item in imports],
                    "is_module": result["isModule"],
                },
            }
        )
    return normalized


def normalize_full_output(data: bytes, expected_count: int, label: str) -> list[dict[str, Any]]:
    value = parse_json_output(data, label)
    rows = value.get("rows")
    if not isinstance(rows, list) or len(rows) != expected_count:
        raise HeaderContractError(
            f"full row-count drift in {label}: expected {expected_count}, "
            f"got {None if not isinstance(rows, list) else len(rows)}"
        )
    normalized = []
    for index, row in enumerate(rows):
        row_label = f"{label}[{index}]"
        if not isinstance(row, dict) or not isinstance(row.get("errors"), list):
            raise HeaderContractError(f"full result schema drift in {row_label}")
        errors = row["errors"]
        if not all(isinstance(error, str) for error in errors):
            raise HeaderContractError(f"full error type drift in {row_label}")
        result = optional_result(row)
        if result is None:
            if not errors:
                raise HeaderContractError(f"full row has neither result nor error: {row_label}")
            normalized.append({"state": "error", "errors": errors, "result": None})
            continue
        if errors or not isinstance(result, dict):
            raise HeaderContractError(f"full row mixes result/error in {row_label}")
        imports = result.get("imports")
        messages = result.get("messages")
        if (
            not isinstance(imports, list)
            or not isinstance(messages, list)
            or not all(isinstance(message, str) for message in messages)
            or not isinstance(result.get("isModule"), bool)
            or not isinstance(result.get("terminalLine"), int)
            or not isinstance(result.get("terminalColumn"), int)
        ):
            raise HeaderContractError(f"full module-header schema drift in {row_label}")
        normalized.append(
            {
                "state": "diagnostic" if messages else "success",
                "errors": [],
                "result": {
                    "imports": [normalize_import(item, row_label) for item in imports],
                    "is_module": result["isModule"],
                    "terminal_line": result["terminalLine"],
                    "terminal_column": result["terminalColumn"],
                    "messages": messages,
                },
            }
        )
    return normalized


def compare_parser_row(fast: dict[str, Any], full: dict[str, Any]) -> str:
    if fast["state"] == "success" and full["state"] in ("success", "diagnostic"):
        fast_result = fast["result"]
        full_result = full["result"]
        if (
            fast_result["imports"] == full_result["imports"]
            and fast_result["is_module"] == full_result["is_module"]
        ):
            return "equal" if full["state"] == "success" else "equal-with-full-diagnostic"
        return "import-or-module-mismatch"
    if fast["state"] == "error" and full["state"] == "error":
        return "paired-error"
    if fast["state"] == "error" and full["state"] == "diagnostic":
        return "fast-error-full-diagnostic"
    if fast["state"] == "error" and full["state"] == "success":
        return "fast-error-full-success"
    return "fast-success-full-error"


def validate_evidence() -> None:
    contract = load_valid_contract()
    verify_provider_files(contract)
    if not EVIDENCE_ROOT.is_dir():
        raise HeaderContractError(f"missing evidence root: {EVIDENCE_ROOT}")
    completion_path = EVIDENCE_ROOT / "completion.json"
    if not completion_path.is_file():
        raise HeaderContractError("attempt is incomplete: completion.json absent")
    completion = load_json(completion_path)
    expected_completion = domain_digest(
        COMPLETION_DOMAIN,
        {key: value for key, value in completion.items() if key != "record_sha256"},
    )
    if completion.get("record_sha256") != expected_completion:
        raise HeaderContractError("completion record seal drift")
    expected_auth = authorization_digest(contract)
    if completion.get("authorization") != expected_auth:
        raise HeaderContractError("completion authorization drift")
    specs = build_process_specs(contract)
    records = []
    for spec in specs:
        directory = process_directory(spec)
        record = load_process_record(directory / "record.json")
        if public_process_spec(spec) != {
            key: record[key] for key in public_process_spec(spec)
        }:
            raise HeaderContractError(f"process specification drift: {spec['process_id']}")
        for field in ("stdin", "stdout", "stderr"):
            path = EVIDENCE_ROOT / record["files"][field]
            if not path.is_file():
                raise HeaderContractError(
                    f"missing {field} evidence for {spec['process_id']}"
                )
            if path.stat().st_size != record[f"{field}_bytes"]:
                raise HeaderContractError(f"{field} byte count drift: {spec['process_id']}")
            if sha256_file(path) != record[f"{field}_sha256"]:
                raise HeaderContractError(f"{field} hash drift: {spec['process_id']}")
        if record["status"] != "complete" or record["returncode"] != 0:
            raise HeaderContractError(f"non-complete process: {spec['process_id']}")
        records.append(record)
    if records[0]["stdout_sha256"] != sha256_bytes(
        (TARGET["lean_commit"] + "\n").encode("ascii")
    ):
        raise HeaderContractError("preflight source HEAD output drift")
    if records[1]["stdout_bytes"] != 0:
        raise HeaderContractError("preflight source checkout is not clean")
    readelf_stdout = (
        EVIDENCE_ROOT / records[2]["files"]["stdout"]
    ).read_text(encoding="utf-8")
    for token in (
        "$ORIGIN/../lib:$ORIGIN/../lib/lean",
        "libInit_shared.so",
        "libleanshared.so",
        "libleanshared_1.so",
        "libleanshared_2.so",
    ):
        if token not in readelf_stdout:
            raise HeaderContractError(f"preflight ELF output missing {token}")
    version_stdout = (
        EVIDENCE_ROOT / records[3]["files"]["stdout"]
    ).read_text(encoding="utf-8")
    for token in ("version 4.30.0", TARGET["lean_commit"], "x86_64"):
        if token not in version_stdout:
            raise HeaderContractError(f"preflight version output missing {token}")
    if any(record["stderr_bytes"] != 0 for record in records):
        raise HeaderContractError("one or more retained processes wrote stderr")
    authorization_record = load_json(EVIDENCE_ROOT / "authorization.json")
    if authorization_record != {
        "authorization": expected_auth,
        "payload": authorization_payload(contract),
    }:
        raise HeaderContractError("authorization record drift")
    for control in contract["controls"]:
        path = EVIDENCE_ROOT / control["relative_path"]
        if control["source"] is None:
            if path.exists() or path.is_symlink():
                raise HeaderContractError(f"missing control exists: {control['id']}")
        elif (
            not path.is_file()
            or path.stat().st_size != control["bytes"]
            or sha256_file(path) != control["sha256"]
        ):
            raise HeaderContractError(f"control identity drift: {control['id']}")
    rows = inventory(EVIDENCE_ROOT, exclude_completion=True)
    if rows != completion.get("inventory"):
        raise HeaderContractError("post-completion evidence inventory drift")
    if completion.get("inventory_count") != len(rows):
        raise HeaderContractError("completion inventory count drift")
    if completion.get("inventory_sha256") != domain_digest(
        "axeyum-lean-u2-native-header-evidence-inventory-m2.1-v1", rows
    ):
        raise HeaderContractError("completion inventory seal drift")
    if completion.get("process_record_sha256s") != [
        row["record_sha256"] for row in records
    ]:
        raise HeaderContractError("completion process-record projection drift")
    print(
        f"LEAN_U2_NATIVE_HEADER_EVIDENCE|processes={len(records)}|"
        f"files={contract['summary']['corpus_rows']}|state=complete-unvalidated|credit=0"
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "command",
        choices=("contract", "check-contract", "render-run", "run", "check-evidence"),
    )
    parser.add_argument("--authorization")
    args = parser.parse_args()
    try:
        if args.command == "contract":
            contract = build_contract()
            write_contract(contract)
            print(
                f"lean-u2-native-header: froze {contract['summary']['corpus_rows']} "
                "inputs; no M2.1 process observed"
            )
        elif args.command == "check-contract":
            check_contract()
        elif args.command == "render-run":
            render_run_command()
        elif args.command == "run":
            if not args.authorization:
                raise HeaderContractError("run requires --authorization")
            run_attempt(args.authorization)
        else:
            validate_evidence()
    except HeaderContractError as error:
        print(f"lean-u2-native-header: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
