#!/usr/bin/env python3
"""Freeze and later execute TL0.6.4 M2.1 header-import evidence."""

from __future__ import annotations

import argparse
import copy
import functools
import hashlib
import importlib.util
import json
import sys
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


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("contract", "check-contract"))
    args = parser.parse_args()
    try:
        if args.command == "contract":
            contract = build_contract()
            write_contract(contract)
            print(
                f"lean-u2-native-header: froze {contract['summary']['corpus_rows']} "
                "inputs; no M2.1 process observed"
            )
        else:
            check_contract()
    except HeaderContractError as error:
        print(f"lean-u2-native-header: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
