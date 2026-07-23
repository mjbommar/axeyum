"""Process-free preparation helpers for the credited full-population run.

The helpers in this module can materialize and revalidate the exact admitted
execution list and can construct registered host argv.  They have no solver,
SSH, systemd, or allocation-launch path.
"""

from __future__ import annotations

import copy
from pathlib import Path
from typing import Any

from full_population import (
    FULL_LIST_SHA256,
    FULL_MANIFEST_SHA256,
    POPULATION_COUNT,
    SELECTED_FILES_SHA256,
    SHARD_COUNT,
    SOLVER_IDS,
    WALL_LIMIT_MS,
)
from resume_contract import ContractError, digest
from resume_fs import atomic_install_bytes, atomic_install_json, read_canonical_json
from resume_runner import official_selection_input_manifest, sha256_file


SELECTION_SCHEMA = "axeyum.smtcomp-credited-full-selection-preparation.v1"
ACCEPTED_COMPLETION_SHA256 = (
    "322adaa78396bf42d4660d12582e6db1cf2166a765bb912fdfb179975a9c9698"
)
SELECTION_FIELDS = {
    "schema",
    "fixture_only",
    "launch_authorized",
    "accepted_selection_root",
    "accepted_completion_sha256",
    "selected_files_sha256",
    "population_count",
    "physical_bytes",
    "full_list_path",
    "full_list_sha256",
    "full_manifest_path",
    "full_manifest_sha256",
    "record_sha256",
}
SOLVER_ENVIRONMENT = {
    "AYU_THREADS": "1",
    "OMP_NUM_THREADS": "1",
    "RAYON_NUM_THREADS": "1",
}


def _sealed(value: dict[str, Any]) -> dict[str, Any]:
    result = copy.deepcopy(value)
    result.pop("record_sha256", None)
    result["record_sha256"] = digest(result)
    return result


def _official_ids(accepted_root: Path) -> list[str]:
    try:
        rows = (accepted_root / "official-selected.txt").read_text(
            encoding="utf-8"
        ).splitlines()
    except (OSError, UnicodeDecodeError) as exc:
        raise ContractError("cannot read accepted full-population selection") from exc
    if not rows or rows != sorted(set(rows)):
        raise ContractError("accepted full-population selection is not strictly ordered")
    return rows


def materialize_full_selection(
    *,
    accepted_root: Path,
    corpus_root: Path,
    output_dir: Path,
    fixture_only: bool = False,
) -> dict[str, Any]:
    """Write and validate the full admitted list/manifest without launching work."""

    if type(fixture_only) is not bool:
        raise ContractError("fixture_only must be Boolean")
    accepted = accepted_root.resolve(strict=True)
    corpus = corpus_root.resolve(strict=True)
    output = output_dir.resolve(strict=True)
    benchmark_ids = _official_ids(accepted)
    paths = [corpus / benchmark_id for benchmark_id in benchmark_ids]
    list_path = output / "full-selected-absolute.txt"
    atomic_install_bytes(
        output,
        list_path.name,
        "".join(f"{path.resolve(strict=True)}\n" for path in paths).encode("utf-8"),
    )
    manifest_path = output / "full-selection-input-v2.json"
    manifest = official_selection_input_manifest(
        list_path, "non-incremental/", accepted
    )
    atomic_install_json(output, manifest_path.name, manifest)
    record = _sealed(
        {
            "schema": SELECTION_SCHEMA,
            "fixture_only": fixture_only,
            "launch_authorized": False,
            "accepted_selection_root": str(accepted),
            "accepted_completion_sha256": sha256_file(accepted / "complete.json"),
            "selected_files_sha256": sha256_file(accepted / "selected-files.jsonl"),
            "population_count": len(manifest["benchmarks"]),
            "physical_bytes": sum(row["input_bytes"] for row in manifest["benchmarks"]),
            "full_list_path": str(list_path.resolve(strict=True)),
            "full_list_sha256": sha256_file(list_path),
            "full_manifest_path": str(manifest_path.resolve(strict=True)),
            "full_manifest_sha256": sha256_file(manifest_path),
        }
    )
    return validate_full_selection(record)


def validate_full_selection(record: dict[str, Any]) -> dict[str, Any]:
    """Rehash the admitted source, selected payloads, list, and v2 manifest."""

    if set(record) != SELECTION_FIELDS or record.get("schema") != SELECTION_SCHEMA:
        raise ContractError("full selection preparation field/schema mismatch")
    if record.get("record_sha256") != _sealed(record)["record_sha256"]:
        raise ContractError("full selection preparation seal mismatch")
    if record.get("launch_authorized") is not False:
        raise ContractError("selection preparation cannot authorize launch")
    fixture_only = record.get("fixture_only")
    if type(fixture_only) is not bool:
        raise ContractError("selection preparation fixture flag mismatch")
    accepted = Path(record.get("accepted_selection_root", ""))
    list_path = Path(record.get("full_list_path", ""))
    manifest_path = Path(record.get("full_manifest_path", ""))
    for label, path in (
        ("accepted selection", accepted),
        ("full list", list_path),
        ("full manifest", manifest_path),
    ):
        if not path.is_absolute() or path.is_symlink() or not path.exists():
            raise ContractError(f"invalid {label} path")
    if not accepted.is_dir() or not list_path.is_file() or not manifest_path.is_file():
        raise ContractError("full selection preparation path type mismatch")
    expected_manifest = official_selection_input_manifest(
        list_path, "non-incremental/", accepted
    )
    if read_canonical_json(manifest_path) != expected_manifest:
        raise ContractError("full selection preparation manifest drift")
    observed = {
        "accepted_completion_sha256": sha256_file(accepted / "complete.json"),
        "selected_files_sha256": sha256_file(accepted / "selected-files.jsonl"),
        "population_count": len(expected_manifest["benchmarks"]),
        "physical_bytes": sum(
            row["input_bytes"] for row in expected_manifest["benchmarks"]
        ),
        "full_list_sha256": sha256_file(list_path),
        "full_manifest_sha256": sha256_file(manifest_path),
    }
    if any(record[field] != value for field, value in observed.items()):
        raise ContractError("full selection preparation artifact drift")
    if not fixture_only:
        frozen = {
            "accepted_completion_sha256": ACCEPTED_COMPLETION_SHA256,
            "selected_files_sha256": SELECTED_FILES_SHA256,
            "population_count": POPULATION_COUNT,
            "full_list_sha256": FULL_LIST_SHA256,
            "full_manifest_sha256": FULL_MANIFEST_SHA256,
        }
        if any(record[field] != value for field, value in frozen.items()):
            raise ContractError("live full selection differs from preregistration")
    return record


def full_host_argv(
    *,
    python_executable: Path,
    staged_source: Path,
    solver_id: str,
    solver_binary: Path,
    shard_ids: list[int],
    session_id: str,
    file_list: Path,
    run_manifest: Path,
    run_dir: Path,
    selection_manifest: Path,
    accepted_root: Path,
    corpus_manifest: Path,
    environment_manifest: Path,
    source_identity_manifest: Path,
    internal_timeout_ms: int | None = None,
    fixture_only: bool = False,
) -> list[str]:
    """Construct one exact, process-free host command for an allocation."""

    if solver_id not in SOLVER_IDS:
        raise ContractError("unknown full-population solver cell")
    if (
        not shard_ids
        or shard_ids != sorted(set(shard_ids))
        or any(type(shard) is not int or not 0 <= shard < SHARD_COUNT for shard in shard_ids)
    ):
        raise ContractError("invalid full-population host shard set")
    if not session_id or any(character.isspace() for character in session_id):
        raise ContractError("invalid full-population resource session")
    argv = [
        str(python_executable.resolve(strict=True)),
        "-B",
        str((staged_source / "compete.py").resolve(strict=True)),
        "--host-run",
        "--host-shards",
        ",".join(str(shard) for shard in shard_ids),
        "--host-session-id",
        session_id,
        "--file-list",
        str(file_list.resolve(strict=True)),
        "--solver",
        f"{solver_id}={solver_binary.resolve(strict=True)} {{bench}}",
        "--track",
        "single_query",
        "--wall-limit",
        str(WALL_LIMIT_MS // 1000),
        "--mem-gb",
        "8",
        "--cores",
        "1",
        "--run-manifest",
        str(run_manifest.resolve(strict=True)),
        "--run-dir",
        str(run_dir.resolve(strict=True)),
        "--selection-manifest",
        str(selection_manifest.resolve(strict=True)),
        "--official-selection-root",
        str(accepted_root.resolve(strict=True)),
        "--corpus-manifest",
        str(corpus_manifest.resolve(strict=True)),
        "--environment-manifest",
        str(environment_manifest.resolve(strict=True)),
        "--source-identity-manifest",
        str(source_identity_manifest.resolve(strict=True)),
    ]
    for key, value in SOLVER_ENVIRONMENT.items():
        argv.extend(["--solver-env", f"{key}={value}"])
    if internal_timeout_ms is not None:
        if solver_id != "axeyum" or internal_timeout_ms != 19_000:
            raise ContractError("invalid full-population internal timeout")
        argv.extend(["--internal-timeout-ms", str(internal_timeout_ms)])
    elif solver_id == "axeyum":
        raise ContractError("Axeyum full-population command requires its soft timeout")
    if fixture_only:
        argv.append("--allow-unadmitted-selection-fixture")
    argv.append("--quiet")
    return argv
