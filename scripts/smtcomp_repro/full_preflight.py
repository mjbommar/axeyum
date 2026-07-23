"""Host and incident-sentinel evidence for credited full preparation.

This module validates already-captured observations.  It has no SSH, solver,
systemd, allocation, or process-launch path.
"""

from __future__ import annotations

import copy
import sys
from pathlib import Path
from typing import Any

from full_population import HOST_IDS, SOLVER_IDS
from incident_sentinels import validate_incident_sentinel_records
from multi_host import (
    environment_manifest,
    host_registration,
    validate_host_observation,
)
from resume_contract import ContractError, digest
from resume_fs import read_canonical_json
from resume_runner import sha256_file


PREFLIGHT_SCHEMA = "axeyum.smtcomp-credited-full-preflight.v1"
PREFLIGHT_MAX_AGE_NS = 30 * 60 * 1_000_000_000
PREFLIGHT_FIELDS = {
    "schema",
    "fixture_only",
    "attempt_root",
    "started_at_ns",
    "ended_at_ns",
    "expires_at_ns",
    "environment_path",
    "environment_sha256",
    "host_observations",
    "host_registrations",
    "sentinel_records",
    "record_sha256",
}


def _sealed(value: dict[str, Any]) -> dict[str, Any]:
    result = copy.deepcopy(value)
    result.pop("record_sha256", None)
    result["record_sha256"] = digest(result)
    return result


def _inside(path: Path, root: Path, label: str) -> Path:
    if not path.is_absolute() or path.is_symlink():
        raise ContractError(f"full preflight {label} path is not canonical")
    resolved = path.resolve(strict=True)
    if resolved != path:
        raise ContractError(f"full preflight {label} path is not canonical")
    try:
        resolved.relative_to(root)
    except ValueError as exc:
        raise ContractError(f"full preflight {label} escapes attempt root") from exc
    if not resolved.is_file():
        raise ContractError(f"full preflight {label} path mismatch")
    return resolved


def _composition_registrations(composition: dict[str, Any]) -> list[dict[str, Any]]:
    cells = composition.get("cells")
    if (
        not isinstance(cells, list)
        or [cell.get("solver_id") for cell in cells] != list(SOLVER_IDS)
    ):
        raise ContractError("full preflight composition cell mismatch")
    registrations = None
    for cell in cells:
        plan = read_canonical_json(Path(cell.get("plan_path", "")))
        current = plan.get("host_registrations")
        if registrations is None:
            registrations = current
        elif current != registrations:
            raise ContractError("full preflight cell registrations differ")
    if not isinstance(registrations, list):
        raise ContractError("full preflight registration inventory mismatch")
    return registrations


def build_full_preflight(
    *,
    attempt_root: Path,
    environment_path: Path,
    composition: dict[str, Any],
    solver_binaries: dict[str, Path],
    host_observations: list[dict[str, Any]],
    sentinel_records: list[dict[str, Any]],
    started_at_ns: int,
    ended_at_ns: int,
    fixture_only: bool = False,
) -> dict[str, Any]:
    """Build one sealed, process-free preflight from captured evidence."""

    attempt = attempt_root.resolve(strict=True)
    environment = _inside(environment_path, attempt, "environment manifest")
    if type(fixture_only) is not bool:
        raise ContractError("full preflight fixture flag mismatch")
    if (
        type(started_at_ns) is not int
        or type(ended_at_ns) is not int
        or started_at_ns <= 0
        or ended_at_ns < started_at_ns
        or ended_at_ns > started_at_ns + PREFLIGHT_MAX_AGE_NS
    ):
        raise ContractError("full preflight capture interval mismatch")
    if not isinstance(host_observations, list) or len(host_observations) != len(HOST_IDS):
        raise ContractError("full preflight host observation inventory mismatch")
    observations = [validate_host_observation(row) for row in host_observations]
    expected_environment = environment_manifest(observations)
    if read_canonical_json(environment) != expected_environment:
        raise ContractError("full preflight environment manifest drift")
    environment_sha256 = sha256_file(environment)
    registrations = [
        host_registration(
            host_id=host_id,
            ssh_target=host_id,
            observation=observation,
            environment_sha256=environment_sha256,
        )
        for host_id, observation in zip(HOST_IDS, observations, strict=True)
    ]
    if registrations != _composition_registrations(composition):
        raise ContractError("full preflight host registration drift")
    if observations[0]["python_executable_sha256"] != sha256_file(
        Path(sys.executable).resolve(strict=True)
    ):
        raise ContractError("full preflight coordinator/host Python drift")
    validated_sentinels = validate_incident_sentinel_records(
        sentinel_records,
        attempt_root=attempt,
        solver_binaries=solver_binaries,
        fixture_only=fixture_only,
    )
    sentinel_starts = [row["started_at_ns"] for row in validated_sentinels]
    sentinel_ends = [row["ended_at_ns"] for row in validated_sentinels]
    if min(sentinel_starts) < started_at_ns or max(sentinel_ends) > ended_at_ns:
        raise ContractError("full preflight sentinel interval escapes capture")
    return _sealed(
        {
            "schema": PREFLIGHT_SCHEMA,
            "fixture_only": fixture_only,
            "attempt_root": str(attempt),
            "started_at_ns": started_at_ns,
            "ended_at_ns": ended_at_ns,
            "expires_at_ns": started_at_ns + PREFLIGHT_MAX_AGE_NS,
            "environment_path": str(environment),
            "environment_sha256": environment_sha256,
            "host_observations": observations,
            "host_registrations": registrations,
            "sentinel_records": validated_sentinels,
        }
    )


def validate_full_preflight(
    preflight: dict[str, Any],
    *,
    attempt_root: Path,
    composition: dict[str, Any],
    solver_binaries: dict[str, Path],
    prepared_at_ns: int,
) -> dict[str, Any]:
    """Replay a preflight and require publication inside its frozen window."""

    if (
        not isinstance(preflight, dict)
        or set(preflight) != PREFLIGHT_FIELDS
        or preflight.get("schema") != PREFLIGHT_SCHEMA
        or preflight.get("record_sha256") != _sealed(preflight)["record_sha256"]
    ):
        raise ContractError("full preflight field/schema/seal mismatch")
    attempt = attempt_root.resolve(strict=True)
    fixture_only = preflight.get("fixture_only")
    if (
        type(fixture_only) is not bool
        or preflight.get("attempt_root") != str(attempt)
        or type(prepared_at_ns) is not int
        or prepared_at_ns <= 0
    ):
        raise ContractError("full preflight publication scope mismatch")
    environment_path = preflight.get("environment_path")
    if not isinstance(environment_path, str) or not environment_path:
        raise ContractError("full preflight environment path mismatch")
    rebuilt = build_full_preflight(
        attempt_root=attempt,
        environment_path=Path(environment_path),
        composition=composition,
        solver_binaries=solver_binaries,
        host_observations=preflight.get("host_observations"),
        sentinel_records=preflight.get("sentinel_records"),
        started_at_ns=preflight.get("started_at_ns"),
        ended_at_ns=preflight.get("ended_at_ns"),
        fixture_only=fixture_only,
    )
    if rebuilt != preflight:
        raise ContractError("full preflight replay drift")
    if (
        preflight.get("expires_at_ns")
        != preflight["started_at_ns"] + PREFLIGHT_MAX_AGE_NS
        or prepared_at_ns < preflight["ended_at_ns"]
        or prepared_at_ns > preflight["expires_at_ns"]
    ):
        raise ContractError("full preflight publication is outside capture window")
    return preflight
