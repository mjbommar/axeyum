"""Repository and gate readiness evidence for SMT-COMP full preparation.

This layer is read-only with respect to Git and cannot launch solvers or hosts.
It binds gate observations to one exact repository state and one fixed
integrated origin revision. Later movement of ``origin/main`` cannot rewrite
the meaning of retained readiness evidence.
"""

from __future__ import annotations

import copy
import hashlib
import subprocess
import time
from pathlib import Path
from typing import Any

from resume_contract import ContractError, digest
from resume_runner import sha256_file


GATE_SCHEMA = "axeyum.smtcomp-credited-full-gate-observation.v1"
READINESS_SCHEMA = "axeyum.smtcomp-credited-full-readiness.v2"
REQUIRED_GATE_COMMANDS = (
    ("just", "check"),
    ("./scripts/check-smtcomp-resume.sh",),
)
DEFAULT_REQUIRED_PATHS = (
    "docs/plan/smtcomp-credited-full-admission-fixture-2026-07-23.md",
    "docs/plan/smtcomp-credited-full-execution-coordinator-fixture-2026-07-23.md",
    "docs/plan/smtcomp-credited-full-population-f1-result-2026-07-23.md",
    "docs/plan/smtcomp-credited-full-population-plan-2026-07-23.md",
    "docs/plan/smtcomp-credited-full-preparation-f2-implementation-2026-07-23.md",
    "docs/plan/smtcomp-credited-full-publication-fixture-2026-07-23.md",
    "docs/plan/smtcomp-credited-full-scheduler-authorization-fixture-2026-07-23.md",
    "docs/plan/smtcomp-credited-full-scheduler-state-fixture-2026-07-23.md",
    "scripts/check-smtcomp-resume.sh",
    "scripts/smtcomp_repro/full_admission.py",
    "scripts/smtcomp_repro/full_compare.py",
    "scripts/smtcomp_repro/full_coordinator.py",
    "scripts/smtcomp_repro/full_execute.py",
    "scripts/smtcomp_repro/full_population.py",
    "scripts/smtcomp_repro/full_preflight.py",
    "scripts/smtcomp_repro/full_prepare.py",
    "scripts/smtcomp_repro/full_readiness.py",
    "scripts/smtcomp_repro/full_result.py",
    "scripts/smtcomp_repro/incident_sentinels.py",
    "scripts/smtcomp_repro/multi_host.py",
    "scripts/tests/test_smtcomp_full_admission.py",
    "scripts/tests/test_smtcomp_full_compare.py",
    "scripts/tests/test_smtcomp_full_execution.py",
    "scripts/tests/test_smtcomp_full_population.py",
    "scripts/tests/test_smtcomp_full_result.py",
)
GATE_FIELDS = {
    "schema",
    "command",
    "repository_commit",
    "worktree_status_sha256",
    "exit_code",
    "stdout_sha256",
    "stdout_bytes",
    "stderr_sha256",
    "stderr_bytes",
    "started_at_ns",
    "ended_at_ns",
    "record_sha256",
}
READINESS_FIELDS = {
    "schema",
    "repository_root",
    "fixture_only",
    "head_commit",
    "origin_revision",
    "worktree_status_sha256",
    "worktree_clean",
    "required_paths",
    "gate_observations",
    "prerequisites_satisfied",
    "ready_for_live_preparation",
    "record_sha256",
}


def _sealed(value: dict[str, Any]) -> dict[str, Any]:
    result = copy.deepcopy(value)
    result.pop("record_sha256", None)
    result["record_sha256"] = digest(result)
    return result


def _git(root: Path, *args: str) -> bytes:
    try:
        return subprocess.check_output(
            ["git", *args], cwd=root, stderr=subprocess.STDOUT
        )
    except (OSError, subprocess.CalledProcessError) as exc:
        raise ContractError(f"unable to inspect Git state: {' '.join(args)}") from exc


def _commit(root: Path, revision: str) -> str:
    try:
        value = _git(root, "rev-parse", "--verify", f"{revision}^{{commit}}").decode(
            "ascii"
        ).strip()
    except UnicodeDecodeError as exc:
        raise ContractError("Git returned a non-ASCII commit identity") from exc
    if len(value) != 40 or any(character not in "0123456789abcdef" for character in value):
        raise ContractError("Git returned an invalid commit identity")
    return value


def _is_ancestor(root: Path, ancestor: str, descendant: str) -> bool:
    try:
        completed = subprocess.run(
            ["git", "merge-base", "--is-ancestor", ancestor, descendant],
            cwd=root,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.PIPE,
            check=False,
        )
    except OSError as exc:
        raise ContractError("unable to inspect Git ancestry") from exc
    if completed.returncode not in {0, 1}:
        raise ContractError("unable to inspect Git ancestry")
    return completed.returncode == 0


def worktree_status(root: Path) -> bytes:
    return _git(root, "status", "--porcelain=v1", "-z", "--untracked-files=all")


def _sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def build_gate_observation(
    *,
    repository_root: Path,
    command: list[str],
    exit_code: int,
    stdout: bytes,
    stderr: bytes,
    started_at_ns: int,
    ended_at_ns: int,
) -> dict[str, Any]:
    """Bind one already-executed gate result to the current repository state."""

    root = repository_root.resolve(strict=True)
    if tuple(command) not in REQUIRED_GATE_COMMANDS:
        raise ContractError("unregistered full-preparation gate command")
    if type(exit_code) is not int or not 0 <= exit_code <= 255:
        raise ContractError("invalid full-preparation gate exit code")
    if not isinstance(stdout, bytes) or not isinstance(stderr, bytes):
        raise ContractError("gate output must be byte-exact")
    if (
        type(started_at_ns) is not int
        or type(ended_at_ns) is not int
        or started_at_ns <= 0
        or ended_at_ns < started_at_ns
    ):
        raise ContractError("invalid full-preparation gate timestamps")
    status = worktree_status(root)
    return _sealed(
        {
            "schema": GATE_SCHEMA,
            "command": command,
            "repository_commit": _commit(root, "HEAD"),
            "worktree_status_sha256": _sha256_bytes(status),
            "exit_code": exit_code,
            "stdout_sha256": _sha256_bytes(stdout),
            "stdout_bytes": len(stdout),
            "stderr_sha256": _sha256_bytes(stderr),
            "stderr_bytes": len(stderr),
            "started_at_ns": started_at_ns,
            "ended_at_ns": ended_at_ns,
        }
    )


def run_gate(
    *, repository_root: Path, command: list[str]
) -> dict[str, Any]:
    """Execute one registered local gate and retain its byte-exact outcome."""

    if tuple(command) not in REQUIRED_GATE_COMMANDS:
        raise ContractError("unregistered full-preparation gate command")
    root = repository_root.resolve(strict=True)
    started_at_ns = time.time_ns()
    try:
        completed = subprocess.run(
            command,
            cwd=root,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
    except OSError as exc:
        raise ContractError("unable to execute full-preparation gate") from exc
    ended_at_ns = time.time_ns()
    return build_gate_observation(
        repository_root=root,
        command=command,
        exit_code=completed.returncode,
        stdout=completed.stdout,
        stderr=completed.stderr,
        started_at_ns=started_at_ns,
        ended_at_ns=ended_at_ns,
    )


def validate_gate_observation(
    observation: dict[str, Any],
    *,
    repository_commit: str,
    worktree_status_sha256: str,
) -> dict[str, Any]:
    if set(observation) != GATE_FIELDS or observation.get("schema") != GATE_SCHEMA:
        raise ContractError("full-preparation gate field/schema mismatch")
    if observation.get("record_sha256") != _sealed(observation)["record_sha256"]:
        raise ContractError("full-preparation gate seal mismatch")
    if tuple(observation.get("command", [])) not in REQUIRED_GATE_COMMANDS:
        raise ContractError("unregistered full-preparation gate command")
    if (
        observation.get("repository_commit") != repository_commit
        or observation.get("worktree_status_sha256") != worktree_status_sha256
    ):
        raise ContractError("full-preparation gate repository state drift")
    for prefix in ("stdout", "stderr"):
        sha = observation.get(f"{prefix}_sha256")
        count = observation.get(f"{prefix}_bytes")
        if (
            not isinstance(sha, str)
            or len(sha) != 64
            or any(character not in "0123456789abcdef" for character in sha)
            or type(count) is not int
            or count < 0
        ):
            raise ContractError("full-preparation gate output identity mismatch")
    if (
        type(observation.get("exit_code")) is not int
        or not 0 <= observation["exit_code"] <= 255
        or type(observation.get("started_at_ns")) is not int
        or type(observation.get("ended_at_ns")) is not int
        or observation["started_at_ns"] <= 0
        or observation["ended_at_ns"] < observation["started_at_ns"]
    ):
        raise ContractError("full-preparation gate numeric field mismatch")
    return observation


def build_readiness(
    *,
    repository_root: Path,
    gate_observations: list[dict[str, Any]],
    required_paths: tuple[str, ...] = DEFAULT_REQUIRED_PATHS,
    fixture_only: bool = False,
    require_ready: bool = False,
) -> dict[str, Any]:
    """Audit local/origin identity and optionally require live-preparation readiness."""

    if type(require_ready) is not bool or type(fixture_only) is not bool:
        raise ContractError("readiness flags must be Boolean")
    root = repository_root.resolve(strict=True)
    head = _commit(root, "HEAD")
    origin_revision = _commit(root, "origin/main")
    status = worktree_status(root)
    status_sha256 = _sha256_bytes(status)
    if (
        not required_paths
        or tuple(sorted(set(required_paths))) != required_paths
        or any(Path(path).is_absolute() or ".." in Path(path).parts for path in required_paths)
    ):
        raise ContractError("invalid full-preparation required path set")
    if not fixture_only and required_paths != DEFAULT_REQUIRED_PATHS:
        raise ContractError("live readiness requires the complete registered path set")
    path_rows = []
    for relative in required_paths:
        local = root / relative
        if local.is_symlink() or not local.is_file():
            raise ContractError(f"missing full-preparation required path: {relative}")
        origin_bytes = _git(root, "show", f"{origin_revision}:{relative}")
        path_rows.append(
            {
                "path": relative,
                "local_sha256": sha256_file(local),
                "origin_revision_sha256": _sha256_bytes(origin_bytes),
                "byte_identical": local.read_bytes() == origin_bytes,
            }
        )
    by_command: dict[tuple[str, ...], dict[str, Any]] = {}
    for observation in gate_observations:
        validate_gate_observation(
            observation,
            repository_commit=head,
            worktree_status_sha256=status_sha256,
        )
        command = tuple(observation["command"])
        if command in by_command:
            raise ContractError("duplicate full-preparation gate observation")
        by_command[command] = observation
    gates_complete = set(by_command) == set(REQUIRED_GATE_COMMANDS)
    gates_green = gates_complete and all(
        by_command[command]["exit_code"] == 0 for command in REQUIRED_GATE_COMMANDS
    )
    prerequisites = (
        _is_ancestor(root, origin_revision, head)
        and not status
        and all(row["byte_identical"] for row in path_rows)
        and gates_green
    )
    ready = prerequisites and not fixture_only
    result = _sealed(
        {
            "schema": READINESS_SCHEMA,
            "repository_root": str(root),
            "fixture_only": fixture_only,
            "head_commit": head,
            "origin_revision": origin_revision,
            "worktree_status_sha256": status_sha256,
            "worktree_clean": not status,
            "required_paths": path_rows,
            "gate_observations": [
                by_command[command]
                for command in REQUIRED_GATE_COMMANDS
                if command in by_command
            ],
            "prerequisites_satisfied": prerequisites,
            "ready_for_live_preparation": ready,
        }
    )
    validate_readiness(result, repository_root=root)
    if require_ready and not ready:
        raise ContractError("repository is not ready for live full preparation")
    return result


def validate_readiness(
    readiness: dict[str, Any], *, repository_root: Path, inspect_current: bool = True
) -> dict[str, Any]:
    if set(readiness) != READINESS_FIELDS or readiness.get("schema") != READINESS_SCHEMA:
        raise ContractError("full-preparation readiness field/schema mismatch")
    if readiness.get("record_sha256") != _sealed(readiness)["record_sha256"]:
        raise ContractError("full-preparation readiness seal mismatch")
    root = repository_root.resolve(strict=True)
    if readiness.get("repository_root") != str(root):
        raise ContractError("full-preparation readiness root mismatch")
    if type(inspect_current) is not bool:
        raise ContractError("inspect_current must be Boolean")
    recorded_head = readiness.get("head_commit")
    recorded_origin = readiness.get("origin_revision")
    for value in (recorded_head, recorded_origin):
        if (
            not isinstance(value, str)
            or len(value) != 40
            or any(character not in "0123456789abcdef" for character in value)
        ):
            raise ContractError("full-preparation readiness commit mismatch")
        if _commit(root, value) != value:
            raise ContractError("full-preparation readiness commit object drift")
    if not _is_ancestor(root, recorded_origin, recorded_head):
        raise ContractError("full-preparation origin revision is not integrated")
    status_sha256 = readiness.get("worktree_status_sha256")
    worktree_clean = readiness.get("worktree_clean")
    if (
        not isinstance(status_sha256, str)
        or len(status_sha256) != 64
        or any(character not in "0123456789abcdef" for character in status_sha256)
        or type(worktree_clean) is not bool
        or (worktree_clean and status_sha256 != _sha256_bytes(b""))
    ):
        raise ContractError("full-preparation readiness worktree state mismatch")
    observed = (
        build_readiness_state(root)
        if inspect_current
        else {
            "head_commit": recorded_head,
            "worktree_status_sha256": status_sha256,
            "worktree_clean": worktree_clean,
        }
    )
    if inspect_current:
        for field in (
            "head_commit",
            "worktree_status_sha256",
            "worktree_clean",
        ):
            if readiness.get(field) != observed[field]:
                raise ContractError("full-preparation readiness repository drift")
    paths = readiness.get("required_paths")
    if (
        not isinstance(paths, list)
        or not paths
        or any(not isinstance(row, dict) for row in paths)
    ):
        raise ContractError("full-preparation readiness path inventory mismatch")
    relative_paths = [row.get("path") for row in paths if isinstance(row, dict)]
    if (
        relative_paths != sorted(set(relative_paths))
        or any(
            not isinstance(path, str)
            or Path(path).is_absolute()
            or ".." in Path(path).parts
            for path in relative_paths
        )
        or (
            readiness.get("fixture_only") is False
            and tuple(relative_paths) != DEFAULT_REQUIRED_PATHS
        )
        or type(readiness.get("fixture_only")) is not bool
    ):
        raise ContractError("full-preparation readiness path profile mismatch")
    for row in paths:
        if set(row) != {
            "path",
            "local_sha256",
            "origin_revision_sha256",
            "byte_identical",
        }:
            raise ContractError("full-preparation readiness path row mismatch")
        relative = row["path"]
        head_bytes = _git(root, "show", f"{recorded_head}:{relative}")
        origin_bytes = _git(root, "show", f"{recorded_origin}:{relative}")
        local = root / relative
        if inspect_current and (local.is_symlink() or not local.is_file()):
            raise ContractError("full-preparation readiness local path drift")
        expected_local_sha = (
            sha256_file(local)
            if inspect_current
            else _sha256_bytes(head_bytes)
        )
        expected_equal = (
            local.read_bytes() == origin_bytes
            if inspect_current
            else head_bytes == origin_bytes
        )
        if (
            row["local_sha256"] != expected_local_sha
            or row["origin_revision_sha256"] != _sha256_bytes(origin_bytes)
            or row["byte_identical"] is not expected_equal
        ):
            raise ContractError("full-preparation readiness path drift")
    gates = readiness.get("gate_observations")
    if not isinstance(gates, list):
        raise ContractError("full-preparation readiness gate inventory mismatch")
    commands = [tuple(gate.get("command", [])) for gate in gates if isinstance(gate, dict)]
    expected_commands = [
        command for command in REQUIRED_GATE_COMMANDS if command in commands
    ]
    if commands != expected_commands:
        raise ContractError("full-preparation readiness gate order/identity mismatch")
    for gate in gates:
        validate_gate_observation(
            gate,
            repository_commit=observed["head_commit"],
            worktree_status_sha256=observed["worktree_status_sha256"],
        )
    expected_prerequisites = (
        _is_ancestor(root, recorded_origin, recorded_head)
        and observed["worktree_clean"]
        and all(row["byte_identical"] for row in paths)
        and {tuple(row["command"]) for row in gates}
        == set(REQUIRED_GATE_COMMANDS)
        and all(row["exit_code"] == 0 for row in gates)
    )
    expected_ready = expected_prerequisites and not readiness["fixture_only"]
    if (
        readiness.get("prerequisites_satisfied") is not expected_prerequisites
        or readiness.get("ready_for_live_preparation") is not expected_ready
    ):
        raise ContractError("full-preparation readiness conclusion mismatch")
    return readiness


def build_readiness_state(root: Path) -> dict[str, Any]:
    status = worktree_status(root)
    return {
        "head_commit": _commit(root, "HEAD"),
        "worktree_status_sha256": _sha256_bytes(status),
        "worktree_clean": not status,
    }
