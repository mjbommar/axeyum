"""Live capture operator for credited SMT-COMP full preparation.

This is the only live F2 orchestration layer.  It may run the two registered
repository gates, probe the three registered hosts, and execute the eight
bounded incident sentinels.  It deliberately has no admission, allocation,
systemd-unit, or solver-wave execution import or call path.
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import time
from collections.abc import Callable
from pathlib import Path
from typing import Any

from full_population import (
    HOST_IDS,
    SOLVER_IDS,
    THERMAL_STOP_MILLICELSIUS,
    build_thermal_observation,
    validate_schedule,
)
from full_preflight import build_full_preflight
from full_prepare import (
    FullSolverCell,
    compose_full_cell_manifests,
    materialize_full_selection,
    publish_full_preparation_candidate,
    validate_full_preparation,
)
from full_readiness import (
    REQUIRED_GATE_COMMANDS,
    build_readiness,
    run_gate,
    validate_readiness,
    worktree_status,
)
from incident_sentinels import (
    EXPECTED_SENTINELS,
    SENTINEL_ROWS,
    SENTINEL_SCHEMA,
    SOLVER_ENVIRONMENT,
    seal_sentinel,
    validate_incident_sentinel_records,
)
from multi_host import (
    environment_manifest,
    host_registration,
    remote_probe,
    remote_thermal_sample,
    stage_execution_bundle,
)
from p0_compare import derive_live_comparison, validate_comparison
from resume_contract import ContractError, canonical_bytes, digest
from resume_fs import atomic_install_bytes, atomic_install_json, read_canonical_json
from resume_runner import sha256_file
from runner import run_solver


ATTEMPT_DIRECTORY = "credited-full-preparations"
SAFE_ATTEMPT_ID = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.-]{0,127}\Z")
SENTINEL_KIND_BY_ID = {
    "qf-abvfp-query-26": "qf_abvfp",
    "qf-bvfp-query-26": "qf_bvfp",
    "qf-auflia-pipeline-invalid": "qf_auflia",
}
REPAIRED_P0_COMPARISON_PATH = Path(
    "docs/plan/generated/smtcomp-repaired-p0-comparison.json"
)

GateRunner = Callable[..., dict[str, Any]]
Progress = Callable[[str], None]
RemoteProbe = Callable[..., dict[str, Any]]
RepairedP0Validator = Callable[..., None]
SolverRunner = Callable[..., Any]
ThermalProbe = Callable[..., bytes]


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
    if len(value) != 40 or any(
        character not in "0123456789abcdef" for character in value
    ):
        raise ContractError("Git returned an invalid commit identity")
    return value


def _remote_main(root: Path) -> str:
    try:
        completed = subprocess.run(
            ["git", "ls-remote", "--exit-code", "origin", "refs/heads/main"],
            cwd=root,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=30,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise ContractError("unable to observe remote main") from exc
    if completed.returncode != 0:
        raise ContractError("unable to observe remote main")
    try:
        lines = completed.stdout.decode("ascii").splitlines()
    except UnicodeDecodeError as exc:
        raise ContractError("remote main observation is not ASCII") from exc
    if len(lines) != 1:
        raise ContractError("remote main observation is incomplete or ambiguous")
    fields = lines[0].split("\t")
    if len(fields) != 2 or fields[1] != "refs/heads/main":
        raise ContractError("remote main observation has an unexpected shape")
    value = fields[0]
    if len(value) != 40 or any(
        character not in "0123456789abcdef" for character in value
    ):
        raise ContractError("remote main observation has an invalid commit")
    return value


def require_exact_integrated_main(repository_root: Path) -> str:
    """Require one clean commit shared by HEAD, tracking main, and remote main."""

    root = repository_root.resolve(strict=True)
    if worktree_status(root):
        raise ContractError("live full preparation requires a clean worktree")
    head = _commit(root, "HEAD")
    tracking = _commit(root, "origin/main")
    remote = _remote_main(root)
    if head != tracking or tracking != remote:
        raise ContractError("live full preparation requires exact integrated remote main")
    return head


def capture_live_readiness(
    *,
    repository_root: Path,
    gate_runner: GateRunner = run_gate,
    fixture_only: bool = False,
    progress: Progress | None = None,
) -> dict[str, Any]:
    """Run and seal the two registered gates before any preparation write."""

    if type(fixture_only) is not bool:
        raise ContractError("readiness-capture fixture flag mismatch")
    if not fixture_only and gate_runner is not run_gate:
        raise ContractError("live readiness capture requires the registered gate runner")
    root = repository_root.resolve(strict=True)
    expected_commit = require_exact_integrated_main(root)
    observations = []
    for command in REQUIRED_GATE_COMMANDS:
        if progress is not None:
            progress(f"running registered readiness gate: {' '.join(command)}")
        observation = gate_runner(repository_root=root, command=list(command))
        if not isinstance(observation, dict) or observation.get("exit_code") != 0:
            raise ContractError(
                f"registered full-preparation gate failed: {' '.join(command)}"
            )
        observations.append(observation)
        if require_exact_integrated_main(root) != expected_commit:
            raise ContractError("integrated main changed during readiness gates")
    readiness = build_readiness(
        repository_root=root,
        gate_observations=observations,
        require_ready=True,
    )
    if readiness["head_commit"] != expected_commit:
        raise ContractError("full-preparation readiness commit drift")
    return readiness


def validate_repaired_p0_authority(
    *, repository_root: Path, preparation_root: Path
) -> None:
    """Replay all frozen repaired-P0 roots against the committed comparison."""

    repository = repository_root.resolve(strict=True)
    if preparation_root.is_symlink():
        raise ContractError("repaired-P0 preparation root must not be a symlink")
    try:
        preparation = preparation_root.resolve(strict=True)
    except OSError as exc:
        raise ContractError("missing repaired-P0 preparation root") from exc
    if not preparation.is_dir():
        raise ContractError("repaired-P0 preparation root is not a directory")
    derived = derive_live_comparison(preparation)
    validate_comparison(derived)
    committed = read_canonical_json(repository / REPAIRED_P0_COMPARISON_PATH)
    validate_comparison(committed)
    if derived != committed:
        raise ContractError("repaired-P0 comparison differs from committed authority")


def _safe_attempt_id(value: str) -> str:
    if not isinstance(value, str) or not SAFE_ATTEMPT_ID.fullmatch(value):
        raise ContractError("unsafe credited-full preparation attempt ID")
    return value


def _regular_file(path: Path, label: str, *, executable: bool = False) -> Path:
    if path.is_symlink():
        raise ContractError(f"{label} must not be a symlink")
    try:
        resolved = path.resolve(strict=True)
    except OSError as exc:
        raise ContractError(f"missing {label}") from exc
    if not resolved.is_file() or (executable and not os.access(resolved, os.X_OK)):
        raise ContractError(f"invalid {label}")
    return resolved


def _install_copy(
    *, source: Path, destination: Path, label: str, executable: bool = False
) -> Path:
    source_path = _regular_file(source, label, executable=executable)
    atomic_install_bytes(destination.parent, destination.name, source_path.read_bytes())
    if executable:
        destination.chmod(0o555)
        with destination.open("rb") as handle:
            os.fsync(handle.fileno())
    if sha256_file(destination) != sha256_file(source_path):
        raise ContractError(f"staged {label} differs from source")
    return destination.resolve(strict=True)


def _create_attempt(shared_root: Path, attempt_id: str) -> Path:
    if shared_root.is_symlink():
        raise ContractError("invalid credited-full shared root")
    shared = shared_root.resolve(strict=True)
    if not shared.is_dir():
        raise ContractError("invalid credited-full shared root")
    safe_attempt_id = _safe_attempt_id(attempt_id)
    parent = shared / ATTEMPT_DIRECTORY
    parent.mkdir(mode=0o755, exist_ok=True)
    if parent.is_symlink() or not parent.is_dir():
        raise ContractError("invalid credited-full preparation parent")
    attempt = parent / safe_attempt_id
    try:
        attempt.mkdir(mode=0o755)
    except FileExistsError as exc:
        raise ContractError("credited-full preparation attempt already exists") from exc
    return attempt.resolve(strict=True)


def _sentinel_is_safe(record: dict[str, Any]) -> bool:
    kind = record["sentinel_kind"]
    solver_id = record["solver_id"]
    status = record["observed_status"]
    completed = record["termination_class"] == "completed" and record["exit_code"] == 0
    if kind in {"qf_abvfp", "qf_bvfp"}:
        return completed and status == "unsat"
    if solver_id == "cvc5":
        return completed and status == "sat"
    return (completed and status in {"sat", "unknown"}) or (
        record["termination_class"] == "wall-timeout" and status is None
    )


def capture_incident_sentinels(
    *,
    attempt_root: Path,
    solver_binaries: dict[str, Path],
    sentinel_inputs: dict[str, Path],
    output_dir: Path,
    fixture_only: bool = False,
    solver_runner: SolverRunner = run_solver,
    now_ns: Callable[[], int] = time.time_ns,
) -> list[dict[str, Any]]:
    """Execute and replay the exact eight-row incident-sentinel matrix."""

    if type(fixture_only) is not bool:
        raise ContractError("incident sentinel fixture flag mismatch")
    if not fixture_only and (
        solver_runner is not run_solver or now_ns is not time.time_ns
    ):
        raise ContractError("live incident capture requires registered runtime hooks")
    if set(solver_binaries) != set(SOLVER_IDS):
        raise ContractError("incident sentinel binary inventory mismatch")
    if set(sentinel_inputs) != set(SENTINEL_KIND_BY_ID):
        raise ContractError("incident sentinel input inventory mismatch")
    attempt = attempt_root.resolve(strict=True)
    binaries = {
        solver_id: _regular_file(path, f"{solver_id} sentinel binary", executable=True)
        for solver_id, path in solver_binaries.items()
    }
    inputs = {
        sentinel_id: _regular_file(path, f"{sentinel_id} sentinel input")
        for sentinel_id, path in sentinel_inputs.items()
    }
    for path in [*binaries.values(), *inputs.values()]:
        try:
            path.relative_to(attempt)
        except ValueError as exc:
            raise ContractError("incident sentinel input escapes attempt root") from exc
    output = output_dir.resolve(strict=True)
    try:
        output.relative_to(attempt)
    except ValueError as exc:
        raise ContractError("incident sentinel output escapes attempt root") from exc

    environment = os.environ.copy()
    environment.update(SOLVER_ENVIRONMENT)
    records = []
    for sentinel_id, kind, solver_id in SENTINEL_ROWS:
        binary = binaries[solver_id]
        sentinel = inputs[sentinel_id]
        if kind != SENTINEL_KIND_BY_ID[sentinel_id]:
            raise ContractError("incident sentinel kind mapping drift")
        if not fixture_only and sha256_file(sentinel) != EXPECTED_SENTINELS[kind]:
            raise ContractError(f"incident sentinel bytes differ: {sentinel_id}")
        command = [str(binary), str(sentinel)]
        if solver_id == "axeyum":
            command.extend(["--timeout-ms", "19000"])
        started_at_ns = now_ns()
        result = solver_runner(
            command,
            wall_limit_s=20.0,
            mem_limit_bytes=8 * 1024**3,
            env=environment,
        )
        ended_at_ns = now_ns()
        stem = f"{sentinel_id}-{solver_id}"
        stdout_path = output / f"{stem}.stdout"
        stderr_path = output / f"{stem}.stderr"
        atomic_install_bytes(output, stdout_path.name, result.stdout_bytes)
        atomic_install_bytes(output, stderr_path.name, result.stderr_bytes)
        observed_status = result.observed.value if result.observed is not None else None
        record = seal_sentinel(
            {
                "schema": SENTINEL_SCHEMA,
                "sentinel_id": sentinel_id,
                "sentinel_kind": kind,
                "sentinel_path": str(sentinel),
                "sentinel_sha256": sha256_file(sentinel),
                "solver_id": solver_id,
                "solver_binary_sha256": sha256_file(binary),
                "command_sha256": digest(command),
                "environment_sha256": digest(SOLVER_ENVIRONMENT),
                "observed_status": observed_status,
                "termination_class": result.termination_class,
                "exit_code": result.exit_code,
                "signal": result.signal,
                "resource_limit_kind": result.resource_limit_kind,
                "started_at_ns": started_at_ns,
                "ended_at_ns": ended_at_ns,
                "wall_time_ns": round(result.scoring_wall_time * 1_000_000_000),
                "runner_elapsed_ns": round(result.runner_elapsed * 1_000_000_000),
                "stdout_path": str(stdout_path.resolve(strict=True)),
                "stdout_sha256": sha256_file(stdout_path),
                "stdout_bytes": stdout_path.stat().st_size,
                "stderr_path": str(stderr_path.resolve(strict=True)),
                "stderr_sha256": sha256_file(stderr_path),
                "stderr_bytes": stderr_path.stat().st_size,
            }
        )
        records.append(record)
        if not _sentinel_is_safe(record):
            raise ContractError(
                f"unsafe incident sentinel outcome: {sentinel_id}/{solver_id}"
            )
    return validate_incident_sentinel_records(
        records,
        attempt_root=attempt,
        solver_binaries=binaries,
        fixture_only=fixture_only,
    )


def capture_preflight_thermals(
    *,
    composition: dict[str, Any],
    host_registrations: list[dict[str, Any]],
    remote_helper_path: Path,
    thermal_probe_fn: ThermalProbe = remote_thermal_sample,
    now_ns: Callable[[], int] = time.time_ns,
) -> list[dict[str, Any]]:
    """Capture the three exact first-wave thermal observations without launch."""

    cells = composition.get("cells")
    if (
        not isinstance(cells, list)
        or not cells
        or cells[0].get("solver_id") != "axeyum"
    ):
        raise ContractError("full capture Axeyum composition mismatch")
    cell = cells[0]
    plan = read_canonical_json(Path(cell.get("plan_path", "")))
    schedule = validate_schedule(
        read_canonical_json(Path(cell.get("schedule_path", "")))
    )
    wave = schedule["waves"][0]
    expected_hosts = list(wave["host_ids"])
    if expected_hosts != list(HOST_IDS):
        raise ContractError("full capture first-wave host order mismatch")
    if (
        not isinstance(host_registrations, list)
        or [row.get("host_id") for row in host_registrations] != expected_hosts
    ):
        raise ContractError("full capture thermal registration order mismatch")
    observations = []
    for registration, allocation_id in zip(
        host_registrations, wave["allocation_ids"], strict=True
    ):
        observation = build_thermal_observation(
            sensors_json=thermal_probe_fn(
                registration=registration,
                remote_helper_path=remote_helper_path,
            ),
            plan_sha256=plan["plan_sha256"],
            run_identity_sha256=cell["run_identity_sha256"],
            cell_id="axeyum",
            wave_index=0,
            allocation_id=allocation_id,
            attempt_id=None,
            host_id=registration["host_id"],
            observed_at_ns=now_ns(),
        )
        if observation["temperature_millicelsius"] >= THERMAL_STOP_MILLICELSIUS:
            raise ContractError("full capture thermal stop threshold reached")
        observations.append(observation)
    return observations


def prepare_full_capture(
    *,
    repository_root: Path,
    source_root: Path,
    shared_root: Path,
    accepted_root: Path,
    corpus_root: Path,
    source_corpus_manifest: Path,
    repaired_p0_preparation: Path,
    attempt_id: str,
    solver_sources: dict[str, Path],
    sentinel_sources: dict[str, Path],
    readiness: dict[str, Any],
    fixture_only: bool = False,
    repaired_p0_validator: RepairedP0Validator = validate_repaired_p0_authority,
    remote_probe_fn: RemoteProbe = remote_probe,
    thermal_probe_fn: ThermalProbe = remote_thermal_sample,
    solver_runner: SolverRunner = run_solver,
    now_ns: Callable[[], int] = time.time_ns,
    progress: Progress | None = None,
) -> Path:
    """Capture and publish one no-launch F2 root through existing contracts."""

    root = repository_root.resolve(strict=True)
    source = source_root.resolve(strict=True)
    shared = shared_root.resolve(strict=True)
    accepted = accepted_root.resolve(strict=True)
    corpus = corpus_root.resolve(strict=True)
    corpus_manifest_source = _regular_file(source_corpus_manifest, "corpus manifest")
    if type(fixture_only) is not bool:
        raise ContractError("full capture fixture flag mismatch")
    if not fixture_only and (
        repaired_p0_validator is not validate_repaired_p0_authority
        or remote_probe_fn is not remote_probe
        or thermal_probe_fn is not remote_thermal_sample
        or solver_runner is not run_solver
        or now_ns is not time.time_ns
    ):
        raise ContractError("live full capture requires registered runtime hooks")
    if set(solver_sources) != set(SOLVER_IDS):
        raise ContractError("full capture solver inventory mismatch")
    if set(sentinel_sources) != set(SENTINEL_KIND_BY_ID):
        raise ContractError("full capture sentinel inventory mismatch")
    validate_readiness(readiness, repository_root=root)
    if not fixture_only:
        if readiness.get("ready_for_live_preparation") is not True:
            raise ContractError("live full capture lacks ready repository evidence")
        if require_exact_integrated_main(root) != readiness.get("head_commit"):
            raise ContractError("live full capture repository state drift")
    if progress is not None:
        progress("replaying the frozen repaired-P0 comparison and external roots")
    repaired_p0_validator(
        repository_root=root,
        preparation_root=repaired_p0_preparation,
    )
    if (
        not fixture_only
        and require_exact_integrated_main(root) != readiness["head_commit"]
    ):
        raise ContractError("integrated main changed during repaired-P0 replay")

    attempt = _create_attempt(shared, attempt_id)
    inputs = attempt / "inputs"
    binaries_root = attempt / "binaries"
    sentinel_input_root = inputs / "sentinels"
    sentinel_output_root = attempt / "sentinels" / "outputs"
    staging_parent = attempt / "source-bundles"
    for directory in (
        inputs,
        binaries_root,
        sentinel_input_root,
        sentinel_output_root,
        staging_parent,
    ):
        directory.mkdir(mode=0o755, parents=True, exist_ok=True)

    if progress is not None:
        progress("rehashing the accepted full population")
    selection = materialize_full_selection(
        accepted_root=accepted,
        corpus_root=corpus,
        output_dir=inputs,
        fixture_only=fixture_only,
    )
    corpus_manifest = _install_copy(
        source=corpus_manifest_source,
        destination=inputs / "corpus-audit.json",
        label="corpus manifest",
    )
    solver_binaries = {
        solver_id: _install_copy(
            source=solver_sources[solver_id],
            destination=binaries_root / solver_id,
            label=f"{solver_id} binary",
            executable=True,
        )
        for solver_id in SOLVER_IDS
    }
    sentinel_inputs = {
        sentinel_id: _install_copy(
            source=sentinel_sources[sentinel_id],
            destination=sentinel_input_root / f"{sentinel_id}.smt2",
            label=f"{sentinel_id} sentinel",
        )
        for sentinel_id in SENTINEL_KIND_BY_ID
    }
    bundle_root, _source_identity = stage_execution_bundle(
        repository_root=root,
        source_root=source,
        fixture_root=source / "fixtures" / "e3",
        staging_parent=staging_parent,
    )
    staged_source = bundle_root / "scripts" / "smtcomp_repro"
    source_identity_path = bundle_root / "source-identity.json"

    capture_started_at_ns = now_ns()
    if progress is not None:
        progress("capturing registered s5/s6/s7 host observations")
    helper = staged_source / "multi_host.py"
    observations = [
        remote_probe_fn(
            ssh_target=host_id,
            remote_helper_path=helper,
            shared_root=shared,
        )
        for host_id in HOST_IDS
    ]
    environment = environment_manifest(observations)
    environment_path = inputs / "environment.json"
    atomic_install_json(inputs, environment_path.name, environment)
    environment_sha256 = sha256_file(environment_path)
    registrations = [
        host_registration(
            host_id=host_id,
            ssh_target=host_id,
            observation=observation,
            environment_sha256=environment_sha256,
        )
        for host_id, observation in zip(HOST_IDS, observations, strict=True)
    ]
    solver_cells = [
        FullSolverCell(
            "axeyum",
            solver_binaries["axeyum"],
            f"integrated-release-{readiness['head_commit']}",
            19_000,
        ),
        FullSolverCell("cvc5", solver_binaries["cvc5"], "1.3.4"),
        FullSolverCell("bitwuzla", solver_binaries["bitwuzla"], "0.9.1"),
    ]
    composition = compose_full_cell_manifests(
        repository_root=root,
        source_root=staged_source,
        shared_root=shared,
        attempt_root=attempt,
        selection=selection,
        corpus_manifest=corpus_manifest,
        environment_manifest=environment_path,
        source_identity_manifest=source_identity_path,
        host_registrations=registrations,
        solver_cells=solver_cells,
        fixture_only=fixture_only,
    )
    if progress is not None:
        progress("capturing registered s5/s6/s7 thermal observations")
    thermal_observations = capture_preflight_thermals(
        composition=composition,
        host_registrations=registrations,
        remote_helper_path=helper,
        thermal_probe_fn=thermal_probe_fn,
        now_ns=now_ns,
    )
    if progress is not None:
        progress("executing the eight registered incident sentinels")
    sentinel_records = capture_incident_sentinels(
        attempt_root=attempt,
        solver_binaries=solver_binaries,
        sentinel_inputs=sentinel_inputs,
        output_dir=sentinel_output_root,
        fixture_only=fixture_only,
        solver_runner=solver_runner,
        now_ns=now_ns,
    )
    capture_ended_at_ns = now_ns()
    if (
        not fixture_only
        and require_exact_integrated_main(root) != readiness["head_commit"]
    ):
        raise ContractError("integrated main changed during live full capture")
    preflight = build_full_preflight(
        attempt_root=attempt,
        environment_path=environment_path,
        composition=composition,
        solver_binaries=solver_binaries,
        host_observations=observations,
        thermal_observations=thermal_observations,
        sentinel_records=sentinel_records,
        started_at_ns=capture_started_at_ns,
        ended_at_ns=capture_ended_at_ns,
        fixture_only=fixture_only,
    )
    completion = publish_full_preparation_candidate(
        repository_root=root,
        source_root=staged_source,
        source_identity_manifest=source_identity_path,
        attempt_root=attempt,
        selection=selection,
        composition=composition,
        readiness=readiness,
        preflight=preflight,
        solver_cells=solver_cells,
        prepared_at_ns=now_ns(),
    )
    if completion.get("launch_authorized") is not False:
        raise ContractError("credited-full preparation unexpectedly authorized launch")
    return attempt


def _default_attempt_id(repository_root: Path) -> str:
    return f"f2-{_commit(repository_root, 'HEAD')[:12]}-{time.time_ns()}"


def _progress(message: str) -> None:
    print(message, file=sys.stderr, flush=True)


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="capture or verify credited SMT-COMP full preparation without launch"
    )
    parser.add_argument("--verify-root", type=Path)
    parser.add_argument("--shared-root", type=Path)
    parser.add_argument("--accepted-selection", type=Path)
    parser.add_argument("--corpus-root", type=Path)
    parser.add_argument("--corpus-manifest", type=Path)
    parser.add_argument("--repaired-p0-preparation", type=Path)
    parser.add_argument("--axeyum-binary", type=Path)
    parser.add_argument("--cvc5-binary", type=Path)
    parser.add_argument("--bitwuzla-binary", type=Path)
    parser.add_argument("--qf-abvfp-sentinel", type=Path)
    parser.add_argument("--qf-bvfp-sentinel", type=Path)
    parser.add_argument("--qf-auflia-sentinel", type=Path)
    parser.add_argument("--attempt-id")
    return parser


def main(argv: list[str] | None = None) -> int:
    root = Path(__file__).resolve().parents[2]
    parser = _parser()
    args = parser.parse_args(argv)
    preparation_fields = (
        "shared_root",
        "accepted_selection",
        "corpus_root",
        "corpus_manifest",
        "repaired_p0_preparation",
        "axeyum_binary",
        "cvc5_binary",
        "bitwuzla_binary",
        "qf_abvfp_sentinel",
        "qf_bvfp_sentinel",
        "qf_auflia_sentinel",
    )
    if args.verify_root is not None:
        if (
            any(getattr(args, field) is not None for field in preparation_fields)
            or args.attempt_id
        ):
            parser.error("--verify-root cannot be combined with preparation arguments")
        try:
            completion = validate_full_preparation(
                args.verify_root,
                repository_root=root,
            )
        except (ContractError, OSError) as exc:
            print(
                f"credited full preparation verification rejected: {exc}",
                file=sys.stderr,
            )
            return 2
        print(canonical_bytes(completion).decode("utf-8"), end="")
        return 0

    missing = [field for field in preparation_fields if getattr(args, field) is None]
    if missing:
        parser.error(f"missing preparation arguments: {', '.join(missing)}")
    try:
        readiness = capture_live_readiness(
            repository_root=root,
            progress=_progress,
        )
        attempt = prepare_full_capture(
            repository_root=root,
            source_root=root / "scripts" / "smtcomp_repro",
            shared_root=args.shared_root,
            accepted_root=args.accepted_selection,
            corpus_root=args.corpus_root,
            source_corpus_manifest=args.corpus_manifest,
            repaired_p0_preparation=args.repaired_p0_preparation,
            attempt_id=args.attempt_id or _default_attempt_id(root),
            solver_sources={
                "axeyum": args.axeyum_binary,
                "cvc5": args.cvc5_binary,
                "bitwuzla": args.bitwuzla_binary,
            },
            sentinel_sources={
                "qf-abvfp-query-26": args.qf_abvfp_sentinel,
                "qf-bvfp-query-26": args.qf_bvfp_sentinel,
                "qf-auflia-pipeline-invalid": args.qf_auflia_sentinel,
            },
            readiness=readiness,
            progress=_progress,
        )
        completion = validate_full_preparation(attempt, repository_root=root)
    except (ContractError, OSError) as exc:
        print(f"credited full preparation rejected: {exc}", file=sys.stderr)
        return 2
    print(canonical_bytes(completion).decode("utf-8"), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
