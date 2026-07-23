"""Supervised wave execution for the credited full-population run.

The core is dependency-injected so interruption, partial launch, thermal stop,
and terminal handling are proven without SSH or solver processes.  Live hooks
are intentionally a later integration step.
"""

from __future__ import annotations

import copy
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable

from full_population import (
    CHECKPOINT_TERMINAL_FIELDS,
    SHA256,
    THERMAL_MAX_INTERVAL_NS,
    THERMAL_STOP_MILLICELSIUS,
    WAVE_COUNT,
    build_wave_checkpoint,
    scheduler_decision,
    validate_checkpoint_chain,
    validate_schedule,
    validate_thermal_observation,
    validate_thermal_stop,
)
from resume_contract import ContractError, digest
from resume_fs import (
    atomic_install_json,
    read_canonical_json,
    recover_orphan_temporaries,
)


WAVE_OUTCOME_SCHEMA = "axeyum.smtcomp-credited-full-wave-outcome.v1"
CHECKPOINT_DIRECTORY = "full-wave-checkpoints"


def load_wave_checkpoints(
    run_dir: Path,
    *,
    schedule: dict[str, Any],
    plan_sha256: str,
    run_identity_sha256: str,
    cell_id: str,
) -> list[dict[str, Any]]:
    """Load the exact immutable, contiguous checkpoint prefix for one cell."""

    root = run_dir / CHECKPOINT_DIRECTORY
    if not root.exists():
        return []
    if root.is_symlink() or not root.is_dir():
        raise ContractError("full wave checkpoint directory mismatch")
    paths = sorted(root.iterdir(), key=lambda path: path.name)
    if any(path.is_symlink() or not path.is_file() for path in paths):
        raise ContractError("unexpected full wave checkpoint artifact")
    expected_names = [f"wave-{index:02d}.json" for index in range(len(paths))]
    if [path.name for path in paths] != expected_names:
        raise ContractError("full wave checkpoint inventory is not contiguous")
    checkpoints = [read_canonical_json(path) for path in paths]
    return validate_checkpoint_chain(
        checkpoints,
        schedule=schedule,
        plan_sha256=plan_sha256,
        run_identity_sha256=run_identity_sha256,
        cell_id=cell_id,
    )


def publish_wave_checkpoint(
    run_dir: Path,
    *,
    checkpoint: dict[str, Any],
    schedule: dict[str, Any],
    plan_sha256: str,
    run_identity_sha256: str,
    cell_id: str,
    phase_hook: Callable[[str], None] | None = None,
) -> dict[str, Any]:
    """Install one checkpoint without permitting a gap or byte replacement."""

    checkpoint_root = run_dir / CHECKPOINT_DIRECTORY
    recover_orphan_temporaries(
        checkpoint_root,
        quarantine_root=run_dir / "quarantine",
        eligible_targets={f"wave-{index:02d}.json" for index in range(WAVE_COUNT)},
    )
    checkpoints = load_wave_checkpoints(
        run_dir,
        schedule=schedule,
        plan_sha256=plan_sha256,
        run_identity_sha256=run_identity_sha256,
        cell_id=cell_id,
    )
    wave_index = checkpoint.get("wave_index")
    if type(wave_index) is int and 0 <= wave_index < len(checkpoints):
        if checkpoint == checkpoints[wave_index]:
            return checkpoints[wave_index]
        raise ContractError("full wave checkpoint conflicts with installed wave")
    if wave_index != len(checkpoints):
        raise ContractError("full wave checkpoint is not the next exact wave")
    validate_checkpoint_chain(
        [*checkpoints, checkpoint],
        schedule=schedule,
        plan_sha256=plan_sha256,
        run_identity_sha256=run_identity_sha256,
        cell_id=cell_id,
    )
    atomic_install_json(
        checkpoint_root,
        f"wave-{wave_index:02d}.json",
        checkpoint,
        phase_hook=phase_hook,
        quarantine_root=run_dir / "quarantine",
    )
    return load_wave_checkpoints(
        run_dir,
        schedule=schedule,
        plan_sha256=plan_sha256,
        run_identity_sha256=run_identity_sha256,
        cell_id=cell_id,
    )[-1]


@dataclass(frozen=True)
class WaveHandle:
    allocation_id: str
    host_id: str
    attempt_id: str
    session_id: str
    remote_unit: str


def _sealed(value: dict[str, Any]) -> dict[str, Any]:
    result = copy.deepcopy(value)
    result.pop("record_sha256", None)
    result["record_sha256"] = digest(result)
    return result


def _validate_handle(handle: WaveHandle, allocation: dict[str, Any]) -> None:
    if (
        handle.allocation_id != allocation["allocation_id"]
        or handle.host_id != allocation["host_id"]
        or not handle.attempt_id
        or not handle.session_id
        or handle.remote_unit
        != f"axeyum-smtcomp-e3-{handle.session_id}.service"
    ):
        raise ContractError("wave launcher returned a mismatched handle")


def supervise_one_wave(
    *,
    schedule: dict[str, Any],
    checkpoints: list[dict[str, Any]],
    plan_sha256: str,
    run_identity_sha256: str,
    cell_id: str,
    open_attempt_ids: list[str],
    failed_allocation_ids: list[str],
    lost_allocation_ids: list[str],
    cooldown_required: bool,
    prewave_thermal_observations: list[dict[str, Any]],
    launch: Callable[[dict[str, Any]], WaveHandle],
    poll_terminal: Callable[[WaveHandle], dict[str, Any] | None],
    observe_active: Callable[[WaveHandle, int], dict[str, Any]],
    stop_overheated: Callable[[WaveHandle, dict[str, Any]], dict[str, Any]],
    now_ns: Callable[[], int],
    wait: Callable[[], None],
    pause_requested: Callable[[], bool],
) -> dict[str, Any]:
    """Launch and supervise at most one exact wave through durable terminals."""

    validate_schedule(schedule)
    decision_time = now_ns()
    initial_pause = pause_requested()
    decision = scheduler_decision(
        schedule=schedule,
        checkpoints=checkpoints,
        plan_sha256=plan_sha256,
        run_identity_sha256=run_identity_sha256,
        cell_id=cell_id,
        open_attempt_ids=open_attempt_ids,
        failed_allocation_ids=failed_allocation_ids,
        lost_allocation_ids=lost_allocation_ids,
        pause_requested=initial_pause,
        cooldown_required=cooldown_required,
        thermal_observations=prewave_thermal_observations,
        decided_at_ns=decision_time,
    )
    if decision["status"] != "launch":
        return _sealed(
            {
                "schema": WAVE_OUTCOME_SCHEMA,
                "status": decision["status"],
                "scheduler_decision_sha256": decision["record_sha256"],
                "wave_index": decision["next_wave_index"],
                "launched_allocation_ids": [],
                "allocation_terminals": [],
                "thermal_stop_record_sha256s": [],
                "active_thermal_observation_sha256s": [],
                "checkpoint": None,
                "pause_observed": initial_pause,
            }
        )

    wave_index = decision["next_wave_index"]
    wave = schedule["waves"][wave_index]
    allocations = {
        row["allocation_id"]: row
        for row in schedule["allocations"]
        if row["generation"] == 0
    }
    active: dict[str, WaveHandle] = {}
    launched_ids: list[str] = []
    terminals: dict[str, dict[str, Any]] = {}
    thermal_stops: list[dict[str, Any]] = []
    active_thermal_ids: list[str] = []
    thermally_stopped: set[str] = set()
    launch_failed = False
    pause_seen = False
    for allocation_id in wave["allocation_ids"]:
        try:
            handle = launch(allocations[allocation_id])
        except OSError:
            launch_failed = True
            break
        _validate_handle(handle, allocations[allocation_id])
        active[allocation_id] = handle
        launched_ids.append(allocation_id)

    last_thermal_ns = decision_time
    thermal_failed = False
    while active:
        pause_seen = pause_seen or pause_requested()
        for allocation_id, handle in list(active.items()):
            terminal = poll_terminal(handle)
            if terminal is None:
                continue
            if set(terminal) != CHECKPOINT_TERMINAL_FIELDS:
                raise ContractError("wave terminal field mismatch")
            if (
                terminal.get("allocation_id") != allocation_id
                or terminal.get("attempt_id") != handle.attempt_id
                or terminal.get("status") not in {"completed", "failed", "lost"}
                or not isinstance(terminal.get("terminal_record_sha256"), str)
                or not SHA256.fullmatch(terminal["terminal_record_sha256"])
            ):
                raise ContractError("wave terminal identity mismatch")
            terminals[allocation_id] = terminal
            del active[allocation_id]
        if not active:
            break
        observed_now = now_ns()
        if observed_now < last_thermal_ns:
            raise ContractError("wave clock moved backwards")
        if observed_now - last_thermal_ns >= THERMAL_MAX_INTERVAL_NS:
            for allocation_id, handle in list(active.items()):
                observation = observe_active(handle, observed_now)
                validate_thermal_observation(observation)
                active_thermal_ids.append(observation["record_sha256"])
                if (
                    observation["allocation_id"] != allocation_id
                    or observation["attempt_id"] != handle.attempt_id
                    or observation["host_id"] != handle.host_id
                    or observation["plan_sha256"] != plan_sha256
                    or observation["run_identity_sha256"] != run_identity_sha256
                    or observation["cell_id"] != cell_id
                    or observation["wave_index"] != wave_index
                    or observation["observed_at_ns"] != observed_now
                ):
                    raise ContractError("active thermal observation identity mismatch")
                if (
                    observation["temperature_millicelsius"]
                    >= THERMAL_STOP_MILLICELSIUS
                    and allocation_id not in thermally_stopped
                ):
                    stop = stop_overheated(handle, observation)
                    validate_thermal_stop(
                        stop,
                        observation=observation,
                        session_id=handle.session_id,
                        unit_prefix="axeyum-smtcomp-e3",
                    )
                    thermal_stops.append(stop)
                    thermally_stopped.add(allocation_id)
                    thermal_failed = True
            last_thermal_ns = observed_now
        wait()

    ordered_terminals = [
        terminals[allocation_id]
        for allocation_id in wave["allocation_ids"]
        if allocation_id in terminals
    ]
    all_completed = (
        not launch_failed
        and not thermal_failed
        and len(ordered_terminals) == len(wave["allocation_ids"])
        and all(row["status"] == "completed" for row in ordered_terminals)
    )
    checkpoint = None
    if all_completed:
        checkpoint = build_wave_checkpoint(
            schedule=schedule,
            plan_sha256=plan_sha256,
            run_identity_sha256=run_identity_sha256,
            cell_id=cell_id,
            wave_index=wave_index,
            allocation_terminals=ordered_terminals,
            cumulative_records=sum(
                row["benchmark_count"] for row in schedule["waves"][: wave_index + 1]
            ),
        )
    status = (
        "wave-completed-paused"
        if all_completed and pause_seen
        else "wave-completed"
        if all_completed
        else "cell-stopped"
    )
    return _sealed(
        {
            "schema": WAVE_OUTCOME_SCHEMA,
            "status": status,
            "scheduler_decision_sha256": decision["record_sha256"],
            "wave_index": wave_index,
            "launched_allocation_ids": launched_ids,
            "allocation_terminals": ordered_terminals,
            "thermal_stop_record_sha256s": [
                stop["record_sha256"] for stop in thermal_stops
            ],
            "active_thermal_observation_sha256s": active_thermal_ids,
            "checkpoint": checkpoint,
            "pause_observed": pause_seen,
        }
    )
