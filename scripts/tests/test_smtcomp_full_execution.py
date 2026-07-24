"""Execution-evidence gates for credited full-population cells."""

from __future__ import annotations

import copy
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts" / "smtcomp_repro"))

from full_execute import (  # noqa: E402
    load_wave_checkpoints,
    publish_wave_checkpoint,
    supervise_admitted_wave,
)
import full_execute as full_execute_module  # noqa: E402
from full_coordinator import derive_full_execution_authority  # noqa: E402
import full_coordinator as full_coordinator_module  # noqa: E402
from full_population import (  # noqa: E402
    WAVE_COUNT,
    build_schedule,
    build_wave_checkpoint,
    cumulative_benchmark_count,
)
from full_result import CELL_RESULT_SCHEMA, publish_full_cell_result  # noqa: E402
from multi_host import (  # noqa: E402
    COMPLETION_SCHEMA as MULTI_HOST_COMPLETION_SCHEMA,
    build_allocation_scheduler_state,
)
from resource_enforcement import COMPLETION_SCHEMA as RESOURCE_COMPLETION_SCHEMA  # noqa: E402
from resume_contract import ContractError, canonical_bytes, digest  # noqa: E402


ENFORCEMENT_ID = "e" * 64
PLAN_ID = "a" * 64
RUN_ID = "b" * 64
CELL_ID = "axeyum"


def reseal(value: dict) -> dict:
    result = copy.deepcopy(value)
    result.pop("record_sha256", None)
    result["record_sha256"] = digest(result)
    return result


def checkpoint(schedule: dict, wave_index: int, *, cell_id: str = CELL_ID) -> dict:
    terminals = [
        {
            "allocation_id": allocation_id,
            "attempt_id": f"attempt-{wave_index:02d}-{position}",
            "status": "completed",
            "terminal_record_sha256": f"{wave_index * 3 + position:064x}",
        }
        for position, allocation_id in enumerate(
            schedule["waves"][wave_index]["allocation_ids"]
        )
    ]
    return build_wave_checkpoint(
        schedule=schedule,
        plan_sha256=PLAN_ID,
        run_identity_sha256=RUN_ID,
        cell_id=cell_id,
        wave_index=wave_index,
        allocation_terminals=terminals,
        cumulative_records=cumulative_benchmark_count(schedule, wave_index),
    )


def cell_records(solver_id: str, *, first_status: str = "sat") -> list[dict]:
    return [
        reseal(
            {
                "solver_id": solver_id,
                "sequence": 0,
                "benchmark_id": "QF_BV/fixture/a.smt2",
                "benchmark_sha256": "1" * 64,
                "expected_status": "sat",
                "reported_status": first_status,
                "termination_class": "completed",
            }
        ),
        reseal(
            {
                "solver_id": solver_id,
                "sequence": 1,
                "benchmark_id": "QF_UF/fixture/b.smt2",
                "benchmark_sha256": "2" * 64,
                "expected_status": None,
                "reported_status": "unknown",
                "termination_class": "completed",
            }
        ),
    ]


def completion_records(
    *, run_id: str = RUN_ID, plan_id: str = PLAN_ID, canonical_bundle: str = "c" * 64
) -> tuple[dict, dict]:
    resource = reseal(
        {
            "schema": RESOURCE_COMPLETION_SCHEMA,
            "run_identity_sha256": run_id,
            "enforcement_id": ENFORCEMENT_ID,
            "session_ids": ["session-0"],
            "terminal_session_ids": ["session-0"],
            "unclosed_session_ids": [],
            "observed_peak_memory_bytes": 1024,
            "completed_at_ns": 100,
        }
    )
    multi = reseal(
        {
            "schema": MULTI_HOST_COMPLETION_SCHEMA,
            "plan_sha256": plan_id,
            "run_identity_sha256": run_id,
            "allocation_attempt_ids": ["attempt-0"],
            "unclosed_allocation_attempt_ids": [],
            "recovery_record_sha256s": [],
            "resource_session_ids": ["session-0"],
            "canonical_bundle_sha256": canonical_bundle,
            "resource_completion_sha256": resource["record_sha256"],
            "fault_record_sha256": None,
            "completed_at_ns": 200,
        }
    )
    return resource, multi


def checkpoint_material(
    schedule: dict, *, cell_id: str
) -> tuple[list[dict], list[dict]]:
    checkpoints = [
        checkpoint(schedule, wave_index, cell_id=cell_id)
        for wave_index in range(WAVE_COUNT)
    ]
    terminal_by_hash = {}
    for row in checkpoints:
        for shard in row["shard_completions"]:
            terminal_by_hash.setdefault(
                shard["terminal_record_sha256"],
                {
                    "allocation_id": shard["allocation_id"],
                    "attempt_id": shard["attempt_id"],
                    "status": shard["status"],
                    "terminal_record_sha256": shard[
                        "terminal_record_sha256"
                    ],
                },
            )
    return checkpoints, list(terminal_by_hash.values())


def prior_completion(solver_id: str) -> dict:
    return reseal(
        {
            "schema": CELL_RESULT_SCHEMA,
            "fixture_only": True,
            "solver_id": solver_id,
            "preparation_record_sha256": "d" * 64,
            "selection_record_sha256": "e" * 64,
            "execution_authority_record_sha256": "3" * 64,
            "execution_authority_file_sha256": "4" * 64,
            "adjudication_record_sha256": "5" * 64,
            "adjudication_file_sha256": "6" * 64,
            "records_file_sha256": "7" * 64,
            "population_count": 2,
            "key_set_sha256": "8" * 64,
            "record_set_sha256": "9" * 64,
            "safe_to_continue": True,
            "published_at_ns": 300,
        }
    )


class FullExecutionCheckpointTests(unittest.TestCase):
    def test_admitted_entrypoint_derives_identities_and_persists_checkpoint(
        self,
    ) -> None:
        schedule = build_schedule(ENFORCEMENT_ID)
        first = checkpoint(schedule, 0)
        with tempfile.TemporaryDirectory() as temp:
            attempt = Path(temp) / "attempt"
            inputs = attempt / "inputs"
            run_dir = attempt / "cells" / CELL_ID
            inputs.mkdir(parents=True)
            run_dir.mkdir(parents=True)
            run_path = inputs / "axeyum-run.json"
            plan_path = run_dir / "multi-host-plan.json"
            schedule_path = run_dir / "full-schedule.json"
            run_path.write_bytes(canonical_bytes({"identity_sha256": RUN_ID}))
            plan_path.write_bytes(canonical_bytes({"plan_sha256": PLAN_ID}))
            schedule_path.write_bytes(canonical_bytes(schedule))
            composition = {
                "cells": [
                    {
                        "solver_id": CELL_ID,
                        "run_manifest_path": str(run_path),
                        "plan_path": str(plan_path),
                        "schedule_path": str(schedule_path),
                    }
                ]
            }
            (inputs / "full-cell-composition.json").write_bytes(
                canonical_bytes(composition)
            )
            admission = {
                "solver_id": CELL_ID,
                "run_identity_sha256": RUN_ID,
                "plan_sha256": PLAN_ID,
                "schedule_record_sha256": schedule["record_sha256"],
            }
            outcome = {"status": "wave-completed", "checkpoint": first}
            allocation_ids = {
                row["allocation_id"] for row in schedule["allocations"]
            }
            allocation_state = build_allocation_scheduler_state(
                plan_sha256=PLAN_ID,
                run_identity_sha256=RUN_ID,
                cell_id=CELL_ID,
                allocation_ids=allocation_ids,
                allocation_attempts=[],
            )
            unused = mock.Mock(side_effect=AssertionError("unexpected callback"))
            with (
                mock.patch(
                    "full_admission.validate_full_cell_admission",
                    return_value=admission,
                ) as validate_admission,
                mock.patch.object(
                    full_execute_module,
                    "derive_allocation_scheduler_state",
                    return_value=allocation_state,
                ) as derive_state,
                mock.patch.object(
                    full_execute_module,
                    "supervise_one_wave",
                    return_value=outcome,
                ) as supervise,
            ):
                observed = supervise_admitted_wave(
                    admission,
                    preparation_root=attempt,
                    repository_root=ROOT,
                    expected_logic_counts={"QF_BV": 1, "QF_UF": 1},
                    prior_result_roots={},
                    acceptance={"fixture": True},
                    inspect_shared_root=False,
                    cooldown_required=False,
                    prewave_thermal_observations=[],
                    launch=unused,
                    poll_terminal=unused,
                    observe_active=unused,
                    stop_overheated=unused,
                    now_ns=unused,
                    wait=unused,
                    pause_requested=unused,
                )
            self.assertEqual(observed, outcome)
            validate_admission.assert_called_once()
            derive_state.assert_called_once()
            self.assertEqual(supervise.call_args.kwargs["schedule"], schedule)
            self.assertEqual(supervise.call_args.kwargs["checkpoints"], [])
            self.assertEqual(
                supervise.call_args.kwargs["allocation_scheduler_state"],
                allocation_state,
            )
            self.assertEqual(
                load_wave_checkpoints(
                    run_dir,
                    schedule=schedule,
                    plan_sha256=PLAN_ID,
                    run_identity_sha256=RUN_ID,
                    cell_id=CELL_ID,
                ),
                [first],
            )

            blocked_state = build_allocation_scheduler_state(
                plan_sha256=PLAN_ID,
                run_identity_sha256=RUN_ID,
                cell_id=CELL_ID,
                allocation_ids=allocation_ids,
                allocation_attempts=[
                    {
                        "allocation_id": "full-initial-00",
                        "attempt_id": "unclosed-attempt",
                        "attempt_record_sha256": "e" * 64,
                        "terminal_status": None,
                        "terminal_record_sha256": None,
                    }
                ],
            )
            launch = mock.Mock()
            with (
                mock.patch(
                    "full_admission.validate_full_cell_admission",
                    return_value=admission,
                ),
                mock.patch.object(
                    full_execute_module,
                    "derive_allocation_scheduler_state",
                    return_value=blocked_state,
                ),
            ):
                blocked = supervise_admitted_wave(
                    admission,
                    preparation_root=attempt,
                    repository_root=ROOT,
                    expected_logic_counts={},
                    prior_result_roots={},
                    inspect_shared_root=False,
                    cooldown_required=False,
                    prewave_thermal_observations=[],
                    launch=launch,
                    poll_terminal=unused,
                    observe_active=unused,
                    stop_overheated=unused,
                    now_ns=lambda: 2000,
                    wait=unused,
                    pause_requested=lambda: False,
                )
            self.assertEqual(blocked["status"], "blocked-unclosed")
            launch.assert_not_called()

            drifted = copy.deepcopy(admission)
            drifted["schedule_record_sha256"] = "0" * 64
            with (
                mock.patch(
                    "full_admission.validate_full_cell_admission",
                    return_value=drifted,
                ),
                self.assertRaisesRegex(ContractError, "identity drift"),
            ):
                supervise_admitted_wave(
                    drifted,
                    preparation_root=attempt,
                    repository_root=ROOT,
                    expected_logic_counts={},
                    prior_result_roots={},
                    inspect_shared_root=False,
                    cooldown_required=False,
                    prewave_thermal_observations=[],
                    launch=unused,
                    poll_terminal=unused,
                    observe_active=unused,
                    stop_overheated=unused,
                    now_ns=unused,
                    wait=unused,
                    pause_requested=unused,
                )

    def test_checkpoint_publication_is_contiguous_immutable_and_replayable(self) -> None:
        schedule = build_schedule(ENFORCEMENT_ID)
        first = checkpoint(schedule, 0)
        second = checkpoint(schedule, 1)
        with tempfile.TemporaryDirectory() as temp:
            run_dir = Path(temp) / "run"
            self.assertEqual(
                publish_wave_checkpoint(
                    run_dir,
                    checkpoint=first,
                    schedule=schedule,
                    plan_sha256=PLAN_ID,
                    run_identity_sha256=RUN_ID,
                    cell_id=CELL_ID,
                ),
                first,
            )
            self.assertEqual(
                publish_wave_checkpoint(
                    run_dir,
                    checkpoint=first,
                    schedule=schedule,
                    plan_sha256=PLAN_ID,
                    run_identity_sha256=RUN_ID,
                    cell_id=CELL_ID,
                ),
                first,
            )
            with self.assertRaisesRegex(ContractError, "next exact wave"):
                publish_wave_checkpoint(
                    run_dir,
                    checkpoint=checkpoint(schedule, 2),
                    schedule=schedule,
                    plan_sha256=PLAN_ID,
                    run_identity_sha256=RUN_ID,
                    cell_id=CELL_ID,
                )
            mutated = copy.deepcopy(first)
            mutated["shard_completions"][0]["attempt_id"] = "replacement"
            with self.assertRaisesRegex(ContractError, "conflicts"):
                publish_wave_checkpoint(
                    run_dir,
                    checkpoint=reseal(mutated),
                    schedule=schedule,
                    plan_sha256=PLAN_ID,
                    run_identity_sha256=RUN_ID,
                    cell_id=CELL_ID,
                )
            publish_wave_checkpoint(
                run_dir,
                checkpoint=second,
                schedule=schedule,
                plan_sha256=PLAN_ID,
                run_identity_sha256=RUN_ID,
                cell_id=CELL_ID,
            )
            self.assertEqual(
                load_wave_checkpoints(
                    run_dir,
                    schedule=schedule,
                    plan_sha256=PLAN_ID,
                    run_identity_sha256=RUN_ID,
                    cell_id=CELL_ID,
                ),
                [first, second],
            )

    def test_interrupted_checkpoint_is_quarantined_before_exact_retry(self) -> None:
        schedule = build_schedule(ENFORCEMENT_ID)
        first = checkpoint(schedule, 0)
        with tempfile.TemporaryDirectory() as temp:
            run_dir = Path(temp) / "run"

            def interrupt(phase: str) -> None:
                if phase == "after_temp_fsync":
                    raise RuntimeError("fixture interruption")

            with self.assertRaisesRegex(RuntimeError, "fixture interruption"):
                publish_wave_checkpoint(
                    run_dir,
                    checkpoint=first,
                    schedule=schedule,
                    plan_sha256=PLAN_ID,
                    run_identity_sha256=RUN_ID,
                    cell_id=CELL_ID,
                    phase_hook=interrupt,
                )
            self.assertFalse(
                (run_dir / "full-wave-checkpoints" / "wave-00.json").exists()
            )
            self.assertEqual(
                publish_wave_checkpoint(
                    run_dir,
                    checkpoint=first,
                    schedule=schedule,
                    plan_sha256=PLAN_ID,
                    run_identity_sha256=RUN_ID,
                    cell_id=CELL_ID,
                ),
                first,
            )
            orphans = list((run_dir / "quarantine" / "orphans").iterdir())
            self.assertEqual(len(orphans), 1)

    def test_extra_checkpoint_artifact_rejects_replay(self) -> None:
        schedule = build_schedule(ENFORCEMENT_ID)
        with tempfile.TemporaryDirectory() as temp:
            run_dir = Path(temp) / "run"
            publish_wave_checkpoint(
                run_dir,
                checkpoint=checkpoint(schedule, 0),
                schedule=schedule,
                plan_sha256=PLAN_ID,
                run_identity_sha256=RUN_ID,
                cell_id=CELL_ID,
            )
            extra = run_dir / "full-wave-checkpoints" / "unexpected.json"
            extra.write_bytes(b"{}\n")
            with self.assertRaisesRegex(ContractError, "not contiguous"):
                load_wave_checkpoints(
                    run_dir,
                    schedule=schedule,
                    plan_sha256=PLAN_ID,
                    run_identity_sha256=RUN_ID,
                    cell_id=CELL_ID,
                )


class FullExecutionAuthorityTests(unittest.TestCase):
    def authority(
        self,
        solver_id: str,
        records: list[dict],
        *,
        prior: list[tuple[dict, list[dict]]] | None = None,
    ) -> dict:
        schedule = build_schedule(ENFORCEMENT_ID)
        checkpoints, terminals = checkpoint_material(schedule, cell_id=solver_id)
        resource, multi = completion_records()
        return derive_full_execution_authority(
            solver_id=solver_id,
            fixture_only=True,
            preparation_record_sha256="d" * 64,
            selection_record_sha256="e" * 64,
            run_identity_sha256=RUN_ID,
            plan_sha256=PLAN_ID,
            schedule=schedule,
            checkpoints=checkpoints,
            records=records,
            terminal_evidence=terminals,
            resource_completion=resource,
            multi_host_completion=multi,
            canonical_bundle_sha256="c" * 64,
            expected_logic_counts={"QF_BV": 1, "QF_UF": 1},
            prior_cell_results=[] if prior is None else prior,
        )

    def test_authority_derives_all_sixteen_checkpoints_and_exact_terminals(self) -> None:
        authority = self.authority("axeyum", cell_records("axeyum"))
        self.assertEqual(len(authority["wave_checkpoint_record_sha256s"]), 16)
        self.assertEqual(authority["population_count"], 2)
        self.assertEqual(authority["prior_cell_result_record_sha256s"], [])
        self.assertEqual(authority["cross_solver_disagreement_count"], 0)

    def test_missing_or_reassigned_terminal_blocks_authority(self) -> None:
        schedule = build_schedule(ENFORCEMENT_ID)
        checkpoints, terminals = checkpoint_material(schedule, cell_id="axeyum")
        resource, multi = completion_records()
        common = {
            "solver_id": "axeyum",
            "fixture_only": True,
            "preparation_record_sha256": "d" * 64,
            "selection_record_sha256": "e" * 64,
            "run_identity_sha256": RUN_ID,
            "plan_sha256": PLAN_ID,
            "schedule": schedule,
            "checkpoints": checkpoints,
            "records": cell_records("axeyum"),
            "resource_completion": resource,
            "multi_host_completion": multi,
            "canonical_bundle_sha256": "c" * 64,
            "expected_logic_counts": {"QF_BV": 1, "QF_UF": 1},
            "prior_cell_results": [],
        }
        with self.assertRaisesRegex(ContractError, "exact terminal evidence"):
            derive_full_execution_authority(
                **common, terminal_evidence=terminals[1:]
            )
        reassigned = copy.deepcopy(terminals)
        reassigned[0]["allocation_id"] = "full-initial-01"
        with self.assertRaisesRegex(ContractError, "exact terminal evidence"):
            derive_full_execution_authority(
                **common, terminal_evidence=reassigned
            )
        extra = [
            *terminals,
            {
                "allocation_id": "full-retry-00",
                "attempt_id": "unreferenced-completed",
                "status": "completed",
                "terminal_record_sha256": "f" * 64,
            },
        ]
        with self.assertRaisesRegex(ContractError, "accounting drift"):
            derive_full_execution_authority(**common, terminal_evidence=extra)

    def test_prior_cell_population_and_disagreement_are_recomputed(self) -> None:
        axeyum_records = cell_records("axeyum", first_status="sat")
        cvc5_records = cell_records("cvc5", first_status="unsat")
        authority = self.authority(
            "cvc5",
            cvc5_records,
            prior=[(prior_completion("axeyum"), axeyum_records)],
        )
        self.assertEqual(
            authority["prior_cell_result_record_sha256s"],
            [prior_completion("axeyum")["record_sha256"]],
        )
        self.assertEqual(authority["cross_solver_disagreement_count"], 1)
        with tempfile.TemporaryDirectory() as temp:
            completion = publish_full_cell_result(
                Path(temp) / "cvc5-result",
                records=cvc5_records,
                execution_authority=authority,
                expected_logic_counts={"QF_BV": 1, "QF_UF": 1},
                published_at_ns=300,
            )
        self.assertFalse(completion["safe_to_continue"])

        drifted = copy.deepcopy(axeyum_records)
        drifted.pop()
        with self.assertRaises(ContractError):
            self.authority(
                "cvc5",
                cvc5_records,
                prior=[(prior_completion("axeyum"), drifted)],
            )

    def test_publication_entrypoint_replays_execution_before_result_install(self) -> None:
        authority = {"record_sha256": "a" * 64}
        records = cell_records("axeyum")
        published = {"record_sha256": "b" * 64}
        with (
            mock.patch.object(
                full_coordinator_module,
                "load_full_execution_authority",
                return_value=(authority, records),
            ) as load,
            mock.patch.object(
                full_coordinator_module,
                "publish_full_cell_result",
                return_value=published,
            ) as publish,
        ):
            observed = (
                full_coordinator_module.publish_full_cell_result_from_execution(
                    Path("/fixture/preparation"),
                    Path("/fixture/result"),
                    repository_root=ROOT,
                    solver_id="axeyum",
                    expected_logic_counts={"QF_BV": 1, "QF_UF": 1},
                    prior_result_roots={},
                    inspect_shared_root=False,
                    published_at_ns=1000,
                )
            )
        self.assertEqual(observed, published)
        load.assert_called_once()
        self.assertEqual(publish.call_args.kwargs["execution_authority"], authority)
        self.assertEqual(publish.call_args.kwargs["records"], records)


if __name__ == "__main__":
    unittest.main()
