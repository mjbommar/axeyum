"""Execution-evidence gates for credited full-population cells."""

from __future__ import annotations

import copy
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts" / "smtcomp_repro"))

from full_execute import (  # noqa: E402
    load_wave_checkpoints,
    publish_wave_checkpoint,
)
from full_population import (  # noqa: E402
    build_schedule,
    build_wave_checkpoint,
    cumulative_benchmark_count,
)
from resume_contract import ContractError, digest  # noqa: E402


ENFORCEMENT_ID = "e" * 64
PLAN_ID = "a" * 64
RUN_ID = "b" * 64
CELL_ID = "axeyum"


def reseal(value: dict) -> dict:
    result = copy.deepcopy(value)
    result.pop("record_sha256", None)
    result["record_sha256"] = digest(result)
    return result


def checkpoint(schedule: dict, wave_index: int) -> dict:
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
        cell_id=CELL_ID,
        wave_index=wave_index,
        allocation_terminals=terminals,
        cumulative_records=cumulative_benchmark_count(schedule, wave_index),
    )


class FullExecutionCheckpointTests(unittest.TestCase):
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


if __name__ == "__main__":
    unittest.main()
