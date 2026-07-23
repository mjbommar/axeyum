"""Fixture gates for the credited SMT-COMP full-population contracts."""

from __future__ import annotations

import copy
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SMTCOMP = ROOT / "scripts" / "smtcomp_repro"
sys.path.insert(0, str(SMTCOMP))

from full_population import (  # noqa: E402
    HOST_IDS,
    INITIAL_ALLOCATION_COUNT,
    POPULATION_COUNT,
    RETRY_ALLOCATION_COUNT,
    SHARD_COUNT,
    SOLVER_IDS,
    WAVE_COUNT,
    build_population_contract,
    build_schedule,
    shard_benchmark_count,
    validate_population_contract,
    validate_schedule,
)
from multi_host import (  # noqa: E402
    PLAN_SCHEMA,
    REGISTRATION_SCHEMA,
    TRANSPORT,
    validate_plan,
)
from resource_enforcement import MULTI_HOST_KIND  # noqa: E402
from resume_contract import ContractError, digest  # noqa: E402


ENFORCEMENT_ID = "e" * 64


def reseal(value: dict) -> dict:
    result = copy.deepcopy(value)
    result.pop("record_sha256", None)
    result["record_sha256"] = digest(result)
    return result


def seal_as(value: dict, field: str) -> dict:
    result = copy.deepcopy(value)
    result.pop(field, None)
    result[field] = digest(result)
    return result


class FullPopulationContractTests(unittest.TestCase):
    def test_population_is_identical_for_all_three_cells(self) -> None:
        contract = validate_population_contract(build_population_contract())
        self.assertEqual(contract["population_count"], POPULATION_COUNT)
        self.assertEqual(
            [cell["solver_id"] for cell in contract["cells"]], list(SOLVER_IDS)
        )
        identities = {
            (
                cell["population_count"],
                cell["full_list_sha256"],
                cell["full_manifest_sha256"],
            )
            for cell in contract["cells"]
        }
        self.assertEqual(len(identities), 1)

    def test_population_mutations_reject_even_when_resealed(self) -> None:
        for label, mutate in (
            ("count", lambda row: row.__setitem__("population_count", 45_904)),
            ("list", lambda row: row.__setitem__("full_list_sha256", "0" * 64)),
            (
                "manifest",
                lambda row: row["cells"][2].__setitem__(
                    "full_manifest_sha256", "1" * 64
                ),
            ),
            ("order", lambda row: row["cells"].reverse()),
            ("subset", lambda row: row["cells"].pop()),
        ):
            with self.subTest(label=label):
                mutated = build_population_contract()
                mutate(mutated)
                with self.assertRaises(ContractError):
                    validate_population_contract(reseal(mutated))

    def test_schedule_partitions_all_shards_into_sixteen_host_distinct_waves(self) -> None:
        schedule = validate_schedule(build_schedule(ENFORCEMENT_ID))
        allocations = schedule["allocations"]
        initial = allocations[:INITIAL_ALLOCATION_COUNT]
        retries = allocations[INITIAL_ALLOCATION_COUNT:]
        self.assertEqual(len(initial), INITIAL_ALLOCATION_COUNT)
        self.assertEqual(len(retries), RETRY_ALLOCATION_COUNT)
        self.assertEqual(len(schedule["waves"]), WAVE_COUNT)
        self.assertEqual(
            sorted(shard for row in initial for shard in row["shard_ids"]),
            list(range(SHARD_COUNT)),
        )
        self.assertEqual(
            sum(shard_benchmark_count(shard) for shard in range(SHARD_COUNT)),
            POPULATION_COUNT,
        )
        for wave_index, wave in enumerate(schedule["waves"]):
            self.assertEqual(wave["wave_index"], wave_index)
            self.assertEqual(wave["host_ids"], list(HOST_IDS))
            self.assertEqual(len(wave["allocation_ids"]), 3)
            self.assertEqual(len(wave["shard_ids"]), 6)
            self.assertEqual(
                wave["benchmark_count"],
                sum(shard_benchmark_count(shard) for shard in wave["shard_ids"]),
            )

    def test_every_shard_has_one_different_host_retry(self) -> None:
        allocations = build_schedule(ENFORCEMENT_ID)["allocations"]
        initial = {
            row["allocation_id"]: row
            for row in allocations
            if row["generation"] == 0
        }
        retries = [row for row in allocations if row["generation"] == 1]
        self.assertEqual(
            sorted(row["shard_ids"][0] for row in retries), list(range(SHARD_COUNT))
        )
        for retry in retries:
            owner = initial[retry["recovers_allocation_id"]]
            self.assertIn(retry["shard_ids"][0], owner["shard_ids"])
            self.assertNotEqual(retry["host_id"], owner["host_id"])

    def test_schedule_is_accepted_by_generic_multi_host_partition_gate(self) -> None:
        filesystem_id = "f" * 64
        environment_id = "d" * 64
        registrations = [
            reseal(
                {
                    "schema": REGISTRATION_SCHEMA,
                    "host_id": host_id,
                    "ssh_target": host_id,
                    "hostname": f"server-{host_id}",
                    "kernel_release": "fixture-kernel",
                    "machine": "x86_64",
                    "python_version": "3.fixture",
                    "python_executable_sha256": "1" * 64,
                    "toolchain_identity_sha256": "2" * 64,
                    "cgroup_controllers": ["cpu", "io", "memory", "pids"],
                    "user_systemd_transient": True,
                    "shared_filesystem_class_sha256": filesystem_id,
                    "environment_class_sha256": environment_id,
                }
            )
            for host_id in HOST_IDS
        ]
        run = {
            "identity_sha256": "a" * 64,
            "identity": {"shard_count": SHARD_COUNT},
            "resource_enforcement": {
                "kind": MULTI_HOST_KIND,
                "enforcement_id": ENFORCEMENT_ID,
            },
        }
        plan = seal_as(
            {
                "schema": PLAN_SCHEMA,
                "run_identity_sha256": run["identity_sha256"],
                "transport": TRANSPORT,
                "shared_root": "/fixture/shared",
                "shared_filesystem_class_sha256": filesystem_id,
                "environment_class_sha256": environment_id,
                "host_registrations": registrations,
                "allocations": build_schedule(ENFORCEMENT_ID)["allocations"],
                "fault_injection": {"kind": "none"},
            },
            "plan_sha256",
        )
        validate_plan(plan, run, inspect_shared_root=False)

    def test_schedule_resource_and_topology_mutations_reject(self) -> None:
        for label, mutate in (
            (
                "workers",
                lambda row: row["resources"].__setitem__("workers_per_allocation", 3),
            ),
            (
                "memory",
                lambda row: row["resources"].__setitem__(
                    "aggregate_memory_bytes", 8 * 1024**3
                ),
            ),
            (
                "same-host retry",
                lambda row: row["allocations"][INITIAL_ALLOCATION_COUNT].__setitem__(
                    "host_id", "s5"
                ),
            ),
            (
                "wave order",
                lambda row: row["waves"][0]["allocation_ids"].reverse(),
            ),
            ("missing retry", lambda row: row["allocations"].pop()),
        ):
            with self.subTest(label=label):
                mutated = build_schedule(ENFORCEMENT_ID)
                mutate(mutated)
                with self.assertRaises(ContractError):
                    validate_schedule(reseal(mutated))

    def test_bad_enforcement_identity_rejects(self) -> None:
        with self.assertRaises(ContractError):
            build_schedule("not-a-sha")


if __name__ == "__main__":
    unittest.main()
