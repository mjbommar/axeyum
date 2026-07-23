"""Portable E2 descriptor and cgroup-controller validation gates."""

from __future__ import annotations

import os
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SMTCOMP = ROOT / "scripts" / "smtcomp_repro"
sys.path.insert(0, str(SMTCOMP))

from resume_contract import ContractError, canonical_bytes, digest  # noqa: E402
from resource_enforcement import (  # noqa: E402
    CGROUP_KIND,
    build_preflight,
    build_terminal,
    cgroup_enforcement,
    cgroup_snapshot,
    configure_current_cgroup,
    systemd_run_command,
    validate_enforcement,
    validate_resource_session,
    validate_snapshot,
)


class ResourceEnforcementTests(unittest.TestCase):
    def run_fixture(self, enforcement: dict, *, memory: int = 64 * 1024**2) -> dict:
        return {
            "identity": {
                "memory_limit_bytes": memory,
                "cores": 1,
                "shard_count": 4,
                "resource_enforcement_sha256": digest(enforcement),
            },
            "resource_enforcement": enforcement,
        }

    def test_descriptor_binds_exact_limits_and_rejects_memory_overcommit(self) -> None:
        enforcement = cgroup_enforcement(
            worker_slots=2,
            aggregate_memory_bytes=128 * 1024**2,
            aggregate_cpu_cores=2,
            pids_max=32,
        )
        self.assertEqual(validate_enforcement(self.run_fixture(enforcement))["kind"], CGROUP_KIND)

        overcommitted = dict(enforcement, aggregate_memory_bytes=127 * 1024**2)
        unsealed = dict(overcommitted)
        unsealed.pop("enforcement_id")
        overcommitted["enforcement_id"] = digest(unsealed)
        with self.assertRaisesRegex(ContractError, "memory budget overcommitted"):
            validate_enforcement(self.run_fixture(overcommitted))

    def test_descriptor_rejects_cpu_and_pid_overcommit(self) -> None:
        cpu = cgroup_enforcement(
            worker_slots=2,
            aggregate_memory_bytes=128 * 1024**2,
            aggregate_cpu_cores=1,
            pids_max=32,
        )
        with self.assertRaisesRegex(ContractError, "CPU budget overcommitted"):
            validate_enforcement(self.run_fixture(cpu))

        pids = cgroup_enforcement(
            worker_slots=2,
            aggregate_memory_bytes=128 * 1024**2,
            aggregate_cpu_cores=2,
            pids_max=8,
        )
        with self.assertRaisesRegex(ContractError, "PID budget"):
            validate_enforcement(self.run_fixture(pids))

    def test_fake_cgroup_snapshot_checks_membership_and_exact_controller_limits(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            proc_root = root / "proc"
            cgroup_root = root / "cgroup"
            relative = "/user.slice/axeyum-smtcomp-e2-session.service"
            directory = cgroup_root / relative.lstrip("/")
            (proc_root / "self").mkdir(parents=True)
            directory.mkdir(parents=True)
            (proc_root / "self" / "cgroup").write_text(
                f"0::{relative}\n", encoding="ascii"
            )
            files = {
                "cpu.max": "200000 100000\n",
                "cgroup.controllers": "cpu io memory pids\n",
                "cgroup.procs": f"{os.getpid()}\n",
                "cgroup.type": "domain\n",
                "memory.max": f"{128 * 1024**2}\n",
                "memory.swap.max": "0\n",
                "memory.oom.group": "1\n",
                "memory.peak": "8388608\n",
                "memory.events": "low 0\nhigh 0\nmax 0\noom 0\noom_kill 0\n",
                "cpu.stat": "usage_usec 100\nuser_usec 60\nsystem_usec 40\n",
                "pids.max": "32\n",
                "pids.current": "1\n",
                "pids.peak": "3\n",
                "pids.events": "max 0\n",
            }
            for name, value in files.items():
                (directory / name).write_text(value, encoding="ascii")

            snapshot = cgroup_snapshot(proc_root=proc_root, cgroup_root=cgroup_root)
            enforcement = cgroup_enforcement(
                worker_slots=2,
                aggregate_memory_bytes=128 * 1024**2,
                aggregate_cpu_cores=2,
                pids_max=32,
            )
            validate_snapshot(snapshot, enforcement, session_id="session")
            snapshot["memory_max_bytes"] -= 1
            with self.assertRaisesRegex(ContractError, "memory_max_bytes"):
                validate_snapshot(snapshot, enforcement, session_id="session")

            snapshot["memory_max_bytes"] += 1
            oom_group = directory / "memory.oom.group"
            oom_group.write_text("0\n", encoding="ascii")
            with self.assertRaisesRegex(ContractError, "unit identity"):
                configure_current_cgroup(
                    enforcement,
                    session_id="other-session",
                    proc_root=proc_root,
                    cgroup_root=cgroup_root,
                )
            self.assertEqual(oom_group.read_text(encoding="ascii"), "0\n")
            configure_current_cgroup(
                enforcement,
                session_id="session",
                proc_root=proc_root,
                cgroup_root=cgroup_root,
            )
            self.assertEqual(oom_group.read_text(encoding="ascii"), "1")

    def test_systemd_command_places_the_whole_host_run_under_exact_properties(self) -> None:
        enforcement = cgroup_enforcement(
            worker_slots=2,
            aggregate_memory_bytes=128 * 1024**2,
            aggregate_cpu_cores=2,
            pids_max=32,
        )
        command = systemd_run_command(
            enforcement=enforcement,
            session_id="session",
            command=["/bin/true"],
        )
        self.assertIn("--property=KillMode=control-group", command)
        self.assertIn(f"--property=MemoryMax={128 * 1024**2}", command)
        self.assertIn("--property=MemorySwapMax=0", command)
        self.assertIn("--property=CPUQuota=200%", command)
        self.assertIn("--property=TasksMax=32", command)
        self.assertEqual(command[-1], "/bin/true")

    def test_closed_resource_session_validates_exact_failed_terminal(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            enforcement = cgroup_enforcement(
                worker_slots=1,
                aggregate_memory_bytes=64 * 1024**2,
                aggregate_cpu_cores=1,
                pids_max=32,
            )
            environment = "e" * 64
            run = {
                "identity_sha256": "a" * 64,
                "identity": {
                    "memory_limit_bytes": 64 * 1024**2,
                    "cores": 1,
                    "shard_count": 1,
                    "environment_class_sha256": environment,
                    "resource_enforcement_sha256": digest(enforcement),
                },
                "resource_enforcement": enforcement,
            }
            session_id = "failed-session"
            unit = f"{enforcement['unit_prefix']}-{session_id}.service"
            snapshot = {
                "cgroup_path": f"/user.slice/{unit}",
                "cgroup_inode": 1,
                "controllers": ["cpu", "memory", "pids"],
                "cgroup_type": "domain",
                "memory_max_bytes": 64 * 1024**2,
                "memory_swap_max_bytes": 0,
                "memory_oom_group": 1,
                "memory_peak_bytes": 1024,
                "memory_events": {"oom": 0, "oom_kill": 0},
                "cpu_quota_usec": 100_000,
                "cpu_period_usec": 100_000,
                "cpu_stat": {"usage_usec": 1},
                "pids_max": 32,
                "pids_current": 1,
                "pids_peak": 1,
                "pids_events": {"max": 0},
                "member_pids": [os.getpid()],
            }
            preflight = build_preflight(
                run=run,
                session_id=session_id,
                environment_class_sha256=environment,
                snapshot=snapshot,
                shard_ids=[0],
            )
            final_snapshot = dict(
                snapshot,
                memory_peak_bytes=2048,
                pids_peak=2,
                cpu_stat={"usage_usec": 2},
            )
            terminal = build_terminal(
                preflight=preflight,
                final_snapshot=final_snapshot,
                enforcement=enforcement,
                worker_exit_codes=[2],
            )
            session = root / "resource-sessions" / session_id
            session.mkdir(parents=True)
            session.joinpath("preflight.json").write_bytes(
                canonical_bytes(preflight)
            )
            session.joinpath("terminal.json").write_bytes(
                canonical_bytes(terminal)
            )

            observed = validate_resource_session(
                run_dir=root,
                run=run,
                session_id=session_id,
                expected_status="failed",
            )
            self.assertEqual(observed, (preflight, terminal))
            with self.assertRaisesRegex(ContractError, "status mismatch"):
                validate_resource_session(
                    run_dir=root,
                    run=run,
                    session_id=session_id,
                    expected_status="completed",
                )


if __name__ == "__main__":
    unittest.main()
