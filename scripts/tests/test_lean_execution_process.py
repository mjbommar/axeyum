from __future__ import annotations

import copy
import json
import os
import re
import subprocess
import tempfile
import unittest
from pathlib import Path

from scripts import lean_execution_process as PROCESS


class LeanExecutionProcessContractTests(unittest.TestCase):
    def test_registered_specs_are_canonical_exact_and_zero_credit(self) -> None:
        self.assertEqual(len(PROCESS.CONTROL_IDS), 8)
        for control_id in PROCESS.CONTROL_IDS:
            with self.subTest(control_id=control_id):
                spec = PROCESS.build_control_spec(control_id)
                self.assertEqual(PROCESS.validate_spec(spec), spec)
                self.assertEqual(spec["assigned_case_ids"], [])
                self.assertEqual(spec["credit_class"], "synthetic-no-credit")
                self.assertTrue(Path(spec["command"][0]).is_absolute())
                self.assertNotIsInstance(spec["command"], str)

    def test_spec_reader_rejects_noncanonical_and_hash_drift(self) -> None:
        spec = PROCESS.build_control_spec("exit-zero-4g")
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "spec.json"
            path.write_text(json.dumps(spec, indent=2) + "\n", encoding="utf-8")
            with self.assertRaisesRegex(PROCESS.ProcessEvidenceError, "not canonical"):
                PROCESS.read_canonical_spec(path)
            path.write_bytes(PROCESS.canonical_bytes(spec))
            self.assertEqual(PROCESS.read_canonical_spec(path), spec)
            changed = copy.deepcopy(spec)
            changed["wall_timeout_ms"] += 1
            path.write_bytes(PROCESS.canonical_bytes(changed))
            with self.assertRaisesRegex(PROCESS.ProcessEvidenceError, "hash drift"):
                PROCESS.read_canonical_spec(path)

    def test_mutated_lane_command_environment_source_and_credit_reject(self) -> None:
        base = PROCESS.build_control_spec("exit-zero-4g")
        mutations = []
        for field, value in (
            ("lane_id", "official-export-8g"),
            ("command", "shell command"),
            ("environment", {}),
            ("credit_class", "native-parity"),
            ("working_directory", "/tmp"),
        ):
            changed = copy.deepcopy(base)
            changed[field] = value
            mutations.append(PROCESS._seal_spec(changed))
        changed = copy.deepcopy(base)
        changed["source_files"][0]["sha256"] = "0" * 64
        mutations.append(PROCESS._seal_spec(changed))
        for changed in mutations:
            with self.subTest(field_diff=set(key for key in changed if changed[key] != base[key])):
                with self.assertRaises(PROCESS.ProcessEvidenceError):
                    PROCESS.validate_spec(changed)

    def test_memory_evidence_mutations_cannot_self_certify(self) -> None:
        spec = PROCESS.build_control_spec("memory-limit-4g")
        evidence = spec["cooperative_memory_evidence"]
        assert evidence is not None
        marker = (evidence["marker"] + "\n").encode()
        self.assertTrue(PROCESS._cooperative_memory_matches(spec, 86, marker))
        self.assertFalse(PROCESS._cooperative_memory_matches(spec, 137, marker))
        self.assertFalse(PROCESS._cooperative_memory_matches(spec, 86, b"MemoryError\n"))
        self.assertFalse(PROCESS._cooperative_memory_matches(spec, 86, marker + marker))
        changed = copy.deepcopy(spec)
        changed["cooperative_memory_evidence"]["mapping_bytes"] = evidence["limit_bytes"]
        changed = PROCESS._seal_spec(changed)
        with self.assertRaises(PROCESS.ProcessEvidenceError):
            PROCESS.validate_spec(changed)

    def test_run_spec_attribution_is_checkout_root_portable(self) -> None:
        for control_id in PROCESS.CONTROL_IDS:
            with self.subTest(control_id=control_id):
                spec = PROCESS.build_control_spec(control_id)
                retained_root = Path("/var/tmp/independent-axeyum-worktree")
                command = []
                for argument in spec["command"]:
                    try:
                        relative = Path(argument).relative_to(PROCESS.ROOT)
                    except ValueError:
                        command.append(argument)
                    else:
                        command.append(str(retained_root / relative))
                relative_cwd = Path(spec["working_directory"]).relative_to(PROCESS.ROOT)
                run = {
                    "command": command,
                    "working_directory": str(retained_root / relative_cwd),
                }
                self.assertTrue(PROCESS._run_matches_spec_attribution(run, spec))

                wrong_target = copy.deepcopy(run)
                wrong_target["command"][-2 if control_id.startswith("memory-limit-") else -1] = (
                    str(retained_root / "scripts/not_the_registered_probe.py")
                )
                self.assertFalse(
                    PROCESS._run_matches_spec_attribution(wrong_target, spec)
                )

                wrong_cwd = copy.deepcopy(run)
                wrong_cwd["working_directory"] += "-other"
                self.assertFalse(PROCESS._run_matches_spec_attribution(wrong_cwd, spec))

    def test_run_spec_attribution_keeps_external_executable_exact(self) -> None:
        spec = PROCESS.build_control_spec("exit-zero-4g")
        run = {
            "command": list(spec["command"]),
            "working_directory": spec["working_directory"],
        }
        run["command"][0] = "/usr/bin/not-the-recorded-python"
        self.assertFalse(PROCESS._run_matches_spec_attribution(run, spec))

    def test_historical_result_inputs_remain_immutable(self) -> None:
        authority = json.loads(PROCESS.RESULT_AUTHORITY.read_bytes())
        self.assertEqual(
            authority["source_inputs"], PROCESS.historical_result_source_inputs()
        )
        changed = copy.deepcopy(authority)
        changed["source_inputs"][1]["sha256"] = "0" * 64
        changed["authority_sha256"] = PROCESS.domain_digest(
            PROCESS.RESULT_SCHEMA,
            {
                key: value
                for key, value in changed.items()
                if key != "authority_sha256"
            },
        )
        self.assertTrue(PROCESS.validate_result_authority(changed))

    def test_result_builder_rejects_missing_or_partial_evidence(self) -> None:
        with tempfile.TemporaryDirectory(dir=PROCESS.ROOT) as temporary:
            with self.assertRaisesRegex(PROCESS.ProcessEvidenceError, "directory set"):
                PROCESS.build_result_authority(
                    Path(temporary), implementation_revision="0" * 40
                )


@unittest.skipUnless(os.name == "posix" and Path("/proc/self/status").is_file(), "Linux /proc required")
class LeanExecutionProcessLiveTests(unittest.TestCase):
    def _run(self, control_id: str, parent: Path, suffix: str = "") -> tuple[Path, dict]:
        directory = parent / f"{control_id}{suffix}"
        terminal = PROCESS.execute_spec(PROCESS.build_control_spec(control_id), directory)
        self.assertEqual(PROCESS.validate_attempt_directory(
            directory, expected_spec=PROCESS.build_control_spec(control_id)
        ), [])
        self.assertEqual(set(item.name for item in directory.iterdir()), {
            "run.json",
            "stdout.bin",
            "stderr.bin",
            "attempt-prelaunch.json",
            "attempt-terminal.json",
        })
        return directory, terminal

    def test_prelaunch_record_is_sealed_before_popen(self) -> None:
        observed = []

        def checked_popen(*args, **kwargs):
            cwd = Path(kwargs["cwd"])
            self.assertEqual(cwd, PROCESS.ROOT)
            # The output path is available from the raw file handles passed to Popen.
            output_directory = Path(kwargs["stdout"].name).parent
            prelaunch_path = output_directory / "attempt-prelaunch.json"
            self.assertTrue((output_directory / "run.json").is_file())
            raw = prelaunch_path.read_bytes()
            value = json.loads(raw)
            self.assertEqual(raw, PROCESS.canonical_bytes(value))
            self.assertTrue(value["recorded_before_launch"])
            self.assertIsNone(value["terminal"])
            observed.append(value["sha256"])
            return subprocess.Popen(*args, **kwargs)

        with tempfile.TemporaryDirectory() as temporary:
            terminal = PROCESS.execute_spec(
                PROCESS.build_control_spec("exit-zero-4g"),
                Path(temporary) / "attempt",
                popen_factory=checked_popen,
            )
        self.assertEqual(len(observed), 1)
        self.assertEqual(terminal["prelaunch_sha256"], observed[0])

    def test_all_eight_preregistered_controls(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            results = {}
            for control_id in PROCESS.CONTROL_IDS:
                _, results[control_id] = self._run(control_id, root)
        self.assertEqual(results["exit-zero-4g"]["terminal"]["exit_code"], 0)
        self.assertEqual(results["exit-seven-4g"]["terminal"]["exit_code"], 7)
        self.assertEqual(results["self-sigterm-4g"]["terminal"]["signal"], 15)
        timeout = results["wall-timeout-tree-4g"]
        self.assertTrue(timeout["process"]["watchdog_fired"])
        self.assertTrue(timeout["process"]["sigterm_sent"])
        self.assertTrue(timeout["process"]["sigkill_sent"])
        self.assertEqual(timeout["process"]["live_non_zombie_pids_after_cleanup"], [])
        for control_id in ("memory-limit-4g", "memory-limit-8g"):
            terminal = results[control_id]
            self.assertEqual(terminal["terminal"]["class"], "memory-limit")
            self.assertEqual(terminal["terminal"]["exit_code"], 86)
        self.assertEqual(
            results["invalid-interpreter-4g"]["diagnostic"]["kind"], "launch-failed"
        )
        self.assertEqual(
            results["missing-cwd-4g"]["diagnostic"]["kind"], "preflight-invalid"
        )

    def test_timeout_descendant_is_not_live(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            directory, terminal = self._run("wall-timeout-tree-4g", Path(temporary))
            stderr = (directory / "stderr.bin").read_text(encoding="ascii")
            match = re.search(r"AXEYUM_TL0_7_2_DESCENDANT_PID_V1=(\d+)", stderr)
            self.assertIsNotNone(match)
            descendant = int(match.group(1))
            stat_path = Path(f"/proc/{descendant}/stat")
            if stat_path.is_file():
                text = stat_path.read_text(encoding="ascii")
                state = text[text.rfind(")") + 2 :].split()[0]
                self.assertEqual(state, "Z")
            self.assertEqual(terminal["process"]["live_non_zombie_pids_after_cleanup"], [])

    def test_raw_tamper_extra_file_and_existing_directory_reject(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            directory, _ = self._run("exit-zero-4g", root)
            with (directory / "stderr.bin").open("ab") as handle:
                handle.write(b"tamper\n")
            failures = PROCESS.validate_attempt_directory(
                directory, expected_spec=PROCESS.build_control_spec("exit-zero-4g")
            )
            self.assertIn("raw artifact identity drift", failures)
            (directory / "completion.json").touch()
            failures = PROCESS.validate_attempt_directory(
                directory, expected_spec=PROCESS.build_control_spec("exit-zero-4g")
            )
            self.assertIn("attempt directory file set must be exact", failures)
            with self.assertRaisesRegex(PROCESS.ProcessEvidenceError, "must be new"):
                PROCESS.execute_spec(PROCESS.build_control_spec("exit-zero-4g"), directory)

    def test_unobserved_metrics_are_null_and_structure_is_stable(self) -> None:
        def normalize(wrapper: dict) -> dict:
            normalized = copy.deepcopy(wrapper)
            normalized["terminal"]["wall_time"]["value"] = "observed"
            normalized["terminal"]["peak_rss"]["value"] = "observed"
            normalized["process"]["pid"] = "observed"
            normalized["process"]["process_group_id"] = "observed"
            normalized["record_sha256"] = "observed"
            return normalized

        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            _, first = self._run("exit-zero-4g", root, "-a")
            _, second = self._run("exit-zero-4g", root, "-b")
        for result in (first, second):
            self.assertEqual(result["terminal"]["cpu_time"], {
                "state": "not-observed",
                "value": None,
                "unit": "milliseconds",
            })
        self.assertEqual(normalize(first), normalize(second))

    def test_result_authority_closes_only_the_synthetic_control_population(self) -> None:
        with tempfile.TemporaryDirectory(dir=PROCESS.ROOT) as temporary:
            root = Path(temporary)
            for control_id in PROCESS.CONTROL_IDS:
                self._run(control_id, root)
            authority = PROCESS.build_result_authority(
                root, implementation_revision="0" * 40
            )
        self.assertEqual(authority["summary"]["retained_process_attempts"], 8)
        self.assertEqual(authority["summary"]["case_records"], 0)
        self.assertEqual(authority["summary"]["completion_records"], 0)
        self.assertTrue(all(value == 0 for value in authority["credits"].values()))
        markdown = PROCESS.render_result_markdown(authority)
        self.assertIn("synthetic process-control evidence only", markdown)
        self.assertIn("Terminal Lean parity credit: **0**", markdown)


if __name__ == "__main__":
    unittest.main()
