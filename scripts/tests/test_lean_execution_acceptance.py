from __future__ import annotations

import copy
import os
import shutil
import stat
import tempfile
import unittest
from pathlib import Path

from scripts import lean_execution_acceptance as ACCEPTANCE


class LeanExecutionAcceptanceContractTests(unittest.TestCase):
    def build_record(self) -> dict:
        lake = "/opt/lean-4.30/bin/lake"
        environment = {
            "LANG": "C.UTF-8",
            "LAKE_NO_CACHE": "1",
            "LEAN_NUM_THREADS": "1",
            "PATH": "/opt/lean-4.30/bin:/usr/bin:/bin",
        }
        rows = [
            {"mode": mode, "type": kind, "object": object_id, "path": path}
            for mode, kind, object_id, path in ACCEPTANCE.EXPORTER_TREE_ROWS
        ]
        record = ACCEPTANCE.seal(
            {
                "schema": ACCEPTANCE.BUILD_SCHEMA,
                "preregistration_commit": ACCEPTANCE.PREREGISTRATION_COMMIT,
                "repository": ACCEPTANCE.EXPORTER_REPOSITORY,
                "tag": ACCEPTANCE.EXPORTER_TAG,
                "source_commit": ACCEPTANCE.EXPORTER_COMMIT,
                "source_tree": ACCEPTANCE.EXPORTER_TREE,
                "source_archive_sha256": ACCEPTANCE.EXPORTER_ARCHIVE_SHA256,
                "source_files": rows,
                "source_file_count": len(rows),
                "named_source_sha256": ACCEPTANCE.EXPORTER_SOURCE_HASHES,
                "clean_before_build": True,
                "clean_after_build": True,
                "attempts": [
                    {
                        "sequence": 1,
                        "command": [lake, "-j1", "build", "lean4export"],
                        "working_directory": "/opt/src/lean4export",
                        "environment": environment,
                        "exit_code": 1,
                        "stdout": {"path": "preparation/attempt-001.stdout.bin", "bytes": 0, "sha256": ACCEPTANCE.sha256_bytes(b"")},
                        "stderr": {"path": "preparation/attempt-001.stderr.bin", "bytes": 33, "sha256": ACCEPTANCE.sha256_bytes(b"error: unknown short option '-j'\n")},
                        "compiled_sources": False,
                        "classification": "cli-option-rejected-before-build",
                    },
                    {
                        "sequence": 2,
                        "command": [lake, "build", "lean4export"],
                        "working_directory": "/opt/src/lean4export",
                        "environment": environment,
                        "exit_code": 0,
                        "stdout": {"path": "preparation/attempt-002.stdout.bin", "bytes": 3, "sha256": ACCEPTANCE.sha256_bytes(b"ok\n")},
                        "stderr": {"path": "preparation/attempt-002.stderr.bin", "bytes": 0, "sha256": ACCEPTANCE.sha256_bytes(b"")},
                        "compiled_sources": True,
                        "classification": "completed",
                    },
                ],
                "toolchain": {
                    "lean_path": "/opt/lean-4.30/bin/lean",
                    "lean_sha256": ACCEPTANCE.PINNED_LEAN_SHA256,
                    "lean_version": ACCEPTANCE.LEAN_VERSION_LINE,
                    "lake_path": lake,
                    "lake_sha256": ACCEPTANCE.PINNED_LAKE_SHA256,
                    "lake_version": ACCEPTANCE.LAKE_VERSION_LINE,
                },
                "executable": {
                    "path": "/opt/src/lean4export/.lake/build/bin/lean4export",
                    "bytes": 100,
                    "mode": 0o755,
                    "sha256": "e" * 64,
                },
                "record_sha256": "",
            },
            ACCEPTANCE.BUILD_SCHEMA,
        )
        self.assertEqual(ACCEPTANCE.validate_build_record(record), [])
        return record

    def compile_spec(self, parent: Path) -> dict:
        return ACCEPTANCE.build_control_spec(
            ACCEPTANCE.COMPILE_CONTROL,
            implementation_revision="a" * 40,
            lean=Path("/opt/lean-4.30/bin/lean"),
            lake=Path("/opt/lean-4.30/bin/lake"),
            exporter=Path("/opt/src/lean4export/.lake/build/bin/lean4export"),
            exporter_source_root=Path("/opt/src/lean4export"),
            private_root=parent / "private-compile",
            compile_artifact_directory=None,
            build_record=self.build_record(),
        )

    def export_spec(self, parent: Path) -> dict:
        compile_artifacts = parent / "compile-artifacts"
        compile_artifacts.mkdir(parents=True, exist_ok=True)
        output = compile_artifacts / "AxeyumProbe.olean"
        output.write_bytes(b"synthetic-olean-contract-fixture\n")
        output.chmod(0o444)
        return ACCEPTANCE.build_control_spec(
            ACCEPTANCE.EXPORT_CONTROL,
            implementation_revision="a" * 40,
            lean=Path("/opt/lean-4.30/bin/lean"),
            lake=Path("/opt/lean-4.30/bin/lake"),
            exporter=Path("/opt/src/lean4export/.lake/build/bin/lean4export"),
            exporter_source_root=Path("/opt/src/lean4export"),
            private_root=parent / "private-export",
            compile_artifact_directory=compile_artifacts,
            build_record=self.build_record(),
            compile_completion={"record_sha256": "c" * 64},
        )

    def rewrite_json(self, path: Path, value: dict) -> None:
        path.chmod(0o600)
        path.write_bytes(ACCEPTANCE.canonical_bytes(value))
        path.chmod(0o444)

    def materialize(self, parent: Path, control_id: str) -> Path:
        spec = (
            self.compile_spec(parent)
            if control_id == ACCEPTANCE.COMPILE_CONTROL
            else self.export_spec(parent)
        )
        root = parent / control_id
        root.mkdir(parents=True)
        storage = ACCEPTANCE.STORE.capture_storage_class(
            ACCEPTANCE.STORE.STORAGE_CLASS_IDS[0], ACCEPTANCE.ROOT
        )
        manifest = ACCEPTANCE._manifest(control_id, spec, storage)
        run = ACCEPTANCE._run_record(spec, storage)
        prelaunch = ACCEPTANCE._prelaunch_record(spec)
        ACCEPTANCE._install_json(root, "manifest.json", manifest)
        ACCEPTANCE._install_json(root, "spec.json", spec)
        ACCEPTANCE._install_json(root, "run.json", run)
        ACCEPTANCE._install_json(root, "attempt-prelaunch.json", prelaunch)

        stdout = (
            b"" if control_id == ACCEPTANCE.COMPILE_CONTROL
            else ACCEPTANCE.REFERENCE_STREAM.read_bytes()
        )
        stderr = b""
        ACCEPTANCE._install_bytes(root, "raw/stdout.bin", stdout)
        ACCEPTANCE._install_bytes(root, "raw/stderr.bin", stderr)
        if control_id == ACCEPTANCE.COMPILE_CONTROL:
            source = ACCEPTANCE.FLAT_SOURCE.read_bytes()
            olean = b"synthetic-olean-contract-fixture\n"
            ACCEPTANCE._install_bytes(root, "artifacts/AxeyumProbe.lean", source)
            ACCEPTANCE._install_bytes(root, "artifacts/AxeyumProbe.olean", olean)
            artifact = ACCEPTANCE._artifact_record(
                control_id,
                [
                    ACCEPTANCE._raw_descriptor("artifacts/AxeyumProbe.lean", source),
                    ACCEPTANCE._raw_descriptor("artifacts/AxeyumProbe.olean", olean),
                ],
                {
                    "source_copy_equal": True,
                    "artifact_nonempty": True,
                    "stderr_empty": True,
                    "stdout_empty": True,
                    "reference_bytes_equal": None,
                    "metadata_equal": None,
                },
            )
        else:
            ACCEPTANCE._install_bytes(root, "artifacts/export.ndjson", stdout)
            artifact = ACCEPTANCE._artifact_record(
                control_id,
                [ACCEPTANCE._raw_descriptor("artifacts/export.ndjson", stdout)],
                {
                    "source_copy_equal": None,
                    "artifact_nonempty": True,
                    "stderr_empty": True,
                    "stdout_empty": False,
                    "reference_bytes_equal": True,
                    "metadata_equal": True,
                },
            )
        terminal = ACCEPTANCE.seal(
            {
                "schema": ACCEPTANCE.TERMINAL_SCHEMA,
                "control_id": control_id,
                "run_id": spec["run_id"],
                "attempt_id": spec["attempt_id"],
                "sequence": 1,
                "prelaunch_sha256": prelaunch["record_sha256"],
                "class": "exited",
                "exit_code": 0,
                "signal": None,
                "events": [
                    "prelaunch-record-installed",
                    "rlimit-as-installed",
                    "direct-child-reaped",
                    "process-group-no-live-members-observed",
                ],
                "wall_time": ACCEPTANCE.metric("observed", 1, "milliseconds"),
                "cpu_time": ACCEPTANCE.metric("not-observed", None, "milliseconds"),
                "peak_rss": ACCEPTANCE.metric("observed", 4096, "bytes"),
                "process": {
                    "pid": 123,
                    "process_group_id": 123,
                    "rlimit_as_bytes": ACCEPTANCE.LANES[control_id]["memory_limit_bytes"],
                    "watchdog_fired": False,
                    "sigterm_sent": False,
                    "sigkill_sent": False,
                    "direct_child_reaped": True,
                    "live_non_zombie_pids_after_cleanup": [],
                },
                "raw_outputs": [
                    ACCEPTANCE._raw_descriptor("raw/stderr.bin", stderr),
                    ACCEPTANCE._raw_descriptor("raw/stdout.bin", stdout),
                ],
                "record_sha256": "",
            },
            ACCEPTANCE.TERMINAL_SCHEMA,
        )
        ACCEPTANCE._install_json(root, "artifact.json", artifact)
        ACCEPTANCE._install_json(root, "attempt-terminal.json", terminal)
        completion = ACCEPTANCE._completion_record(root, spec, terminal, artifact)
        ACCEPTANCE._install_json(root, "completion.json", completion)
        self.assertEqual(
            ACCEPTANCE.validate_control_store(root, expected_control=control_id), []
        )
        return root

    def test_01_repository_and_fixture_pins_are_exact(self) -> None:
        self.assertEqual(ACCEPTANCE.validate_repository_inputs(), [])
        self.assertEqual(ACCEPTANCE.sha256_file(ACCEPTANCE.FLAT_SOURCE), ACCEPTANCE.FLAT_SOURCE_SHA256)
        self.assertEqual(ACCEPTANCE.sha256_file(ACCEPTANCE.REFERENCE_STREAM), ACCEPTANCE.REFERENCE_SHA256)
        self.assertEqual(ACCEPTANCE.REFERENCE_STREAM.stat().st_size, 3_849)
        self.assertEqual(len(ACCEPTANCE.REFERENCE_STREAM.read_bytes().splitlines()), 65)

    def test_02_build_record_closes_source_tool_and_attempt_order(self) -> None:
        record = self.build_record()
        self.assertEqual(record["source_file_count"], 13)
        self.assertEqual([item["exit_code"] for item in record["attempts"]], [1, 0])
        self.assertEqual([item["compiled_sources"] for item in record["attempts"]], [False, True])

    def test_03_build_pin_dirty_command_and_binary_mutations_reject(self) -> None:
        base = self.build_record()
        mutations = []
        for field, value in (
            ("source_commit", "0" * 40),
            ("source_file_count", 12),
            ("clean_after_build", False),
        ):
            changed = copy.deepcopy(base)
            changed[field] = value
            mutations.append(ACCEPTANCE.seal(changed, ACCEPTANCE.BUILD_SCHEMA))
        changed = copy.deepcopy(base)
        changed["attempts"][1]["command"] = ["lake", "build"]
        mutations.append(ACCEPTANCE.seal(changed, ACCEPTANCE.BUILD_SCHEMA))
        changed = copy.deepcopy(base)
        changed["executable"]["mode"] = 0o644
        mutations.append(ACCEPTANCE.seal(changed, ACCEPTANCE.BUILD_SCHEMA))
        for changed in mutations:
            with self.subTest(changed=changed):
                self.assertTrue(ACCEPTANCE.validate_build_record(changed))

    def test_04_compile_spec_is_absolute_bounded_empty_and_zero_credit(self) -> None:
        with tempfile.TemporaryDirectory(dir=ACCEPTANCE.ROOT) as temporary:
            spec = self.compile_spec(Path(temporary))
        self.assertEqual(ACCEPTANCE.validate_control_spec(spec), [])
        self.assertEqual(spec["command"][1:3], ["-j1", "-o"])
        self.assertTrue(all(Path(item).is_absolute() for item in (spec["command"][0], spec["command"][3], spec["command"][4])))
        self.assertEqual(spec["selection_case_ids"], [])
        self.assertEqual(spec["case_records"], [])
        self.assertEqual(spec["credit_class"], ACCEPTANCE.CREDIT_CLASS)

    def test_05_export_spec_owns_compile_artifact_and_forbids_filtering(self) -> None:
        with tempfile.TemporaryDirectory(dir=ACCEPTANCE.ROOT) as temporary:
            spec = self.export_spec(Path(temporary))
        self.assertEqual(ACCEPTANCE.validate_control_spec(spec), [])
        self.assertEqual(spec["command"][1:], ["env", "/opt/src/lean4export/.lake/build/bin/lean4export", "AxeyumProbe"])
        self.assertNotIn("--", spec["command"])
        self.assertNotIn("--export-unsafe", spec["command"])
        self.assertNotIn("--export-mdata", spec["command"])

    def test_06_spec_exact_fields_and_self_hash_drift_reject(self) -> None:
        with tempfile.TemporaryDirectory(dir=ACCEPTANCE.ROOT) as temporary:
            spec = self.compile_spec(Path(temporary))
        changed = copy.deepcopy(spec)
        changed["unexpected"] = True
        changed = ACCEPTANCE.seal(changed, ACCEPTANCE.SPEC_SCHEMA)
        self.assertIn("control spec fields must be exact", ACCEPTANCE.validate_control_spec(changed))
        changed = copy.deepcopy(spec)
        changed["record_sha256"] = "0" * 64
        self.assertIn("control spec identity drift", ACCEPTANCE.validate_control_spec(changed))

    def test_07_ambient_command_environment_lane_and_limit_drift_reject(self) -> None:
        with tempfile.TemporaryDirectory(dir=ACCEPTANCE.ROOT) as temporary:
            base = self.compile_spec(Path(temporary))
        for mutate in (
            lambda value: value["command"].__setitem__(0, "lean"),
            lambda value: value["environment"].__setitem__("PATH", "/usr/bin"),
            lambda value: value.__setitem__("lane_id", "official-export-8g"),
            lambda value: value["resource_envelope"]["memory_limit"].__setitem__("value", 1),
        ):
            changed = copy.deepcopy(base)
            mutate(changed)
            changed = ACCEPTANCE.seal(changed, ACCEPTANCE.SPEC_SCHEMA)
            self.assertTrue(ACCEPTANCE.validate_control_spec(changed))

    def test_08_any_selection_case_or_credit_surface_rejects(self) -> None:
        with tempfile.TemporaryDirectory(dir=ACCEPTANCE.ROOT) as temporary:
            base = self.compile_spec(Path(temporary))
        for field, value in (
            ("selection_set_id", "u2-real"),
            ("selection_case_ids", ["case-a"]),
            ("case_records", [{"id": "case-a"}]),
            ("credit_class", "parity"),
        ):
            changed = copy.deepcopy(base)
            changed[field] = value
            changed = ACCEPTANCE.seal(changed, ACCEPTANCE.SPEC_SCHEMA)
            self.assertTrue(ACCEPTANCE.validate_control_spec(changed))

    def test_09_prelaunch_missing_late_duplicate_and_wrong_attribution_reject(self) -> None:
        with tempfile.TemporaryDirectory(dir=ACCEPTANCE.ROOT) as temporary:
            parent = Path(temporary)
            for mutation in ("missing", "terminal", "wrong-run", "duplicate"):
                with self.subTest(mutation=mutation):
                    root = self.materialize(parent / mutation, ACCEPTANCE.COMPILE_CONTROL)
                    path = root / "attempt-prelaunch.json"
                    if mutation == "missing":
                        path.unlink()
                    elif mutation == "duplicate":
                        shutil.copyfile(path, root / "duplicate.json")
                    else:
                        value = ACCEPTANCE.load_canonical(path)
                        if mutation == "terminal":
                            value["terminal"] = {"class": "exited"}
                        else:
                            value["run_id"] = "wrong-run"
                        self.rewrite_json(path, ACCEPTANCE.seal(value, ACCEPTANCE.PRELAUNCH_SCHEMA))
                    self.assertTrue(ACCEPTANCE.validate_control_store(root, expected_control=ACCEPTANCE.COMPILE_CONTROL))

    def test_10_raw_output_hash_size_and_extra_file_drift_reject(self) -> None:
        with tempfile.TemporaryDirectory(dir=ACCEPTANCE.ROOT) as temporary:
            root = self.materialize(Path(temporary), ACCEPTANCE.EXPORT_CONTROL)
            raw = root / "raw/stdout.bin"
            raw.chmod(0o600)
            raw.write_bytes(raw.read_bytes() + b"x")
            raw.chmod(0o444)
            failures = ACCEPTANCE.validate_control_store(root, expected_control=ACCEPTANCE.EXPORT_CONTROL)
            self.assertTrue(any("raw output" in item or "export byte" in item for item in failures))

    def test_11_exit_signal_timeout_survivor_and_guessed_terminal_reject(self) -> None:
        with tempfile.TemporaryDirectory(dir=ACCEPTANCE.ROOT) as temporary:
            base_parent = Path(temporary)
            mutations = (
                ("exit", lambda value: value.__setitem__("exit_code", 7)),
                ("signal", lambda value: (value.__setitem__("class", "signaled"), value.__setitem__("exit_code", None), value.__setitem__("signal", 9))),
                ("timeout", lambda value: value["process"].__setitem__("watchdog_fired", True)),
                ("survivor", lambda value: value["process"].__setitem__("live_non_zombie_pids_after_cleanup", [999])),
            )
            for name, mutate in mutations:
                root = self.materialize(base_parent / name, ACCEPTANCE.COMPILE_CONTROL)
                path = root / "attempt-terminal.json"
                value = ACCEPTANCE.load_canonical(path)
                mutate(value)
                self.rewrite_json(path, ACCEPTANCE.seal(value, ACCEPTANCE.TERMINAL_SCHEMA))
                self.assertTrue(ACCEPTANCE.validate_control_store(root, expected_control=ACCEPTANCE.COMPILE_CONTROL))

    def test_12_changed_source_empty_symlink_and_writable_olean_reject(self) -> None:
        with tempfile.TemporaryDirectory(dir=ACCEPTANCE.ROOT) as temporary:
            base = Path(temporary)
            for mutation in ("source", "empty", "writable", "symlink"):
                root = self.materialize(base / mutation, ACCEPTANCE.COMPILE_CONTROL)
                target = root / ("artifacts/AxeyumProbe.lean" if mutation == "source" else "artifacts/AxeyumProbe.olean")
                target.chmod(0o600)
                if mutation == "source":
                    target.write_bytes(b"changed\n")
                    target.chmod(0o444)
                elif mutation == "empty":
                    target.write_bytes(b"")
                    target.chmod(0o444)
                elif mutation == "writable":
                    pass
                else:
                    target.unlink()
                    target.symlink_to(ACCEPTANCE.FLAT_SOURCE)
                self.assertTrue(ACCEPTANCE.validate_control_store(root, expected_control=ACCEPTANCE.COMPILE_CONTROL))

    def test_13_export_one_byte_line_metadata_and_stderr_drift_reject(self) -> None:
        with tempfile.TemporaryDirectory(dir=ACCEPTANCE.ROOT) as temporary:
            base = Path(temporary)
            for mutation in ("byte", "metadata", "stderr"):
                root = self.materialize(base / mutation, ACCEPTANCE.EXPORT_CONTROL)
                path = root / ("raw/stderr.bin" if mutation == "stderr" else "raw/stdout.bin")
                path.chmod(0o600)
                if mutation == "byte":
                    path.write_bytes(path.read_bytes()[:-1])
                elif mutation == "metadata":
                    path.write_bytes(path.read_bytes().replace(b'"version":"3.1.0"', b'"version":"3.1.1"', 1))
                else:
                    path.write_bytes(b"warning\n")
                path.chmod(0o444)
                self.assertTrue(ACCEPTANCE.validate_control_store(root, expected_control=ACCEPTANCE.EXPORT_CONTROL))

    def test_14_namespace_missing_extra_symlink_and_writable_record_reject(self) -> None:
        with tempfile.TemporaryDirectory(dir=ACCEPTANCE.ROOT) as temporary:
            base = Path(temporary)
            root = self.materialize(base / "missing", ACCEPTANCE.COMPILE_CONTROL)
            (root / "artifact.json").unlink()
            self.assertIn("control store file set must be exact", ACCEPTANCE.validate_control_store(root, expected_control=ACCEPTANCE.COMPILE_CONTROL))
            root = self.materialize(base / "extra", ACCEPTANCE.COMPILE_CONTROL)
            (root / "extra.bin").write_bytes(b"x")
            self.assertIn("control store file set must be exact", ACCEPTANCE.validate_control_store(root, expected_control=ACCEPTANCE.COMPILE_CONTROL))
            root = self.materialize(base / "writable", ACCEPTANCE.COMPILE_CONTROL)
            (root / "run.json").chmod(0o644)
            self.assertTrue(any("not read-only" in item for item in ACCEPTANCE.validate_control_store(root, expected_control=ACCEPTANCE.COMPILE_CONTROL)))
            root = self.materialize(base / "symlink", ACCEPTANCE.COMPILE_CONTROL)
            target = root / "artifacts/AxeyumProbe.olean"
            target.unlink()
            target.symlink_to(ACCEPTANCE.FLAT_SOURCE)
            self.assertTrue(any("symlinked" in item for item in ACCEPTANCE.validate_control_store(root, expected_control=ACCEPTANCE.COMPILE_CONTROL)))

    def test_15_every_json_family_rejects_exact_field_or_self_hash_drift(self) -> None:
        families = (
            ("manifest.json", ACCEPTANCE.MANIFEST_SCHEMA),
            ("run.json", ACCEPTANCE.RUN_SCHEMA),
            ("attempt-prelaunch.json", ACCEPTANCE.PRELAUNCH_SCHEMA),
            ("attempt-terminal.json", ACCEPTANCE.TERMINAL_SCHEMA),
            ("artifact.json", ACCEPTANCE.ARTIFACT_SCHEMA),
            ("completion.json", ACCEPTANCE.COMPLETION_SCHEMA),
        )
        with tempfile.TemporaryDirectory(dir=ACCEPTANCE.ROOT) as temporary:
            base = Path(temporary)
            for index, (relative, schema) in enumerate(families):
                root = self.materialize(base / str(index), ACCEPTANCE.COMPILE_CONTROL)
                path = root / relative
                value = ACCEPTANCE.load_canonical(path)
                value["unexpected"] = True
                self.rewrite_json(path, ACCEPTANCE.seal(value, schema))
                self.assertTrue(ACCEPTANCE.validate_control_store(root, expected_control=ACCEPTANCE.COMPILE_CONTROL))

    def test_16_completion_dependency_digest_order_and_credit_drift_reject(self) -> None:
        with tempfile.TemporaryDirectory(dir=ACCEPTANCE.ROOT) as temporary:
            base = Path(temporary)
            for mutation in ("missing", "order", "digest", "credit"):
                root = self.materialize(base / mutation, ACCEPTANCE.COMPILE_CONTROL)
                path = root / "completion.json"
                value = ACCEPTANCE.load_canonical(path)
                if mutation == "missing":
                    value["dependencies"].pop()
                elif mutation == "order":
                    value["dependencies"].reverse()
                elif mutation == "digest":
                    value["record_set_sha256"] = "0" * 64
                else:
                    value["credits"]["parity_credit"] = 1
                self.rewrite_json(path, ACCEPTANCE.seal(value, ACCEPTANCE.COMPLETION_SCHEMA))
                self.assertTrue(ACCEPTANCE.validate_control_store(root, expected_control=ACCEPTANCE.COMPILE_CONTROL))

    def test_17_identical_install_is_idempotent_and_conflict_preserves_final(self) -> None:
        with tempfile.TemporaryDirectory(dir=ACCEPTANCE.ROOT) as temporary:
            root = Path(temporary) / "store"
            root.mkdir()
            value = {"schema": "fixture", "value": 1}
            self.assertEqual(ACCEPTANCE._install_json(root, "run.json", value), "installed")
            self.assertEqual(ACCEPTANCE._install_json(root, "run.json", value), "existing-valid")
            with self.assertRaises(ACCEPTANCE.CheckpointConflict):
                ACCEPTANCE._install_json(root, "run.json", {"schema": "fixture", "value": 2})
            self.assertEqual(ACCEPTANCE.load_canonical(root / "run.json"), value)
            self.assertEqual(len(list((root / "quarantine" / "conflicts").iterdir())), 1)

    def test_18_projection_excludes_pid_duration_and_cache_paths(self) -> None:
        with tempfile.TemporaryDirectory(dir=ACCEPTANCE.ROOT) as temporary:
            root = self.materialize(Path(temporary), ACCEPTANCE.COMPILE_CONTROL)
            spec = ACCEPTANCE.load_canonical(root / "spec.json")
            terminal = ACCEPTANCE.load_canonical(root / "attempt-terminal.json")
            artifact = ACCEPTANCE.load_canonical(root / "artifact.json")
            first = ACCEPTANCE._projection(spec, terminal, artifact)
            terminal["process"]["pid"] = 999_999
            terminal["process"]["process_group_id"] = 999_999
            terminal["wall_time"]["value"] = 99_999
            terminal["peak_rss"]["value"] = 99_999
            second = ACCEPTANCE._projection(spec, terminal, artifact)
            self.assertEqual(first, second)
            rendered = ACCEPTANCE.canonical_bytes(first)
            self.assertNotIn(str(Path(temporary)).encode(), rendered)
            self.assertNotIn(b"999999", rendered)

    def test_19_result_validator_refuses_nonzero_parity_surface(self) -> None:
        authority = ACCEPTANCE.seal(
            {
                "schema": ACCEPTANCE.RESULT_SCHEMA,
                "status": "accepted-no-credit-real-controls",
                "preregistration_commit": ACCEPTANCE.PREREGISTRATION_COMMIT,
                "implementation_revision": "a" * 40,
                "source_inputs": [],
                "build": {},
                "controls": [{}, {}],
                "summary": {
                    "u2_cases": 0,
                    "case_records": 0,
                    "official_outcomes": 0,
                    "axeyum_outcomes": 0,
                    "paired_cells": 0,
                    "performance_rows": 0,
                },
                "evidence_files": [],
                "evidence_manifest_sha256": ACCEPTANCE.domain_digest(
                    "axeyum-lean-execution-acceptance-evidence-files-v1", []
                ),
                "claims": {},
                "credits": ACCEPTANCE.ZERO_CREDITS,
                "record_sha256": "",
            },
            ACCEPTANCE.RESULT_SCHEMA,
        )
        self.assertEqual(ACCEPTANCE.validate_result_authority(authority), [])
        changed = copy.deepcopy(authority)
        changed["credits"]["parity_credit"] = 1
        changed = ACCEPTANCE.seal(changed, ACCEPTANCE.RESULT_SCHEMA)
        self.assertIn(
            "acceptance result cannot receive parity credit",
            ACCEPTANCE.validate_result_authority(changed),
        )


@unittest.skipUnless(
    os.environ.get("AXEYUM_RUN_LEAN_EXECUTION_ACCEPTANCE_LIVE") == "1",
    "set AXEYUM_RUN_LEAN_EXECUTION_ACCEPTANCE_LIVE=1 and invoke the CLI explicitly",
)
class LeanExecutionAcceptanceLiveOptInTests(unittest.TestCase):
    def test_live_pair_is_cli_only_and_never_implicit(self) -> None:
        self.fail("Run scripts/lean_execution_acceptance.py run-pair with exact pinned paths")


if __name__ == "__main__":
    unittest.main()
