import copy
import importlib.util
import io
import os
import subprocess
import sys
import tarfile
import tempfile
import unittest
from argparse import Namespace
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/capture-tock-log2.py"
SPEC = importlib.util.spec_from_file_location("capture_tock_log2", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
CAPTURE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = CAPTURE
SPEC.loader.exec_module(CAPTURE)


def capture_error_kind(callable_):
    with unittest.TestCase().assertRaises(CAPTURE.CaptureError) as raised:
        callable_()
    return raised.exception.stage, raised.exception.kind


class CaptureTockLog2Tests(unittest.TestCase):
    def registration(self, producer_hash):
        return {
            "schema": CAPTURE.REGISTRATION_SCHEMA,
            "upstream": {
                "commit": "ac5d597d22fbf3b03ef2169a577bac246ef65ffb",
                "tree": "5243357a7034d3a5fa68487ea839a25e573a25ef",
            },
            "environment": CAPTURE.EXPECTED_ENVIRONMENT,
            "build_args": CAPTURE.EXPECTED_BUILD_ARGS,
            "metadata_args": CAPTURE.EXPECTED_METADATA_ARGS,
            "resource_scope": CAPTURE.EXPECTED_RESOURCE_SCOPE,
            "tools": {name: {} for name in CAPTURE.EXPECTED_TOOLS},
            "admitter": {
                "path": "producer.py",
                "sha256": producer_hash,
                "source": "producer.py",
                "source_sha256": producer_hash,
            },
            "namespace": {
                "probe_argv": CAPTURE.EXPECTED_BWRAP_PROBE,
                "root_argv": CAPTURE.EXPECTED_BWRAP_ROOT,
                "source": "/axeyum-vroot/source",
                "target": "/axeyum-vroot/target",
                "cwd": "/axeyum-vroot/source",
            },
            "critical_files": [{"path": "Cargo.lock", "sha256": "0" * 64}],
            "producer_files": [
                {"path": "producer.py", "sha256": producer_hash},
            ],
            "targets": [
                {
                    "name": "log_base_two",
                    "parameter_widths": [32],
                    "return_width": 32,
                },
                {
                    "name": "log_base_two_u64",
                    "parameter_widths": [64],
                    "return_width": 32,
                },
            ],
        }

    def test_registration_rejects_frozen_field_and_producer_drift(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            producer = root / "producer.py"
            producer.write_bytes(b"producer\n")
            base = self.registration(CAPTURE.sha256_file(producer))
            with mock.patch.object(CAPTURE, "REPO", root):
                CAPTURE.validate_registration(base)
                mutations = [
                    ("schema", lambda row: row.__setitem__("schema", "wrong")),
                    (
                        "upstream",
                        lambda row: row["upstream"].__setitem__("commit", "0" * 40),
                    ),
                    (
                        "environment",
                        lambda row: row["environment"].append(["RUSTFLAGS", "-O"]),
                    ),
                    (
                        "build_args",
                        lambda row: row["build_args"].remove("--offline"),
                    ),
                    (
                        "metadata_args",
                        lambda row: row["metadata_args"].remove("--locked"),
                    ),
                    (
                        "resource_scope",
                        lambda row: row["resource_scope"].__setitem__(
                            "memory_max_bytes", 1
                        ),
                    ),
                    (
                        "namespace",
                        lambda row: row["namespace"].__setitem__(
                            "source", "/different"
                        ),
                    ),
                    (
                        "producer_hash",
                        lambda row: row["producer_files"][0].__setitem__(
                            "sha256", "f" * 64
                        ),
                    ),
                ]
                for name, mutate in mutations:
                    with self.subTest(name=name):
                        candidate = copy.deepcopy(base)
                        mutate(candidate)
                        self.assertEqual(
                            capture_error_kind(
                                lambda candidate=candidate: CAPTURE.validate_registration(
                                    candidate
                                )
                            )[0],
                            "registration",
                        )

    def test_tool_hash_and_version_are_both_pinned(self):
        with tempfile.TemporaryDirectory() as raw:
            tool = Path(raw) / "tool"
            tool.write_text("#!/bin/sh\nprintf 'tool 1\\n'\n", encoding="utf-8")
            tool.chmod(0o755)
            entry = {
                "path": str(tool),
                "sha256": CAPTURE.sha256_file(tool),
                "version_args": ["--version"],
                "version": "tool 1",
            }
            self.assertEqual(CAPTURE.tool_report(entry, "fake")["version"], "tool 1")
            wrong_hash = {**entry, "sha256": "0" * 64}
            self.assertEqual(
                capture_error_kind(lambda: CAPTURE.tool_report(wrong_hash, "fake")),
                ("tool", "fake_hash"),
            )
            wrong_version = {**entry, "version": "tool 2"}
            self.assertEqual(
                capture_error_kind(lambda: CAPTURE.tool_report(wrong_version, "fake")),
                ("tool", "fake_version"),
            )

    def test_archive_extraction_rejects_parent_traversal(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            archive = root / "bad.tar"
            with tarfile.open(archive, "w") as stream:
                item = tarfile.TarInfo("../escape")
                item.size = 1
                stream.addfile(item, io.BytesIO(b"x"))
            destination = root / "destination"
            destination.mkdir()
            self.assertEqual(
                capture_error_kind(lambda: CAPTURE.safe_extract(archive, destination)),
                ("source", "archive_traversal"),
            )
            self.assertFalse((root / "escape").exists())

            symlink_archive = root / "bad-symlink.tar"
            with tarfile.open(symlink_archive, "w") as stream:
                item = tarfile.TarInfo("link")
                item.type = tarfile.SYMTYPE
                item.linkname = "../escape"
                stream.addfile(item)
            self.assertEqual(
                capture_error_kind(
                    lambda: CAPTURE.safe_extract(symlink_archive, destination)
                ),
                ("source", "archive_extract"),
            )

    def test_ambient_flags_roots_and_namespace_are_exact(self):
        CAPTURE.reject_ambient_flags({"PATH": "/bin"})
        self.assertEqual(
            capture_error_kind(
                lambda: CAPTURE.reject_ambient_flags({"RUSTFLAGS": "-Ctarget-cpu=native"})
            ),
            ("build", "ambient_rustflags"),
        )
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            CAPTURE.validate_distinct_roots([root / "a", root / "b"])
            self.assertEqual(
                capture_error_kind(
                    lambda: CAPTURE.validate_distinct_roots([root / "a", root / "a"])
                ),
                ("build", "physical_root_alias"),
            )
            registration = {"tools": {"bwrap": {"path": "/usr/bin/bwrap"}}}
            command = CAPTURE.bwrap_command(
                registration, root / "a", root / "b", ["/bin/child", "arg"]
            )
            self.assertEqual(command.count("/bin/child"), 1)
            self.assertEqual(command[-3:], ["--", "/bin/child", "arg"])
            self.assertEqual(
                command[1 : 1 + len(CAPTURE.EXPECTED_BWRAP_ROOT)],
                CAPTURE.EXPECTED_BWRAP_ROOT,
            )

    def test_cgroup_scope_and_oom_deltas(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            proc = root / "proc-self-cgroup"
            cgroups = root / "sys-fs-cgroup"
            scope = cgroups / "user.slice/test.scope"
            scope.mkdir(parents=True)
            proc.write_text("0::/user.slice/test.scope\n", encoding="utf-8")
            (scope / "memory.high").write_text(
                str(CAPTURE.EXPECTED_MEMORY_HIGH), encoding="utf-8"
            )
            (scope / "memory.max").write_text(
                str(CAPTURE.EXPECTED_MEMORY_MAX), encoding="utf-8"
            )
            (scope / "memory.swap.max").write_text(
                str(CAPTURE.EXPECTED_SWAP_MAX), encoding="utf-8"
            )
            (scope / "memory.events").write_text(
                "low 0\nhigh 1\nmax 0\noom 2\noom_kill 3\noom_group_kill 4\n",
                encoding="utf-8",
            )
            snapshot = CAPTURE.resource_snapshot(proc, cgroups)
            self.assertEqual(snapshot["memory_max_bytes"], 4 * 1024**3)
            self.assertEqual(CAPTURE.resource_delta(snapshot, copy.deepcopy(snapshot))["oom"], 0)
            after = copy.deepcopy(snapshot)
            after["events"]["oom_kill"] += 1
            self.assertEqual(
                capture_error_kind(lambda: CAPTURE.resource_delta(snapshot, after)),
                ("resource", "oom_delta"),
            )
            (scope / "memory.max").write_text("max", encoding="utf-8")
            self.assertEqual(
                capture_error_kind(lambda: CAPTURE.resource_snapshot(proc, cgroups)),
                ("resource", "memory_max_unbounded"),
            )

    def test_host_tokens_and_raw_module_identity(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            module = b"/axeyum-vroot/source /axeyum-vroot/target"
            counts = CAPTURE.reject_host_tokens(module, [root])
            rows = [{**counts}, {**counts}]
            self.assertEqual(
                CAPTURE.validate_module_identity([module, module], rows), module
            )
            self.assertEqual(
                capture_error_kind(
                    lambda: CAPTURE.validate_module_identity([module], rows)
                ),
                ("identity", "module_count"),
            )
            for changed, kind in [
                ([module, module + b"x"], "module_size"),
                ([b"aa", b"bb"], "module_hash"),
            ]:
                with self.subTest(kind=kind):
                    self.assertEqual(
                        capture_error_kind(
                            lambda changed=changed: CAPTURE.validate_module_identity(
                                changed, rows
                            )
                        ),
                        ("identity", kind),
                    )
            drift = [rows[0], {**rows[1], "virtual_source_occurrences": 2}]
            self.assertEqual(
                capture_error_kind(
                    lambda: CAPTURE.validate_module_identity([module, module], drift)
                ),
                ("identity", "virtual_path_counts"),
            )
            self.assertEqual(
                capture_error_kind(
                    lambda: CAPTURE.reject_host_tokens(str(root).encode(), [root])
                ),
                ("identity", "host_path"),
            )

    def test_symbol_discovery_is_exact_and_width_checked(self):
        module = (
            b"; kernel::utilities::math::log_base_two\n"
            b"define noundef range(i32 0, 32) i32 @_ZN3log(i32 noundef %num) {\n"
            b"  ret i32 0\n}\n"
        )
        entry = {"name": "log_base_two", "parameter_widths": [32], "return_width": 32}
        self.assertEqual(CAPTURE.discover_target(module, entry)["symbol"], "_ZN3log")
        wrong = {**entry, "parameter_widths": [64]}
        self.assertEqual(
            capture_error_kind(lambda: CAPTURE.discover_target(module, wrong)),
            ("symbol", "parameter_widths"),
        )
        ambiguous = module + module
        self.assertEqual(
            capture_error_kind(lambda: CAPTURE.discover_target(ambiguous, entry)),
            ("symbol", "comment_count"),
        )

    def test_module_id_admission_and_identity_projection(self):
        extracted = b"; ModuleID = '/tmp/input.ll'\nsource_filename = \"x\"\n"
        self.assertEqual(
            CAPTURE.moduleid_agnostic(extracted), b"source_filename = \"x\"\n"
        )
        self.assertEqual(
            capture_error_kind(
                lambda: CAPTURE.moduleid_agnostic(b"source_filename = \"x\"\n")
            ),
            ("extract", "module_id"),
        )
        accepted = {
            "stage": "accepted",
            "kind": "straight_line_scalar",
            "function": "f",
            "parameter_widths": "32",
            "return_width": "32",
            "blocks": "1",
            "phis": "0",
            "instructions": "4",
            "canonical_bytes": "10",
        }
        stdout = "".join(f"{key}={value}\n" for key, value in accepted.items())
        self.assertEqual(CAPTURE.parse_admission(stdout), accepted)
        declined = stdout.replace("stage=accepted", "stage=declined")
        self.assertEqual(
            capture_error_kind(lambda: CAPTURE.parse_admission(declined)),
            ("admission", "declined"),
        )
        result = {"stable": 1, "observations": {"timing": 2}, "identity_sha256": "x"}
        self.assertEqual(CAPTURE.identity_projection(result), {"stable": 1})

    def test_external_command_failures_preserve_stage_and_kind(self):
        for stage, kind in [
            ("extract", "llvm_extract"),
            ("llvm", "extract_assemble"),
            ("admission", "binary"),
        ]:
            with self.subTest(stage=stage, kind=kind):
                self.assertEqual(
                    capture_error_kind(
                        lambda stage=stage, kind=kind: CAPTURE.command(
                            ["/usr/bin/false"], stage=stage, kind=kind
                        )
                    ),
                    (stage, kind),
                )

    def test_failure_removes_partial_output(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            output = root / "target/capture"
            registration = {
                "tools": {"dpkg_query": {"path": "/usr/bin/dpkg-query"}},
                "llvm_package_version": "1:22.1.2-1ubuntu1",
                "admitter": {"sha256": "0" * 64},
                "upstream": {"commit": "x", "tree": "y"},
            }
            completed = subprocess.CompletedProcess(
                ["dpkg-query"], 0, stdout=registration["llvm_package_version"], stderr=""
            )
            resource = {
                "cgroup": "/scope",
                "memory_high_bytes": CAPTURE.EXPECTED_MEMORY_HIGH,
                "memory_max_bytes": CAPTURE.EXPECTED_MEMORY_MAX,
                "swap_max_bytes": CAPTURE.EXPECTED_SWAP_MAX,
                "events": {"oom": 0, "oom_kill": 0, "oom_group_kill": 0},
            }

            def materialize(_repo, destination, _registration):
                destination.mkdir()

            with (
                mock.patch.object(CAPTURE, "REPO", root),
                mock.patch.object(CAPTURE, "read_json", return_value=registration),
                mock.patch.object(CAPTURE, "validate_registration"),
                mock.patch.object(CAPTURE, "reject_ambient_flags"),
                mock.patch.object(CAPTURE, "validate_source_repo"),
                mock.patch.object(CAPTURE, "command", return_value=completed),
                mock.patch.object(CAPTURE, "tool_report", return_value={}),
                mock.patch.object(CAPTURE, "validate_file"),
                mock.patch.object(CAPTURE, "probe_namespace"),
                mock.patch.object(CAPTURE, "resource_snapshot", return_value=resource),
                mock.patch.object(CAPTURE, "materialize", side_effect=materialize),
                mock.patch.object(CAPTURE, "validate_cache"),
                mock.patch.object(
                    CAPTURE,
                    "build_kernel",
                    side_effect=CAPTURE.CaptureError("build", "cargo_rustc", "failed"),
                ),
            ):
                args = Namespace(
                    registration=root / "registration.json",
                    tock_repo=root / "tock",
                    output=output,
                    admitter=root / "admitter",
                )
                self.assertEqual(
                    capture_error_kind(lambda: CAPTURE.run_capture(args)),
                    ("build", "cargo_rustc"),
                )
            self.assertFalse(output.exists())
            self.assertEqual(list(output.parent.glob(".capture.partial-*")), [])


if __name__ == "__main__":
    unittest.main()
