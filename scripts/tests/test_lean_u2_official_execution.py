from __future__ import annotations

import copy
import json
import shutil
import tempfile
import unittest
from pathlib import Path

from scripts import lean_u2_official_execution as U2


class LeanU2OfficialExecutionTests(unittest.TestCase):
    def spec(self) -> dict:
        return U2.build_spec(
            implementation_revision="a" * 40,
            source_root=Path("/tmp/axeyum-u2-source"),
            toolchain_root=Path("/tmp/axeyum-u2-toolchain"),
            harness_build=Path("/tmp/axeyum-u2-harness"),
            junit_path=Path("/tmp/axeyum-u2-private/test-results.xml"),
        )

    def terminal(self, exit_code: int = 0, prelaunch_sha256: str = "b" * 64) -> dict:
        return U2.seal(
            {
                "schema": U2.TERMINAL_SCHEMA,
                "run_id": U2.RUN_ID,
                "attempt_id": U2.ATTEMPT_ID,
                "sequence": U2.SEQUENCE,
                "prelaunch_sha256": prelaunch_sha256,
                "class": "exited",
                "exit_code": exit_code,
                "signal": None,
                "events": ["prelaunch-record-installed", "direct-child-reaped"],
                "wall_time": U2.metric("observed", 10, "milliseconds"),
                "cpu_time": U2.metric("not-observed", None, "milliseconds"),
                "peak_rss": U2.metric("observed", 4096, "bytes"),
                "process": {
                    "pid": 1,
                    "process_group_id": 1,
                    "rlimit_as_bytes": U2.MEMORY_LIMIT_BYTES,
                    "watchdog_fired": False,
                    "sigterm_sent": False,
                    "sigkill_sent": False,
                    "direct_child_reaped": True,
                    "live_non_zombie_pids_after_cleanup": [],
                },
                "raw_outputs": [
                    U2._raw_descriptor("raw/stderr.bin", b""),
                    U2._raw_descriptor("raw/stdout.bin", b""),
                ],
                "record_sha256": "",
            },
            U2.TERMINAL_SCHEMA,
        )

    def reseal(self, value: dict, schema: str) -> dict:
        return U2.seal(value, schema)

    def write_readonly(self, root: Path, relative: str, value: bytes) -> None:
        path = root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(value)
        path.chmod(0o444)

    def source_record(self) -> dict:
        definitions = (
            (U2.CASE_SOURCE, U2.CASE_SOURCE_SHA256),
            (U2.CASE_EXPECTED, U2.CASE_EXPECTED_SHA256),
            (U2.CASE_RUNNER, U2.CASE_RUNNER_SHA256),
            (U2.UTIL_SOURCE, U2.UTIL_SHA256),
            (U2.WITH_ENV_SOURCE, U2.WITH_ENV_SHA256),
            (U2.UNICODE_SOURCE_PATHS[0], "1" * 64),
            (U2.UNICODE_SOURCE_PATHS[1], "2" * 64),
        )
        rows = [
            {"path": path, "kind": "file", "mode": 0o644, "bytes": 1, "sha256": sha, "target": None}
            for path, sha in sorted(definitions)
        ]
        return U2.seal({
            "schema": U2.SOURCE_SCHEMA,
            "repository": "https://github.com/leanprover/lean4",
            "commit": U2.LEAN_COMMIT,
            "tree": U2.LEAN_TREE,
            "archive_bytes": 1,
            "archive_sha256": "c" * 64,
            "file_count": len(rows),
            "files_sha256": U2.domain_digest("axeyum-lean-u2-source-files-v1", rows),
            "files": rows,
            "record_sha256": "",
        }, U2.SOURCE_SCHEMA)

    def toolchain_record(self) -> dict:
        executables = {
            "lean": {"path": "/lean", "resolved_path": "/lean", "bytes": 1, "sha256": U2.PINNED_LEAN_SHA256, "version": U2.LEAN_VERSION_LINE},
            "leanc": {"path": "/leanc", "resolved_path": "/leanc", "bytes": 1, "sha256": U2.PINNED_LEANC_SHA256, "version": U2.LEANC_VERSION_PREFIX},
            "lake": {"path": "/lake", "resolved_path": "/lake", "bytes": 1, "sha256": U2.PINNED_LAKE_SHA256, "version": U2.LAKE_VERSION_LINE},
        }
        return U2.seal({
            "schema": U2.TOOLCHAIN_SCHEMA,
            "root": "/tmp/axeyum-u2-toolchain",
            "executables": executables,
            "file_count": 0,
            "files_sha256": U2.domain_digest("axeyum-lean-u2-toolchain-files-v1", []),
            "files": [],
            "record_sha256": "",
        }, U2.TOOLCHAIN_SCHEMA)

    def tools_record(self) -> dict:
        hashes = {
            "bash": U2.BASH_SHA256,
            "cmake": U2.CMAKE_SHA256,
            "ctest": U2.CTEST_SHA256,
            "python": U2.PYTHON_SHA256,
            "cxx": U2.CXX_SHA256,
            "cc": U2.CC_SHA256,
            "diff": U2.DIFF_SHA256,
            "perl": U2.PERL_SHA256,
        }
        tools = {
            name: {
                "path": f"/usr/bin/{name}",
                "resolved_path": f"/usr/bin/{name}",
                "bytes": 1,
                "sha256": sha,
                "version": "fixture version",
                "version_argv": [f"/usr/bin/{name}", "--version"],
            }
            for name, sha in hashes.items()
        }
        return U2.seal({
            "schema": U2.TOOLS_SCHEMA,
            "tools": tools,
            "record_sha256": "",
        }, U2.TOOLS_SCHEMA)

    def materialize_evidence(self, root: Path) -> None:
        spec = self.spec()
        source = self.source_record()
        toolchain = self.toolchain_record()
        tools = self.tools_record()
        wrapper = U2.render_environment_wrapper(Path(spec["source_root"]), Path(spec["toolchain_root"]))
        ctest_file = U2.render_ctest_file(Path(spec["source_root"]))
        discovery_payload = {
            "tests": [{
                "name": U2.CASE_ID,
                "command": [
                    "/usr/bin/bash",
                    f"{spec['source_root']}/tests/with_stage1_test_env.sh",
                    f"{spec['source_root']}/{U2.CASE_RUNNER}",
                    "534.lean",
                ],
                "properties": [{
                    "name": "WORKING_DIRECTORY",
                    "value": f"{spec['source_root']}/tests/compile",
                }],
            }]
        }
        discovery_raw = U2.canonical_bytes(discovery_payload)
        harness = U2.seal({
            "schema": U2.HARNESS_SCHEMA,
            "case_id": U2.CASE_ID,
            "wrapper": {"bytes": len(wrapper), "sha256": U2.sha256_bytes(wrapper), "mode": 0o755},
            "ctest_file": {"bytes": len(ctest_file), "sha256": U2.sha256_bytes(ctest_file)},
            "discovery": U2.normalize_discovery(discovery_payload, source_root=Path(spec["source_root"])),
            "discovery_raw_bytes": len(discovery_raw),
            "discovery_raw_sha256": U2.sha256_bytes(discovery_raw),
            "record_sha256": "",
        }, U2.HARNESS_SCHEMA)
        storage = U2.STORE.capture_storage_class(U2.STORE.STORAGE_CLASS_IDS[0], U2.ROOT)
        run = U2.build_run_record(spec, source, toolchain, tools, harness, storage)
        prelaunch = U2.build_prelaunch(
            spec,
            run,
            U2.failed_attempt_dependency(
                live_readonly_validated=True, git_index_validated=True
            ),
        )
        terminal = self.terminal(prelaunch_sha256=prelaunch["record_sha256"])
        raw_junit = b'<testsuite tests="1" failures="0"><testcase name="compile/534.lean"/></testsuite>'
        junit = U2.parse_junit(raw_junit, terminal)
        generated_payloads = {
            "tests/with_stage1_test_env.sh": wrapper,
            "tests/compile/534.lean.c": b"generated c\n",
            "tests/compile/534.lean.out": b"generated executable\n",
            "tests/compile/534.lean.out.produced": b"expected output\n",
            U2.CTEST_SOURCE_PATHS[0]: b"compile/534.lean 1 0\n---\n",
            U2.CTEST_SOURCE_PATHS[1]: b"passed CTest log\n",
        }
        modes = {
            "tests/with_stage1_test_env.sh": 0o755,
            "tests/compile/534.lean.c": 0o644,
            "tests/compile/534.lean.out": 0o755,
            "tests/compile/534.lean.out.produced": 0o644,
            U2.CTEST_SOURCE_PATHS[0]: 0o644,
            U2.CTEST_SOURCE_PATHS[1]: 0o644,
        }
        generated_paths = sorted(generated_payloads)
        generated_rows = [
            {
                "path": path,
                "kind": "file",
                "mode": modes[path],
                "bytes": len(generated_payloads[path]),
                "sha256": U2.sha256_bytes(generated_payloads[path]),
                "target": None,
            }
            for path in generated_paths
        ]
        post = U2.seal({
            "schema": U2.POST_SCHEMA,
            "source_record_sha256": source["record_sha256"],
            "original_file_count": len(source["files"]),
            "original_files_unchanged": True,
            "generated_paths": generated_paths,
            "case_generated_paths": [
                path for path in generated_paths if path in U2.CASE_GENERATED_SOURCE_PATHS
            ],
            "ctest_generated_paths": [
                path for path in generated_paths if path in U2.CTEST_SOURCE_PATHS
            ],
            "generated_files": generated_rows,
            "generated_files_sha256": U2.domain_digest("axeyum-lean-u2-generated-files-v1", generated_rows),
            "undeclared_paths": [],
            "record_sha256": "",
        }, U2.POST_SCHEMA)
        case = U2.build_case_record(spec, terminal, junit, post)
        json_records = {
            "source.json": source,
            "toolchain.json": toolchain,
            "tools.json": tools,
            "harness.json": harness,
            "spec.json": spec,
            "run.json": run,
            "prelaunch.json": prelaunch,
            "terminal.json": terminal,
            "junit.json": junit,
            "post.json": post,
            "case.json": case,
        }
        for relative, record in json_records.items():
            self.write_readonly(root, relative, U2.canonical_bytes(record))
        byte_records = {
            "artifacts/with_stage1_test_env.sh": wrapper,
            "artifacts/CTestTestfile.cmake": ctest_file,
            "raw/discovery.json": discovery_raw,
            "raw/stdout.bin": b"",
            "raw/stderr.bin": b"",
            "raw/junit.xml": raw_junit,
        }
        byte_records.update({U2.EVIDENCE_GENERATED_PATHS[path]: data for path, data in generated_payloads.items()})
        for relative, data in byte_records.items():
            self.write_readonly(root, relative, data)
        completion = U2.build_completion(root, case)
        self.write_readonly(root, "completion.json", U2.canonical_bytes(completion))

    def test_frozen_repository_and_parent_selection_authorities_are_current(self) -> None:
        self.assertEqual(U2.validate_repository_inputs(), [])
        self.assertEqual(U2.validate_selection_authorities(), [])

    def test_resume_contract_successor_is_current_only(self) -> None:
        relative = "scripts/smtcomp_repro/resume_contract.py"
        historical = "4713707b26d81e0e5444acc7c653b461fa79c2a94c392873c8565b443ba33930"
        current = "c128444f940b04a99a5be5def253d56df9f17d488dcb2d739891b0085dd0efd7"
        self.assertEqual(U2.REPOSITORY_INPUTS[relative], historical)
        self.assertEqual(U2.CURRENT_REPOSITORY_INPUT_OVERRIDES[relative], current)
        self.assertEqual(U2.sha256_file(U2.ROOT / relative), current)

        U2.CURRENT_REPOSITORY_INPUT_OVERRIDES[relative] = "0" * 64
        try:
            self.assertIn(
                f"frozen repository input drift: {relative}",
                U2.validate_repository_inputs(),
            )
        finally:
            U2.CURRENT_REPOSITORY_INPUT_OVERRIDES[relative] = current

    def test_spec_freezes_singleton_parent_command_environment_and_lane(self) -> None:
        spec = self.spec()
        self.assertEqual(U2.validate_spec(spec), [])
        self.assertEqual(spec["attempt_id"], "attempt-002")
        self.assertEqual(spec["sequence"], 2)
        self.assertEqual(spec["selection_case_ids"], [U2.CASE_ID])
        self.assertEqual(len(spec["command"]), 12)
        self.assertEqual(spec["command"][-4:], ["-E", "foreign", "-R", r"^compile/534[.]lean$"])
        self.assertEqual(spec["resource_envelope"]["memory_limit"]["value"], 8_589_934_592)
        self.assertEqual(spec["resource_envelope"]["ctest_worker_limit"]["value"], 1)
        self.assertEqual(spec["resource_envelope"]["lean_shell_worker_limit"]["value"], 1)
        self.assertEqual(
            spec["resource_envelope"]["generated_runtime_worker_limit"]["state"],
            "requested",
        )
        self.assertEqual(spec["resource_envelope"]["os_thread_limit"]["state"], "not-enforced")
        self.assertEqual(
            spec["resource_envelope"]["task_stack_policy"],
            "unmodified-Lean-default-no-s-option",
        )

    def test_wrapper_freezes_both_official_test_arrays_and_no_stack_override(self) -> None:
        wrapper = U2.render_environment_wrapper(
            Path("/tmp/axeyum-u2-source"), Path("/tmp/axeyum-u2-toolchain")
        ).decode()
        lean = "TEST_LEAN_ARGS=(-j1)"
        leani = "TEST_LEANI_ARGS=(-j1)"
        source = 'source "$TEST_DIR/util.sh"'
        self.assertEqual(wrapper.count(lean), 1)
        self.assertEqual(wrapper.count(leani), 1)
        self.assertLess(wrapper.index(lean), wrapper.index(leani))
        self.assertLess(wrapper.index(leani), wrapper.index(source))
        self.assertNotIn("--tstack", wrapper)
        self.assertNotRegex(wrapper, r"(?:^|\s)-s\d")

    def test_utf8_canonical_json_accepts_unicode_and_rejects_ascii_escaping(self) -> None:
        value = {"paths": list(U2.UNICODE_SOURCE_PATHS)}
        canonical = U2.canonical_bytes(value)
        self.assertIn("英語".encode(), canonical)
        with tempfile.TemporaryDirectory(dir=U2.ROOT) as temporary:
            path = Path(temporary) / "record.json"
            path.write_bytes(canonical)
            self.assertEqual(U2.load_canonical(path), value)
            path.write_bytes(
                (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()
            )
            with self.assertRaisesRegex(U2.U2ExecutionError, "noncanonical"):
                U2.load_canonical(path)

    def test_spec_rejects_shard_parent_command_environment_and_credit_drift(self) -> None:
        mutations = (
            lambda item: item.__setitem__("selection_case_ids", [U2.CASE_ID, "extra"]),
            lambda item: item["parent"].__setitem__("completed", True),
            lambda item: item["command"].__setitem__(-1, ".*"),
            lambda item: item["environment"].__setitem__("LEAN_NUM_THREADS", "2"),
            lambda item: item["resource_envelope"]["memory_limit"].__setitem__("value", 4),
            lambda item: item.__setitem__("credit_class", "parity"),
        )
        for mutate in mutations:
            with self.subTest(mutate=mutate):
                changed = copy.deepcopy(self.spec())
                mutate(changed)
                changed = self.reseal(changed, U2.SPEC_SCHEMA)
                self.assertTrue(U2.validate_spec(changed))

    def test_discovery_requires_exact_name_command_and_working_directory(self) -> None:
        source = Path("/tmp/axeyum-u2-source")
        payload = {
            "tests": [{
                "name": U2.CASE_ID,
                "command": [
                    "/usr/bin/bash",
                    str(source / "tests/with_stage1_test_env.sh"),
                    str(source / U2.CASE_RUNNER),
                    "534.lean",
                ],
                "properties": [{
                    "name": "WORKING_DIRECTORY",
                    "value": str(source / "tests/compile"),
                }],
            }]
        }
        self.assertEqual(U2.normalize_discovery(payload, source_root=source)["case_id"], U2.CASE_ID)
        for mutation in ("name", "command", "working"):
            changed = copy.deepcopy(payload)
            if mutation == "name":
                changed["tests"][0]["name"] = "compile/535.lean"
            elif mutation == "command":
                changed["tests"][0]["command"][-1] = "535.lean"
            else:
                changed["tests"][0]["properties"][0]["value"] = "/tmp/wrong"
            with self.subTest(mutation=mutation), self.assertRaises(U2.U2ExecutionError):
                U2.normalize_discovery(changed, source_root=source)

    def test_passing_junit_is_one_official_outcome_only(self) -> None:
        raw = (
            b'<testsuite name="release" tests="1" failures="0" errors="0" skipped="0" time="0.1">'
            b'<testcase name="compile/534.lean" classname="compile" time="0.1"/>'
            b"</testsuite>"
        )
        record = U2.parse_junit(raw, self.terminal())
        self.assertEqual(record["testcase"]["outcome"], "passed")
        credits = U2.case_credits("passed")
        self.assertEqual(credits["official_outcomes"], 1)
        self.assertEqual(credits["parity_credit"], 0)
        self.assertEqual(credits["parent_profile_completions"], 0)

    def test_failed_junit_is_a_decided_failure_not_a_parity_result(self) -> None:
        raw = (
            b'<testsuite tests="1" failures="1" errors="0" skipped="0">'
            b'<testcase name="compile/534.lean"><failure message="failed"/></testcase>'
            b"</testsuite>"
        )
        record = U2.parse_junit(raw, self.terminal(8))
        self.assertEqual(record["testcase"]["outcome"], "failed")
        self.assertEqual(U2.case_credits("failed")["official_failures"], 1)
        self.assertEqual(U2.case_credits("failed")["provider_completions"], 0)

    def test_junit_rejects_malformed_wrong_duplicate_extra_and_skipped_cases(self) -> None:
        invalid = (
            b"<testsuite>",
            b'<testsuite tests="1" failures="0"><testcase name="wrong"/></testsuite>',
            b'<testsuite tests="2" failures="0"><testcase name="compile/534.lean"/><testcase name="compile/534.lean"/></testsuite>',
            b'<testsuites><testsuite tests="1" failures="0"><testcase name="compile/534.lean"/></testsuite><testsuite tests="0" failures="0"/></testsuites>',
            b'<testsuite tests="1" failures="0" skipped="1"><testcase name="compile/534.lean"><skipped/></testcase></testsuite>',
        )
        for raw in invalid:
            with self.subTest(raw=raw), self.assertRaises(U2.U2ExecutionError):
                U2.parse_junit(raw, self.terminal())

    def test_junit_and_terminal_must_agree(self) -> None:
        passed = b'<testsuite tests="1" failures="0"><testcase name="compile/534.lean"/></testsuite>'
        failed = b'<testsuite tests="1" failures="1"><testcase name="compile/534.lean"><failure/></testcase></testsuite>'
        with self.assertRaisesRegex(U2.U2ExecutionError, "disagrees"):
            U2.parse_junit(passed, self.terminal(8))
        with self.assertRaisesRegex(U2.U2ExecutionError, "disagrees"):
            U2.parse_junit(failed, self.terminal(0))

    def test_manifest_rows_reject_unsafe_duplicate_and_unsorted_paths(self) -> None:
        base = {"kind": "file", "mode": 0o644, "bytes": 0, "sha256": U2.sha256_bytes(b""), "target": None}
        for rows in (
            [base | {"path": "../escape"}],
            [base | {"path": "b"}, base | {"path": "a"}],
            [base | {"path": "a"}, base | {"path": "a"}],
        ):
            with self.subTest(rows=rows):
                self.assertTrue(U2._validate_manifest_rows(rows, "fixture"))

    def test_source_record_binds_exact_official_files(self) -> None:
        record = self.source_record()
        self.assertEqual(U2.validate_source_record(record), [])
        changed = copy.deepcopy(record)
        changed["files"][0]["sha256"] = "d" * 64
        changed["files_sha256"] = U2.domain_digest("axeyum-lean-u2-source-files-v1", changed["files"])
        changed = U2.seal(changed, U2.SOURCE_SCHEMA)
        self.assertTrue(U2.validate_source_record(changed))

    def test_post_run_rejects_source_mutation_and_undeclared_artifacts(self) -> None:
        with tempfile.TemporaryDirectory(dir=U2.ROOT) as temporary:
            root = Path(temporary)
            tracked = root / "tracked"
            tracked.write_bytes(b"source")
            source = {"files": U2.manifest_tree(root), "record_sha256": "e" * 64}
            wrapper = U2.render_environment_wrapper(root, root)
            payloads_by_path = {
                "tests/with_stage1_test_env.sh": wrapper,
                "tests/compile/534.lean.c": b"c",
                "tests/compile/534.lean.out": b"out",
                "tests/compile/534.lean.out.produced": b"produced",
                U2.CTEST_SOURCE_PATHS[0]: b"cost",
                U2.CTEST_SOURCE_PATHS[1]: b"log",
            }
            for relative, payload in payloads_by_path.items():
                generated = root / relative
                generated.parent.mkdir(parents=True, exist_ok=True)
                generated.write_bytes(payload)
            record, payloads = U2.build_post_record(root, source, wrapper, "passed")
            self.assertEqual(
                set(record["generated_paths"]),
                {*U2.CASE_GENERATED_SOURCE_PATHS, *U2.CTEST_REQUIRED_SOURCE_PATHS},
            )
            self.assertEqual(payloads["tests/with_stage1_test_env.sh"], wrapper)
            (root / "undeclared").write_bytes(b"x")
            with self.assertRaisesRegex(U2.U2ExecutionError, "undeclared"):
                U2.build_post_record(root, source, wrapper, "passed")
            (root / "undeclared").unlink()
            tracked.write_bytes(b"changed")
            with self.assertRaisesRegex(U2.U2ExecutionError, "mutated"):
                U2.build_post_record(root, source, wrapper, "passed")

    def test_post_run_enforces_ctest_pass_and_failure_artifact_closure(self) -> None:
        with tempfile.TemporaryDirectory(dir=U2.ROOT) as temporary:
            root = Path(temporary)
            source = {"files": [], "record_sha256": "e" * 64}
            wrapper = U2.render_environment_wrapper(root, root)
            payloads = {
                "tests/with_stage1_test_env.sh": wrapper,
                "tests/compile/534.lean.c": b"c",
                "tests/compile/534.lean.out": b"out",
                "tests/compile/534.lean.out.produced": b"produced",
                U2.CTEST_SOURCE_PATHS[0]: b"cost",
                U2.CTEST_SOURCE_PATHS[1]: b"last",
            }
            for relative, payload in payloads.items():
                path = root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(payload)
            U2.build_post_record(root, source, wrapper, "passed")
            failed_log = root / U2.CTEST_SOURCE_PATHS[2]
            failed_log.write_bytes(b"failed")
            with self.assertRaisesRegex(U2.U2ExecutionError, "LastTestsFailed"):
                U2.build_post_record(root, source, wrapper, "passed")
            U2.build_post_record(root, source, wrapper, "failed")
            failed_log.unlink()
            with self.assertRaisesRegex(U2.U2ExecutionError, "required CTest"):
                U2.build_post_record(root, source, wrapper, "failed")
            (root / U2.CTEST_SOURCE_PATHS[1]).unlink()
            with self.assertRaisesRegex(U2.U2ExecutionError, "exact declared"):
                U2.build_post_record(root, source, wrapper, "passed")

    def test_case_record_cannot_claim_parent_provider_axeyum_or_parity_credit(self) -> None:
        junit = U2.parse_junit(
            b'<testsuite tests="1" failures="0"><testcase name="compile/534.lean"/></testsuite>',
            self.terminal(),
        )
        post = U2.seal({
            "schema": U2.POST_SCHEMA,
            "source_record_sha256": "f" * 64,
            "original_file_count": 1,
            "original_files_unchanged": True,
            "generated_paths": ["tests/with_stage1_test_env.sh"],
            "case_generated_paths": ["tests/with_stage1_test_env.sh"],
            "ctest_generated_paths": [],
            "generated_files": [],
            "generated_files_sha256": U2.domain_digest("axeyum-lean-u2-generated-files-v1", []),
            "undeclared_paths": [],
            "record_sha256": "",
        }, U2.POST_SCHEMA)
        case = U2.build_case_record(self.spec(), self.terminal(), junit, post)
        self.assertFalse(case["official_provider_claimed"])
        self.assertFalse(case["parent"]["completed"])
        self.assertEqual(case["credits"]["axeyum_outcomes"], 0)
        self.assertEqual(case["credits"]["parity_credit"], 0)

    def test_synthetic_complete_evidence_closes_exact_dependencies_offline(self) -> None:
        with tempfile.TemporaryDirectory(dir=U2.ROOT) as temporary:
            root = Path(temporary)
            self.materialize_evidence(root)
            completion, evidence = U2.validate_evidence_root(root)
            self.assertEqual(completion["projection"]["case_outcome"], "passed")
            self.assertEqual(completion["credits"]["official_outcomes"], 1)
            self.assertEqual(completion["credits"]["parity_credit"], 0)
            self.assertEqual({row["path"] for row in evidence}, set(U2.BASE_EVIDENCE_PATHS))

    def test_result_authority_retains_two_attempts_and_one_bounded_outcome(self) -> None:
        with tempfile.TemporaryDirectory(dir=U2.ROOT) as temporary:
            root = Path(temporary)
            self.materialize_evidence(root)
            authority = U2.build_result_authority(
                root, implementation_revision="a" * 40
            )
            self.assertEqual(U2.validate_result_authority(authority), [])
            self.assertEqual(authority["summary"]["process_attempts"], 2)
            self.assertEqual(authority["summary"]["official_outcomes"], 1)
            self.assertEqual(authority["attempts"][0]["official_outcomes"], 0)
            self.assertEqual(authority["attempts"][1]["official_outcomes"], 1)
            self.assertEqual(authority["credits"]["parity_credit"], 0)
            source_inputs = {
                row["path"]: row["sha256"] for row in authority["source_inputs"]
            }
            self.assertEqual(
                source_inputs["scripts/smtcomp_repro/resume_contract.py"],
                U2.REPOSITORY_INPUTS["scripts/smtcomp_repro/resume_contract.py"],
            )

    def test_complete_evidence_rejects_missing_extra_and_raw_drift(self) -> None:
        mutations = ("missing", "extra", "raw-drift")
        for mutation in mutations:
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory(dir=U2.ROOT) as temporary:
                root = Path(temporary)
                self.materialize_evidence(root)
                if mutation == "missing":
                    (root / "raw/stdout.bin").unlink()
                elif mutation == "extra":
                    self.write_readonly(root, "extra.bin", b"extra")
                else:
                    path = root / "raw/stdout.bin"
                    path.chmod(0o644)
                    path.write_bytes(b"drift")
                    path.chmod(0o444)
                with self.assertRaises(U2.U2ExecutionError):
                    U2.validate_evidence_root(root)

    def test_live_evidence_rejects_writable_but_offline_checkout_accepts_it(self) -> None:
        with tempfile.TemporaryDirectory(dir=U2.ROOT) as temporary:
            root = Path(temporary)
            self.materialize_evidence(root)
            path = root / "case.json"
            path.chmod(0o644)
            U2.validate_evidence_root(root)
            with self.assertRaisesRegex(U2.U2ExecutionError, "not read-only"):
                U2.validate_evidence_root(root, require_live_readonly=True)

    def test_failed_attempt_dependency_validates_checkout_git_mode(self) -> None:
        dependency = U2.validate_failed_attempt(
            require_live_readonly=False,
            require_git_index=True,
        )
        self.assertEqual(
            dependency,
            U2.failed_attempt_dependency(
                live_readonly_validated=False, git_index_validated=True
            ),
        )
        self.assertEqual(dependency["official_outcomes"], 0)
        self.assertEqual(dependency["parity_credit"], 0)

    def test_failed_attempt_live_mode_is_distinct_from_offline_content_validation(self) -> None:
        with tempfile.TemporaryDirectory(dir=U2.ROOT) as temporary:
            root = Path(temporary) / "failed"
            shutil.copytree(U2.FAILED_EVIDENCE_ROOT, root)
            for path in root.rglob("*"):
                if path.is_file():
                    path.chmod(0o444)
            U2.validate_failed_attempt(
                root, require_live_readonly=True, require_git_index=False
            )
            path = root / "terminal.json"
            path.chmod(0o644)
            U2.validate_failed_attempt(
                root, require_live_readonly=False, require_git_index=False
            )
            with self.assertRaisesRegex(U2.U2ExecutionError, "mode 0444"):
                U2.validate_failed_attempt(
                    root, require_live_readonly=True, require_git_index=False
                )

    def test_failed_attempt_rejects_added_missing_symlink_and_content_drift(self) -> None:
        for mutation in ("added", "missing", "symlink", "content"):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory(
                dir=U2.ROOT
            ) as temporary:
                root = Path(temporary) / "failed"
                shutil.copytree(U2.FAILED_EVIDENCE_ROOT, root)
                if mutation == "added":
                    (root / "extra").write_bytes(b"extra")
                elif mutation == "missing":
                    (root / "raw/stderr.bin").unlink()
                elif mutation == "symlink":
                    path = root / "raw/stderr.bin"
                    path.unlink()
                    path.symlink_to("stdout.bin")
                else:
                    path = root / "raw/stderr.bin"
                    path.chmod(0o644)
                    path.write_bytes(b"drift")
                with self.assertRaises(U2.U2ExecutionError):
                    U2.validate_failed_attempt(
                        root, require_live_readonly=False, require_git_index=False
                    )

    def test_complete_evidence_rejects_case_credit_and_completion_drift(self) -> None:
        with tempfile.TemporaryDirectory(dir=U2.ROOT) as temporary:
            root = Path(temporary)
            self.materialize_evidence(root)
            path = root / "case.json"
            changed = U2.load_canonical(path)
            changed["credits"]["parity_credit"] = 1
            changed = U2.seal(changed, U2.CASE_SCHEMA)
            path.chmod(0o644)
            path.write_bytes(U2.canonical_bytes(changed))
            path.chmod(0o444)
            with self.assertRaisesRegex(U2.U2ExecutionError, "case record"):
                U2.validate_evidence_root(root)

    def test_toolchain_manifest_and_executable_identity_drift_reject(self) -> None:
        record = self.toolchain_record()
        self.assertEqual(U2.validate_toolchain_record(record), [])
        for mutation in ("hash", "manifest"):
            changed = copy.deepcopy(record)
            if mutation == "hash":
                changed["executables"]["lean"]["sha256"] = "0" * 64
            else:
                changed["file_count"] = 1
            changed = U2.seal(changed, U2.TOOLCHAIN_SCHEMA)
            with self.subTest(mutation=mutation):
                self.assertTrue(U2.validate_toolchain_record(changed))


if __name__ == "__main__":
    unittest.main()
