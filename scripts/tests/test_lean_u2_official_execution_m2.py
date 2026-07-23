from __future__ import annotations

import copy
import subprocess
import sys
import unittest
import xml.etree.ElementTree as ET
from pathlib import Path
from unittest import mock

from scripts import lean_u2_official_execution as BASE
from scripts import lean_u2_official_execution_m2 as M2


ROOT = Path(__file__).resolve().parents[2]


def terminal(exit_code: int) -> dict:
    return BASE.seal(
        {
            "schema": BASE.TERMINAL_SCHEMA,
            "class": "exited",
            "exit_code": exit_code,
            "signal": None,
            "process": {
                "watchdog_fired": False,
                "direct_child_reaped": True,
                "live_non_zombie_pids_after_cleanup": [],
            },
            "record_sha256": "",
        },
        BASE.TERMINAL_SCHEMA,
    )


def junit_xml(*, failed_index: int | None = None, skipped_index: int | None = None) -> bytes:
    case_ids = M2.selected_contract()["shard"]["case_ids"]
    suite = ET.Element(
        "testsuite",
        {
            "name": "M2",
            "tests": str(len(case_ids)),
            "failures": "1" if failed_index is not None else "0",
            "errors": "0",
            "skipped": "1" if skipped_index is not None else "0",
            "time": "1.0",
        },
    )
    for index, case_id in enumerate(case_ids):
        testcase = ET.SubElement(
            suite,
            "testcase",
            {"name": case_id, "classname": "CTest", "time": "0.01"},
        )
        if index == failed_index:
            ET.SubElement(testcase, "failure", {"message": "expected synthetic failure"})
        if index == skipped_index:
            ET.SubElement(testcase, "skipped")
    return ET.tostring(suite, encoding="utf-8", xml_declaration=True)


def file_rows(paths: list[str]) -> list[dict]:
    return [
        {
            "path": path,
            "kind": "file",
            "mode": 0o644,
            "bytes": len(path),
            "sha256": BASE.sha256_bytes(path.encode()),
            "target": None,
        }
        for path in sorted(paths)
    ]


class LeanU2OfficialExecutionM2Tests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.contract = M2.selected_contract()
        cls.source = Path("/m2/source")
        cls.toolchain = Path("/m2/toolchain")
        cls.harness = Path("/m2/harness")

    def spec(self) -> dict:
        return M2.build_spec(
            implementation_revision="1" * 40,
            source_root=self.source,
            toolchain_root=self.toolchain,
            harness_build=self.harness,
            junit_path=Path("/m2/attempt/test-results.xml"),
        )

    def discovery(self) -> dict:
        return M2.synthetic_discovery(
            source_root=self.source,
            toolchain_root=self.toolchain,
            harness_root=self.harness,
        )

    def test_frozen_contract_selects_exact_lowest_zero_history_shard(self) -> None:
        contract = self.contract
        shard = contract["shard"]
        self.assertEqual(shard["id"], M2.SHARD_ID)
        self.assertEqual(shard["record_sha256"], M2.SHARD_SHA256)
        self.assertEqual((shard["ordinal"], shard["start_offset"], shard["end_offset"]), (1, 64, 128))
        self.assertEqual(shard["case_count"], 64)
        self.assertEqual(shard["historical_observation_case_ids"], [])
        self.assertEqual(contract["cases"][0]["id"], "compile/uint_fold.lean")
        self.assertEqual(contract["cases"][-1]["id"], "docparse/block_0004.txt")
        self.assertEqual(
            sum(1 for row in contract["cases"] if row["family"] == "compile_bench"),
            24,
        )
        self.assertEqual(sum(1 for row in contract["cases"] if row["family"] == "docparse"), 35)

    def test_current_u2_runner_override_preserves_historical_identity(self) -> None:
        relative = "scripts/lean_u2_official_execution.py"
        self.assertEqual(
            M2.REPOSITORY_INPUTS[relative],
            "47c779d5b465e32b1ffa8faf3598472ed2ac98bd058928494e65a68d4f205fc2",
        )
        self.assertEqual(
            M2.CURRENT_REPOSITORY_INPUT_OVERRIDES[relative],
            "1f44b340daeae2c03eb3157515609f158cdaf4733575aa9c36cccc510e301ad9",
        )
        self.assertEqual(
            BASE.sha256_file(BASE.ROOT / relative),
            "1f44b340daeae2c03eb3157515609f158cdaf4733575aa9c36cccc510e301ad9",
        )
        self.assertEqual(M2.validate_repository_inputs(), [])

    def test_spec_is_exact_and_forbids_execution_shortcuts(self) -> None:
        spec = self.spec()
        self.assertEqual(M2.validate_spec(spec), [])
        self.assertEqual(len(spec["case_refs"]), 64)
        self.assertEqual(spec["command"][-2:], ["-E", "foreign"])
        self.assertNotIn("-R", spec["command"])
        self.assertNotIn("LEAN_CC", spec["environment"])
        self.assertNotIn("TEST_BENCH", spec["environment"])
        self.assertEqual(spec["resource_envelope"]["wall_timeout"]["value"], 3_600_000)
        self.assertEqual(spec["resource_envelope"]["memory_limit"]["value"], 8_589_934_592)
        self.assertFalse(spec["resource_envelope"]["official_provider_claimed"])

    def test_resealed_spec_mutations_are_rejected(self) -> None:
        mutations = (
            lambda row: row["command"].append("-R"),
            lambda row: row["environment"].__setitem__("LEAN_CC", "/usr/bin/cc"),
            lambda row: row["resource_envelope"]["wall_timeout"].__setitem__("value", 1),
            lambda row: row["case_refs"].pop(),
            lambda row: row["parent"].__setitem__("completed", True),
            lambda row: row.__setitem__("credit_class", "parent-profile"),
        )
        for mutate in mutations:
            changed = copy.deepcopy(self.spec())
            mutate(changed)
            changed = BASE.seal(changed, M2.SPEC_SCHEMA)
            with self.subTest(mutate=mutate):
                self.assertTrue(M2.validate_spec(changed))

    def test_wrapper_and_ctest_file_render_all_cases_without_live_discovery(self) -> None:
        wrapper = M2.render_environment_wrapper(self.source, self.toolchain)
        self.assertNotIn(b"LEAN_CC", wrapper)
        self.assertNotIn(b"TEST_BENCH", wrapper)
        self.assertEqual(wrapper.count(b"TEST_LEAN_ARGS=(-j1)"), 1)
        ctest = M2.render_ctest_file(
            source_root=self.source,
            toolchain_root=self.toolchain,
            harness_root=self.harness,
        ).decode()
        self.assertEqual(ctest.count("add_test("), 64)
        self.assertEqual(ctest.count("set_tests_properties("), 64)
        self.assertIn("compile/uint_fold.lean", ctest)
        self.assertIn("docparse/block_0004.txt", ctest)
        self.assertNotIn("compile/534.lean", ctest)

    def test_synthetic_discovery_round_trips_exact_order_and_properties(self) -> None:
        payload = self.discovery()
        normalized = M2.normalize_discovery(
            payload,
            source_root=self.source,
            toolchain_root=self.toolchain,
            harness_root=self.harness,
        )
        self.assertEqual(len(normalized), 64)
        self.assertEqual([row["id"] for row in normalized], self.contract["shard"]["case_ids"])
        record = M2.build_harness_record(
            source_root=self.source,
            toolchain_root=self.toolchain,
            harness_root=self.harness,
            discovery_payload=payload,
        )
        self.assertTrue(BASE.valid_seal(record, M2.HARNESS_SCHEMA))

    def test_discovery_count_order_command_and_property_mutations_reject(self) -> None:
        mutations = (
            lambda rows: rows.pop(),
            lambda rows: rows.__setitem__(slice(0, 2), list(reversed(rows[:2]))),
            lambda rows: rows[0]["command"].append("invented"),
            lambda rows: rows[0]["properties"][0].__setitem__("value", "/wrong"),
            lambda rows: rows[1].__setitem__("name", rows[0]["name"]),
        )
        for mutate in mutations:
            payload = self.discovery()
            mutate(payload["tests"])
            with self.subTest(mutate=mutate):
                with self.assertRaises(M2.M2ContractError):
                    M2.normalize_discovery(
                        payload,
                        source_root=self.source,
                        toolchain_root=self.toolchain,
                        harness_root=self.harness,
                    )

    def test_junit_all_pass_and_mixed_failure_are_exact(self) -> None:
        passed = M2.parse_junit(junit_xml(), terminal(0))
        self.assertEqual(
            passed["summary"],
            {
                "official_cases": 64,
                "official_outcomes": 64,
                "official_passes": 64,
                "official_failures": 0,
            },
        )
        failed = M2.parse_junit(junit_xml(failed_index=17), terminal(8))
        self.assertEqual((failed["summary"]["official_passes"], failed["summary"]["official_failures"]), (63, 1))
        self.assertEqual(failed["cases"][17]["outcome"], "failed")

    def test_junit_missing_reordered_skipped_aggregate_and_terminal_mutations_reject(self) -> None:
        cases = self.contract["shard"]["case_ids"]
        bad_payloads = []
        missing = ET.fromstring(junit_xml())
        missing.remove(list(missing)[-1])
        bad_payloads.append(ET.tostring(missing))
        reordered = ET.fromstring(junit_xml())
        reordered[0].set("name", cases[1])
        bad_payloads.append(ET.tostring(reordered))
        skipped = junit_xml(skipped_index=0)
        bad_payloads.append(skipped)
        disabled = ET.fromstring(junit_xml())
        disabled.set("disabled", "1")
        bad_payloads.append(ET.tostring(disabled))
        aggregate = ET.fromstring(junit_xml(failed_index=0))
        aggregate.set("failures", "0")
        bad_payloads.append(ET.tostring(aggregate))
        bad_payloads.append(b"<not-xml")
        for payload in bad_payloads:
            with self.subTest(payload=payload[:40]):
                with self.assertRaises(M2.M2ContractError):
                    M2.parse_junit(payload, terminal(0))
        with self.assertRaisesRegex(M2.M2ContractError, "terminal"):
            M2.parse_junit(junit_xml(), terminal(8))
        with self.assertRaisesRegex(M2.M2ContractError, "terminal"):
            M2.parse_junit(junit_xml(failed_index=0), terminal(0))

    def test_generated_artifact_closure_and_credit_projection_are_bounded(self) -> None:
        original = file_rows(["tests/compile/uint_fold.lean", "tests/util.sh"])
        passed_junit = M2.parse_junit(junit_xml(), terminal(0))
        pass_paths = sorted(
            set(M2.declared_generated_paths()) - {BASE.CTEST_SOURCE_PATHS[2]}
        )
        post = M2.build_post_record(
            original_files=original,
            generated_files=file_rows(pass_paths),
            junit=passed_junit,
        )
        projection = M2.result_projection(passed_junit, post)
        credits = projection["credits"]
        self.assertEqual(credits["official_cases"], 64)
        self.assertEqual(credits["unique_new_official_cases"], 64)
        self.assertEqual(credits["local_physical_shards_completed"], 1)
        self.assertEqual(credits["parent_profile_completions"], 0)
        self.assertEqual(credits["parity_credit"], 0)
        self.assertFalse(projection["claims"]["lean_parity_established"])

        failed_junit = M2.parse_junit(junit_xml(failed_index=0), terminal(8))
        failed_paths = sorted(set(pass_paths) | {BASE.CTEST_SOURCE_PATHS[2]})
        failed_post = M2.build_post_record(
            original_files=original,
            generated_files=file_rows(failed_paths),
            junit=failed_junit,
        )
        self.assertTrue(BASE.valid_seal(failed_post, M2.POST_SCHEMA))

    def test_artifact_undeclared_missing_passed_and_malformed_rows_reject(self) -> None:
        original = file_rows(["tests/util.sh"])
        junit = M2.parse_junit(junit_xml(), terminal(0))
        pass_paths = sorted(
            set(M2.declared_generated_paths()) - {BASE.CTEST_SOURCE_PATHS[2]}
        )
        bad_sets = (
            pass_paths + ["tests/invented"],
            [path for path in pass_paths if path != BASE.CTEST_REQUIRED_SOURCE_PATHS[0]],
            [path for path in pass_paths if path != "tests/compile/uint_fold.lean.out.produced"],
        )
        for paths in bad_sets:
            with self.subTest(paths=len(paths)):
                with self.assertRaises(M2.M2ContractError):
                    M2.build_post_record(
                        original_files=original,
                        generated_files=file_rows(paths),
                        junit=junit,
                    )
        malformed = file_rows(pass_paths)
        malformed[0]["sha256"] = "bad"
        with self.assertRaises(M2.M2ContractError):
            M2.build_post_record(
                original_files=original, generated_files=malformed, junit=junit
            )
        malformed_original = file_rows(["tests/util.sh"])
        malformed_original[0].pop("mode")
        with self.assertRaises(M2.M2ContractError):
            M2.build_post_record(
                original_files=malformed_original,
                generated_files=file_rows(pass_paths),
                junit=junit,
            )
        forged_junit = copy.deepcopy(junit)
        forged_junit["summary"]["official_passes"] = 63
        forged_junit = BASE.seal(forged_junit, M2.JUNIT_SCHEMA)
        with self.assertRaisesRegex(M2.M2ContractError, "JUnit summary"):
            M2.build_post_record(
                original_files=original,
                generated_files=file_rows(pass_paths),
                junit=forged_junit,
            )

    def test_credit_projection_rejects_forged_junit_or_post_linkage(self) -> None:
        junit = M2.parse_junit(junit_xml(), terminal(0))
        paths = sorted(
            set(M2.declared_generated_paths()) - {BASE.CTEST_SOURCE_PATHS[2]}
        )
        post = M2.build_post_record(
            original_files=file_rows(["tests/util.sh"]),
            generated_files=file_rows(paths),
            junit=junit,
        )
        forged_junit = copy.deepcopy(junit)
        forged_junit["cases"][0]["outcome"] = "failed"
        forged_junit = BASE.seal(forged_junit, M2.JUNIT_SCHEMA)
        with self.assertRaises(M2.M2ContractError):
            M2.result_projection(forged_junit, post)
        forged_post = copy.deepcopy(post)
        forged_post["junit_sha256"] = "0" * 64
        forged_post = BASE.seal(forged_post, M2.POST_SCHEMA)
        with self.assertRaisesRegex(M2.M2ContractError, "linkage"):
            M2.result_projection(junit, forged_post)

    def test_input_and_lowest_ordinal_mutations_fail_closed(self) -> None:
        hashes = dict(M2.REPOSITORY_INPUTS)
        hashes[next(iter(hashes))] = "0" * 64
        M2.validated_authorities.cache_clear()
        M2.selected_contract.cache_clear()
        with mock.patch.object(M2, "REPOSITORY_INPUTS", hashes):
            with self.assertRaisesRegex(M2.M2ContractError, "repository input drift"):
                M2.selected_contract()

        M2.validated_authorities.cache_clear()
        M2.selected_contract.cache_clear()
        u2, profiles, shards = M2.validated_authorities()
        mutated_shards = copy.deepcopy(shards)
        shard0 = next(
            row
            for row in mutated_shards["shards"]
            if row["ordinal"] == 0
            and row["membership_plan_id"] == M2.MEMBERSHIP_ID
        )
        shard0["historical_observation_case_ids"] = []

        M2.selected_contract.cache_clear()
        with mock.patch.object(
            M2,
            "validated_authorities",
            return_value=(u2, profiles, mutated_shards),
        ):
            with self.assertRaisesRegex(M2.M2ContractError, "lowest-ordinal"):
                M2.selected_contract()
        M2.validated_authorities.cache_clear()
        M2.selected_contract.cache_clear()
        M2.selected_contract()

    def test_direct_cli_is_offline_only(self) -> None:
        help_result = subprocess.run(
            [sys.executable, str(Path(M2.__file__).resolve()), "--help"],
            cwd=ROOT,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            timeout=30,
        )
        self.assertEqual(help_result.returncode, 0, help_result.stderr.decode())
        self.assertNotIn(b"run-m2", help_result.stdout)
        checked = subprocess.run(
            [sys.executable, str(Path(M2.__file__).resolve()), "--check"],
            cwd=ROOT,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            timeout=30,
        )
        self.assertEqual(checked.returncode, 0, checked.stderr.decode())
        self.assertIn(b"live_execution=false|outcomes=0|pairs=0|parity=0", checked.stdout)


if __name__ == "__main__":
    unittest.main()
