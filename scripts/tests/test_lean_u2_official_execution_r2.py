from __future__ import annotations

import base64
import copy
import unittest
from pathlib import Path

from scripts import lean_u2_official_execution as BASE
from scripts import lean_u2_official_execution_r2 as R2


class LeanU2OfficialExecutionR2Tests(unittest.TestCase):
    def spec(self) -> dict:
        with R2.base_r2_configuration():
            return BASE.build_spec(
                implementation_revision="a" * 40,
                source_root=Path("/tmp/axeyum-u2-r2-source"),
                toolchain_root=Path("/tmp/axeyum-u2-r2-toolchain"),
                harness_build=Path("/tmp/axeyum-u2-r2-harness"),
                junit_path=Path("/tmp/axeyum-u2-r2-private/test-results.xml"),
            )

    def compiler_contract(self) -> dict:
        root = Path("/toolchain")
        stdout = b""
        stderr = (
            f"{root}/bin/clang --sysroot {root} probe.c\n"
            f'"{root}/bin/ld.lld" --sysroot={root} probe.o\n'
        ).encode()
        output = b"\x7fELFfixture"
        payload = {
            "domain": R2.COMPILER_CONTRACT_DOMAIN,
            "lean_cc": {"state": "absent", "value": None},
            "command": [
                str(root / "bin/leanc"),
                "-v",
                "-o",
                "/probe/probe.out",
                "/probe/probe.c",
            ],
            "environment": {
                "LANG": "C.UTF-8",
                "LC_ALL": "C.UTF-8",
                "PATH": f"{root}/bin:/usr/bin:/bin",
                "TZ": "UTC",
            },
            "source": {
                "bytes": len(R2.COMPILER_PROBE_SOURCE),
                "sha256": BASE.sha256_bytes(R2.COMPILER_PROBE_SOURCE),
                "utf8": R2.COMPILER_PROBE_SOURCE.decode(),
            },
            "terminal": {"class": "exited", "exit_code": 0},
            "stdout": {
                "bytes": len(stdout),
                "sha256": BASE.sha256_bytes(stdout),
                "utf8": stdout.decode(),
            },
            "stderr": {
                "bytes": len(stderr),
                "sha256": BASE.sha256_bytes(stderr),
                "utf8": stderr.decode(),
            },
            "output": {
                "bytes": len(output),
                "sha256": BASE.sha256_bytes(output),
                "base64": base64.b64encode(output).decode(),
            },
            "selected_compiler": R2._expected_file_identity("bin/clang"),
            "selected_linker": R2._expected_file_identity("bin/ld.lld"),
            "static_cxx": [
                R2._expected_file_identity("lib/libc++.a"),
                R2._expected_file_identity("lib/libc++abi.a"),
            ],
        }
        return payload | {
            "identity_sha256": BASE.domain_digest(R2.COMPILER_CONTRACT_DOMAIN, payload)
        }

    def result_authority(self, outcome: str = "passed") -> dict:
        credits = R2.aggregate_credits(outcome)
        evidence: list[dict] = []
        value = {
            "schema": R2.RESULT_SCHEMA,
            "status": "complete-local-official-case-history",
            "implementation_revision": "a" * 40,
            "r2_preregistration_commit": R2.R2_PREREGISTRATION_COMMIT,
            "r2_plan_sha256": R2.R2_PLAN_SHA256,
            "r1_authority_bytes_sha256": R2.R1_AUTHORITY_BYTES_SHA256,
            "r1_authority_record_sha256": R2.R1_AUTHORITY_RECORD_SHA256,
            "failed_attempt": R2.failed_attempt_dependency(
                live_readonly_validated=True, git_index_validated=True
            ),
            "attempts": [
                {
                    "id": "attempt-001",
                    "sequence": 1,
                    "official_outcomes": 0,
                },
                {
                    "id": "attempt-002",
                    "sequence": 2,
                    "outcome": "failed",
                    "official_outcomes": 1,
                },
                {
                    "id": R2.ATTEMPT_ID,
                    "sequence": R2.SEQUENCE,
                    "outcome": outcome,
                    "official_outcomes": 1,
                },
            ],
            "case": {"id": BASE.CASE_ID, "outcome": outcome},
            "summary": {
                "process_attempts": 3,
                "incomplete_process_attempts": 1,
                "completed_process_attempts": 2,
                "official_outcomes": 2,
                "official_passes": int(outcome == "passed"),
                "official_failures": 1 + int(outcome == "failed"),
                "parent_profiles_completed": 0,
                "axeyum_outcomes": 0,
                "paired_cells": 0,
                "performance_rows": 0,
            },
            "claims": {
                "parent_profile_complete": False,
                "official_provider_reproduced": False,
                "axeyum_observed": False,
                "matched_pair_formed": False,
                "performance_measured": False,
                "lean_parity_established": False,
            },
            "evidence_files": evidence,
            "evidence_manifest_sha256": BASE.domain_digest(
                "axeyum-lean-u2-official-execution-evidence-files-v1", evidence
            ),
            "credits": credits,
            "record_sha256": "",
        }
        return BASE.seal(value, R2.RESULT_SCHEMA)

    def test_repository_r2_plan_and_r1_authority_are_frozen(self) -> None:
        self.assertEqual(R2.validate_repository_inputs(), [])

    def test_prior_attempts_validate_offline_with_one_decided_failure(self) -> None:
        dependency = R2.validate_failed_attempt(
            require_live_readonly=False,
            require_git_index=True,
        )
        self.assertEqual(dependency["process_attempts"], 2)
        self.assertEqual(dependency["official_outcomes"], 1)
        self.assertEqual(dependency["official_passes"], 0)
        self.assertEqual(dependency["official_failures"], 1)
        self.assertEqual(dependency["parity_credit"], 0)
        self.assertEqual([row["attempt_id"] for row in dependency["attempts"]], [
            "attempt-001",
            "attempt-002",
        ])

    def test_r2_spec_freezes_attempt_lane_prior_history_and_no_lean_cc(self) -> None:
        spec = self.spec()
        with R2.base_r2_configuration():
            self.assertEqual(BASE.validate_spec(spec), [])
        self.assertEqual(spec["attempt_id"], R2.ATTEMPT_ID)
        self.assertEqual(spec["sequence"], R2.SEQUENCE)
        self.assertEqual(spec["resource_envelope"]["lane_id"], R2.LANE_ID)
        self.assertEqual(spec["r2_preregistration_commit"], R2.R2_PREREGISTRATION_COMMIT)
        self.assertNotIn("LEAN_CC", spec["environment"])

    def test_r2_spec_rejects_plan_prior_lane_and_environment_drift(self) -> None:
        mutations = (
            lambda item: item.__setitem__("r2_plan_sha256", "0" * 64),
            lambda item: item.__setitem__("prior_attempts_sha256", "0" * 64),
            lambda item: item["resource_envelope"].__setitem__("lane_id", "wrong"),
            lambda item: item["environment"].__setitem__("LEAN_CC", "/usr/bin/cc"),
        )
        for mutate in mutations:
            changed = copy.deepcopy(self.spec())
            mutate(changed)
            changed = BASE.seal(changed, BASE.SPEC_SCHEMA)
            with self.subTest(mutate=mutate), R2.base_r2_configuration():
                self.assertTrue(BASE.validate_spec(changed))

    def test_wrapper_removes_only_lean_cc_and_preserves_worker_arrays(self) -> None:
        source = Path("/tmp/source")
        toolchain = Path("/tmp/toolchain")
        r1 = R2.ORIG_RENDER_WRAPPER(source, toolchain)
        r2 = R2.render_environment_wrapper(source, toolchain)
        self.assertEqual(
            r1.replace(b"export LEAN_CC=/usr/bin/cc ", b"export ", 1), r2
        )
        self.assertNotIn(b"LEAN_CC", r2)
        self.assertEqual(r2.count(b"TEST_LEAN_ARGS=(-j1)"), 1)
        self.assertEqual(r2.count(b"TEST_LEANI_ARGS=(-j1)"), 1)
        self.assertNotIn(b"--tstack", r2)

    def test_compiler_contract_binds_bundled_tools_archives_and_raw_evidence(self) -> None:
        contract = self.compiler_contract()
        self.assertEqual(R2.validate_compiler_contract(contract, Path("/toolchain")), [])

    def test_compiler_contract_rejects_environment_command_source_tool_and_output_drift(
        self,
    ) -> None:
        mutations = (
            lambda item: item["environment"].__setitem__("LEAN_CC", "/usr/bin/cc"),
            lambda item: item["environment"].__setitem__("TZ", "America/New_York"),
            lambda item: item["command"].__setitem__(1, "--version"),
            lambda item: item["source"].__setitem__("utf8", "int main(void) { return 1; }\n"),
            lambda item: item["stderr"].__setitem__(
                "utf8", item["stderr"]["utf8"] + "/usr/bin/cc ld.bfd"
            ),
            lambda item: item["static_cxx"][0].__setitem__("sha256", "0" * 64),
            lambda item: item["output"].__setitem__("base64", "not-base64"),
        )
        for mutate in mutations:
            changed = copy.deepcopy(self.compiler_contract())
            mutate(changed)
            payload = {key: value for key, value in changed.items() if key != "identity_sha256"}
            changed["identity_sha256"] = BASE.domain_digest(
                R2.COMPILER_CONTRACT_DOMAIN, payload
            )
            with self.subTest(mutate=mutate):
                self.assertTrue(
                    R2.validate_compiler_contract(changed, Path("/toolchain"))
                )

    def test_context_restores_r1_globals_and_result_replay(self) -> None:
        before = (BASE.ATTEMPT_ID, BASE.SEQUENCE, BASE.LANE_ID)
        with R2.base_r2_configuration():
            self.assertEqual((BASE.ATTEMPT_ID, BASE.SEQUENCE, BASE.LANE_ID), (
                R2.ATTEMPT_ID,
                R2.SEQUENCE,
                R2.LANE_ID,
            ))
        self.assertEqual((BASE.ATTEMPT_ID, BASE.SEQUENCE, BASE.LANE_ID), before)
        BASE.generate_result(
            root=BASE.DEFAULT_EVIDENCE_ROOT,
            implementation_revision=None,
            check=True,
        )

    def test_aggregate_credit_retains_r1_failure_without_parity(self) -> None:
        passed = R2.aggregate_credits("passed")
        failed = R2.aggregate_credits("failed")
        self.assertEqual((passed["official_outcomes"], passed["official_passes"], passed["official_failures"]), (2, 1, 1))
        self.assertEqual((failed["official_outcomes"], failed["official_passes"], failed["official_failures"]), (2, 0, 2))
        self.assertEqual(passed["parity_credit"], 0)
        self.assertEqual(failed["paired_cells"], 0)

    def test_r2_result_validator_rejects_history_credit_and_claim_drift(self) -> None:
        authority = self.result_authority()
        self.assertEqual(R2.validate_result_authority(authority), [])
        mutations = (
            lambda item: item["attempts"][1].__setitem__("outcome", "passed"),
            lambda item: item["credits"].__setitem__("parity_credit", 1),
            lambda item: item["claims"].__setitem__("lean_parity_established", True),
        )
        for mutate in mutations:
            changed = copy.deepcopy(authority)
            mutate(changed)
            changed = BASE.seal(changed, R2.RESULT_SCHEMA)
            with self.subTest(mutate=mutate):
                self.assertTrue(R2.validate_result_authority(changed))


if __name__ == "__main__":
    unittest.main()
