from __future__ import annotations

import copy
import importlib.util
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "gen_lean_execution_evidence",
    ROOT / "scripts" / "gen-lean-execution-evidence.py",
)
assert SPEC and SPEC.loader
GEN = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = GEN
SPEC.loader.exec_module(GEN)


class LeanExecutionEvidenceTests(unittest.TestCase):
    def setUp(self) -> None:
        self.authority = GEN.load_json(GEN.MANIFEST)

    def bundle(self, control_id: str = "clean-complete") -> dict:
        return GEN.synthetic_bundle(control_id)

    @staticmethod
    def rehash_run(bundle: dict) -> None:
        run = bundle["run"]
        run["resource_envelope_sha256"] = GEN.digest(run["resource_envelope"])
        run["platform_sha256"] = GEN.digest(run["platform"])
        run["artifact_policy_sha256"] = GEN.digest(run["artifact_policy"])
        run["command_sha256"] = GEN.digest(run["command"])
        run["environment_sha256"] = GEN.digest(run["environment"])
        run["selection_sha256"] = GEN.digest(run["selection_case_ids"])
        run["identity_sha256"] = GEN.object_digest(run, "identity_sha256")

    @staticmethod
    def rehash_attempt(attempt: dict) -> None:
        attempt["sha256"] = GEN.object_digest(attempt, "sha256")

    @staticmethod
    def rehash_case(case: dict) -> None:
        case["sha256"] = GEN.object_digest(case, "sha256")

    @staticmethod
    def rehash_artifact(artifact: dict) -> None:
        artifact["record_sha256"] = GEN.object_digest(artifact, "record_sha256")

    @staticmethod
    def rehash_completion(bundle: dict) -> None:
        completion = bundle["completion"]
        assert completion is not None
        completion["case_records_sha256"] = GEN.digest(bundle["cases"])
        completion["artifact_records_sha256"] = GEN.digest(bundle["artifacts"])
        completion["sha256"] = GEN.object_digest(completion, "sha256")

    def test_committed_authority_and_report_are_valid_deterministic_and_zero_credit(self) -> None:
        self.assertEqual(GEN.validate_authority(self.authority), [])
        first = GEN.summarize(self.authority)
        second = GEN.summarize(copy.deepcopy(self.authority))
        self.assertEqual(first, second)
        self.assertEqual(
            first["verdict"],
            "execution evidence contract represented; no process or parity outcome observed",
        )
        self.assertEqual(first["observed"], GEN.zero_credits())
        self.assertTrue(all(item["valid"] for item in first["synthetic_controls"]))
        markdown = GEN.render_markdown(first)
        self.assertIn("64 GiB default is not either registered lane", markdown)
        self.assertIn("All real counters remain zero", markdown)

    def test_exact_lane_taxonomy_control_and_mutation_registers(self) -> None:
        lanes = {item["id"]: item for item in self.authority["lane_policies"]}
        self.assertEqual(lanes["standard-local-4g"]["memory_limit_bytes"], 4_294_967_296)
        self.assertEqual(lanes["standard-local-4g"]["worker_limit"], 2)
        self.assertEqual(lanes["official-export-8g"]["memory_limit_bytes"], 8_589_934_592)
        self.assertEqual(lanes["official-export-8g"]["worker_limit"], 1)
        self.assertEqual(len(self.authority["taxonomies"]["termination_classes"]), 12)
        self.assertEqual(len(self.authority["synthetic_controls"]), 5)
        self.assertEqual(len(self.authority["mutation_classes"]), 19)

    def test_all_five_synthetic_controls_validate_with_no_real_credit(self) -> None:
        for control_id, _ in GEN.SYNTHETIC_CONTROLS:
            with self.subTest(control=control_id):
                bundle = self.bundle(control_id)
                self.assertEqual(GEN.validate_bundle(bundle, self.authority), [])
                self.assertEqual(bundle["credits"], GEN.zero_credits())
        resumed = self.bundle("interrupted-resumed")
        self.assertEqual(
            resumed["completion"]["terminal_less_attempt_ids"], ["attempt-001"]
        )
        self.assertIsNone(self.bundle("incomplete")["completion"])
        self.assertIsNone(self.bundle("preflight-invalid")["completion"])

    def test_source_lane_and_contract_outcome_mutations_reject(self) -> None:
        self.authority["source_inputs"][0]["sha256"] = "0" * 64
        self.authority["lane_policies"][0]["memory_limit_bytes"] = 64 * 1024**3
        self.authority["observed"]["real_runs"] = 1
        failures = GEN.validate_authority(self.authority)
        self.assertTrue(any("source input" in item for item in failures))
        self.assertTrue(any("lane policy" in item for item in failures))
        self.assertTrue(any("cannot claim real outcomes" in item for item in failures))

    def test_resource_wrapper_default_and_runner_substitution_reject(self) -> None:
        bundle = self.bundle()
        resource = bundle["run"]["resource_envelope"]
        resource["explicit_mem_limit_gb"] = 64
        resource["wall_timeout"]["value"] = 0
        bundle["run"]["platform"]["runner_id"] = None
        self.rehash_run(bundle)
        failures = GEN.validate_bundle(bundle, self.authority)
        self.assertTrue(any("explicit MEM_LIMIT_GB" in item for item in failures))
        self.assertTrue(any("observed metric must be a positive" in item for item in failures))
        self.assertTrue(any("runner label cannot substitute" in item for item in failures))

    def test_run_command_environment_selection_and_complete_identity_mutations_reject(self) -> None:
        bundle = self.bundle()
        run = bundle["run"]
        run["command"].append("--changed")
        run["command_sha256"] = GEN.digest(run["command"])
        run["environment"]["NPROC"] = "2"
        run["environment_sha256"] = GEN.digest(run["environment"])
        run["working_directory"] = "/different"
        run["selection_case_ids"].reverse()
        run["selection_sha256"] = GEN.digest(run["selection_case_ids"])
        failures = GEN.validate_bundle(bundle, self.authority)
        self.assertTrue(any("selection case ids must be unique and sorted" in item for item in failures))
        self.assertTrue(any("complete run identity drift" in item for item in failures))

    def test_attempt_closure_and_guessed_termination_reject(self) -> None:
        bundle = self.bundle()
        attempt = bundle["attempts"][0]
        attempt["sequence"] = 2
        attempt["terminal"]["class"] = "memory-limit"
        attempt["terminal"]["exit_code"] = None
        attempt["terminal"]["events"] = ["signal-observed"]
        self.rehash_attempt(attempt)
        failures = GEN.validate_bundle(bundle, self.authority)
        self.assertTrue(any("attempt sequences" in item for item in failures))
        self.assertTrue(any("memory-limit lacks enforcement evidence" in item for item in failures))

    def test_case_closure_identity_and_attempt_attribution_mutations_reject(self) -> None:
        bundle = self.bundle()
        bundle["cases"].pop()
        self.rehash_completion(bundle)
        failures = GEN.validate_bundle(bundle, self.authority)
        self.assertTrue(any("all and only selected case" in item for item in failures))

        bundle = self.bundle()
        bundle["cases"][0]["attempt_id"] = "attempt-missing"
        self.rehash_case(bundle["cases"][0])
        self.rehash_completion(bundle)
        failures = GEN.validate_bundle(bundle, self.authority)
        self.assertTrue(any("invalid attempt attribution" in item for item in failures))

    def test_artifact_hash_retention_and_checkpoint_conflicts_reject(self) -> None:
        bundle = self.bundle()
        artifact = bundle["artifacts"][0]
        artifact["sha256"] = "0" * 64
        self.rehash_artifact(artifact)
        self.rehash_completion(bundle)
        failures = GEN.validate_bundle(bundle, self.authority)
        self.assertTrue(any("durable copy identity" in item for item in failures))

        bundle = self.bundle()
        provider = next(item for item in bundle["artifacts"] if item["provider"])
        provider["expires_at"] = None
        self.rehash_artifact(provider)
        self.rehash_completion(bundle)
        failures = GEN.validate_bundle(bundle, self.authority)
        self.assertTrue(any("provider retention/expiry" in item for item in failures))

        bundle = self.bundle()
        duplicate = copy.deepcopy(bundle["artifacts"][0])
        duplicate["bytes"] += 1
        self.rehash_artifact(duplicate)
        bundle["artifacts"].insert(1, duplicate)
        self.rehash_completion(bundle)
        failures = GEN.validate_bundle(bundle, self.authority)
        self.assertTrue(any("artifact ids must be unique" in item for item in failures))

    def test_completion_order_sidecar_only_and_lost_attempt_mutations_reject(self) -> None:
        bundle = self.bundle()
        bundle["cases"] = []
        completion = bundle["completion"]
        completion["case_ids"] = []
        self.rehash_completion(bundle)
        failures = GEN.validate_bundle(bundle, self.authority)
        self.assertTrue(any("all and only selected case" in item for item in failures))

        bundle = self.bundle()
        bundle["completion"]["installed_last"] = False
        self.rehash_completion(bundle)
        failures = GEN.validate_bundle(bundle, self.authority)
        self.assertTrue(any("installed last" in item for item in failures))

        bundle = self.bundle("interrupted-resumed")
        bundle["completion"]["terminal_less_attempt_ids"] = []
        self.rehash_completion(bundle)
        failures = GEN.validate_bundle(bundle, self.authority)
        self.assertTrue(any("terminal-less attempt" in item for item in failures))

    def test_incomplete_and_profile_promotion_credit_mutations_reject(self) -> None:
        bundle = self.bundle("incomplete")
        bundle["credits"]["completed_cases"] = 1
        failures = GEN.validate_bundle(bundle, self.authority)
        self.assertTrue(any("cannot receive execution or parity credit" in item for item in failures))

        bundle = self.bundle()
        bundle["run"]["system_profile"] = "native-system"
        bundle["run"]["credit_class"] = "native-parity"
        bundle["run"]["identity_sha256"] = GEN.object_digest(
            bundle["run"], "identity_sha256"
        )
        failures = GEN.validate_bundle(bundle, self.authority)
        self.assertTrue(any("cannot promote adapter or native" in item for item in failures))

    def test_every_termination_class_is_representable_but_evidence_gated(self) -> None:
        for termination_class in GEN.TERMINATION_CLASSES:
            with self.subTest(termination=termination_class):
                kwargs: dict = {"exit_code": None, "signal": None, "events": []}
                if termination_class == "exited":
                    kwargs = {"exit_code": 0, "signal": None, "events": ["exit-status-observed"]}
                elif termination_class == "signaled":
                    kwargs = {"exit_code": None, "signal": 9, "events": ["signal-observed"]}
                elif termination_class in {
                    "wall-timeout",
                    "cpu-timeout",
                    "memory-limit",
                    "pids-limit",
                    "disk-limit",
                }:
                    kwargs["events"] = [termination_class + "-observed"]
                else:
                    kwargs["events"] = [termination_class + "-observed"]
                failures: list[str] = []
                GEN.validate_terminal(
                    "attempt-termination",
                    GEN.terminal(termination_class, **kwargs),
                    failures,
                )
                self.assertEqual(failures, [])

        failures = []
        GEN.validate_terminal(
            "attempt-bad",
            GEN.terminal("memory-limit", exit_code=None, events=["signal-observed"]),
            failures,
        )
        self.assertTrue(any("lacks enforcement evidence" in item for item in failures))

        failures = []
        terminal = GEN.terminal()
        terminal["peak_rss"] = GEN.metric("not-observed", 0, "bytes")
        GEN.validate_terminal("attempt-zero", terminal, failures)
        self.assertTrue(any("value must be null" in item for item in failures))


if __name__ == "__main__":
    unittest.main()
