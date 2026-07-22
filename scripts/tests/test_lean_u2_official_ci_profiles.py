from __future__ import annotations

import copy
import importlib.util
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "gen_lean_u2_official_ci_profiles",
    ROOT / "scripts" / "gen-lean-u2-official-ci-profiles.py",
)
assert SPEC and SPEC.loader
GEN = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = GEN
SPEC.loader.exec_module(GEN)


class LeanU2OfficialCiProfilesTests(unittest.TestCase):
    def setUp(self) -> None:
        self.data = GEN.load_json(GEN.MANIFEST)

    def failures(self) -> list[str]:
        return GEN.validate_manifest(self.data)

    def cell(self, cell_id: str) -> dict:
        return next(item for item in self.data["cells"] if item["id"] == cell_id)

    def attempt(self, attempt_id: str) -> dict:
        return next(item for item in self.data["attempts"] if item["id"] == attempt_id)

    def selection(self, selection_id: str) -> dict:
        return next(
            item for item in self.data["selection_sets"] if item["id"] == selection_id
        )

    def test_committed_authority_is_valid_deterministic_and_non_terminal(self) -> None:
        self.assertEqual(self.failures(), [])
        first = GEN.summarize(self.data)
        second = GEN.summarize(copy.deepcopy(self.data))
        self.assertEqual(first, second)
        self.assertEqual(
            first["verdict"],
            "official CI profiles derived; no execution or parity outcome established",
        )
        self.assertEqual(first["outcomes"]["state"], "not-run")
        markdown = GEN.render_markdown(first)
        self.assertIn("111 CTest attempts", markdown)
        self.assertIn("Every attempt below remains `not-run`", markdown)

    def test_context_job_cell_and_attempt_closure_is_exact(self) -> None:
        derivation = self.data["derivation"]
        self.assertEqual(derivation["contexts"], 17)
        self.assertEqual(derivation["active_job_literals"], 9)
        self.assertEqual(derivation["candidate_cells"], 153)
        self.assertEqual(
            derivation["cell_state_counts"],
            {"ctest": 85, "disabled": 53, "packaging-only": 15},
        )
        self.assertEqual(derivation["ctest_attempts"], 111)
        self.assertEqual(
            derivation["attempt_phase_counts"], {"primary": 85, "rebootstrap": 26}
        )
        self.assertEqual(derivation["selection_sets"], 8)

    def test_exact_filter_sets_include_the_noop_foreign_correction(self) -> None:
        rows = {
            (item["profile"], item["exclude_regex"]): (
                item["registered_count"],
                item["selected_count"],
                item["excluded_count"],
            )
            for item in self.data["selection_sets"]
        }
        self.assertEqual(rows[("default", None)], (3678, 3678, 0))
        self.assertEqual(rows[("full-lake", None)], (3723, 3723, 0))
        self.assertEqual(rows[("default", "foreign")], (3678, 3678, 0))
        self.assertEqual(rows[("full-lake", "foreign")], (3723, 3723, 0))
        self.assertEqual(rows[("default", "elab_bench/big_do")], (3678, 3677, 1))
        self.assertEqual(rows[("full-lake", "elab_bench/big_do")], (3723, 3722, 1))
        sanitizer = next(
            pattern
            for profile, pattern in rows
            if profile == "default" and pattern and "StackOverflow" in pattern
        )
        self.assertEqual(rows[("default", sanitizer)], (3678, 3477, 201))
        self.assertEqual(rows[("full-lake", sanitizer)], (3723, 3477, 246))

    def test_level_zero_merge_push_and_release_context_shapes_are_distinct(self) -> None:
        report = GEN.summarize(self.data)
        contexts = {item["id"]: item for item in report["contexts"]}
        self.assertEqual(
            (
                contexts["pr-l0"]["enabled_jobs"],
                contexts["pr-l0"]["packaging_only_jobs"],
                contexts["pr-l0"]["ctest_attempts"],
            ),
            (4, 2, 2),
        )
        self.assertEqual(contexts["merge-group-l1"]["ctest_attempts"], 4)
        self.assertEqual(contexts["push-master-l1"]["ctest_attempts"], 5)
        self.assertEqual(contexts["release-tag-l3"]["ctest_attempts"], 10)

    def test_rebootstrap_is_stage1_unfiltered_and_has_no_junit(self) -> None:
        cell = self.cell("release-tag-l3--linux-lake")
        self.assertTrue(cell["check_rebootstrap"])
        primary = self.attempt(f"{cell['id']}--primary")
        rebootstrap = self.attempt(f"{cell['id']}--rebootstrap")
        self.assertEqual(primary["target_stage"], "stage1")
        self.assertEqual(primary["junit_path"], "test-results.xml")
        self.assertEqual(rebootstrap["target_stage"], "stage1")
        self.assertEqual(rebootstrap["ctest_options"], "")
        self.assertEqual(rebootstrap["selection_set_id"], "default-all")
        self.assertIsNone(rebootstrap["junit_path"])

    def test_context_and_candidate_cell_closure_mutations_are_rejected(self) -> None:
        self.data["contexts"].pop()
        self.data["cells"].pop()
        failures = self.failures()
        self.assertTrue(any("context closure" in item for item in failures))
        self.assertTrue(any("candidate cell closure" in item for item in failures))

    def test_commented_job_and_cell_configuration_mutations_are_rejected(self) -> None:
        self.data["jobs"][0]["name"] = "Linux LLVM"
        cell = self.data["cells"][0]
        cell["runner"] = "invented-runner"
        failures = self.failures()
        self.assertTrue(any("active matrix job literals" in item for item in failures))
        self.assertTrue(any("commented matrix job" in item for item in failures))
        self.assertTrue(any("cell digest drift" in item for item in failures))

    def test_disabled_or_packaging_cell_cannot_acquire_attempt(self) -> None:
        disabled = next(item for item in self.data["cells"] if item["state"] == "disabled")
        attempt = copy.deepcopy(self.data["attempts"][0])
        attempt["id"] = f"{disabled['id']}--primary"
        attempt["cell_id"] = disabled["id"]
        attempt["sha256"] = GEN.attempt_digest(attempt)
        self.data["attempts"].append(attempt)
        self.data["attempts"].sort(key=lambda item: item["id"])
        failures = self.failures()
        self.assertTrue(any("disabled/packaging cell cannot own attempt" in item for item in failures))

    def test_missing_primary_and_spurious_rebootstrap_are_rejected(self) -> None:
        primary = next(item for item in self.data["attempts"] if item["phase"] == "primary")
        self.data["attempts"].remove(primary)
        non_rebootstrap = next(
            item
            for item in self.data["cells"]
            if item["state"] == "ctest" and not item["check_rebootstrap"]
        )
        template = next(item for item in self.data["attempts"] if item["phase"] == "rebootstrap")
        extra = copy.deepcopy(template)
        extra["id"] = f"{non_rebootstrap['id']}--rebootstrap"
        extra["cell_id"] = non_rebootstrap["id"]
        extra["preset"] = non_rebootstrap["preset"]
        extra["selection_set_id"] = "default-all"
        extra["command"] = GEN.attempt_command(
            preset=extra["preset"], target_stage="stage1", options="", junit=None
        )
        extra["sha256"] = GEN.attempt_digest(extra)
        self.data["attempts"].append(extra)
        self.data["attempts"].sort(key=lambda item: item["id"])
        failures = self.failures()
        self.assertTrue(any("attempt phase closure drift" in item for item in failures))
        self.assertTrue(any("unregistered rebootstrap attempt" in item for item in failures))

    def test_rebootstrap_filter_stage_and_command_mutations_are_rejected(self) -> None:
        attempt = next(item for item in self.data["attempts"] if item["phase"] == "rebootstrap")
        attempt["ctest_options"] = "-E foreign"
        attempt["target_stage"] = "stage2"
        attempt["command"] = ["ctest", "invented"]
        attempt["sha256"] = GEN.attempt_digest(attempt)
        failures = self.failures()
        self.assertTrue(any("command configuration drift" in item for item in failures))
        self.assertTrue(any("normalized command drift" in item for item in failures))

    def test_selection_membership_count_digest_and_reference_mutations_are_rejected(self) -> None:
        selection = next(item for item in self.data["selection_sets"] if item["excluded_count"])
        selection["selected_case_ids"].pop()
        selection["selected_count"] -= 1
        selection["selected_ids_sha256"] = GEN.digest(selection["selected_case_ids"])
        selection["sha256"] = GEN.selection_digest(selection)
        attempt = self.data["attempts"][0]
        attempt["selection_set_id"] = selection["id"]
        attempt["sha256"] = GEN.attempt_digest(attempt)
        failures = self.failures()
        self.assertTrue(any("exact selection membership" in item for item in failures))
        self.assertTrue(any("attempt/selection mismatch" in item for item in failures))

    def test_unsupported_filter_and_outcome_credit_are_rejected(self) -> None:
        cell = next(item for item in self.data["cells"] if item["state"] == "ctest")
        cell["ctest_options"] = "--repeat until-pass:3"
        cell["sha256"] = GEN.cell_digest(cell)
        self.data["outcomes"]["official_executed_attempts"] = 1
        self.data["attempts"][0]["outcome"] = "passed"
        failures = self.failures()
        self.assertTrue(any("unsupported CTest option" in item for item in failures))
        self.assertTrue(any("cannot claim execution" in item for item in failures))
        self.assertTrue(any("cannot claim outcome" in item for item in failures))

    def test_input_registration_and_bootstrap_identity_mutations_are_rejected(self) -> None:
        self.data["source_inputs"][0]["sha256"] = "0" * 64
        self.data["registration_authority"]["cases_sha256"] = "0" * 64
        self.data["derivation"]["target_stage"] = "stage2"
        failures = self.failures()
        self.assertTrue(any("source input paths/digests" in item for item in failures))
        self.assertTrue(any("registration authority identity" in item for item in failures))
        self.assertTrue(any("method/bootstrap identity" in item for item in failures))


if __name__ == "__main__":
    unittest.main()
