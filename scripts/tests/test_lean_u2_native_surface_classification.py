from __future__ import annotations

import copy
import importlib.util
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "gen_lean_u2_native_surface_classification",
    ROOT / "scripts/gen-lean-u2-native-surface-classification.py",
)
assert SPEC and SPEC.loader
GEN = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = GEN
SPEC.loader.exec_module(GEN)


class LeanU2NativeSurfaceClassificationTests(unittest.TestCase):
    def setUp(self) -> None:
        self.data = GEN.load_json(GEN.MANIFEST)

    def failures(self) -> list[str]:
        return GEN.validate_authority(self.data)

    def reseal_top(self) -> None:
        self.data["record_sha256"] = GEN.domain_digest(
            GEN.SCHEMA,
            {
                key: value
                for key, value in self.data.items()
                if key != "record_sha256"
            },
        )

    def reseal_case_rows(self) -> None:
        self.data["case_rows_sha256"] = GEN.domain_digest(
            "axeyum-lean-u2-native-surface-cases-v1",
            self.data["case_rows"],
        )
        self.reseal_top()

    def test_committed_authority_is_valid_deterministic_and_non_crediting(self) -> None:
        self.assertEqual(self.failures(), [])
        self.assertEqual(self.data, GEN.build_authority())
        report = GEN.summarize(self.data)
        self.assertEqual(
            report["verdict"],
            "all U2 cases have a harness floor; TL0.6.4 and Lean parity remain incomplete",
        )
        self.assertIn("3,723", GEN.render_markdown(report))
        self.assertEqual(report["summary"]["registration_cases"], 3723)
        self.assertEqual(report["summary"]["classification_state_counts"], {"harness-floor": 3723})
        self.assertEqual(report["summary"]["content_refinement_counts"], {"not-run": 3723})
        self.assertEqual(report["summary"]["module_dependency_closure_counts"], {"not-run": 3723})
        self.assertEqual(report["summary"]["native_outcome_counts"], {"not-run": 3723})
        self.assertTrue(all(value == 0 for value in report["credits"].values()))

    def test_family_kind_and_profile_denominators_are_exact(self) -> None:
        summary = self.data["summary"]
        self.assertEqual(summary["profile_case_occurrences"], {"default": 3678, "full-lake": 3723})
        self.assertEqual(
            summary["kind_counts"],
            {"directory": 31, "lake-directory": 52, "lint": 1, "pile": 3639},
        )
        self.assertEqual(
            summary["family_counts"],
            {
                "bench": 1,
                "compile": 60,
                "compile_bench": 24,
                "doc-examples": 8,
                "docparse": 197,
                "elab": 2854,
                "elab_bench": 40,
                "elab_fail": 316,
                "lake": 52,
                "lint": 1,
                "misc": 5,
                "misc_dir": 2,
                "pkg": 27,
                "server": 4,
                "server_interactive": 132,
            },
        )
        self.assertEqual(summary["family_rules_used"], 14)
        self.assertEqual(summary["case_overrides_used"], 3)

    def test_direct_and_transitive_surface_denominators_are_exact(self) -> None:
        summary = self.data["summary"]
        self.assertEqual(
            summary["direct_surface_counts"],
            {
                "adversarial": 316,
                "compiler-runtime": 282,
                "editor-rpc": 137,
                "elaborator": 3217,
                "modules-lake": 81,
                "parser-macro": 197,
                "tactic-meta": 2,
                "toolchain-cli": 6,
            },
        )
        self.assertEqual(
            summary["closure_surface_counts"],
            {
                "adversarial": 316,
                "compiler-runtime": 282,
                "editor-rpc": 137,
                "elaborator": 3717,
                "kernel-import": 3717,
                "modules-lake": 217,
                "parser-macro": 3717,
                "tactic-meta": 2,
                "toolchain-cli": 6,
            },
        )
        self.assertEqual(summary["direct_surface_occurrences"], 4238)
        self.assertEqual(summary["closure_surface_occurrences"], 12111)
        self.assertNotIn("ffi", summary["direct_surface_counts"])
        self.assertFalse(self.data["claims"]["pinned_content_refined"])

    def test_compile_expected_failure_and_server_floors_stay_distinct(self) -> None:
        rows = {row["case_id"]: row for row in self.data["case_rows"]}
        compile_row = rows["compile/534.lean"]
        self.assertEqual(compile_row["direct_surfaces"], ["compiler-runtime"])
        self.assertEqual(
            compile_row["surface_closure"],
            ["kernel-import", "parser-macro", "elaborator", "compiler-runtime"],
        )
        failure_row = next(row for row in self.data["case_rows"] if row["family"] == "elab_fail")
        self.assertEqual(failure_row["direct_surfaces"], ["elaborator", "adversarial"])
        self.assertIn("adversarial", failure_row["surface_closure"])
        server_row = next(row for row in self.data["case_rows"] if row["family"] == "server_interactive")
        self.assertEqual(server_row["direct_surfaces"], ["editor-rpc"])
        self.assertIn("modules-lake", server_row["surface_closure"])
        self.assertEqual(server_row["native_outcome"], "not-run")

    def test_three_directory_overrides_are_exact_and_used_once(self) -> None:
        rows = {row["case_id"]: row for row in self.data["case_rows"]}
        self.assertEqual(rows["../doc/examples/compiler"]["direct_surfaces"], ["compiler-runtime"])
        self.assertEqual(rows["misc_dir/plugin"]["direct_surfaces"], ["modules-lake", "tactic-meta"])
        self.assertEqual(rows["misc_dir/server_project"]["direct_surfaces"], ["modules-lake", "editor-rpc"])
        override_rows = [row for row in self.data["case_rows"] if row["rule_kind"] == "override"]
        self.assertEqual(len(override_rows), 3)
        self.assertEqual({row["rule_id"] for row in override_rows}, {row["id"] for row in GEN.CASE_OVERRIDES})

    def test_parent_case_identity_and_order_mutations_are_rejected(self) -> None:
        self.data["case_rows"][0]["source_case_sha256"] = "0" * 64
        self.data["case_rows"][0] = GEN.seal(self.data["case_rows"][0], GEN.CASE_DOMAIN)
        self.data["case_rows"][0], self.data["case_rows"][1] = self.data["case_rows"][1], self.data["case_rows"][0]
        self.reseal_case_rows()
        failures = self.failures()
        self.assertTrue(any("parent identity drift" in item for item in failures))
        self.assertTrue(any("case row" in item or "case " in item for item in failures))

    def test_surface_cycle_unknown_dependency_and_order_drift_are_rejected(self) -> None:
        surface = self.data["surface_registry"][0]
        surface["dependencies"] = ["kernel-import", "missing-surface"]
        self.data["surface_registry"][0] = GEN.seal(surface, GEN.SURFACE_DOMAIN)
        self.data["surface_registry_sha256"] = GEN.domain_digest(
            "axeyum-lean-u2-native-surface-registry-v1",
            self.data["surface_registry"],
        )
        self.reseal_top()
        failures = self.failures()
        self.assertTrue(any("unknown dependency" in item for item in failures))
        self.assertTrue(any("surface registry semantic or order drift" in item for item in failures))

        cycle = copy.deepcopy(GEN.SURFACES)
        cycle[0]["dependencies"] = ["elaborator"]
        self.assertTrue(any("cycle" in item for item in GEN.validate_surface_definitions(list(cycle))))

    def test_rule_closure_and_override_mutations_are_rejected(self) -> None:
        row = next(item for item in self.data["case_rows"] if item["family"] == "compile")
        row["direct_surfaces"] = ["elaborator"]
        row["surface_closure"] = ["kernel-import", "parser-macro", "elaborator"]
        row.update(GEN.seal(row, GEN.CASE_DOMAIN))
        self.reseal_case_rows()
        self.assertTrue(any("classifier rule or closure drift" in item for item in self.failures()))

        data = GEN.build_authority()
        data["case_overrides"][0]["case_id"] = "compile/534.lean"
        data["case_overrides"][0] = GEN.seal(data["case_overrides"][0], GEN.OVERRIDE_DOMAIN)
        data["case_overrides_sha256"] = GEN.domain_digest(
            "axeyum-lean-u2-native-surface-overrides-v1", data["case_overrides"]
        )
        data["record_sha256"] = GEN.domain_digest(
            GEN.SCHEMA,
            {key: value for key, value in data.items() if key != "record_sha256"},
        )
        self.data = data
        self.assertTrue(any("case override semantic" in item for item in self.failures()))

    def test_native_outcome_credit_and_claim_promotions_are_rejected(self) -> None:
        row = self.data["case_rows"][0]
        row["native_outcome"] = "passed"
        row["execution_credit"] = 1
        self.data["case_rows"][0] = GEN.seal(row, GEN.CASE_DOMAIN)
        self.data["credits"]["axeyum_outcomes"] = 1
        self.data["claims"]["matched_pair_formed"] = True
        self.reseal_case_rows()
        failures = self.failures()
        self.assertTrue(any("non-crediting state drift" in item for item in failures))
        self.assertTrue(any("credit drift" in item for item in failures))
        self.assertTrue(any("claims drift" in item for item in failures))

    def test_record_list_summary_and_top_level_seals_have_teeth(self) -> None:
        self.data["case_rows"][0]["record_sha256"] = "0" * 64
        self.data["case_rows_sha256"] = "1" * 64
        self.data["summary"]["registration_cases"] = 3722
        self.data["record_sha256"] = "2" * 64
        failures = self.failures()
        self.assertTrue(any("record seal drift" in item for item in failures))
        self.assertTrue(any("case row list seal drift" in item for item in failures))
        self.assertTrue(any("summary drift" in item for item in failures))
        self.assertTrue(any("top-level record seal drift" in item for item in failures))


if __name__ == "__main__":
    unittest.main()
