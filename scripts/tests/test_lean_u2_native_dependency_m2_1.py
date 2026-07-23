from __future__ import annotations

import importlib.util
import json
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "lean_u2_native_dependency_m2_1",
    ROOT / "scripts/lean_u2_native_dependency_m2_1.py",
)
assert SPEC and SPEC.loader
GEN = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = GEN
SPEC.loader.exec_module(GEN)


class LeanU2NativeHeaderContractTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.data = GEN.build_contract()

    def test_exact_corpus_denominator_and_parent_projection(self) -> None:
        summary = self.data["summary"]
        self.assertEqual(summary["case_rows"], 3723)
        self.assertEqual(summary["corpus_rows"], 4092)
        self.assertEqual(summary["corpus_bytes"], 9_697_571)
        self.assertEqual(summary["mode_counts"], {"100644": 4084, "100755": 8})
        self.assertEqual(summary["max_path_utf8_bytes"], 69)
        self.assertEqual(summary["newline_or_cr_paths"], 0)
        self.assertEqual(summary["first_path"], "doc/examples/Certora2022/ex1.lean")
        self.assertEqual(summary["last_path"], "tests/simpperf/simp500.lean")
        self.assertEqual(
            self.data["parent_logical_seals"]["m1_record_sha256"],
            GEN.M1_RECORD_SHA256,
        )
        self.assertEqual(
            self.data["parent_logical_seals"]["m20_record_sha256"],
            GEN.M20_RECORD_SHA256,
        )

    def test_contiguous_batch_partition_and_stdin_hashes_are_exact(self) -> None:
        batches = self.data["batches"]
        self.assertEqual(len(batches), 32)
        self.assertEqual([row["input_count"] for row in batches[:-1]], [128] * 31)
        self.assertEqual(batches[-1]["input_count"], 124)
        self.assertEqual(
            sum(row["input_count"] for row in batches),
            self.data["summary"]["corpus_rows"],
        )
        for ordinal, batch in enumerate(batches):
            self.assertEqual(batch["batch_ordinal"], ordinal)
            self.assertEqual(batch["start_ordinal"], ordinal * GEN.BATCH_SIZE)
            self.assertEqual(
                batch["stop_ordinal_exclusive"],
                batch["start_ordinal"] + batch["input_count"],
            )
            rows = self.data["corpus_rows"][
                batch["start_ordinal"] : batch["stop_ordinal_exclusive"]
            ]
            stdin = ("\n".join(row["path"] for row in rows) + "\n").encode()
            self.assertEqual(batch["stdin_sha256"], GEN.sha256_bytes(stdin))

    def test_control_matrix_preserves_semantics_and_negative_boundaries(self) -> None:
        controls = {row["id"]: row for row in self.data["controls"]}
        self.assertEqual(len(controls), 14)
        default = controls["legacy-default-init"]
        self.assertEqual(
            [(row["module"], row["is_meta"], row["origin"]) for row in default["imports"]],
            [
                ("Init", False, "implicit-default-prelude"),
                ("Init", True, "implicit-default-prelude"),
                ("Lean", False, "explicit"),
            ],
        )
        duplicate = controls["duplicate-imports"]
        self.assertEqual([row["module"] for row in duplicate["imports"]].count("Lean"), 2)
        mixed = controls["module-mixed-modifiers"]["imports"]
        self.assertTrue(mixed[-2]["is_exported"] and mixed[-2]["is_meta"])
        self.assertTrue(mixed[-1]["import_all"])
        self.assertEqual(controls["missing-input"]["source"], None)
        self.assertFalse(controls["missing-input"]["exists"])
        self.assertEqual(
            sum(row["fast_state"] == "error" for row in controls.values()), 4
        )

    def test_provider_floor_process_budget_and_zero_credit_are_explicit(self) -> None:
        self.assertEqual(self.data["policy"]["attempt_process_budget"], 39)
        self.assertEqual(self.data["policy"]["parser_process_budget"], 35)
        self.assertEqual(self.data["policy"]["preflight_process_budget"], 4)
        self.assertEqual(self.data["policy"]["retry_budget"], 0)
        self.assertEqual(self.data["summary"]["observed_processes"], 0)
        self.assertEqual(self.data["summary"]["declared_header_edges"], 0)
        self.assertEqual(self.data["summary"]["resolved_nodes"], 0)
        self.assertFalse(self.data["claims"]["provider_identity_observed"])
        self.assertFalse(self.data["claims"]["fast_parser_observed"])
        self.assertFalse(self.data["claims"]["lean_parity_established"])
        self.assertTrue(all(value == 0 for value in self.data["credits"].values()))

    def test_process_program_is_closed_ordered_and_nonexecuting(self) -> None:
        specs = GEN.build_process_specs(self.data)
        self.assertEqual(len(specs), 39)
        self.assertEqual(
            [row["category"] for row in specs[:4]], ["preflight"] * 4
        )
        self.assertEqual(
            [row["category"] for row in specs[4:36]], ["fast-corpus"] * 32
        )
        self.assertEqual(specs[36]["category"], "fast-controls")
        self.assertEqual(specs[37]["category"], "full-corpus")
        self.assertEqual(specs[38]["category"], "full-controls")
        self.assertEqual(specs[4]["argv"][-2:], ["--deps-json", "--stdin"])
        self.assertEqual(specs[37]["argv"][-2], "--run")
        self.assertEqual(specs[37]["stdin_bytes"], sum(
            len(row["path"].encode()) + 1 for row in self.data["corpus_rows"]
        ))
        payload = GEN.authorization_payload(self.data)
        self.assertEqual(payload["process_count"], 39)
        self.assertEqual(payload["retry_budget"], 0)
        self.assertEqual(len(GEN.authorization_digest(self.data)), 64)

    def test_parser_output_normalization_preserves_order_duplicates_and_diagnostics(self) -> None:
        imports = [
            {
                "module": "Init",
                "importAll": False,
                "isExported": True,
                "isMeta": False,
            },
            {
                "module": "Lean",
                "importAll": False,
                "isExported": False,
                "isMeta": False,
            },
            {
                "module": "Lean",
                "importAll": False,
                "isExported": False,
                "isMeta": False,
            },
        ]
        fast_bytes = json.dumps(
            {
                "imports": [
                    {"result": {"imports": imports, "isModule": True}, "errors": []}
                ]
            }
        ).encode()
        full_bytes = json.dumps(
            {
                "rows": [
                    {
                        "result": {
                            "imports": imports,
                            "isModule": True,
                            "terminalLine": 3,
                            "terminalColumn": 0,
                            "messages": ["retained diagnostic"],
                        },
                        "errors": [],
                    }
                ]
            }
        ).encode()
        fast = GEN.normalize_fast_output(fast_bytes, 1, "fast")
        full = GEN.normalize_full_output(full_bytes, 1, "full")
        self.assertEqual(
            [row["module"] for row in fast[0]["result"]["imports"]],
            ["Init", "Lean", "Lean"],
        )
        self.assertEqual(GEN.compare_parser_row(fast[0], full[0]), "equal-with-full-diagnostic")

    def test_parser_output_normalization_rejects_schema_and_row_count_drift(self) -> None:
        with self.assertRaises(GEN.HeaderContractError):
            GEN.normalize_fast_output(b"{}", 1, "missing")
        malformed_import = {
            "imports": [
                {
                    "result": {
                        "imports": [{"module": "Lean", "isExported": True}],
                        "isModule": False,
                    },
                    "errors": [],
                }
            ]
        }
        with self.assertRaises(GEN.HeaderContractError):
            GEN.normalize_fast_output(json.dumps(malformed_import).encode(), 1, "bad")


@unittest.skipUnless(GEN.CONTRACT.is_file(), "M2.1 contract not derived yet")
class LeanU2NativeHeaderContractAuthorityTests(unittest.TestCase):
    def setUp(self) -> None:
        self.data = GEN.load_json(GEN.CONTRACT)

    def failures(self) -> list[str]:
        return GEN.validate_contract(self.data)

    def reseal_top(self) -> None:
        self.data["record_sha256"] = GEN.domain_digest(
            GEN.SCHEMA,
            {key: value for key, value in self.data.items() if key != "record_sha256"},
        )

    def reseal_row(self, field: str, index: int, domain: str) -> None:
        self.data[field][index] = GEN.seal(self.data[field][index], domain)

    def reseal_list(self, field: str, domain: str) -> None:
        self.data[f"{field}_sha256"] = GEN.domain_digest(domain, self.data[field])
        self.reseal_top()

    def test_committed_contract_is_valid_and_non_crediting(self) -> None:
        self.assertEqual(self.failures(), [])
        report = GEN.summarize(self.data)
        self.assertIn("no header parser process", report["verdict"])
        self.assertEqual(report["summary"]["observed_processes"], 0)
        self.assertTrue(all(value == 0 for value in report["credits"].values()))

    def test_corpus_and_batch_mutations_are_rejected_after_resealing(self) -> None:
        self.data["corpus_rows"][0]["path"] = "tests/invented.lean"
        self.reseal_row("corpus_rows", 0, GEN.CORPUS_DOMAIN)
        self.reseal_list(
            "corpus_rows", "axeyum-lean-u2-native-header-corpus-rows-m2.1-v1"
        )
        self.data["batches"][0]["input_count"] = 127
        self.reseal_row("batches", 0, GEN.BATCH_DOMAIN)
        self.reseal_list(
            "batches", "axeyum-lean-u2-native-header-batches-m2.1-v1"
        )
        failures = self.failures()
        self.assertTrue(any("corpus_rows semantic" in item for item in failures))
        self.assertTrue(any("batches semantic" in item for item in failures))

    def test_control_and_credit_mutations_are_rejected_after_resealing(self) -> None:
        duplicate_index = next(
            index
            for index, row in enumerate(self.data["controls"])
            if row["id"] == "duplicate-imports"
        )
        self.data["controls"][duplicate_index]["imports"].pop()
        self.reseal_row("controls", duplicate_index, GEN.CONTROL_DOMAIN)
        self.reseal_list(
            "controls", "axeyum-lean-u2-native-header-controls-m2.1-v1"
        )
        self.data["credits"]["parity_credit"] = 1
        self.reseal_top()
        failures = self.failures()
        self.assertTrue(any("controls semantic" in item for item in failures))
        self.assertIn("credits drift", failures)

    def test_parent_summary_and_seals_have_teeth(self) -> None:
        self.data["parent_logical_seals"]["m1_record_sha256"] = "0" * 64
        self.data["summary"]["corpus_rows"] = 4091
        self.data["corpus_rows_sha256"] = "1" * 64
        self.data["record_sha256"] = "2" * 64
        failures = self.failures()
        self.assertIn("parent_logical_seals drift", failures)
        self.assertIn("summary drift", failures)
        self.assertIn("corpus_rows list seal drift", failures)
        self.assertIn("top-level record seal drift", failures)


if __name__ == "__main__":
    unittest.main()
