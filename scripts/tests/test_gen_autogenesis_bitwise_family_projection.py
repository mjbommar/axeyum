import json
import unittest
from pathlib import Path
from unittest import mock
import importlib.util

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/gen-autogenesis-bitwise-family-projection.py"
SPEC = importlib.util.spec_from_file_location("bitwise_family_projection", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class BitwiseFamilyProjectionTests(unittest.TestCase):
    def test_live_projection(self):
        result = MODULE.build()
        self.assertEqual(
            result["census"],
            {
                "development_targets": 3,
                "clean_axiom_free_analogues": 3,
                "exact_imported_matches": 0,
                "authoritative_operation_eligible": 0,
            },
        )
        self.assertTrue(all(not row["exact_imported_identity"] for row in result["rows"]))
        self.assertTrue(
            all(not row["authoritative_operation_eligible"] for row in result["rows"])
        )

    def test_settled_exact_fact_fails_closed(self):
        original = MODULE.json.loads

        def changed_loads(text):
            data = original(text)
            if isinstance(data, dict) and data.get("id") == MODULE.MAPPINGS[0][0]:
                data["epistemic_status"] = "proved"
            return data

        with mock.patch.object(MODULE.json, "loads", side_effect=changed_loads):
            with self.assertRaisesRegex(ValueError, "no longer an open"):
                MODULE.build()

    def test_artifact_is_current(self):
        expected = json.dumps(MODULE.build(), indent=2, sort_keys=True) + "\n"
        self.assertEqual(MODULE.OUTPUT.read_text(), expected)


if __name__ == "__main__":
    unittest.main()
