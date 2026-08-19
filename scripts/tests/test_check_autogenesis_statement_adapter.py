from __future__ import annotations

import copy
import importlib.util
from pathlib import Path
import unittest


SCRIPT = Path(__file__).parents[1] / "check-autogenesis-statement-adapter.py"
SPEC = importlib.util.spec_from_file_location("check_autogenesis_statement_adapter", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class StatementAdapterCheckerTests(unittest.TestCase):
    def setUp(self) -> None:
        self.manifest = MODULE.load_manifest()
        expected = self.manifest["independent_import"]
        source = self.manifest["adapter_source"]
        goal = "checked goal"
        expected["goal_sha256"] = MODULE.hashlib.sha256(goal.encode()).hexdigest()
        self.receipt = {
            "target": source["target_definition"],
            "goal_sha256": expected["goal_sha256"],
            "target_content_sha256": expected["target_content_sha256"],
            "dependencies": str(expected["direct_dependencies"]),
            "declarations": str(expected["admitted_declarations"]),
            "axioms": str(expected["axioms"]),
            "lean": self.manifest["toolchain"]["lean_version"],
            "goal": goal,
        }

    def test_exact_receipt_is_accepted(self) -> None:
        MODULE.validate_receipt(self.manifest, self.receipt)

    def test_type_altered_goal_is_rejected(self) -> None:
        receipt = copy.deepcopy(self.receipt)
        receipt["goal"] += " changed"
        with self.assertRaisesRegex(MODULE.AdapterError, "rendered goal"):
            MODULE.validate_receipt(self.manifest, receipt)

    def test_target_content_change_is_rejected(self) -> None:
        receipt = copy.deepcopy(self.receipt)
        receipt["target_content_sha256"] = "0" * 64
        with self.assertRaisesRegex(MODULE.AdapterError, "identity changed"):
            MODULE.validate_receipt(self.manifest, receipt)

    def test_receipt_parser_rejects_extra_output(self) -> None:
        with self.assertRaisesRegex(MODULE.AdapterError, "receipt shape"):
            MODULE.parse_receipt("STATEMENT_ADAPTER_IMPORT|target=x\nGOAL|x\nextra")


if __name__ == "__main__":
    unittest.main()
