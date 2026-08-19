from __future__ import annotations

import copy
import importlib.util
from pathlib import Path
import unittest


SCRIPT = Path(__file__).parents[1] / "check-autogenesis-statement-reflexivity.py"
SPEC = importlib.util.spec_from_file_location("check_autogenesis_statement_reflexivity", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class StatementReflexivityCheckerTests(unittest.TestCase):
    def setUp(self) -> None:
        self.manifest = MODULE.load_manifest()
        operation = self.manifest["operation"]
        goal = "checked goal"
        proof = "checked proof"
        operation["goal_sha256"] = MODULE.hashlib.sha256(goal.encode()).hexdigest()
        operation["proof_sha256"] = MODULE.hashlib.sha256(proof.encode()).hexdigest()
        self.receipt = {
            "target": operation["target_definition"],
            "goal_sha256": operation["goal_sha256"],
            "proof_sha256": operation["proof_sha256"],
            "target_content_sha256": operation["target_content_sha256"],
            "binders": str(operation["binders"]),
            "constructed_nodes": str(operation["constructed_nodes"]),
            "max_binders": str(operation["max_binders"]),
            "max_nodes": str(operation["max_constructed_nodes"]),
            "declarations": str(operation["admitted_declarations"]),
            "axioms": str(operation["axioms"]),
            "theorem_dependencies": str(operation["theorem_dependencies"]),
            "target_dependency": "false",
            "ledger_writes": "0",
            "goal": goal,
            "proof": proof,
        }

    def test_exact_receipt_is_accepted(self) -> None:
        MODULE.validate_receipt(self.manifest, self.receipt)

    def test_mutated_proof_is_rejected(self) -> None:
        receipt = copy.deepcopy(self.receipt)
        receipt["proof"] += " changed"
        with self.assertRaisesRegex(MODULE.ReflexivityError, "proof digest"):
            MODULE.validate_receipt(self.manifest, receipt)

    def test_target_dependency_is_rejected(self) -> None:
        receipt = copy.deepcopy(self.receipt)
        receipt["target_dependency"] = "true"
        with self.assertRaisesRegex(MODULE.ReflexivityError, "identity changed"):
            MODULE.validate_receipt(self.manifest, receipt)

    def test_receipt_parser_rejects_extra_output(self) -> None:
        with self.assertRaisesRegex(MODULE.ReflexivityError, "receipt shape"):
            MODULE.parse_receipt("STATEMENT_REFLEXIVITY_OK|target=x\nGOAL|x\nPROOF|x\nextra")


if __name__ == "__main__":
    unittest.main()
