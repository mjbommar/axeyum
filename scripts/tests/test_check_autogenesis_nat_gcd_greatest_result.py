from __future__ import annotations

import copy
import importlib.util
from pathlib import Path
import unittest


SCRIPT = Path(__file__).parents[1] / "check-autogenesis-nat-gcd-greatest-result.py"
SPEC = importlib.util.spec_from_file_location("check_nat_gcd_greatest_result", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class NatGcdGreatestResultTests(unittest.TestCase):
    def setUp(self):
        self.result = MODULE.load(MODULE.RESULT)

    def test_exact_result_is_accepted(self):
        MODULE.validate(self.result)

    def test_footprint_mutation_is_rejected(self):
        changed = copy.deepcopy(self.result)
        changed["target"]["axiom_footprint"] = ["propext"]
        with self.assertRaisesRegex(MODULE.ResultError, "target"):
            MODULE.validate(changed)

    def test_execution_count_mutation_is_rejected(self):
        changed = copy.deepcopy(self.result)
        changed["execution"]["fresh_imports"] = 3
        with self.assertRaisesRegex(MODULE.ResultError, "execution"):
            MODULE.validate(changed)

    def test_authority_widening_is_rejected(self):
        changed = copy.deepcopy(self.result)
        changed["authority"]["ledger_writes"] = 1
        with self.assertRaisesRegex(MODULE.ResultError, "authority"):
            MODULE.validate(changed)


if __name__ == "__main__":
    unittest.main()
