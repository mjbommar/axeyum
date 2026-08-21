from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/gen-autogenesis-euclidean-bounded-induction-plan.py"
SPEC = importlib.util.spec_from_file_location("euclidean_bounded_induction_plan", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class EuclideanBoundedInductionPlanTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.plan = MODULE.build()

    def reject(self, mutate) -> None:
        changed = copy.deepcopy(self.plan)
        mutate(changed)
        with self.assertRaises(MODULE.BoundedInductionPlanError):
            MODULE.validate(changed)

    def test_generated_plan_is_current(self) -> None:
        MODULE.validate(self.plan)
        self.assertEqual(MODULE.OUTPUT.read_text(), MODULE.render(self.plan))

    def test_statement_population_is_exact(self) -> None:
        rows = self.plan["inputs"]["allowed_statements"]
        self.assertEqual([row["name"] for row in rows], MODULE.NAMES)
        self.assertEqual(len(rows), 15)

    def test_generated_recursion_cannot_be_enabled(self) -> None:
        self.reject(
            lambda value: value["fixed_induction"].__setitem__(
                "generated_well_founded_recursion_allowed", True
            )
        )

    def test_external_strong_induction_cannot_be_enabled(self) -> None:
        self.reject(
            lambda value: value["fixed_induction"].__setitem__(
                "Nat_strong_induction_on_allowed", True
            )
        )

    def test_target_budget_cannot_expand(self) -> None:
        self.reject(
            lambda value: value["budget"].__setitem__(
                "max_exact_fibonacci_target_submissions", 1
            )
        )

    def test_ledger_authority_cannot_expand(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("ledger_writes", 1))


if __name__ == "__main__":
    unittest.main()
