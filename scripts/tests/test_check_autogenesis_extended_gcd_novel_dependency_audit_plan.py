from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-extended-gcd-novel-dependency-audit-plan.py"
SPEC = importlib.util.spec_from_file_location("extended_gcd_novel_plan", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class ExtendedGcdNovelDependencyAuditPlanTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.plan = MODULE.load(MODULE.PLAN)

    def reject(self, mutate, message: str) -> None:
        changed = copy.deepcopy(self.plan)
        mutate(changed)
        with self.assertRaisesRegex(
            MODULE.ExtendedGcdNovelDependencyAuditPlanError, message
        ):
            MODULE.validate(changed)

    def test_exact_plan_is_accepted(self) -> None:
        MODULE.validate(self.plan)

    def test_root_removal_is_rejected(self) -> None:
        self.reject(lambda value: value["fixed_roots"].pop(), "fixed novel roots")

    def test_eq_symm_reread_is_rejected(self) -> None:
        self.reject(
            lambda value: value["fixed_roots"].append("Eq.symm"),
            "fixed novel roots",
        )

    def test_reused_footprint_change_is_rejected(self) -> None:
        self.reject(
            lambda value: value["inputs"]["established_eq_symm_result"][
                "axiom_footprint"
            ].append("propext"),
            "Eq.symm reuse contract",
        )

    def test_second_import_is_rejected(self) -> None:
        self.reject(
            lambda value: value["budget"].__setitem__("max_batch_importer_runs", 2),
            "audit budget",
        )

    def test_reconstruction_authority_is_rejected(self) -> None:
        self.reject(
            lambda value: value["authority"].__setitem__(
                "reconstruction_allowed", True
            ),
            "audit authority",
        )


if __name__ == "__main__":
    unittest.main()
