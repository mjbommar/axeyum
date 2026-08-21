from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-xgcd-val-baseline-preserving-reconstruction-result.py"
SPEC = importlib.util.spec_from_file_location("xgcd_val_baseline_result", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class XgcdValBaselinePreservingResultTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.result = MODULE.load(MODULE.RESULT)

    def reject(self, mutate) -> None:
        changed = copy.deepcopy(self.result)
        mutate(changed)
        with self.assertRaisesRegex(
            MODULE.XgcdValBaselineResultError, "measured baseline result"
        ):
            MODULE.validate(changed)

    def test_exact_result_is_accepted(self) -> None:
        MODULE.validate(self.result)

    def test_empty_footprint_claim_is_rejected(self) -> None:
        self.reject(
            lambda value: value["outcome"].__setitem__(
                "axiom_footprint_empty", True
            )
        )

    def test_propext_removal_is_rejected(self) -> None:
        self.reject(lambda value: value["measured_row"]["axiom_footprint"].clear())

    def test_single_import_claim_is_rejected(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("importer_runs", 1))

    def test_baseline_restore_claim_is_rejected(self) -> None:
        self.reject(
            lambda value: value["outcome"].__setitem__(
                "preexisting_baseline_restored", False
            )
        )

    def test_projection_credit_is_rejected(self) -> None:
        self.reject(
            lambda value: value["authority"].__setitem__(
                "projection_equation_credit", 1
            )
        )


if __name__ == "__main__":
    unittest.main()
