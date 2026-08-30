from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-xgcd-val-direct-reconstruction-result.py"
SPEC = importlib.util.spec_from_file_location("xgcd_val_direct_result", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class XgcdValDirectReconstructionResultTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.result = MODULE.load(MODULE.RESULT)

    def reject(self, mutate) -> None:
        changed = copy.deepcopy(self.result)
        mutate(changed)
        with self.assertRaisesRegex(
            MODULE.XgcdValDirectResultError, "measured direct result"
        ):
            MODULE.validate(changed)

    def test_exact_result_is_accepted(self) -> None:
        MODULE.validate(self.result)

    def test_elaboration_claim_is_rejected(self) -> None:
        self.reject(
            lambda value: value["outcome"].__setitem__("theorem_elaborated", True)
        )

    def test_definition_test_claim_is_rejected(self) -> None:
        self.reject(
            lambda value: value["outcome"].__setitem__(
                "definitional_equality_tested", True
            )
        )

    def test_export_claim_is_rejected(self) -> None:
        self.reject(
            lambda value: value["budget"].__setitem__("exporter_invocations", 1)
        )

    def test_retry_claim_is_rejected(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("retries", 1))

    def test_projection_credit_is_rejected(self) -> None:
        self.reject(
            lambda value: value["authority"].__setitem__(
                "projection_equation_credit", 1
            )
        )


if __name__ == "__main__":
    unittest.main()
