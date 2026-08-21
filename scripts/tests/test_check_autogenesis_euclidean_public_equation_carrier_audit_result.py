from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-euclidean-public-equation-carrier-audit-result.py"
SPEC = importlib.util.spec_from_file_location(
    "euclidean_equation_carrier_audit_result", SCRIPT
)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class EuclideanEquationCarrierAuditResultTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.result = MODULE.load(MODULE.RESULT)

    def reject(self, mutate) -> None:
        changed = copy.deepcopy(self.result)
        mutate(changed)
        with self.assertRaisesRegex(
            MODULE.EquationCarrierAuditResultError,
            "measured equation carrier audit",
        ):
            MODULE.validate(changed)

    def test_exact_result_is_accepted(self) -> None:
        MODULE.validate(self.result)

    def test_remainder_carrier_removal_is_rejected(self) -> None:
        self.reject(lambda value: value["rows"][5].__setitem__("axiom_footprint", []))

    def test_generic_carrier_reclassification_is_rejected(self) -> None:
        self.reject(
            lambda value: value["rows"][8].__setitem__("class", "empty-footprint")
        )

    def test_private_fuel_contamination_is_rejected(self) -> None:
        self.reject(
            lambda value: value["rows"][7].__setitem__(
                "axiom_footprint", ["propext"]
            )
        )

    def test_replacement_claim_is_rejected(self) -> None:
        self.reject(
            lambda value: value["authority"].__setitem__(
                "replacement_source_compilations", 1
            )
        )

    def test_ledger_claim_is_rejected(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("ledger_writes", 1))


if __name__ == "__main__":
    unittest.main()
