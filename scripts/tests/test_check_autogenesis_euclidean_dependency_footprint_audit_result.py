from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-euclidean-dependency-footprint-audit-result.py"
SPEC = importlib.util.spec_from_file_location("euclidean_dependency_audit_result", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class EuclideanDependencyAuditResultTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.result = MODULE.load(MODULE.RESULT)

    def reject(self, mutate, message: str) -> None:
        changed = copy.deepcopy(self.result)
        mutate(changed)
        with self.assertRaisesRegex(MODULE.AuditResultError, message):
            MODULE.validate(changed)

    def test_exact_result_is_accepted(self) -> None:
        MODULE.validate(self.result)

    def test_carrier_erasure_is_rejected(self) -> None:
        row = list(MODULE.IDENTITIES).index("Nat.sub_add_cancel")
        self.reject(
            lambda value: value["rows"][row].__setitem__("axiom_footprint", []),
            "Nat.sub_add_cancel",
        )

    def test_second_carrier_is_rejected(self) -> None:
        self.reject(
            lambda value: value["rows"][0].__setitem__("axiom_footprint", ["propext"]),
            "Eq.symm",
        )

    def test_population_drop_is_rejected(self) -> None:
        self.reject(lambda value: value["rows"].pop(), "population coverage")

    def test_aggregate_mutation_is_rejected(self) -> None:
        self.reject(
            lambda value: value["summary"]["class_counts"].__setitem__(
                "empty-footprint", 15
            ),
            "audit aggregate",
        )

    def test_revised_proof_claim_is_rejected(self) -> None:
        self.reject(
            lambda value: value["authority"].__setitem__("revised_proof_compilations", 1),
            "no-credit authority",
        )


if __name__ == "__main__":
    unittest.main()
