from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / (
    "scripts/check-autogenesis-euclidean-bounded-induction-dependency-audit-result.py"
)
SPEC = importlib.util.spec_from_file_location(
    "euclidean_bounded_dependency_audit_result", SCRIPT
)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class EuclideanBoundedDependencyAuditResultTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.result = MODULE.load(MODULE.RESULT)

    def reject(self, mutate) -> None:
        changed = copy.deepcopy(self.result)
        mutate(changed)
        with self.assertRaisesRegex(
            MODULE.BoundedAuditResultError, "measured dependency audit"
        ):
            MODULE.validate(changed)

    def test_exact_result_is_accepted(self) -> None:
        MODULE.validate(self.result)

    def test_carrier_removal_is_rejected(self) -> None:
        self.reject(
            lambda value: value["rows"][5].__setitem__("axiom_footprint", [])
        )

    def test_carrier_reclassification_is_rejected(self) -> None:
        self.reject(
            lambda value: value["rows"][11].__setitem__(
                "class", "empty-footprint"
            )
        )

    def test_population_change_is_rejected(self) -> None:
        self.reject(lambda value: value["rows"].pop())

    def test_retry_claim_is_rejected(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("retries", 1))

    def test_proof_revision_claim_is_rejected(self) -> None:
        self.reject(
            lambda value: value["authority"].__setitem__(
                "revised_proof_compilations", 1
            )
        )

    def test_ledger_claim_is_rejected(self) -> None:
        self.reject(
            lambda value: value["authority"].__setitem__("ledger_writes", 1)
        )


if __name__ == "__main__":
    unittest.main()
