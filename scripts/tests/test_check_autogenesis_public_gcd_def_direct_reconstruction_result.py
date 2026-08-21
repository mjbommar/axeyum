from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-public-gcd-def-direct-reconstruction-result.py"
SPEC = importlib.util.spec_from_file_location("public_gcd_def_direct_result", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class PublicGcdDefDirectResultTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.result = MODULE.load(MODULE.RESULT)

    def reject(self, mutate) -> None:
        changed = copy.deepcopy(self.result)
        mutate(changed)
        with self.assertRaisesRegex(MODULE.PublicGcdDefDirectResultError, "measured direct result"):
            MODULE.validate(changed)

    def test_exact_result_is_accepted(self) -> None:
        MODULE.validate(self.result)

    def test_zero_branch_claim_is_rejected(self) -> None:
        self.reject(
            lambda value: value["outcome"].__setitem__("zero_branch_definitionally_equal", True)
        )

    def test_export_claim_is_rejected(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("exporter_invocations", 1))

    def test_retry_claim_is_rejected(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("retries", 1))

    def test_ledger_credit_is_rejected(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("ledger_writes", 1))


if __name__ == "__main__":
    unittest.main()
