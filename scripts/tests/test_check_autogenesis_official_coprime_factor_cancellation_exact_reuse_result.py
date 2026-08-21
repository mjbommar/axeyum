from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
PATH = ROOT / "scripts/check-autogenesis-official-coprime-factor-cancellation-exact-reuse-result.py"
SPEC = importlib.util.spec_from_file_location("official_cancellation_exact_reuse_result", PATH)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class OfficialCancellationExactReuseResultTests(unittest.TestCase):
    def setUp(self) -> None:
        self.result = MODULE.load(MODULE.RESULT)

    def reject(self, mutation) -> None:
        changed = copy.deepcopy(self.result)
        mutation(changed)
        with self.assertRaises(MODULE.OfficialCancellationExactReuseResultError):
            MODULE.validate(changed)

    def test_current_result_passes(self) -> None:
        MODULE.validate(copy.deepcopy(self.result))

    def test_rejects_one_run(self) -> None:
        self.reject(lambda value: value["execution"].__setitem__("complete_invocations", 1))

    def test_rejects_retry(self) -> None:
        self.reject(lambda value: value["execution"].__setitem__("retries", 1))

    def test_rejects_nonexact_leaf_identity(self) -> None:
        self.reject(lambda value: value["reused_declarations"]["Axeyum.Autogenesis.balancedBezoutMulAssocLeafV1"].__setitem__("target_declaration_sha256", "0" * 64))

    def test_rejects_non_kernel_compatibility(self) -> None:
        self.reject(lambda value: value["reused_declarations"]["Axeyum.Autogenesis.balancedBezoutRightDistribLeafV1"].__setitem__("compatibility", "translated-definitional-equality"))

    def test_rejects_axiom_footprint(self) -> None:
        self.reject(lambda value: value["theorem"].__setitem__("axiom_footprint", ["propext"]))

    def test_rejects_dependency_change(self) -> None:
        self.reject(lambda value: value["theorem"]["direct_theorem_dependencies"].pop())

    def test_rejects_lost_credit(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("official_cancellation_credit", 0))

    def test_rejects_fibonacci_submission(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("exact_fibonacci_target_submissions", 1))

    def test_rejects_ledger_write(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("ledger_writes", 1))


if __name__ == "__main__":
    unittest.main()
