from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
PATH = ROOT / "scripts/check-autogenesis-official-gcd-balanced-bezout-reconstruction-result.py"
SPEC = importlib.util.spec_from_file_location("balanced_bezout_result", PATH)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class BalancedBezoutResultTests(unittest.TestCase):
    def setUp(self) -> None:
        self.result = MODULE.load(MODULE.RESULT)

    def reject(self, mutation) -> None:
        changed = copy.deepcopy(self.result)
        mutation(changed)
        with self.assertRaises(MODULE.BalancedBezoutResultError):
            MODULE.validate(changed)

    def test_current_result_passes(self) -> None:
        MODULE.validate(copy.deepcopy(self.result))

    def test_rejects_compilation_credit(self) -> None:
        self.reject(lambda value: value["result"].__setitem__("generic_main_source_compiled", True))

    def test_rejects_hidden_export(self) -> None:
        self.reject(lambda value: value["execution"].__setitem__("exporter_invocations", 1))

    def test_rejects_retry(self) -> None:
        self.reject(lambda value: value["execution"].__setitem__("retries_after_compilation", 1))

    def test_rejects_baseline_change(self) -> None:
        self.reject(lambda value: value["cleanup"].__setitem__("preexisting_baseline_unchanged", False))

    def test_rejects_missing_diagnostic(self) -> None:
        self.reject(lambda value: value["result"]["diagnostic_classes"].pop())

    def test_rejects_specialization_credit(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("target_specialization_credit", 1))

    def test_rejects_reusing_support_as_credit(self) -> None:
        self.reject(lambda value: value["next_boundary"].__setitem__("reuse_successful_private_support_compilation_as_theorem_credit", True))


if __name__ == "__main__":
    unittest.main()
