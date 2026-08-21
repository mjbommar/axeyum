from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
PATH = ROOT / "scripts/check-autogenesis-nat-gcd-fib-add-self-clean-dvd-antisymm-result.py"
SPEC = importlib.util.spec_from_file_location("clean_dvd_antisymm_result", PATH)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class CleanDvdAntisymmResultTests(unittest.TestCase):
    def setUp(self) -> None:
        self.result = MODULE.load(MODULE.RESULT)

    def reject(self, mutation) -> None:
        changed = copy.deepcopy(self.result)
        mutation(changed)
        with self.assertRaises(MODULE.CleanDvdAntisymmResultError):
            MODULE.validate(changed)

    def test_current_result_passes(self) -> None:
        MODULE.validate(copy.deepcopy(self.result))

    def test_rejects_second_run(self) -> None:
        self.reject(lambda value: value["execution"].__setitem__("complete_invocations", 2))

    def test_rejects_published_support(self) -> None:
        self.reject(lambda value: value["execution"].__setitem__("published_support_theorems", 1))

    def test_rejects_diagnostic_change(self) -> None:
        self.reject(lambda value: value["decline"].__setitem__("diagnostic", "UnknownConst"))

    def test_rejects_partial_publication(self) -> None:
        self.reject(lambda value: value["decline"].__setitem__("partial_kernel_published", True))

    def test_rejects_retry(self) -> None:
        self.reject(lambda value: value["execution"].__setitem__("retries", 1))

    def test_rejects_support_credit(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("support_credit", 1))

    def test_rejects_target_submission(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("exact_target_submissions", 1))


if __name__ == "__main__":
    unittest.main()
