from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
PATH = ROOT / "scripts/check-autogenesis-nat-gcd-fib-add-self-portable-support-capsules-result.py"
SPEC = importlib.util.spec_from_file_location("portable_support_capsules_result", PATH)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class PortableSupportCapsulesResultTests(unittest.TestCase):
    def setUp(self) -> None:
        self.result = MODULE.load(MODULE.RESULT)

    def reject(self, mutation) -> None:
        changed = copy.deepcopy(self.result)
        mutation(changed)
        with self.assertRaises(MODULE.PortableCapsuleResultError):
            MODULE.validate(changed)

    def test_current_result_passes(self) -> None:
        MODULE.validate(copy.deepcopy(self.result))

    def test_rejects_missing_capsule(self) -> None:
        self.reject(lambda value: value["capsules"].pop("clean_order"))

    def test_rejects_declaration_identity_change(self) -> None:
        self.reject(lambda value: value["capsules"]["fibonacci_coprimality"].__setitem__("declaration_sha256", "0" * 64))

    def test_rejects_import_count_change(self) -> None:
        self.reject(lambda value: value["verification"].__setitem__("raw_fresh_import_invocations", 8))

    def test_rejects_axiom_credit(self) -> None:
        self.reject(lambda value: value["verification"].__setitem__("all_axiom_footprints", ["propext"]))

    def test_rejects_target_credit(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("target_credit", 1))

    def test_rejects_target_submission(self) -> None:
        self.reject(lambda value: value["budget_accounting"].__setitem__("exact_target_submissions", 1))


if __name__ == "__main__":
    unittest.main()
