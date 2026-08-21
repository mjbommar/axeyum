from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
PATH = ROOT / "scripts/check-autogenesis-nat-gcd-fib-add-self-dvd-antisymm-dependency-audit-plan.py"
SPEC = importlib.util.spec_from_file_location("dvd_antisymm_dependency_audit_plan", PATH)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class DvdAntisymmDependencyAuditPlanTests(unittest.TestCase):
    def setUp(self) -> None:
        self.plan = MODULE.load(MODULE.PLAN)

    def reject(self, mutation) -> None:
        changed = copy.deepcopy(self.plan)
        mutation(changed)
        with self.assertRaises(MODULE.DvdAntisymmDependencyAuditPlanError):
            MODULE.validate(changed)

    def test_current_plan_passes(self) -> None:
        MODULE.validate(copy.deepcopy(self.plan))

    def test_rejects_root_reordering(self) -> None:
        self.reject(lambda value: value["ordered_roots"].reverse())

    def test_rejects_textual_read(self) -> None:
        self.reject(lambda value: value["input"].__setitem__("textual_read_allowed", True))

    def test_rejects_second_read(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_proof_bearing_stream_reads", 2))

    def test_rejects_theorem_submission(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_new_theorem_submissions", 1))

    def test_rejects_rendering(self) -> None:
        self.reject(lambda value: value["tool"].__setitem__("proof_terms_types_or_values_may_be_rendered", True))

    def test_rejects_target_authority(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("exact_target_submissions", 1))

    def test_rejects_ledger_write(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("ledger_writes", 1))


if __name__ == "__main__":
    unittest.main()
