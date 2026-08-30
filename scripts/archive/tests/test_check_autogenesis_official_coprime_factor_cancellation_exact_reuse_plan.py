from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
PATH = ROOT / "scripts/check-autogenesis-official-coprime-factor-cancellation-exact-reuse-plan.py"
SPEC = importlib.util.spec_from_file_location("official_cancellation_exact_reuse_plan", PATH)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class OfficialCancellationExactReusePlanTests(unittest.TestCase):
    def setUp(self) -> None:
        self.plan = MODULE.load(MODULE.PLAN)

    def reject(self, mutation) -> None:
        changed = copy.deepcopy(self.plan)
        mutation(changed)
        with self.assertRaises(MODULE.OfficialCancellationExactReusePlanError):
            MODULE.validate(changed)

    def test_current_plan_passes(self) -> None:
        MODULE.validate(copy.deepcopy(self.plan))

    def test_rejects_one_run(self) -> None:
        self.reject(lambda value: value["acceptance"].__setitem__("fresh_complete_invocations", 1))

    def test_rejects_leaf_composition(self) -> None:
        self.reject(lambda value: value["acceptance"]["new_cancellation_composed_roots"].append(MODULE.REUSED[0]))

    def test_rejects_nonexact_identity(self) -> None:
        self.reject(lambda value: value["acceptance"].__setitem__("each_reused_root_source_and_target_declaration_sha256_must_match", False))

    def test_rejects_compatibility_loss(self) -> None:
        self.reject(lambda value: value["acceptance"].__setitem__("each_reused_root_checked_compatibility_must_be_kernel_type_shape", False))

    def test_rejects_extra_composition(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_composition_operations", 14))

    def test_rejects_retry(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_retries", 1))

    def test_rejects_early_credit(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("official_cancellation_credit", 1))

    def test_rejects_ledger_write(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("ledger_writes", 1))


if __name__ == "__main__":
    unittest.main()
