from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
PATH = ROOT / "scripts/check-autogenesis-official-gcd-succ-root-export-result.py"
SPEC = importlib.util.spec_from_file_location("official_gcd_succ_root_export_result", PATH)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class OfficialGcdSuccRootExportResultTests(unittest.TestCase):
    def setUp(self) -> None:
        self.result = MODULE.load(MODULE.RESULT)

    def reject(self, mutation) -> None:
        changed = copy.deepcopy(self.result)
        mutation(changed)
        with self.assertRaises(MODULE.OfficialGcdSuccRootExportResultError):
            MODULE.validate(changed)

    def test_current_result_passes(self) -> None:
        MODULE.validate(copy.deepcopy(self.result))

    def test_rejects_representation_change(self) -> None:
        self.reject(lambda value: value["stream"].__setitem__("representation", "native"))

    def test_rejects_stream_size_change(self) -> None:
        self.reject(lambda value: value["stream"].__setitem__("bytes", 2000001))

    def test_rejects_dependency_loss(self) -> None:
        self.reject(lambda value: value["theorem"]["direct_theorem_dependencies"].clear())

    def test_rejects_axiom_footprint(self) -> None:
        self.reject(lambda value: value["theorem"]["axiom_footprint"].append("propext"))

    def test_rejects_one_import(self) -> None:
        self.reject(lambda value: value["execution"].__setitem__("importer_runs", 1))

    def test_rejects_successor_credit_loss(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("new_official_gcd_succ_credit", 0))

    def test_rejects_closed_credit(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("closed_gcd_balanced_bezout_credit", 1))

    def test_rejects_leaf_completion_loss(self) -> None:
        self.reject(lambda value: value["next_boundary"].__setitem__("official_representation_gcd_leaves_completed", False))

    def test_rejects_cleanup_drift(self) -> None:
        self.reject(lambda value: value["cleanup"].__setitem__("preexisting_baseline_unchanged", False))

    def test_rejects_ledger_write(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("ledger_writes", 1))


if __name__ == "__main__":
    unittest.main()
