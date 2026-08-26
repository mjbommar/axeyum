from __future__ import annotations

import copy
import importlib.util
import json
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-nat-fib-child-qualification.py"
SPEC = importlib.util.spec_from_file_location("check_fib_child_qualification", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class FibChildQualificationTests(unittest.TestCase):
    def setUp(self) -> None:
        self.manifest = json.loads(MODULE.MANIFEST.read_text())

    def test_exact_qualification_is_accepted(self) -> None:
        MODULE.validate(self.manifest)

    def test_selection_and_authority_mutations_are_rejected(self) -> None:
        changed = copy.deepcopy(self.manifest)
        changed["selection"]["fact_id"] = changed["candidates"][1]["fact_id"]
        with self.assertRaisesRegex(MODULE.QualificationError, "selected"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["authority"]["kernel_submissions"] = 1
        with self.assertRaisesRegex(MODULE.QualificationError, "authority"):
            MODULE.validate(changed)

    def test_slice_and_probe_mutations_are_rejected(self) -> None:
        changed = copy.deepcopy(self.manifest)
        changed["candidates"][0]["slice_retained"] += 1
        with self.assertRaisesRegex(MODULE.QualificationError, "type-slice"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["candidates"][0]["whnf_head"] = "Nat.Coprime"
        with self.assertRaisesRegex(MODULE.QualificationError, "probe"):
            MODULE.validate(changed)

    def test_direct_unlock_mutation_is_rejected(self) -> None:
        changed = copy.deepcopy(self.manifest)
        changed["candidates"][0]["direct_unlocks"] = [
            "F:ml430-nat-fib-mono-cc6afe09"
        ]
        with self.assertRaisesRegex(MODULE.QualificationError, "direct unlock"):
            MODULE.validate(changed)

    def test_dependency_receipt_mutation_is_rejected(self) -> None:
        changed = copy.deepcopy(self.manifest)
        changed["candidates"][1]["fact_dependencies"] = [
            "F:ml430-nat-fib-add-two-b86e0c82"
        ]
        with self.assertRaisesRegex(MODULE.QualificationError, "dependency"):
            MODULE.validate(changed)

    def test_selected_live_progress_requires_checked_axiom_free_kernel_evidence(self) -> None:
        fact_id = self.manifest["selection"]["fact_id"]
        fact_path = MODULE.FACTS / (fact_id.replace("F:", "F-") + ".json")
        original = MODULE.load(fact_path)
        self.assertEqual(original["epistemic_status"], "proved")

        changed = copy.deepcopy(original)
        changed["axiom_footprint"] = ["propext"]
        old_load = MODULE.load

        def load_with_changed_fact(path: pathlib.Path):
            if path == fact_path:
                return changed
            return old_load(path)

        MODULE.load = load_with_changed_fact
        try:
            with self.assertRaisesRegex(MODULE.QualificationError, "axiom-free"):
                MODULE.validate(self.manifest)
        finally:
            MODULE.load = old_load

    def test_any_candidate_progress_requires_checked_axiom_free_evidence(self) -> None:
        fact_id = self.manifest["candidates"][1]["fact_id"]
        fact_path = MODULE.FACTS / (fact_id.replace("F:", "F-") + ".json")
        changed = MODULE.load(fact_path)
        changed["epistemic_status"] = "proved"
        changed["proof_route"] = "kernel-lean"
        changed["axiom_footprint"] = ["propext"]
        changed["evidence"] = [{"check_status": "unchecked"}]
        old_load = MODULE.load

        def load_with_changed_fact(path: pathlib.Path):
            if path == fact_path:
                return changed
            return old_load(path)

        MODULE.load = load_with_changed_fact
        try:
            with self.assertRaisesRegex(MODULE.QualificationError, "axiom-free"):
                MODULE.validate(self.manifest)
        finally:
            MODULE.load = old_load


if __name__ == "__main__":
    unittest.main()
