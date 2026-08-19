import copy
import importlib.util
import json
import unittest
from pathlib import Path


SCRIPT = Path(__file__).resolve().parents[1] / "check-autogenesis-1-result.py"
RESULT = Path(__file__).resolve().parents[2] / "artifacts/autogenesis/autogenesis-1-result.json"
SPEC = importlib.util.spec_from_file_location("check_autogenesis_1_result", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class Autogenesis1ResultTests(unittest.TestCase):
    def setUp(self):
        self.value = json.loads(RESULT.read_text(encoding="utf-8"))

    @staticmethod
    def rehash(value):
        value.pop("result_sha256", None)
        value["result_sha256"] = MODULE.digest(value)

    def test_committed_result_is_valid(self):
        MODULE.validate(self.value)

    def test_rehashed_human_intervention_rejects(self):
        changed = copy.deepcopy(self.value)
        changed["assurance"]["human_interventions_after_launch"] = 1
        self.rehash(changed)
        with self.assertRaisesRegex(MODULE.ResultError, "proof-affecting intervention"):
            MODULE.validate(changed)

    def test_rehashed_budget_change_rejects(self):
        changed = copy.deepcopy(self.value)
        changed["budgets"]["pre_b_a_negative"] = 20
        self.rehash(changed)
        with self.assertRaisesRegex(MODULE.ResultError, "fixed budgets"):
            MODULE.validate(changed)

    def test_rehashed_failed_reproduction_check_rejects(self):
        changed = copy.deepcopy(self.value)
        changed["reproduction"]["checks"]["same_artifact_bytes"] = False
        self.rehash(changed)
        with self.assertRaisesRegex(MODULE.ResultError, "incomplete or failed"):
            MODULE.validate(changed)
