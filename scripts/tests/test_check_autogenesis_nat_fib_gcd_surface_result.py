#!/usr/bin/env python3
"""Mutation controls for the Nat.fib_gcd surface result."""

from __future__ import annotations

import copy
import importlib.util
import json
import types
import unittest
from unittest import mock


SCRIPT = __import__("pathlib").Path(__file__).parents[1] / (
    "check-autogenesis-nat-fib-gcd-surface-result.py"
)
SPEC = importlib.util.spec_from_file_location("check_nat_fib_gcd_surface_result", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class SurfaceResultTests(unittest.TestCase):
    def test_committed_result_passes(self) -> None:
        result = MODULE.validate()
        self.assertEqual(len(result["present"]), 10)
        self.assertEqual(result["missing"], ["Nat.gcd_zero_left", "Nat.gcd_succ"])

    def test_receipt_mutation_fails(self) -> None:
        original = MODULE.json.loads(MODULE.RESULT.read_text())
        observation = json.loads(
            __import__("pathlib").Path(original["evidence_pack"]["path"])
            .joinpath("observation.json")
            .read_text()
        )
        changed = copy.deepcopy(original)
        changed["composition"]["receipt_sha256"] = "0" * 64
        plan = types.SimpleNamespace(validate=lambda: {}, PlanError=RuntimeError)
        with mock.patch.object(MODULE, "load_module", return_value=plan):
            with mock.patch.object(MODULE.json, "loads", side_effect=[changed, observation]):
                with self.assertRaisesRegex(MODULE.ResultError, "identity"):
                    MODULE.validate()

    def test_target_credit_mutation_fails(self) -> None:
        original = MODULE.json.loads(MODULE.RESULT.read_text())
        observation = json.loads(
            __import__("pathlib").Path(original["evidence_pack"]["path"])
            .joinpath("observation.json")
            .read_text()
        )
        changed = copy.deepcopy(original)
        changed["authority"]["target_credit"] = 1
        plan = types.SimpleNamespace(validate=lambda: {}, PlanError=RuntimeError)
        with mock.patch.object(MODULE, "load_module", return_value=plan):
            with mock.patch.object(MODULE.json, "loads", side_effect=[changed, observation]):
                with self.assertRaisesRegex(MODULE.ResultError, "authority"):
                    MODULE.validate()


if __name__ == "__main__":
    unittest.main()
