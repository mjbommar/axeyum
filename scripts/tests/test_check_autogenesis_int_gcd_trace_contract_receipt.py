from __future__ import annotations

import copy
import importlib.util
from pathlib import Path
import sys
import unittest


SCRIPT = Path(__file__).parents[1] / "check-autogenesis-int-gcd-trace-contract-receipt.py"
SPEC = importlib.util.spec_from_file_location("check_int_gcd_trace_contract_receipt", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


class IntGcdTraceContractReceiptTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        manifest = MODULE.load(MODULE.MANIFEST)
        archive = manifest["observation_archive"]
        cls.observation = MODULE.load(Path(archive["root"]) / archive["file"])

    def values(self):
        return copy.deepcopy(self.observation)

    def resign(self, values):
        values.pop("observation_sha256", None)
        values["observation_sha256"] = MODULE.canonical_digest(values)

    def reject(self, mutate, message):
        values = self.values()
        mutate(values)
        self.resign(values)
        with self.assertRaisesRegex(MODULE.TraceContractReceiptError, message):
            MODULE.validate_observation(values)

    def test_exact_control_is_accepted(self):
        MODULE.validate_observation(self.values())

    def test_held_out_access_is_rejected(self):
        self.reject(
            lambda value: value["authority"].__setitem__("held_out_inspected", True),
            "authority",
        )

    def test_source_axiom_cannot_be_hidden(self):
        self.reject(
            lambda value: value["receipt"].__setitem__(
                "source_axiom_footprint", ["Upstream.answer"]
            ),
            "source",
        )

    def test_residual_identity_is_pinned(self):
        self.reject(
            lambda value: value["receipt"]["residual"][0].__setitem__(
                "name", "Nat.lcm"
            ),
            "partition",
        )

    def test_consulted_declaration_cannot_be_widened(self):
        self.reject(
            lambda value: value["receipt"]["delta"].__setitem__(
                "consulted_declarations", ["Int.gcd", "Nat.gcd"]
            ),
            "delta",
        )

    def test_theorem_receipt_cannot_be_self_reported(self):
        self.reject(
            lambda value: value["authority"].__setitem__(
                "semantic_theorem_receipts_issued", 1
            ),
            "authority",
        )


if __name__ == "__main__":
    unittest.main()
