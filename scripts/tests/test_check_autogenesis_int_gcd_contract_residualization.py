from __future__ import annotations

import copy
import importlib.util
from pathlib import Path
import sys
import unittest


SCRIPT = Path(__file__).parents[1] / "check-autogenesis-int-gcd-contract-residualization.py"
SPEC = importlib.util.spec_from_file_location("check_int_gcd_residualization", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


class IntGcdContractResidualizationTests(unittest.TestCase):
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
        with self.assertRaisesRegex(MODULE.ResidualizationError, message):
            MODULE.validate_observation(values)

    def test_exact_control_is_accepted(self):
        MODULE.validate_observation(self.values())

    def test_held_out_access_is_rejected(self):
        self.reject(
            lambda value: value["authority"].__setitem__("held_out_inspected", True),
            "authority",
        )

    def test_residual_identity_is_pinned(self):
        self.reject(
            lambda value: value["residualization"].__setitem__(
                "residual_binders", ["Nat.lcm"]
            ),
            "contract",
        )

    def test_specialization_cannot_be_self_reported_false(self):
        self.reject(
            lambda value: value["residualization"].__setitem__(
                "specialization_verified", False
            ),
            "contract",
        )

    def test_transitive_theorem_closure_cannot_be_hidden(self):
        self.reject(
            lambda value: value["source_witness"].__setitem__(
                "transitive_theorem_dependencies", []
            ),
            "assurance",
        )


if __name__ == "__main__":
    unittest.main()
