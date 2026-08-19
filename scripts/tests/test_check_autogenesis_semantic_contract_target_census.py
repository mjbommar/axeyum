from __future__ import annotations

import copy
import importlib.util
from pathlib import Path
import sys
import unittest


SCRIPT = Path(__file__).parents[1] / "check-autogenesis-semantic-contract-target-census.py"
SPEC = importlib.util.spec_from_file_location("check_semantic_contract_target_census", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


class SemanticContractTargetCensusTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        manifest = MODULE.load(MODULE.MANIFEST)
        archive = manifest["observation_archive"]
        cls.observation = MODULE.load(Path(archive["root"]) / archive["file"])

    def values(self):
        return copy.deepcopy(self.observation)

    def resign(self, observation):
        observation.pop("observation_sha256", None)
        observation["observation_sha256"] = MODULE.canonical_digest(observation)

    def test_exact_external_observation_is_accepted(self):
        MODULE.validate_observation(self.values())

    def test_held_out_access_is_rejected(self):
        values = self.values()
        values["authority"]["held_out_inspected"] = True
        self.resign(values)
        with self.assertRaisesRegex(MODULE.TargetCensusError, "authority"):
            MODULE.validate_observation(values)

    def test_false_eligibility_is_rejected(self):
        values = self.values()
        values["rows"][0]["equation_contract"][
            "all_nonrecursive_dependencies_retained"
        ] = True
        self.resign(values)
        with self.assertRaisesRegex(MODULE.TargetCensusError, "eligibility"):
            MODULE.validate_observation(values)

    def test_missing_inventory_must_be_derived(self):
        values = self.values()
        values["rows"][0]["equation_contract"]["missing_from_proof_free_slice"] = [
            "Fabricated.missing"
        ]
        self.resign(values)
        with self.assertRaisesRegex(MODULE.TargetCensusError, "not derived"):
            MODULE.validate_observation(values)

    def test_narrowest_control_identity_is_pinned(self):
        values = self.values()
        row = next(row for row in values["rows"] if row["artifact_file"] == "r018.ndjson" and row["source_name"] == "Int.gcd")
        row["source_value_nodes"] = 12
        self.resign(values)
        with self.assertRaisesRegex(MODULE.TargetCensusError, "narrowest"):
            MODULE.validate_observation(values)


if __name__ == "__main__":
    unittest.main()
