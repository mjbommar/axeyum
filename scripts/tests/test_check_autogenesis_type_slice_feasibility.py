from __future__ import annotations

import copy
import importlib.util
from pathlib import Path
import sys
import unittest


SCRIPT = Path(__file__).parents[1] / "check-autogenesis-type-slice-feasibility.py"
SPEC = importlib.util.spec_from_file_location(
    "check_autogenesis_type_slice_feasibility", SCRIPT
)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


class TypeSliceResultTests(unittest.TestCase):
    def inputs(self):
        rows = []
        prior = []
        for index in range(138):
            artifact = f"r{index:03d}.ndjson"
            common = {
                "artifact_file": artifact,
                "fact_id": f"F:test-{index:03d}",
                "family": "test",
                "partition": "train" if index < 78 else "development",
                "target_definition": f"Test.r{index:03d}",
            }
            rows.append(
                {
                    **common,
                    "stream_sha256": f"{index:064x}",
                    "declarations": 3,
                    "implementation_declarations": 2,
                    "type_declarations": 1,
                    "implementation_trusted": ["proof"] if index < 114 else [],
                    "type_trusted": [],
                    "abstractable_type_boundary": ["helper"],
                }
            )
            prior.append(
                {
                    **common,
                    "outcome": "adapter-rejection" if index < 114 else "producer-decline",
                }
            )
        observation = {
            "schema_version": 1,
            "kind": "axeyum-autogenesis-type-slice-feasibility",
            "state": "syntactic-diagnostic-no-proof-or-ledger-credit",
            "authority": {
                "partitions_inspected": ["development", "train"],
                "held_out_inspected": False,
                "proof_bodies_executed": False,
                "targets": 138,
            },
            "coverage": {
                "implementation_closure_has_trusted": 114,
                "type_closure_has_no_trusted": 138,
                "type_closure_has_trusted": 0,
            },
            "rows": rows,
        }
        observation["observation_sha256"] = MODULE.canonical_digest(observation)
        manifest = {
            "observation_archive": {
                "observation_sha256": observation["observation_sha256"]
            },
            "coverage": {
                **observation["coverage"],
                "prior_adapter_rejections_with_clean_type_closure": 114,
            },
            "aggregate_declarations": {
                "exported": 414,
                "implementation_closure": 276,
                "type_closure": 138,
                "abstractable_type_boundary_occurrences": 138,
            },
        }
        return manifest, observation, {"rows": prior}

    def test_exact_diagnostic_is_accepted(self):
        MODULE.validate_observation(*self.inputs())

    def test_held_out_row_is_rejected(self):
        manifest, observation, prior = self.inputs()
        observation["rows"][0]["partition"] = "held-out"
        observation["observation_sha256"] = MODULE.canonical_digest(
            {k: v for k, v in observation.items() if k != "observation_sha256"}
        )
        manifest["observation_archive"]["observation_sha256"] = observation[
            "observation_sha256"
        ]
        prior["rows"][0]["partition"] = "held-out"
        with self.assertRaisesRegex(MODULE.TypeSliceResultError, "held-out"):
            MODULE.validate_observation(manifest, observation, prior)

    def test_direct_trusted_type_dependency_changes_totals(self):
        manifest, observation, prior = self.inputs()
        changed = copy.deepcopy(observation)
        changed["rows"][0]["type_trusted"] = ["proof"]
        changed["observation_sha256"] = MODULE.canonical_digest(
            {k: v for k, v in changed.items() if k != "observation_sha256"}
        )
        manifest["observation_archive"]["observation_sha256"] = changed[
            "observation_sha256"
        ]
        with self.assertRaisesRegex(MODULE.TypeSliceResultError, "coverage totals"):
            MODULE.validate_observation(manifest, changed, prior)

    def test_inner_identity_mutation_is_rejected(self):
        manifest, observation, prior = self.inputs()
        observation["rows"][0]["type_declarations"] = 2
        with self.assertRaisesRegex(MODULE.TypeSliceResultError, "identity"):
            MODULE.validate_observation(manifest, observation, prior)


if __name__ == "__main__":
    unittest.main()
