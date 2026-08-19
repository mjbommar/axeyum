from __future__ import annotations

import copy
import importlib.util
from pathlib import Path
import unittest


SCRIPT = Path(__file__).parents[1] / "check-autogenesis-reflexivity-coverage.py"
SPEC = importlib.util.spec_from_file_location("check_autogenesis_reflexivity_coverage", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class ReflexivityCoverageResultTests(unittest.TestCase):
    def inputs(self):
        mapped = []
        observed = []
        for index in range(138):
            row = {
                "fact_id": f"F:test-{index:03d}",
                "family": "test-family",
                "partition": "train" if index < 78 else "development",
                "target_definition": f"Axeyum.Test.r{index:03d}",
                "statement_sha256": f"{index:064x}",
                "artifact_file": f"r{index:03d}.ndjson",
            }
            mapped.append(row)
            observed.append(
                {
                    **row,
                    "outcome": "producer-decline",
                    "reason": "terminal-not-exact-equality",
                    "detail": "terminal goal is not an exact Eq application",
                    "executor_budget_consumed": 0,
                    "ledger_writes": 0,
                }
            )
        mapping = {
            "schema_version": 1,
            "kind": "axeyum-autogenesis-reflexivity-coverage-input",
            "state": "proof-free-source-input",
            "rows": mapped,
        }
        mapping["input_sha256"] = MODULE.digest(mapping)
        coverage = {"producer-decline:terminal-not-exact-equality": 138}
        manifest = {
            "input_sha256": mapping["input_sha256"],
            "population": {"train_development": 138},
            "budget": {
                "max_binders": 8,
                "max_constructed_nodes": 16,
                "executor_invocations": 0,
                "ledger_writes": 0,
            },
            "coverage": coverage,
            "admissible_proofs": [],
        }
        observation = {
            "schema_version": 1,
            "kind": "axeyum-autogenesis-reflexivity-coverage-observation",
            "state": "diagnostic-no-ledger-credit",
            "input_sha256": mapping["input_sha256"],
            "budget": manifest["budget"],
            "coverage": coverage,
            "rows": observed,
        }
        return manifest, mapping, observation

    def test_exact_diagnostic_population_is_accepted(self):
        MODULE.validate_observation(*self.inputs())

    def test_ledger_write_claim_is_rejected(self):
        manifest, mapping, observation = self.inputs()
        observation["rows"][0]["ledger_writes"] = 1
        with self.assertRaisesRegex(MODULE.CoverageResultError, "authoritative budget"):
            MODULE.validate_observation(manifest, mapping, observation)

    def test_held_out_row_is_rejected(self):
        manifest, mapping, observation = self.inputs()
        mapping["rows"][0]["partition"] = "held-out"
        observation["rows"][0]["partition"] = "held-out"
        unsigned = dict(mapping)
        unsigned.pop("input_sha256")
        mapping["input_sha256"] = MODULE.digest(unsigned)
        manifest["input_sha256"] = mapping["input_sha256"]
        observation["input_sha256"] = mapping["input_sha256"]
        with self.assertRaisesRegex(MODULE.CoverageResultError, "held-out"):
            MODULE.validate_observation(manifest, mapping, observation)

    def test_coverage_mutation_is_rejected(self):
        manifest, mapping, observation = self.inputs()
        changed = copy.deepcopy(observation)
        changed["coverage"]["producer-decline:terminal-not-exact-equality"] = 137
        with self.assertRaisesRegex(MODULE.CoverageResultError, "totals"):
            MODULE.validate_observation(manifest, mapping, changed)


if __name__ == "__main__":
    unittest.main()
