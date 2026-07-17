#!/usr/bin/env python3

from __future__ import annotations

import importlib.util
import pathlib
import sys
import types
import unittest


SCRIPT = pathlib.Path(__file__).parents[1] / "analyze-glaurung-profiled-trace.py"
SPEC = importlib.util.spec_from_file_location("profiled_trace", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
profiled = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = profiled
SPEC.loader.exec_module(profiled)


def record(schema: str, sequence: int) -> dict[str, object]:
    warm = schema == profiled.WARM_SCHEMA
    result: dict[str, object] = {
        "schema": schema,
        "sequence": sequence,
        "query_hash": "sha256:" + "a" * 64,
        "outcome": "sat",
        "complete": True,
        "total_nanos": 100,
        "aig_nodes": 3,
        "cnf_variables": 4,
        "cnf_clauses": 5,
    }
    for phase in profiled.WARM_PHASES if warm else profiled.COLD_PHASES:
        result[phase] = 1
    if warm:
        result.update(
            {
                "unattributed_nanos": 100 - len(profiled.WARM_PHASES),
                "aig_nodes_added": 1,
                "cnf_variables_added": 2,
                "cnf_clauses_added": 3,
            }
        )
    return result


class ProfiledTraceAnalysisTests(unittest.TestCase):
    def setUp(self) -> None:
        check = types.SimpleNamespace(
            check_id="check-0",
            query_sha256="a" * 64,
            purpose="fixture",
            axeyum_cold_outcome="sat",
            axeyum_warm_outcome="sat",
            axeyum_warm_execution="warm-retained",
            active_constraint_count=2,
        )
        self.trace = types.SimpleNamespace(
            measurement_schema=profiled.paired.MEASUREMENT_SCHEMA_V2,
            checks=[check],
            driver_label="fixture.sys",
            driver_sha256="d" * 64,
        )

    def test_joins_rotated_profile_pair_and_preserves_timing_identity(self) -> None:
        rows = profiled.join_trace_profiles(
            self.trace,
            [record(profiled.WARM_SCHEMA, 0), record(profiled.COLD_SCHEMA, 1)],
        )
        summary = profiled.aggregate(rows)
        self.assertEqual(summary["occurrences"], 1)
        self.assertEqual(summary["warm"]["adapter_total_nanos"], 100)
        self.assertEqual(summary["structure"]["warm_cnf_clauses_added"], 3)

    def test_rejects_profile_hash_mismatch(self) -> None:
        cold = record(profiled.COLD_SCHEMA, 0)
        cold["query_hash"] = "sha256:" + "b" * 64
        with self.assertRaisesRegex(profiled.paired.AnalysisError, "hash mismatch"):
            profiled.join_trace_profiles(
                self.trace, [cold, record(profiled.WARM_SCHEMA, 1)]
            )

    def test_rejects_cardinality_mismatch(self) -> None:
        with self.assertRaisesRegex(profiled.paired.AnalysisError, "cardinality"):
            profiled.join_trace_profiles(self.trace, [record(profiled.COLD_SCHEMA, 0)])


if __name__ == "__main__":
    unittest.main()
