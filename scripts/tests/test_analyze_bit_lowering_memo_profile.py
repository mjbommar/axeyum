import copy
import importlib.util
import unittest
from pathlib import Path


SCRIPT = Path(__file__).parents[1] / "analyze-bit-lowering-memo-profile.py"
SPEC = importlib.util.spec_from_file_location("analyze_bit_lowering_memo_profile", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


FAMILIES = {"arithmetic": 1, "comparison": 1}
MANIFEST = "a" * 64


def memo(representation: str, *, dense_bytes: int | None = None) -> dict:
    slots = 5 if representation == "dense-v1" else 3
    header = 80 if dense_bytes is None else dense_bytes
    return {
        "profile_complete": True,
        "representation": representation,
        "source_terms": 5,
        "slots": slots,
        "occupied": 3,
        "lookups": 7,
        "hits": 1,
        "writes": 3,
        "payload_literals": 24,
        "payload_capacity_literals": 25,
        "logical_header_bytes": header,
        "logical_payload_bytes": 96,
        "logical_total_bytes": header + 96,
        "payload_capacity_bytes": 100,
        "root_bits": 1,
        "expected_root_bits": 1,
        "header_accounting": "test",
        "digests": {"lowering_fnv64": "0123456789abcdef", "cnf_fnv64": "fedcba9876543210"},
        "invariants": {key: True for key in MODULE.INVARIANTS},
    }


def instance(index: int, family: str, outcome: str, representation: str) -> dict:
    return {
        "file": f"queries/{index}.smt2",
        "outcome": outcome,
        "expected": "unknown",
        "assertions": 1,
        "dag_nodes": 5,
        "tree_nodes": 8,
        "max_depth": 3,
        "distinct_symbols": 1,
        "query_shape": {"shape": index},
        "query_plan": {"mode": "full", "index": index},
        "corpus_manifest": {
            "expected": outcome,
            "decision_compared": True,
            "decision_agrees": True,
            "family": family,
            "path": f"queries/{index}.smt2",
        },
        "oracle": {
            "backend_kind": "z3",
            "enabled": True,
            "outcome": outcome,
            "decision_compared": True,
            "decision_agrees": True,
            "decision_population": "both-decided",
            "query_boundary": "original parsed assertions",
        },
        "backend_stats": {
            "aig_nodes": 10,
            "cnf_variables": 12,
            "cnf_clauses": 20,
            "bit_blast_ms": 1.0,
            "bit_lowering_memo_representation": 1 if representation == "btree-v1" else 2,
            "bit_lowering_memo_slots": 3 if representation == "btree-v1" else 5,
            "bit_lowering_memo_logical_header_bytes": 80,
            "bit_lowering_memo_logical_total_bytes": 176,
            "bit_lowering_memo_occupied": 3,
            "bit_lowering_structure_digest_hi": 0x01234567,
            "bit_lowering_structure_digest_lo": 0x89ABCDEF,
        },
        "layer_attribution": {"bit_lowering_memo": memo(representation)},
    }


def artifact(representation: str) -> dict:
    rows = [
        instance(0, "arithmetic", "sat", representation),
        instance(1, "comparison", "unsat", representation),
    ]
    totals = {
        key: sum(row["layer_attribution"]["bit_lowering_memo"][key] for row in rows)
        for key in MODULE.MEMO_NUMERIC_FIELDS
    }
    return {
        "version": 39,
        "config": {
            "backend_kind": "sat-bv",
            "logic": "QF_BV",
            "jobs": 1,
            "manifest_validation_jobs": 1,
            "profile_bit_demand": True,
            "demand_bit_slicing": False,
            "range_demand_slicing": False,
            "preprocess": False,
            "compare_z3": True,
            "require_in_process_z3": True,
            "require_reproducible_run": True,
            "require_deterministic_resources": True,
            "timeout_ms": 10_000,
            "resource_limit": 2_000_000,
            "node_budget": 300_000,
            "cnf_variable_budget": 3_000_000,
            "cnf_clause_budget": 8_000_000,
            "min_decided_percent": 100.0,
            "rewrite": {"mode": "off"},
            "query_plan": {"mode": "full"},
            "corpus_manifest": {"content_hash": f"sha256:{MANIFEST}"},
            "config_hash": "config",
            "corpus_hash": "corpus",
            "experiment": {"environment_hash": "environment"},
        },
        "summary": {
            "files": 2,
            "sat": 1,
            "unsat": 1,
            "decided": 2,
            "decided_percent": 100.0,
            "unknown": 0,
            "unsupported": 0,
            "errors": 0,
            "disagree": 0,
            "model_replay_failures": 0,
            "manifest": {"expected": 2, "compared": 2, "agree": 2, "disagree": 0},
            "oracle": {
                "enabled": True,
                "compared": 2,
                "agree": 2,
                "disagree": 0,
                "skipped": 0,
                "decision_population": {
                    "accounted": 2,
                    "both_decided": 2,
                    "axeyum_only_decided": 0,
                    "z3_only_decided": 0,
                    "neither_decided": 0,
                },
            },
            "layer_attribution": {
                "bit_lowering_memo": {
                    "profile_complete": True,
                    "profiled_samples": 2,
                    "digest_samples": 2,
                    "samples": 2,
                    "representation_counts": {
                        "btree-v1": 2 if representation == "btree-v1" else 0,
                        "dense-v1": 2 if representation == "dense-v1" else 0,
                        "unavailable": 0,
                    },
                    **totals,
                    "all_instance_invariants_hold": True,
                }
            },
        },
        "instances": rows,
    }


def analyze(value: dict, representation: str) -> dict:
    return MODULE.analyze_artifact(
        value,
        expected_files=2,
        expected_sat=1,
        expected_unsat=1,
        expected_manifest_sha256=MANIFEST,
        expected_families=FAMILIES,
        expected_representation=representation,
    )


class BitLoweringMemoProfileTests(unittest.TestCase):
    def test_accepts_exact_profile_and_resums_aggregate(self) -> None:
        report = analyze(artifact("btree-v1"), "btree-v1")
        self.assertTrue(report["accepted"])
        self.assertEqual(report["memo_totals"]["occupied"], 6)

    def test_rejects_digest_and_invariant_mutations(self) -> None:
        value = artifact("btree-v1")
        value["instances"][0]["layer_attribution"]["bit_lowering_memo"]["digests"]["cnf_fnv64"] = "BAD"
        with self.assertRaisesRegex(RuntimeError, "digest malformed"):
            analyze(value, "btree-v1")

        value = artifact("btree-v1")
        value["instances"][0]["layer_attribution"]["bit_lowering_memo"]["invariants"]["producer"] = False
        with self.assertRaisesRegex(RuntimeError, "invariant failed"):
            analyze(value, "btree-v1")

    def test_candidate_comparison_allows_only_registered_representation_delta(self) -> None:
        baseline = artifact("btree-v1")
        candidate = artifact("dense-v1")
        before = analyze(baseline, "btree-v1")
        after = analyze(candidate, "dense-v1")
        report = MODULE.compare_artifacts(baseline, candidate, before, after)
        self.assertTrue(report["timing_authorized"])

        drift = copy.deepcopy(candidate)
        drift["instances"][0]["backend_stats"]["aig_nodes"] += 1
        with self.assertRaisesRegex(RuntimeError, "backend structure drift"):
            MODULE.compare_artifacts(baseline, drift, before, after)

    def test_candidate_logical_storage_gate_is_fail_closed(self) -> None:
        baseline = artifact("btree-v1")
        candidate = artifact("dense-v1")
        for row in candidate["instances"]:
            profile = row["layer_attribution"]["bit_lowering_memo"]
            profile["logical_header_bytes"] = 1000
            profile["logical_total_bytes"] = 1096
        aggregate = candidate["summary"]["layer_attribution"]["bit_lowering_memo"]
        aggregate["logical_header_bytes"] = 2000
        aggregate["logical_total_bytes"] = 2192
        before = analyze(baseline, "btree-v1")
        after = analyze(candidate, "dense-v1")
        with self.assertRaisesRegex(RuntimeError, "exceed 110%"):
            MODULE.compare_artifacts(baseline, candidate, before, after)


if __name__ == "__main__":
    unittest.main()
