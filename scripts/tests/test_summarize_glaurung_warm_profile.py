#!/usr/bin/env python3
"""Tests for fail-closed Glaurung warm-profile summarization."""

from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "summarize-glaurung-warm-profile.py"
SPEC = importlib.util.spec_from_file_location("warm_profile_summary", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


PHASES = (
    "session_create",
    "translation",
    "word_rewrite",
    "bit_blast",
    "cnf_encode",
    "solve",
    "model_lift",
    "replay",
    "model_extract",
    "unattributed",
)


def record(sequence: int, *, path_created: bool, query: str) -> dict[str, object]:
    row: dict[str, object] = {
        "schema": "glaurung-axeyum-warm-profile-v3",
        "process_id": 17,
        "sequence": sequence,
        "query_hash": query,
        "path_id": 9,
        "path_created": path_created,
        "outcome": "sat",
        "complete": True,
        "assertion_count": 2,
        "common_prefix_assertions": 0 if path_created else 1,
        "assertions_added": 2 if path_created else 1,
        "assertions_popped": 0,
        "translated_exprs": 5,
        "arena_terms": 9,
        "symbols": 1,
        "model_values": 1,
        "root_encodings": 2 if path_created else 1,
        "aig_nodes_added": 4,
        "cnf_variables_added": 5,
        "cnf_clauses_added": 6,
        "aig_nodes": 10,
        "cnf_variables": 11,
        "cnf_clauses": 12,
        "total_nanos": 100,
    }
    for phase in PHASES:
        row[f"{phase}_nanos"] = 0
    row["translation_nanos"] = 20
    row["bit_blast_nanos"] = 30
    row["cnf_encode_nanos"] = 20
    row["solve_nanos"] = 10
    row["unattributed_nanos"] = 20
    row["cnf_gate_mix"] = {field: 0 for field in MODULE.GATE_MIX_FIELDS}
    row["cnf_gate_mix"].update(
        {
            "up_half_definitions": 2,
            "down_half_definitions": 1,
            "xor_half_definitions": 1,
            "not_and_half_definitions": 1,
            "and_tree_half_definitions": 1,
            "direct_positive_and_roots": 1,
            "direct_positive_and_nodes": 2,
            "direct_xor_leaves": 1,
            "fused_positive_and_roots": 1,
            "fused_positive_and_nodes": 2,
            "fused_xor_leaves": 1,
            "repeated_same_context_roots": 1,
            "deduplicated_root_assertions": 1,
            "internal_positive_and_opportunities": 1,
            "internal_positive_and_opportunity_nodes": 3,
            "internal_positive_and_flattened": 1,
            "internal_positive_and_immediate_clauses_avoided": 2,
        }
    )
    return row


class WarmProfileSummaryTests(unittest.TestCase):
    def test_summarizes_paths_duplicates_phases_and_structure(self) -> None:
        query = "sha256:" + "a" * 64
        with tempfile.TemporaryDirectory() as raw_temp:
            profile = Path(raw_temp) / "profile.jsonl"
            profile.write_text(
                "\n".join(
                    json.dumps(row)
                    for row in (
                        record(0, path_created=True, query=query),
                        record(1, path_created=False, query=query),
                    )
                )
                + "\n",
                encoding="utf-8",
            )
            summary = MODULE.summarize([profile])

        self.assertEqual(summary["records"], 2)
        self.assertEqual(summary["unique_queries"], 1)
        self.assertEqual(summary["duplicate_occurrences"], 1)
        self.assertEqual(summary["paths_created"], 1)
        self.assertEqual(summary["decided_percent"], 100.0)
        self.assertEqual(summary["phases"]["bit_blast"], {"nanos": 60, "percent": 30.0})
        self.assertEqual(summary["structure_totals"]["root_encodings"], 3)
        self.assertEqual(summary["cnf_gate_mix_totals"]["xor_half_definitions"], 2)
        self.assertEqual(
            summary["cnf_gate_mix_totals"][
                "internal_positive_and_immediate_clauses_avoided"
            ],
            4,
        )

    def test_rejects_bad_phase_sum_and_path_creation_order(self) -> None:
        query = "sha256:" + "b" * 64
        with tempfile.TemporaryDirectory() as raw_temp:
            profile = Path(raw_temp) / "profile.jsonl"
            bad_sum = record(0, path_created=True, query=query)
            bad_sum["unattributed_nanos"] = 19
            profile.write_text(json.dumps(bad_sum) + "\n", encoding="utf-8")
            with self.assertRaisesRegex(MODULE.ProfileError, "do not equal total_nanos"):
                MODULE.summarize([profile])

            profile.write_text(
                json.dumps(record(0, path_created=False, query=query)) + "\n",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(MODULE.ProfileError, "first occurrence=True"):
                MODULE.summarize([profile])

            bad_mix = record(0, path_created=True, query=query)
            bad_mix["cnf_gate_mix"]["binary_and_half_definitions"] = 1
            profile.write_text(json.dumps(bad_mix) + "\n", encoding="utf-8")
            with self.assertRaisesRegex(MODULE.ProfileError, "shape partition mismatch"):
                MODULE.summarize([profile])

            bad_application = record(0, path_created=True, query=query)
            bad_application["cnf_gate_mix"]["internal_positive_and_flattened"] = 2
            profile.write_text(json.dumps(bad_application) + "\n", encoding="utf-8")
            with self.assertRaisesRegex(MODULE.ProfileError, "applications exceed"):
                MODULE.summarize([profile])

    def test_accepts_historical_v1_without_gate_totals(self) -> None:
        query = "sha256:" + "c" * 64
        historical = record(0, path_created=True, query=query)
        historical["schema"] = "glaurung-axeyum-warm-profile-v1"
        del historical["cnf_gate_mix"]
        with tempfile.TemporaryDirectory() as directory:
            profile = Path(directory) / "profile.jsonl"
            profile.write_text(json.dumps(historical) + "\n", encoding="utf-8")

            summary = MODULE.summarize([profile])

        self.assertEqual(summary["profile_schemas"], [historical["schema"]])
        self.assertNotIn("cnf_gate_mix_totals", summary)

    def test_accepts_historical_v2_gate_mix(self) -> None:
        query = "sha256:" + "d" * 64
        historical = record(0, path_created=True, query=query)
        historical["schema"] = "glaurung-axeyum-warm-profile-v2"
        for field in set(MODULE.GATE_MIX_V3_FIELDS) - set(MODULE.GATE_MIX_V2_FIELDS):
            del historical["cnf_gate_mix"][field]
        with tempfile.TemporaryDirectory() as directory:
            profile = Path(directory) / "profile.jsonl"
            profile.write_text(json.dumps(historical) + "\n", encoding="utf-8")

            summary = MODULE.summarize([profile])

        self.assertEqual(summary["profile_schemas"], [historical["schema"]])
        self.assertEqual(
            set(summary["cnf_gate_mix_totals"]), set(MODULE.GATE_MIX_V2_FIELDS)
        )


if __name__ == "__main__":
    unittest.main()
