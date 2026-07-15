#!/usr/bin/env python3
"""Tests for fail-closed Glaurung native-profile summarization."""

from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "summarize-glaurung-native-profile.py"
SPEC = importlib.util.spec_from_file_location("native_profile_summary", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


PHASES = (
    "arena_create",
    "translation",
    "solver_create",
    "word_rewrite",
    "bit_blast",
    "cnf_encode",
    "solve",
    "model_lift",
    "replay",
    "model_extract",
)


def record(sequence: int, *, query_hash: str, outcome: str = "sat") -> dict[str, object]:
    row: dict[str, object] = {
        "schema": "glaurung-axeyum-native-profile-v1",
        "process_id": 41,
        "sequence": sequence,
        "query_hash": query_hash,
        "word_policy": "raw",
        "timeout_ms": 250,
        "outcome": outcome,
        "complete": True,
        "assertion_count": 1,
        "translated_exprs": 4,
        "arena_terms": 7,
        "symbols": 1,
        "model_values": 1 if outcome == "sat" else 0,
        "root_encodings": 1,
        "checks": 1,
        "aig_nodes": 11,
        "cnf_variables": 9,
        "cnf_clauses": 13,
        "total_nanos": 100,
    }
    for phase in PHASES:
        row[f"{phase}_nanos"] = 0
    row["bit_blast_nanos"] = 40
    row["cnf_encode_nanos"] = 30
    row["solve_nanos"] = 10
    return row


def write_jsonl(path: Path, rows: list[dict[str, object]]) -> None:
    path.write_text("".join(json.dumps(row) + "\n" for row in rows), encoding="utf-8")


class NativeProfileSummaryTests(unittest.TestCase):
    def test_summarizes_ordered_occurrences_and_manifest_overlap(self) -> None:
        query = "sha256:" + "a" * 64
        other = "sha256:" + "b" * 64
        with tempfile.TemporaryDirectory() as raw_temp:
            temp = Path(raw_temp)
            profile = temp / "axeyum-profile-41.jsonl"
            write_jsonl(
                profile,
                [record(0, query_hash=query), record(1, query_hash=query), record(2, query_hash=other, outcome="unsat")],
            )
            manifest = temp / "manifest-v1.json"
            manifest.write_text(
                json.dumps(
                    {
                        "version": 1,
                        "logic": "QF_BV",
                        "files": [
                            {
                                "content_hash": query,
                                "expected": "sat",
                                "family": "register-slice",
                                "path": "queries/a.smt2",
                                "tiers": ["representative"],
                            }
                        ],
                    }
                ),
                encoding="utf-8",
            )

            summary = MODULE.summarize([profile], manifest)

        self.assertEqual(summary["schema"], "axeyum-glaurung-native-profile-summary-v1")
        self.assertEqual(summary["records"], 3)
        self.assertEqual(summary["unique_queries"], 2)
        self.assertEqual(summary["duplicate_occurrences"], 1)
        self.assertEqual(summary["outcomes"], {"sat": 2, "unsat": 1, "unknown": 0})
        self.assertEqual(summary["decided_percent"], 100.0)
        self.assertEqual(summary["latency_nanos"]["p50"], 100)
        self.assertEqual(summary["latency_nanos"]["p95"], 100)
        self.assertEqual(summary["phases"]["bit_blast"]["nanos"], 120)
        self.assertEqual(summary["phases"]["bit_blast"]["percent"], 40.0)
        self.assertEqual(summary["phases"]["unattributed"]["nanos"], 60)
        self.assertEqual(summary["structure_totals"]["aig_nodes"], 33)
        self.assertEqual(summary["processes"], [{"process_id": 41, "first_sequence": 0, "last_sequence": 2, "records": 3}])
        self.assertEqual(
            summary["manifest_overlap"],
            {
                "manifest": str(manifest),
                "unique_queries": 1,
                "occurrences": 2,
                "families": {"register-slice": {"unique_queries": 1, "occurrences": 2}},
            },
        )

    def test_rejects_incomplete_out_of_order_and_manifest_disagreement(self) -> None:
        query = "sha256:" + "c" * 64
        with tempfile.TemporaryDirectory() as raw_temp:
            temp = Path(raw_temp)
            profile = temp / "profile.jsonl"
            manifest = temp / "manifest.json"
            manifest.write_text(
                json.dumps(
                    {
                        "version": 1,
                        "logic": "QF_BV",
                        "files": [
                            {
                                "content_hash": query,
                                "expected": "unsat",
                                "family": "register-slice",
                                "path": "queries/c.smt2",
                                "tiers": ["representative"],
                            }
                        ],
                    }
                ),
                encoding="utf-8",
            )

            incomplete = record(0, query_hash=query)
            incomplete["complete"] = False
            write_jsonl(profile, [incomplete])
            with self.assertRaisesRegex(MODULE.ProfileError, "not complete"):
                MODULE.summarize([profile])

            write_jsonl(profile, [record(1, query_hash=query), record(0, query_hash=query)])
            with self.assertRaisesRegex(MODULE.ProfileError, "strictly increasing"):
                MODULE.summarize([profile])

            write_jsonl(profile, [record(0, query_hash=query)])
            with self.assertRaisesRegex(MODULE.ProfileError, "manifest outcome disagreement"):
                MODULE.summarize([profile], manifest)

    def test_cli_can_require_every_query_decided(self) -> None:
        query = "sha256:" + "d" * 64
        with tempfile.TemporaryDirectory() as raw_temp:
            temp = Path(raw_temp)
            profile = temp / "profile.jsonl"
            write_jsonl(profile, [record(0, query_hash=query, outcome="unknown")])
            completed = subprocess.run(
                [sys.executable, str(SCRIPT), str(profile), "--require-100-percent-decided"],
                check=False,
                capture_output=True,
                text=True,
            )

        self.assertNotEqual(completed.returncode, 0)
        self.assertIn("decided rate is 0.000%", completed.stderr)


if __name__ == "__main__":
    unittest.main()
