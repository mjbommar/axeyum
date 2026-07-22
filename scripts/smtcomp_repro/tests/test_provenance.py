"""Focused tests for the source-family/exact-content provenance generator."""

from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from provenance import build, normalize_id, source_family  # noqa: E402


class ProvenanceTests(unittest.TestCase):
    def test_normalize_and_source_family(self) -> None:
        self.assertEqual(
            normalize_id("/x/non-incremental/QF_UF/cvc5-regress-clean/a.smt2"),
            "QF_UF/cvc5-regress-clean/a.smt2",
        )
        self.assertEqual(
            source_family("QF_UF/cvc5-regress-clean/a.smt2"),
            "QF_UF/cvc5-regress-clean",
        )
        self.assertEqual(
            source_family("QF_BV/20221214-p4dfa-XiaoqiChen/TCP/a.smt2"),
            "QF_BV/20221214-p4dfa-XiaoqiChen/TCP",
        )

    def test_build_finds_exact_duplicates_and_outcomes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / "non-incremental" / "QF_UF" / "pack"
            root.mkdir(parents=True)
            first = root / "a.smt2"
            second = root / "b.smt2"
            third = root / "c.smt2"
            first.write_text("(set-logic QF_UF)\n", encoding="utf-8")
            second.write_bytes(first.read_bytes())
            third.write_text("(set-logic QF_UF)\n(assert true)\n", encoding="utf-8")
            raw = {
                str(first): {
                    "axeyum": {
                        "logic": "QF_UF",
                        "expected_status": "sat",
                        "reported_status": "sat",
                    }
                },
                str(second): {
                    "axeyum": {
                        "logic": "QF_UF",
                        "expected_status": "sat",
                        "reported_status": "unknown",
                    }
                },
                str(third): {
                    "axeyum": {
                        "logic": "QF_UF",
                        "expected_status": "sat",
                        "reported_status": None,
                    }
                },
            }
            report = build(json.loads(json.dumps(raw)))
            self.assertEqual(report["summary"]["files"], 3)
            self.assertEqual(report["summary"]["unique_content_sha256"], 2)
            self.assertEqual(report["summary"]["exact_duplicate_groups"], 1)
            self.assertEqual(report["summary"]["exact_duplicate_excess"], 1)
            row = report["source_family_rows"]["QF_UF/pack"]
            self.assertEqual(row["decided_correct"], 1)
            self.assertEqual(row["declined"], 1)
            self.assertEqual(row["no_answer"], 1)


if __name__ == "__main__":
    unittest.main()
