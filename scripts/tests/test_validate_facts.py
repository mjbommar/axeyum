#!/usr/bin/env python3
"""Mutation controls for `certificate-spec` fact statements."""

from __future__ import annotations

import copy
import importlib.util
import json
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "validate-facts.py"
FACT = ROOT / "artifacts" / "facts" / "F-gf2-general-monomial-composition-criterion.json"

SPEC = importlib.util.spec_from_file_location("validate_facts", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)

class CertificateSpecValidationTests(unittest.TestCase):
    def setUp(self) -> None:
        self.fact = json.loads(FACT.read_text(encoding="utf-8"))

    def errors_for(self, statement: str) -> list[str]:
        fact = copy.deepcopy(self.fact)
        fact["formal"]["statement"] = statement
        return MODULE.validate_one(FACT, fact, {fact["id"]})

    def test_committed_statement_is_valid(self) -> None:
        self.assertEqual(self.errors_for(self.fact["formal"]["statement"]), [])

    def test_malformed_and_non_object_statements_are_rejected(self) -> None:
        for statement, expected in (
            ("{", "not valid JSON"),
            ("[]", "must be a JSON object"),
        ):
            with self.subTest(statement=statement):
                self.assertTrue(any(expected in error for error in self.errors_for(statement)))

    def test_noncanonical_statement_is_rejected(self) -> None:
        parsed = json.loads(self.fact["formal"]["statement"])
        statement = json.dumps(parsed, sort_keys=False, indent=2)
        self.assertTrue(
            any("must use canonical JSON" in error for error in self.errors_for(statement))
        )

    def test_format_and_version_contract_is_rejected_when_mutated(self) -> None:
        parsed = json.loads(self.fact["formal"]["statement"])
        mutations = (
            ({**parsed, "format": ""}, "non-empty string format"),
            ({key: value for key, value in parsed.items() if key != "format"}, "format"),
            ({**parsed, "version": 0}, "positive integer version"),
            ({**parsed, "version": True}, "positive integer version"),
        )
        for mutation, expected in mutations:
            with self.subTest(mutation=mutation):
                statement = json.dumps(mutation, sort_keys=True, separators=(",", ":"))
                self.assertTrue(any(expected in error for error in self.errors_for(statement)))


# The two range-binding controls (semantic and canonicalization mutation of
# `check-gf2-lemire-range.py`) moved out with that checker and the
# `F:gf2-lemire-half-degree-through-400` fact; see
# ../lemire-half-degree-irreducibles. What remains here is the guard that
# lives in this repo: `certificate-spec` statement validation.

if __name__ == "__main__":
    unittest.main()
