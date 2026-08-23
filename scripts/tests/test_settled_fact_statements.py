#!/usr/bin/env python3
"""Controls for `scripts/check-settled-fact-statements.py`.

One test per guard, each built to die when its own guard is removed and no
other. Every test builds its own facts and manifest in a temp directory: reading
live `artifacts/` would make the suite drift as facts land, and a fixture that
passes because of today's repository state stops controlling on a day nobody is
watching.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
import pathlib
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SUBJECT = ROOT / "scripts/check-settled-fact-statements.py"


def load_subject():
    spec = importlib.util.spec_from_file_location("check_settled_fact_statements", SUBJECT)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def sha(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


class SettledFactStatementControls(unittest.TestCase):
    def setUp(self):
        self._dir = tempfile.TemporaryDirectory()
        self.tmp = pathlib.Path(self._dir.name)
        self.facts = self.tmp / "facts"
        self.facts.mkdir()
        self.module = load_subject()
        self.module.FACTS = self.facts
        self.module.PINS = self.tmp / "pins.json"

    def tearDown(self):
        self._dir.cleanup()

    def write_fact(self, fact_id, statement, language="lean4", status="proved"):
        (self.facts / f"{fact_id.replace(':', '-')}.json").write_text(
            json.dumps(
                {
                    "id": fact_id,
                    "epistemic_status": status,
                    "formal": {"language": language, "statement": statement},
                }
            ),
            encoding="utf-8",
        )

    def write_pins(self, pins, amendments=None):
        (self.tmp / "pins.json").write_text(
            json.dumps({"pins": pins, "amendments": amendments or []}), encoding="utf-8"
        )

    def run_check(self):
        try:
            return self.module.check(["--quiet"])
        except self.module.StatementDriftError:
            return 2

    def healthy(self):
        self.write_fact("F:a", "STMT A")
        self.write_fact("F:b", "STMT B")
        self.write_pins(
            [
                {"fact_id": "F:a", "language": "lean4", "statement_sha256": sha("STMT A")},
                {"fact_id": "F:b", "language": "lean4", "statement_sha256": sha("STMT B")},
            ]
        )

    def test_healthy_passes(self):
        """Positive control. Without it, a guard rejecting EVERYTHING would
        satisfy every negative test below and look like a working gate."""
        self.healthy()
        self.assertEqual(self.run_check(), 0)

    # --- guard: an unamended statement change is a violation ---------------
    def test_unamended_statement_change_is_a_violation(self):
        self.healthy()
        self.write_fact("F:a", "STMT A REWRITTEN TO MATCH THE PROOF")
        self.assertEqual(self.run_check(), 1)

    # --- guard: a correct amendment permits the change ---------------------
    def test_amended_change_passes(self):
        self.healthy()
        self.write_fact("F:a", "STMT A CORRECTED")
        self.write_pins(
            [
                {"fact_id": "F:a", "language": "lean4", "statement_sha256": sha("STMT A")},
                {"fact_id": "F:b", "language": "lean4", "statement_sha256": sha("STMT B")},
            ],
            [
                {
                    "fact_id": "F:a",
                    "from_sha256": sha("STMT A"),
                    "to_sha256": sha("STMT A CORRECTED"),
                    "reason": "kernel-dumped type replaces a hand-written seed",
                }
            ],
        )
        self.assertEqual(self.run_check(), 0)

    # --- guard: the amendment must describe THIS change --------------------
    def test_amendment_with_wrong_digests_is_a_violation(self):
        """An amendment naming a different edit must not license this one, or
        one amendment becomes a permanent waiver for a fact."""
        self.healthy()
        self.write_fact("F:a", "STMT A REWRITTEN")
        self.write_pins(
            [{"fact_id": "F:a", "language": "lean4", "statement_sha256": sha("STMT A")}],
            [
                {
                    "fact_id": "F:a",
                    "from_sha256": sha("SOMETHING ELSE"),
                    "to_sha256": sha("SOMETHING ELSE AGAIN"),
                    "reason": "unrelated",
                }
            ],
        )
        self.assertEqual(self.run_check(), 1)

    # --- guard: an amendment must be a record, not a rubber stamp ----------
    def test_amendment_without_a_reason_is_an_error(self):
        self.healthy()
        self.write_pins(
            [{"fact_id": "F:a", "language": "lean4", "statement_sha256": sha("STMT A")}],
            [{"fact_id": "F:a", "from_sha256": sha("x"), "to_sha256": sha("y")}],
        )
        self.assertEqual(self.run_check(), 2)

    # --- guard: a silent retraction is reported ----------------------------
    def test_silent_retraction_is_a_violation(self):
        self.healthy()
        self.write_fact("F:a", "STMT A", status="open")
        self.assertEqual(self.run_check(), 1)

    # --- guard: a newly settled fact is NOT drift --------------------------
    def test_newly_settled_fact_is_not_drift(self):
        """Adding a proved fact must not fail the gate, or every landing does."""
        self.healthy()
        self.write_fact("F:c", "STMT C")
        self.assertEqual(self.run_check(), 0)

    # --- guard: fail closed on an empty manifest ---------------------------
    def test_empty_pin_manifest_is_an_error(self):
        self.healthy()
        self.write_pins([])
        self.assertEqual(self.run_check(), 2)

    # --- guard: fail closed when there are no settled facts ----------------
    def test_no_settled_facts_is_an_error(self):
        self.healthy()
        self.write_fact("F:a", "STMT A", status="open")
        self.write_fact("F:b", "STMT B", status="open")
        self.assertEqual(self.run_check(), 2)


if __name__ == "__main__":
    unittest.main()
