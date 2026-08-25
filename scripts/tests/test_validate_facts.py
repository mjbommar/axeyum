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


GREP_Q_FACT = ROOT / "artifacts" / "facts" / "F-nat-add-assoc.json"


class GrepDashQCheckerCommandTests(unittest.TestCase):
    """`grep -q` as a pipeline consumer under `set -o pipefail` is banned
    (CLAUDE.md, banned-shell-idioms #2): `-q` exits at the first match and
    SIGPIPEs the producer, turning the pipeline's exit status nondeterministic.
    99 committed facts carried this idiom before 2026-08-25's rewrite to
    `grep -c` + a count `test`; this guard is what keeps it from coming back.
    """

    def setUp(self) -> None:
        self.fact = json.loads(GREP_Q_FACT.read_text(encoding="utf-8"))

    def errors_for_checker_command(self, cmd: str) -> list[str]:
        fact = copy.deepcopy(self.fact)
        fact["evidence"][0]["checker_command"] = cmd
        return MODULE.validate_one(GREP_Q_FACT, fact, {fact["id"]})

    def test_committed_checker_commands_use_grep_dash_c_and_are_accepted(self) -> None:
        # The real, already-rewritten command in the committed fact must not
        # trip the guard -- otherwise the guard would be rejecting the exact
        # form it is supposed to require.
        self.assertEqual(self.errors_for_checker_command(
            self.fact["evidence"][0]["checker_command"]
        ), [])

    def test_grep_dash_q_pipeline_consumer_is_rejected(self) -> None:
        # Deliberately ONE assertion, not a subTest loop: the mutation harness
        # counts each subTest failure as a separate death, and this suite's
        # contract is that deleting the guard kills exactly one test. The
        # broader spelling coverage lives in
        # `test_grep_dash_q_helper_detects_every_spelling` below, which calls
        # the detector function directly and so is unaffected by a mutation
        # at the `validate_one` call site.
        errors = self.errors_for_checker_command("cmd 2>/dev/null | grep -q 'pattern'")
        self.assertTrue(
            any("grep -q" in e and "SIGPIPE" in e for e in errors),
            f"expected a grep -q rejection, got {errors!r}",
        )

    def test_grep_dash_q_helper_detects_every_spelling(self) -> None:
        # Exercises `checker_command_uses_grep_dash_q` directly (not through
        # `validate_one`), so this test's outcome is independent of the
        # `fact-checker-grep-dash-q` mutation control above.
        for bad_cmd in (
            "cmd 2>/dev/null | grep -q 'pattern'",
            "cmd 2>/dev/null | grep -qE 'pattern'",
            "cmd 2>/dev/null | grep -Eq 'pattern'",
            "cmd 2>/dev/null | grep -qxF 'pattern'",
            "cmd 2>/dev/null | grep --quiet 'pattern'",
            "cmd 2>/dev/null | grep -q -E 'pattern'",
        ):
            with self.subTest(bad_cmd=bad_cmd):
                self.assertTrue(
                    MODULE.checker_command_uses_grep_dash_q(bad_cmd),
                    f"expected {bad_cmd!r} to be detected as grep -q",
                )
        for ok_cmd in (
            "cmd 2>/dev/null | grep -c 'pattern'",
            "cmd -A1 'x' 2>/dev/null | grep -Ec 'pattern'",
        ):
            with self.subTest(ok_cmd=ok_cmd):
                self.assertFalse(MODULE.checker_command_uses_grep_dash_q(ok_cmd))

    def test_grep_dash_c_forms_are_not_flagged(self) -> None:
        # A guard broad enough to also catch the REMEDY is worse than no
        # guard: every fact using the correct form would fail the ledger.
        for ok_cmd in (
            "cmd 2>/dev/null | grep -c 'pattern'",
            "cmd 2>/dev/null | grep -cE 'pattern'",
            "cmd 2>/dev/null | grep -Ec 'pattern'",
            "cmd 2>/dev/null | grep -xFc 'pattern'",
            "cmd -A1 'x' 2>/dev/null | grep -Ec 'pattern'",
        ):
            with self.subTest(ok_cmd=ok_cmd):
                self.assertEqual(self.errors_for_checker_command(ok_cmd), [])


if __name__ == "__main__":
    unittest.main()
