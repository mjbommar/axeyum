#!/usr/bin/env python3
"""Controls for `scripts/gen-statement-adapters.py`.

The generator turns a fact's `formal.statement` into a proof-free Lean adapter
so `lean4export` can freeze its elaborated type -- the artifact the agent's
tier-C producers consume. These tests pin the two behaviours that matter for
reachability: names are derived deterministically from fact ids, and the
`--exportable-only` filter drops exactly the arrow-bearing statements that
lean4export 3.1.0 silently refuses (measured 2026-08-25).

Each test writes a tiny fact corpus to a temp dir and runs the script as a
subprocess, so a regression is a failed assertion rather than a quiet pass.
"""

from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "gen-statement-adapters.py"

_spec = importlib.util.spec_from_file_location("gen_statement_adapters", SCRIPT)
_mod = importlib.util.module_from_spec(_spec)
assert _spec and _spec.loader
_spec.loader.exec_module(_mod)


def _fact(fid: str, stmt: str, lang: str = "lean4-surface") -> dict:
    return {
        "id": fid,
        "epistemic_status": "open",
        "formal": {"language": lang, "statement": stmt},
    }


class CamelTests(unittest.TestCase):
    def test_strips_prefix_and_hash_and_camelcases(self) -> None:
        self.assertEqual(_mod.camel("F:ml430-int-add-modeq-left-ee732b5b"), "intAddModeqLeft")

    def test_is_deterministic(self) -> None:
        fid = "F:ml430-nat-mod-lcm-ee6bdd41"
        self.assertEqual(_mod.camel(fid), _mod.camel(fid))
        self.assertEqual(_mod.camel(fid), "natModLcm")


class ArrowClassifierTests(unittest.TestCase):
    def test_unicode_and_ascii_arrows_and_iff_are_arrow_bearing(self) -> None:
        for s in ["a → b", "a -> b", "a ↔ b", "a <-> b", "∀ x, P x → Q x"]:
            self.assertTrue(_mod.has_top_level_arrow(s), s)

    def test_atom_statement_is_exportable(self) -> None:
        for s in ["∀ (a n : ℤ), a % n ≡ a [ZMOD n]", "∀ {n : ℕ} (a : ℕ), a ≡ a [MOD n]"]:
            self.assertFalse(_mod.has_top_level_arrow(s), s)


class GenerateTests(unittest.TestCase):
    def _run(self, facts: list[dict], extra: list[str]) -> tuple[dict, str, str]:
        with tempfile.TemporaryDirectory() as td:
            tdp = Path(td)
            fdir = tdp / "facts"
            fdir.mkdir()
            for f in facts:
                (fdir / f"{f['id'].split(':')[1]}.json").write_text(json.dumps(f))
            out_lean = tdp / "out.lean"
            out_map = tdp / "out.map.json"
            cp = subprocess.run(
                [
                    sys.executable, str(SCRIPT),
                    "--facts-dir", str(fdir),
                    "--module", "TestBatch",
                    "--out-lean", str(out_lean),
                    "--out-map", str(out_map),
                    *extra,
                    *sum((["--fact", f["id"]] for f in facts), []),
                ],
                capture_output=True, text=True,
            )
            self.assertEqual(cp.returncode, 0, cp.stderr)
            return json.loads(out_map.read_text()), out_lean.read_text(), cp.stderr

    def test_emits_all_by_default(self) -> None:
        facts = [
            _fact("F:ml430-nat-modeq-refl-aaaaaa", "∀ {n : ℕ} (a : ℕ), a ≡ a [MOD n]"),
            _fact("F:ml430-int-modeq-neg-bbbbbb", "∀ {n a b : ℤ}, a ≡ b [ZMOD n] → -a ≡ -b [ZMOD n]"),
        ]
        mapping, lean, _ = self._run(facts, [])
        self.assertEqual(len(mapping), 2)
        self.assertIn("Axeyum.Autogenesis.Statement.Generated.natModeqRefl", mapping.values())
        self.assertIn("def natModeqRefl : Prop :=", lean)

    def test_exportable_only_drops_arrow_bearing(self) -> None:
        facts = [
            _fact("F:ml430-nat-modeq-refl-aaaaaa", "∀ {n : ℕ} (a : ℕ), a ≡ a [MOD n]"),
            _fact("F:ml430-int-modeq-neg-bbbbbb", "∀ {n a b : ℤ}, a ≡ b [ZMOD n] → -a ≡ -b [ZMOD n]"),
        ]
        mapping, lean, _ = self._run(facts, ["--exportable-only"])
        self.assertEqual(list(mapping), ["F:ml430-nat-modeq-refl-aaaaaa"])
        self.assertNotIn("intModeqNeg", lean)

    def test_non_lean4_statement_is_skipped(self) -> None:
        facts = [_fact("F:ml430-foo-cccccc", "some prose", lang="informal")]
        mapping, _, err = self._run(facts, [])
        self.assertEqual(mapping, {})
        self.assertIn("no lean4 statement", err)


if __name__ == "__main__":
    unittest.main()
