#!/usr/bin/env python3
"""Controls for `scripts/check-mirror-statement-fidelity.py`.

Every guard in the gate has exactly one case here that fires ONLY on it, so
`scripts/tests/mutation_controls.py mirror-statement-fidelity` can delete each
guard in turn and require exactly one test to die. Fixtures are deliberately
ISOLATING -- the real defect trips G1, G2 and G4 at once, and a fixture like
that would keep every one of those tests green while any single guard survived,
which is coverage that was never measured.

The suite carries three things beyond the per-guard cases:

* a FALSE-POSITIVE control over the real committed ledger. A gate that fires on
  healthy input gets ignored, which is the same end state as no gate.
* a regression witness reproducing the actual 2026-08-29 defect verbatim, so
  the gate cannot stop detecting the thing it was built for even if the
  individual signatures are re-cut.
* a check that the gate's SCOPE stops at the mirror programme. Facts outside it
  legitimately carry `render_lean` output; running these guards ledger-wide
  would flag the correct majority.
"""

from __future__ import annotations

import hashlib
import json
import os
import subprocess
import sys
import tempfile
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, "scripts"))

import importlib.util

_spec = importlib.util.spec_from_file_location(
    "check_mirror_statement_fidelity",
    os.path.join(ROOT, "scripts", "check-mirror-statement-fidelity.py"),
)
gate = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(gate)


def sha(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


# A healthy mirror, verbatim in shape from `F-ml430-int-add-comm-c5722728.json`.
ANCHOR_STATEMENT = "∀ (a b : ℤ), a + b = b + a"


def mirror(fid, statement, *, language="lean4-surface", extra_formal=None):
    formal = {"language": language, "statement": statement, "fragment": "Nat"}
    if extra_formal:
        formal.update(extra_formal)
    return {
        "schema_version": 1,
        "id": fid,
        "title": "Mathlib v4.30 source proposition",
        "statement": "The proposition declared as `X` in the pinned Mathlib v4.30 source.",
        "formal": formal,
        "epistemic_status": "open",
        "external_status": "proved",
    }


class Fixture:
    """A minimal repo root: some mirror facts, and optionally a pinning catalog."""

    def __init__(self, facts, *, pin=True, anchor=True):
        self.dir = tempfile.TemporaryDirectory()
        root = self.dir.name
        os.makedirs(os.path.join(root, "artifacts", "facts"))
        os.makedirs(os.path.join(root, "artifacts", "autogenesis"))
        rows = []
        facts = list(facts)
        if anchor:
            facts.append(mirror("F:ml430-anchor-00000000", ANCHOR_STATEMENT))
            rows.append(
                {
                    "fact_id": "F:ml430-anchor-00000000",
                    "source_name": "Anchor.add_comm",
                    "source_statement_sha256": sha(ANCHOR_STATEMENT),
                }
            )
        for f in facts:
            name = f["id"].replace(":", "-").replace(".", "-") + ".json"
            with open(os.path.join(root, "artifacts", "facts", name), "w", encoding="utf-8") as fh:
                json.dump(f, fh, ensure_ascii=False, indent=2)
        if pin:
            with open(
                os.path.join(root, "artifacts", "autogenesis", "catalog-v1.json"),
                "w",
                encoding="utf-8",
            ) as fh:
                json.dump({"kind": "test-catalog", "facts": rows}, fh, ensure_ascii=False)
        self.root = root

    def run(self):
        return gate.check(self.root)

    def __enter__(self):
        return self

    def __exit__(self, *a):
        self.dir.cleanup()


class GuardTests(unittest.TestCase):
    """One case per guard. Each fires on exactly one guard, by construction."""

    def assert_only(self, violations, needle):
        self.assertEqual(
            len(violations), 1, "expected exactly one violation, got: %r" % (violations,)
        )
        self.assertIn(needle, violations[0])

    def test_g1_declaration_keyword_is_rejected(self):
        # `theorem NAME : TYPE` -- a declaration where a proposition belongs.
        # Deliberately free of AxNat / universes / kernel binders so only G1 can fire.
        with Fixture([mirror("F:ml430-g1-00000001", "theorem Foo.bar : Baz")]) as f:
            v, _ = f.run()
            self.assert_only(v, "kernel DECLARATION keyword")

    def test_g2_kernel_carrier_is_rejected(self):
        with Fixture([mirror("F:ml430-g2-00000002", "∀ (n : AxNat), n = n")]) as f:
            v, _ = f.run()
            self.assert_only(v, "kernel carrier")

    def test_g3_universe_annotation_is_rejected(self):
        with Fixture([mirror("F:ml430-g3-00000003", "Eq.{1} α a b")]) as f:
            v, _ = f.run()
            self.assert_only(v, "universe annotation")

    def test_g4_generated_binder_is_rejected(self):
        with Fixture([mirror("F:ml430-g4-00000004", "((x0 : ℕ) -> Foo)")]) as f:
            v, _ = f.run()
            self.assert_only(v, "generated kernel binder")

    def test_g5_kernel_core_language_is_rejected(self):
        # The statement is a perfectly good surface proposition; only the
        # declared language is wrong, which is how the 19 were labelled.
        with Fixture(
            [mirror("F:ml430-g5-00000005", "∀ (n : ℕ), n = n", language="lean4")]
        ) as f:
            v, _ = f.run()
            self.assert_only(v, "must be 'lean4-surface'")

    def test_g6_statement_not_matching_its_pin_is_rejected(self):
        # Surface syntax, right language, no kernel token anywhere -- and still
        # not the proposition that was preregistered. This is the case a token
        # screen structurally cannot see.
        drifted = mirror("F:ml430-anchor-00000000", "∀ (a b : ℤ), a + b = a + b")
        with Fixture([], anchor=False) as f:
            path = os.path.join(f.root, "artifacts", "facts", "drift.json")
            with open(path, "w", encoding="utf-8") as fh:
                json.dump(drifted, fh, ensure_ascii=False)
            with open(
                os.path.join(f.root, "artifacts", "autogenesis", "catalog-v1.json"),
                "w",
                encoding="utf-8",
            ) as fh:
                json.dump(
                    {
                        "facts": [
                            {
                                "fact_id": "F:ml430-anchor-00000000",
                                "source_statement_sha256": sha(ANCHOR_STATEMENT),
                            }
                        ]
                    },
                    fh,
                )
            v, stats = f.run()
            self.assert_only(v, "does not match the preregistered")
            self.assertEqual(stats["pinned"], 1)

    def test_g7_kernel_statement_without_kernel_theorem_is_rejected(self):
        # Deliberately a NON-mirror id: `kernel_statement` is a ledger-wide
        # field, so its one structural rule must hold everywhere, and this case
        # proves the rule is not accidentally scoped to the mirror programme
        # along with the rest of the guards.
        with Fixture(
            [
                mirror(
                    "F:nat-g7-00000007",
                    "∀ (n : ℕ), n = n",
                    extra_formal={"kernel_statement": "theorem Foo.bar : Baz"},
                )
            ]
        ) as f:
            v, _ = f.run()
            self.assert_only(v, "does not name a declaration")

    def test_g8_zero_mirrors_examined_is_rejected(self):
        # The scope selector broke. Everything else in the run looks normal.
        with Fixture([], anchor=False) as f:
            v, stats = f.run()
            self.assertEqual(stats["mirrors"], 0)
            self.assert_only(v, "examined ZERO mirror facts")

    def test_g9_zero_hashes_verified_is_rejected(self):
        # Mirrors present and healthy, but no catalog was read -- so the exact
        # check silently degraded to a token screen. Independent of G8.
        with Fixture([], pin=False) as f:
            v, stats = f.run()
            self.assertGreater(stats["mirrors"], 0)
            self.assertEqual(stats["pinned"], 0)
            self.assert_only(v, "verified ZERO statement hashes")


class FalsePositiveTests(unittest.TestCase):
    """The gate must be silent on healthy input, or it will be ignored."""

    def test_the_committed_ledger_passes(self):
        violations, stats = gate.check(ROOT)
        self.assertEqual(violations, [], "the gate fires on the committed ledger")
        self.assertGreater(stats["mirrors"], 300, "scope selector found almost nothing")
        self.assertGreater(stats["pinned"], 300, "hash check covered almost nothing")

    def test_a_healthy_mirror_alone_passes(self):
        with Fixture([]) as f:
            v, stats = f.run()
            self.assertEqual(v, [])
            self.assertEqual(stats["mirrors"], 1)
            self.assertEqual(stats["pinned"], 1)

    def test_a_mirror_may_carry_the_rendering_in_kernel_statement(self):
        # The whole point of the new field: recording the rendered type is not
        # a violation, overwriting the claim with it is.
        with Fixture(
            [
                mirror(
                    "F:ml430-ok-00000008",
                    "∀ (n : ℕ), n = n",
                    extra_formal={
                        "kernel_theorem": "Nat.refl_example",
                        "kernel_statement": (
                            "theorem Nat.refl_example : ((x0 : AxNat) -> Eq.{1} AxNat x0 x0)"
                        ),
                    },
                )
            ]
        ) as f:
            v, _ = f.run()
            self.assertEqual(v, [])

    def test_non_mirror_facts_are_out_of_scope(self):
        # `lean4` + `render_lean` output is the DOCUMENTED normal shape for a
        # fact that is not a mirror. Flagging those would flag the majority.
        native = mirror("F:nat-refl-example", "theorem Nat.x : ((x0 : AxNat) -> Eq.{1} AxNat x0 x0)")
        native["formal"]["language"] = "lean4"
        with Fixture([native]) as f:
            v, stats = f.run()
            self.assertEqual(v, [])
            self.assertEqual(stats["mirrors"], 1, "only the anchor is in scope")


class RegressionWitnessTests(unittest.TestCase):
    """The 2026-08-29 defect itself, verbatim."""

    OBSERVED = (
        "theorem Nat.coprime_add_self_left : ((x0 : AxNat) -> ((x1 : AxNat) -> "
        "Iff (Eq.{1} AxNat (AxNat.gcd (AxNat.add x0 x1) x1) (AxNat.succ AxNat.zero)) "
        "(Eq.{1} AxNat (AxNat.gcd x0 x1) (AxNat.succ AxNat.zero))))"
    )

    def test_the_original_overwrite_is_caught(self):
        with Fixture(
            [mirror("F:ml430-nat-coprime-add-self-left-5e93448c", self.OBSERVED, language="lean4")]
        ) as f:
            v, _ = f.run()
            self.assertGreaterEqual(len(v), 1)
            self.assertTrue(any("F-ml430-nat-coprime-add-self-left" in x for x in v))

    def test_the_repaired_fact_on_disk_carries_mathlibs_proposition(self):
        path = os.path.join(
            ROOT, "artifacts", "facts", "F-ml430-nat-coprime-add-self-left-5e93448c.json"
        )
        with open(path, encoding="utf-8") as fh:
            doc = json.load(fh)
        self.assertEqual(
            doc["formal"]["statement"], "∀ {m n : ℕ}, (m + n).Coprime n ↔ m.Coprime n"
        )
        self.assertEqual(doc["formal"]["kernel_statement"], self.OBSERVED)


class CliTests(unittest.TestCase):
    """The exit status must depend on the finding, not on the run completing."""

    def _run(self, root):
        return subprocess.run(
            [sys.executable, os.path.join(ROOT, "scripts", "check-mirror-statement-fidelity.py"), root],
            capture_output=True,
            text=True,
        )

    def test_exit_zero_and_pass_verdict_on_healthy_input(self):
        with Fixture([]) as f:
            p = self._run(f.root)
            self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
            self.assertIn("verdict=PASS", p.stdout)

    def test_exit_one_and_fail_verdict_on_a_violation(self):
        # This case checks the PLUMBING -- that the exit status depends on the
        # finding -- so its fixture deliberately trips several guards at once.
        # A fixture tripping exactly one would make this test a second, weaker
        # copy of that guard's control, and the mutation harness would then
        # report two dead tests for one deleted guard instead of one.
        with Fixture(
            [
                mirror(
                    "F:ml430-bad-00000009",
                    "theorem Foo.bar : ((x0 : AxNat) -> Eq.{1} AxNat x0 x0)",
                    language="lean4",
                )
            ]
        ) as f:
            p = self._run(f.root)
            self.assertEqual(p.returncode, 1, p.stdout + p.stderr)
            self.assertIn("verdict=FAIL", p.stdout)
            self.assertNotIn("violations=0", p.stdout)

    def test_exit_two_on_unreadable_input(self):
        with Fixture([]) as f:
            with open(
                os.path.join(f.root, "artifacts", "facts", "broken.json"), "w", encoding="utf-8"
            ) as fh:
                fh.write("{not json")
            p = self._run(f.root)
            self.assertEqual(p.returncode, 2, p.stdout + p.stderr)
            self.assertIn("ERROR", p.stdout)


if __name__ == "__main__":
    unittest.main()
