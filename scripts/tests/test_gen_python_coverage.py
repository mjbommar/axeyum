#!/usr/bin/env python3
"""Controls for `scripts/gen-python-coverage.py`.

Every guard here is mutation-verified to kill exactly one test --
`python3 scripts/tests/mutation_controls.py python-coverage`.

The fixture tree is deliberately tiny and deliberately WRONG in one way per
test: a `pub(crate)` item that must not be counted public, a `#[cfg(test)]`
module that must not leak, a deferral with no reason, a document that claims
the exit criterion while the backlog is non-empty. A ledger whose scanner
over-counts and whose deferral file accepts anything would produce a healthy
looking table over a population it made up.
"""

from __future__ import annotations

import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]

_spec = importlib.util.spec_from_file_location(
    "gen_python_coverage", ROOT / "scripts" / "gen-python-coverage.py"
)
assert _spec is not None and _spec.loader is not None
gpc = importlib.util.module_from_spec(_spec)
sys.modules["gen_python_coverage"] = gpc
_spec.loader.exec_module(gpc)


FAKE_CRATE = '''\
//! A fake crate. Note the doc line with **F32**/**F64** in it: that literal
//! shape contains `/*` and once swallowed the rest of the file.

pub struct Bound;

impl Bound {
    pub fn reachable(&self) -> u32 {
        0
    }

    pub fn never_called(&self) -> u32 {
        1
    }
}

pub struct Unbound;

impl Unbound {
    pub fn reachable(&self) -> u32 {
        2
    }
}

pub fn free_bound() -> u32 {
    3
}

pub fn free_unbound() -> u32 {
    4
}

pub(crate) fn crate_only() -> u32 {
    5
}

pub const AFTER_THE_DOC_COMMENT: u32 = 6;

// `pub`, and NOT named `tests`: the scanner also skips a module called `tests`
// by name, and skips anything under a non-`pub` module as unreachable. With the
// conventional `mod tests` the `#[cfg(test)]` guard could be deleted with every
// dedicated test still green -- two other rules were doing its job. The
// mutation harness reported exactly that, twice, and this shape is the fix.
#[cfg(test)]
pub mod not_named_tests {
    pub fn test_helper() -> u32 {
        7
    }

    pub struct TestOnly;
}
'''

BINDING = '''\
use axeyum_fake::{Bound, free_bound};

/// A doc comment naming `free_unbound` and `Unbound`, which must NOT count.
pub fn wrapper(b: &Bound) -> u32 {
    b.reachable() + free_bound()
}
'''

INVENTORY = '''\
# Fake inventory

## 1. The fake crate -- `crates/axeyum-fake` (tier R)

| path:line | signature | Python name | tier | notes |
|---|---|---|---|---|
| `lib.rs:4` | `pub struct Bound` | `Bound` | R | referenced by the binding |
| `lib.rs:20` | `pub struct Unbound` | `Unbound` | R | not referenced, not deferred |
| `lib.rs:34` | `pub fn free_unbound() -> u32` | *(skip v1)* | R | not referenced |
| `lib.rs:42` | `pub fn crate_only() -> u32` | `--` | P | tier P, never in the backlog |
| `parse.rs:1` | `FpUsage` (hardcoded `false`, fail-closed) | | R | the `false` trap |
'''


def build_tree(directory: Path, *, deferrals: dict | None = None, claim: str = "") -> Path:
    root = directory
    (root / "crates" / "axeyum-fake" / "src").mkdir(parents=True)
    (root / "crates" / "axeyum-fake" / "Cargo.toml").write_text('[package]\nname = "axeyum-fake"\n')
    (root / "crates" / "axeyum-fake" / "src" / "lib.rs").write_text(FAKE_CRATE)
    (root / "crates" / "axeyum-py" / "src").mkdir(parents=True)
    (root / "crates" / "axeyum-py" / "Cargo.toml").write_text('[package]\nname = "axeyum-py"\n')
    (root / "crates" / "axeyum-py" / "src" / "lib.rs").write_text(BINDING)
    (root / "docs" / "python-2026-08" / "inventories").mkdir(parents=True)
    (root / "docs" / "python-2026-08" / "inventories" / "fake.md").write_text(INVENTORY)
    (root / "docs" / "plan" / "generated").mkdir(parents=True)
    (root / "artifacts").mkdir(parents=True)
    (root / "artifacts" / "python-coverage-deferrals.json").write_text(
        json.dumps({"deferrals": deferrals if deferrals is not None else {}}, indent=2)
    )
    if claim:
        (root / "docs" / "python-2026-08" / "claiming.md").write_text(claim + "\n")
    return root


class ScannerTests(unittest.TestCase):
    """What the public-surface scanner counts, and what it must not."""

    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.root = build_tree(Path(self.tmp.name))
        self.addCleanup(self.tmp.cleanup)

    def items(self) -> dict[str, str]:
        ledger = gpc.build(self.root)
        entry = next(c for c in ledger["crates"] if c["crate"] == "axeyum-fake")
        return {row.split("|")[1]: row.split("|")[3] for row in entry["items"]}

    def test_referenced_and_unreferenced_are_distinguished(self) -> None:
        items = self.items()
        self.assertEqual(items["free_bound"], "named-in-crate-path")
        self.assertEqual(items["free_unbound"], "")
        self.assertEqual(items["Bound::reachable"], "method-of-referenced-type")
        # `Unbound::reachable` has the same method name as a referenced type's
        # method. Attribution is by the OWNING type, so it must stay unreferenced.
        self.assertEqual(items["Unbound::reachable"], "")

    def test_pub_crate_is_not_public(self) -> None:
        self.assertNotIn("crate_only", self.items())

    def test_cfg_test_module_is_not_public_surface(self) -> None:
        items = self.items()
        self.assertNotIn("test_helper", items)
        self.assertNotIn("TestOnly", items)

    def test_doc_comment_containing_a_slash_star_does_not_swallow_the_file(self) -> None:
        # `**F32**/**F64**` contains `/*`. The naive block-comment strip lost
        # every item after such a line -- 31 of 61 in `axeyum-fp` -- and the
        # count still looked plausible.
        self.assertIn("AFTER_THE_DOC_COMMENT", self.items())

    def test_doc_comment_reference_does_not_count(self) -> None:
        # `free_unbound` and `Unbound` appear ONLY in a doc comment in the
        # fixture binding. Counting prose would inflate `referenced`.
        self.assertEqual(self.items()["free_unbound"], "")


class InventoryTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.root = build_tree(Path(self.tmp.name))
        self.addCleanup(self.tmp.cleanup)

    def test_backlog_is_tier_r_and_unreferenced_only(self) -> None:
        ledger = gpc.build(self.root)
        entry = next(c for c in ledger["crates"] if c["crate"] == "axeyum-fake")
        backlog = {name for row in entry["backlog"] for name in row["items"]}
        # `FpUsage` is the third: its row is tier R and the binding never
        # names it. `crate_only` is tier P and must NOT appear however
        # unreferenced it is -- the criterion is about tier R.
        self.assertEqual(backlog, {"Unbound", "free_unbound", "FpUsage"})
        self.assertEqual(entry["tier_r_unreferenced"], 3)

    def test_a_backticked_keyword_is_not_an_item(self) -> None:
        # "hardcoded `false`, fail-closed" once entered the backlog as `false`.
        ledger = gpc.build(self.root)
        names = {name for row in ledger["inventory"] for name in row["items"]}
        self.assertNotIn("false", names)

    def test_empty_inventory_directory_is_refused(self) -> None:
        (self.root / "docs" / "python-2026-08" / "inventories" / "fake.md").unlink()
        with self.assertRaises(gpc.CoverageError):
            gpc.build(self.root)

    def test_a_tree_with_no_crates_is_refused(self) -> None:
        # The MESSAGE is asserted, not just the exception type. Every later
        # step of `build` also fails on an empty tree, so a bare
        # `assertRaises(CoverageError)` passed with the guard deleted -- the
        # mutation harness reported it SURVIVED, which is what a control that
        # measures nothing looks like.
        with tempfile.TemporaryDirectory() as empty:
            with self.assertRaises(gpc.CoverageError) as caught:
                gpc.build(Path(empty))
        self.assertIn("no crates found", str(caught.exception))


class DeferralTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.addCleanup(self.tmp.cleanup)

    def test_a_deferral_without_a_reason_is_rejected(self) -> None:
        build_tree(self.root, deferrals={"axeyum-fake:Unbound": {"slice": "S1"}})
        with self.assertRaises(gpc.CoverageError) as caught:
            gpc.build(self.root)
        self.assertIn("reason", str(caught.exception))

    def test_an_empty_reason_is_rejected(self) -> None:
        build_tree(self.root, deferrals={"axeyum-fake:Unbound": {"reason": "   "}})
        with self.assertRaises(gpc.CoverageError):
            gpc.build(self.root)

    def test_a_deferral_with_a_reason_leaves_the_backlog(self) -> None:
        build_tree(
            self.root,
            deferrals={"axeyum-fake:Unbound": {"reason": "no Python consumer yet", "slice": "S1"}},
        )
        ledger = gpc.build(self.root)
        entry = next(c for c in ledger["crates"] if c["crate"] == "axeyum-fake")
        self.assertEqual(entry["deferred"], 1)
        self.assertEqual(entry["tier_r_unreferenced"], 2)
        self.assertEqual(ledger["deferrals"]["axeyum-fake:Unbound"]["matched_rows"], 1)


class ClaimGuardTests(unittest.TestCase):
    """`U > 0` is fine. `U > 0` next to a claim that it is 0 is not."""

    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.addCleanup(self.tmp.cleanup)

    def run_main(self, claim: str) -> int:
        build_tree(self.root, claim=claim)
        return gpc.main(["--root", str(self.root)])

    def test_a_claim_with_a_non_empty_backlog_fails(self) -> None:
        self.assertEqual(
            self.run_main("Every tier-R row is bound, so the criterion is met."), 1
        )

    def test_reporting_the_backlog_is_not_a_claim(self) -> None:
        self.assertEqual(
            self.run_main("The tier-R coverage criterion is NOT met: 8 rows remain."), 0
        )

    def test_a_future_tense_plan_is_not_a_claim(self) -> None:
        self.assertEqual(
            self.run_main("Plan 02 is complete once every tier-R row is bound."), 0
        )

    def test_no_claim_anywhere_is_a_pass(self) -> None:
        self.assertEqual(self.run_main("The backlog stands at eight rows."), 0)


class RegenerationTests(unittest.TestCase):
    def test_regeneration_is_byte_stable(self) -> None:
        first = gpc.build(ROOT)
        second = gpc.build(ROOT)
        self.assertEqual(gpc.render_json(first), gpc.render_json(second))
        self.assertEqual(gpc.render_markdown(first), gpc.render_markdown(second))

    def test_committed_artifacts_are_current(self) -> None:
        ledger = gpc.build(ROOT)
        for relative, rendered in (
            (gpc.JSON_OUT, gpc.render_json(ledger)),
            (gpc.MD_OUT, gpc.render_markdown(ledger)),
        ):
            committed = (ROOT / relative).read_text(encoding="utf-8")
            self.assertEqual(
                gpc._normalise(committed),  # noqa: SLF001 - the git_commit field
                gpc._normalise(rendered),
                f"{relative} is stale: python3 scripts/gen-python-coverage.py",
            )

    def test_check_reports_a_stale_artifact(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = build_tree(Path(tmp))
            self.assertEqual(gpc.main(["--root", str(root)]), 0)
            target = root / gpc.MD_OUT
            target.write_text(target.read_text() + "\ndrift\n")
            self.assertEqual(gpc.main(["--check", "--root", str(root)]), 1)

    def test_a_different_git_commit_is_not_drift(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = build_tree(Path(tmp))
            self.assertEqual(gpc.main(["--root", str(root)]), 0)
            target = root / gpc.JSON_OUT
            target.write_text(
                target.read_text().replace('"git_commit": "unknown"', '"git_commit": "deadbeef"')
            )
            self.assertEqual(gpc.main(["--check", "--root", str(root)]), 0)

    def test_the_census_line_is_the_documented_shape(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            line = gpc.census_line(gpc.build(build_tree(Path(tmp))))
        self.assertTrue(line.startswith("PYTHON_COVERAGE|crates="))
        for field in ("public=", "referenced=", "inventoried=", "tier_r_unreferenced=", "deferred="):
            self.assertIn(field, line)


if __name__ == "__main__":
    unittest.main()
