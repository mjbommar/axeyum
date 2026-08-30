"""Controls for scripts/check-autogenesis-already-proved.py.

Not a fail-closed CI guard (the script is a report, exit 0 by design) so this
does not carry the mutation-testing regime the frontier's G/S guards do. It
still needs to be right in both directions: a name match reported when there
is none, and a name match MISSED when the environment plainly has it, are
both wrong answers a lane could act on. Plus the one behaviour that IS
safety-relevant: refusing a held-out fact id even when named explicitly.
"""

from __future__ import annotations

import importlib.util
import json
import pathlib
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "check-autogenesis-already-proved.py"

_spec = importlib.util.spec_from_file_location("check_autogenesis_already_proved", SCRIPT)
_mod = importlib.util.module_from_spec(_spec)
assert _spec and _spec.loader
sys.modules[_spec.name] = _mod
_spec.loader.exec_module(_mod)  # type: ignore[union-attr]


def _fact(fact_id: str, title: str, status: str = "open") -> dict:
    return {
        "schema_version": 1,
        "id": fact_id,
        "title": title,
        "statement": title,
        "epistemic_status": status,
    }


class SourceNameExtraction(unittest.TestCase):
    def test_matches_the_pinned_title_shape(self) -> None:
        fact = _fact("F:ml430-x", "Mathlib v4.30 source proposition Nat.lcm_comm")
        self.assertEqual(_mod.source_name_of(fact), "Nat.lcm_comm")

    def test_none_for_an_unrelated_title(self) -> None:
        fact = _fact("F:nat-zero-add", "the zero-add identity")
        self.assertIsNone(_mod.source_name_of(fact))

    def test_none_when_title_is_missing(self) -> None:
        self.assertIsNone(_mod.source_name_of({"id": "F:x"}))


class Screen(unittest.TestCase):
    """Positive control (real match), negative control (real non-match), and
    the held-out refusal, over a synthetic facts dir + env snapshot -- never
    the real tree, so this suite cannot be flaky against a sibling lane's
    landed proof."""

    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self._tmp.cleanup)
        self.facts_dir = pathlib.Path(self._tmp.name) / "facts"
        self.facts_dir.mkdir()
        self.env_path = pathlib.Path(self._tmp.name) / "env.json"

        matched = _fact("F:ml430-nat-lcm-comm-aaaa",
                        "Mathlib v4.30 source proposition Nat.lcm_comm")
        unmatched = _fact("F:ml430-nat-brand-new-bbbb",
                          "Mathlib v4.30 source proposition Nat.brand_new_lemma")
        (self.facts_dir / "F-ml430-nat-lcm-comm-aaaa.json").write_text(json.dumps(matched))
        (self.facts_dir / "F-ml430-nat-brand-new-bbbb.json").write_text(json.dumps(unmatched))

        self.env_path.write_text(json.dumps({
            "declarations": ["Nat", "Eq", "Nat.lcm_comm"],
        }))

    def test_positive_control_a_real_match_is_reported(self) -> None:
        result = _mod.screen(
            ["F:ml430-nat-lcm-comm-aaaa"], self.facts_dir, self.env_path, held=set())
        self.assertEqual(result["already_name_matched"], 1)
        self.assertTrue(result["rows"][0]["name_matches_kernel_environment"])

    def test_negative_control_a_real_non_match_is_not_reported(self) -> None:
        result = _mod.screen(
            ["F:ml430-nat-brand-new-bbbb"], self.facts_dir, self.env_path, held=set())
        self.assertEqual(result["already_name_matched"], 0)
        self.assertFalse(result["rows"][0]["name_matches_kernel_environment"])

    def test_mixed_batch_counts_exactly_the_matches(self) -> None:
        result = _mod.screen(
            ["F:ml430-nat-lcm-comm-aaaa", "F:ml430-nat-brand-new-bbbb"],
            self.facts_dir, self.env_path, held=set())
        self.assertEqual(result["screened"], 2)
        self.assertEqual(result["already_name_matched"], 1)

    def test_held_out_fact_id_is_refused_even_when_named_explicitly(self) -> None:
        with self.assertRaises(SystemExit) as ctx:
            _mod.screen(
                ["F:ml430-nat-lcm-comm-aaaa"], self.facts_dir, self.env_path,
                held={"F:ml430-nat-lcm-comm-aaaa"})
        self.assertEqual(ctx.exception.code, 2)

    def test_held_out_refusal_does_not_fire_on_a_dispatchable_row(self) -> None:
        # False-positive control for the refusal above: a row that is NOT in
        # the held-out set must not be blocked by it.
        result = _mod.screen(
            ["F:ml430-nat-brand-new-bbbb"], self.facts_dir, self.env_path,
            held={"F:ml430-some-other-held-out-row"})
        self.assertEqual(result["screened"], 1)


class HeldOutPopulationIsFailClosed(unittest.TestCase):
    """`held_out_ids` must refuse an empty population.

    The refusal in `screen` is `set(fact_ids) & held`, so an empty `held` makes
    it unreachable and this tool would publish a per-fact already-proved verdict
    for every blind row -- printing exactly what it prints when it works. The
    tool always had the refusal and never had this check; added 2026-08-30
    alongside the ADR-0617 refusal in `brief-step0.py`.
    """

    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self._tmp.cleanup)
        self.dir = pathlib.Path(self._tmp.name)

    def _manifest(self, name: str, partitions: list[str]) -> pathlib.Path:
        path = self.dir / name
        path.write_text(json.dumps({"entries": [
            {"fact_id": f"F:row-{i}", "partition": p}
            for i, p in enumerate(partitions)]}))
        return path

    def test_a_population_with_no_held_out_rows_is_refused(self) -> None:
        a = self._manifest("a.json", ["train", "development"])
        b = self._manifest("b.json", ["train"])
        with self.assertRaises(SystemExit) as ctx:
            _mod.held_out_ids(a, b)
        self.assertEqual(ctx.exception.code, 2)

    def test_positive_control_one_held_out_row_is_enough(self) -> None:
        # Without this the guard above is satisfied by refusing every input.
        a = self._manifest("a.json", ["train", "held-out"])
        b = self._manifest("b.json", ["development"])
        self.assertEqual(_mod.held_out_ids(a, b), {"F:row-1"})


if __name__ == "__main__":
    unittest.main()
