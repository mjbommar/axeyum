#!/usr/bin/env python3
"""Controls for the holdout adjacency screen (ADR-0653's rule, as R11).

Every guard here is mutation-verified in
`scripts/tests/mutation_controls.py` under the suite `holdout-adjacency`:
deleting one guard must kill exactly one of these tests. The registration
carries the measured kill sets.

The fixtures are deliberately built rather than read from the repository. A
test that reads the committed manifests measures today's nursery, which is a
moving target and would make a guard's kill set depend on whichever lane
landed a family last.
"""

from __future__ import annotations

import importlib.util
import json
import pathlib
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
_spec = importlib.util.spec_from_file_location(
    "holdout_adjacency", ROOT / "scripts/check-holdout-adjacency.py")
MODULE = importlib.util.module_from_spec(_spec)
assert _spec.loader is not None
_spec.loader.exec_module(MODULE)

Row = MODULE.Row


def row(name: str, module: str, *constants: str) -> "MODULE.Row":
    return Row(name, module, frozenset(constants))


def published() -> tuple[dict[str, list], dict[str, str]]:
    """A published corpus with enough families that plumbing is derivable.

    `plumbing` is DERIVED from the corpus rather than stoplisted, so a corpus
    of one family classifies that family's every constant -- `Eq` included --
    as its subject, and every candidate then comes out adjacent. The fillers
    put the shared constants over `AMBIENT_FAMILIES`, which is what the real
    42-family nursery does.
    """
    rows: dict[str, list] = {
        "pub-gcd": [row(f"Nat.gcd_x{i}", "Mathlib.Data.Nat.GCD.Lemmas",
                        "Nat.gcd", "Eq", "Shared.ambient") for i in range(10)],
        "pub-mod": [row(f"Nat.mod_x{i}", "Mathlib.Data.Nat.Modulus",
                        "Nat.instMod", "Eq", "Shared.ambient") for i in range(10)],
    }
    partition = {"pub-gcd": "development", "pub-mod": "train"}
    for i in range(MODULE.AMBIENT_FAMILIES + 1):
        fam = f"filler-{i}"
        rows[fam] = [row(f"Filler{i}.t{j}", f"Mathlib.Data.Filler{i}.Basic",
                         f"Filler{i}.op", "Eq", "Shared.ambient")
                     for j in range(10)]
        partition[fam] = "development"
    return rows, partition


def screen(rows, **kw):
    pub, part = published()
    kw.setdefault("env", ())
    return MODULE.screen_family("cand", rows, pub, part, **kw)


class TopicTests(unittest.TestCase):
    """The signal that catches the ADR-0762 draw: same module topic."""

    def test_a_shared_topic_segment_is_refused(self):
        # No constant in common at all -- only the topic `GCD`.
        rows = [row(f"Nat.other{i}", "Mathlib.Data.Nat.GCD.Basic",
                    "Nat.unrelated", "Eq") for i in range(10)]
        got = screen(rows)
        self.assertEqual(got.verdict, "refused")
        self.assertTrue(any(r.startswith("topic") for r in got.reasons),
                        got.reasons)

    def test_the_library_root_is_not_a_topic(self):
        """False-positive control. Every module starts with a library name;
        treating that as a topic makes everything adjacent to everything."""
        rows = [row(f"Nat.other{i}", "Mathlib.Data.Nat.Distance",
                    "Nat.unrelated", "Eq") for i in range(10)]
        self.assertEqual(screen(rows).verdict, "clean")


class VocabularyTests(unittest.TestCase):
    """The signal that catches `Squarefree`: shared published subject."""

    def test_rows_about_a_published_subject_are_refused(self):
        rows = [row(f"Nat.sf{i}", "Mathlib.Data.Nat.Squarefree",
                    "Nat.gcd", "Eq") for i in range(10)]
        got = screen(rows)
        self.assertEqual(got.verdict, "refused")
        self.assertTrue(any(r.startswith("vocabulary") for r in got.reasons),
                        got.reasons)

    def test_at_the_allowance_the_family_is_admitted(self):
        """False-positive control, and the reason there IS an allowance: draw 7
        deliberately permitted 2 of 10 `fermat-numbers` rows to mention
        `Nat.Prime` as shared vocabulary, and that draw is authored."""
        rows = [row(f"Nat.mix{i}", "Mathlib.Data.Nat.Squarefree",
                    *(("Nat.gcd", "Eq") if i < MODULE.VOCABULARY_MAX_ROWS
                      else ("Nat.unrelated", "Eq")))
                for i in range(10)]
        got = screen(rows)
        self.assertEqual(got.vocabulary_rows, MODULE.VOCABULARY_MAX_ROWS)
        self.assertEqual(got.verdict, "clean", got.reasons)

    def test_shared_NOTATION_is_not_shared_mathematics(self):
        """`n % m` elaborates to `Nat.instMod`, and `pub-mod` really is
        characteristic in it. Syntax is not mathematics; without that
        distinction the screen refuses every draw."""
        rows = [row(f"Nat.q{i}", "Mathlib.Data.Nat.Quotients",
                    "Nat.instMod", "Eq") for i in range(10)]
        self.assertEqual(screen(rows).verdict, "clean")

    def test_a_constant_common_to_many_families_is_not_a_subject(self):
        """`Shared.ambient` is characteristic of every published family, so it
        is plumbing and cannot make a candidate adjacent to any one of them."""
        rows = [row(f"Nat.a{i}", "Mathlib.Data.Nat.Ambient",
                    "Shared.ambient", "Eq") for i in range(10)]
        self.assertEqual(screen(rows).verdict, "clean")


class SelfScoringTests(unittest.TestCase):
    def test_a_family_scored_against_itself_is_refused_outright(self):
        pub, part = published()
        with self.assertRaises(ValueError):
            MODULE.screen_family("pub-gcd", pub["pub-gcd"], pub, part, env=())


class EnvironmentSweepTests(unittest.TestCase):
    def test_the_sweep_finds_our_declarations_and_says_so(self):
        hits = MODULE.environment_sweep({"Nat.gcd"},
                                        ["Nat.gcd", "Nat.gcd_comm", "Nat.add"])
        self.assertTrue(hits)
        self.assertEqual(hits[0][0], "gcd")

    def test_the_sweep_is_empty_for_an_absent_subject(self):
        """Paired with the positive above in the same class: an empty answer
        and a misaimed query are the same observation otherwise."""
        self.assertEqual(
            MODULE.environment_sweep({"Nat.zzzUnheardOf"}, ["Nat.gcd", "Nat.add"]),
            ())

    def test_the_sweep_is_deterministic_over_an_unordered_environment(self):
        """The caller passes a `set`; string hashing is randomised per process,
        so an unsorted sweep reported a different example declaration on every
        run and no recorded review could ever match it."""
        env = {"Nat.gcd_zz", "Nat.gcd_aa", "Nat.gcd_mm"}
        first = MODULE.environment_sweep({"Nat.gcd"}, env)
        self.assertEqual(first, MODULE.environment_sweep({"Nat.gcd"}, list(env)))
        self.assertEqual(first[0][1], "Nat.gcd_aa")


class DisclosureTests(unittest.TestCase):
    """The environment sweep is a required disclosure, not a threshold."""

    ENV = ["Nat.nthRoot", "Nat.nthRoot_zero_left", "Complex.rootOfUnity"]

    def rows(self):
        return [row(f"Nat.nthRoot{i}", "Mathlib.Analysis.Pow.NthRootLemmas",
                    "Nat.nthRoot", "Eq") for i in range(10)]

    def live(self):
        return MODULE.environment_sweep({"Nat.nthRoot"}, self.ENV)

    def test_an_unreviewed_nonempty_sweep_is_refused_at_draw_time(self):
        got = screen(self.rows(), env=self.ENV, reviews={},
                     require_disclosure=True)
        self.assertEqual(got.verdict, "refused")
        self.assertTrue(any(r.startswith("disclosure") for r in got.reasons),
                        got.reasons)

    def test_a_matching_review_admits_the_family(self):
        reviews = {"cand": {"swept": [list(h) for h in self.live()]}}
        got = screen(self.rows(), env=self.ENV, reviews=reviews,
                     require_disclosure=True)
        self.assertEqual(got.verdict, "clean", got.reasons)

    def test_a_review_that_no_longer_matches_the_environment_is_refused(self):
        reviews = {"cand": {"swept": [["gcd", "Nat.gcd", 1]]}}
        got = screen(self.rows(), env=self.ENV, reviews=reviews,
                     require_disclosure=True)
        self.assertEqual(got.verdict, "refused")
        self.assertTrue(any(r.startswith("disclosure") for r in got.reasons),
                        got.reasons)

    def test_a_stale_review_is_refused_even_where_disclosure_is_optional(self):
        """A review is a claim someone made. It is checked wherever it is
        found; only the DEMAND for one is scoped to draw time."""
        reviews = {"cand": {"swept": [["gcd", "Nat.gcd", 1]]}}
        got = screen(self.rows(), env=self.ENV, reviews=reviews,
                     require_disclosure=False)
        self.assertEqual(got.verdict, "refused")

    def test_no_review_is_demanded_of_the_standing_population(self):
        """False-positive control: every family preregistered before this
        screen existed would otherwise need a review nobody performed."""
        got = screen(self.rows(), env=self.ENV, reviews={},
                     require_disclosure=False)
        self.assertEqual(got.verdict, "clean", got.reasons)


class AcceptanceTests(unittest.TestCase):
    def test_a_recorded_acceptance_raises_the_allowance(self):
        rows = [row(f"Nat.sf{i}", "Mathlib.Data.Nat.Squarefree",
                    "Nat.gcd", "Eq") for i in range(10)]
        MODULE.ADJACENCY_ACCEPTED["cand"] = {"vocabulary_rows": 10}
        try:
            self.assertEqual(screen(rows).verdict, "clean")
        finally:
            MODULE.ADJACENCY_ACCEPTED.pop("cand", None)

    def test_an_acceptance_that_no_longer_matches_is_refused(self):
        rows = [row(f"Nat.sf{i}", "Mathlib.Data.Nat.Squarefree",
                    "Nat.gcd", "Eq") for i in range(10)]
        MODULE.ADJACENCY_ACCEPTED["cand"] = {"vocabulary_rows": 9}
        try:
            got = screen(rows)
            self.assertEqual(got.verdict, "refused")
            self.assertTrue(any(r.startswith("acceptance") for r in got.reasons),
                            got.reasons)
        finally:
            MODULE.ADJACENCY_ACCEPTED.pop("cand", None)


class FailClosedTests(unittest.TestCase):
    """The detector's own infrastructure, where a wrong answer reads as clean."""

    def test_a_manifest_that_contributes_no_rows_is_an_error(self):
        import types
        with tempfile.TemporaryDirectory() as tmp:
            tmp = pathlib.Path(tmp)
            (tmp / "v1.json").write_text(json.dumps({"entries": []}))
            (tmp / "ext.json").write_text(json.dumps(
                {"entries": [{"family": "f", "partition": "held-out",
                              "source_name": "Nat.x", "module": "M.N",
                              "constants": []}]}))
            old = (MODULE.NURSERY_V1, MODULE.EXTENSION, MODULE.FACTS)
            MODULE.NURSERY_V1 = tmp / "v1.json"
            MODULE.EXTENSION = tmp / "ext.json"
            MODULE.FACTS = tmp
            try:
                fake = types.SimpleNamespace(
                    read_inventory=lambda: {}, CONST_RE=MODULE.re.compile("(x)"))
                with self.assertRaises(SystemExit):
                    MODULE.resolve_families(fake)
            finally:
                MODULE.NURSERY_V1, MODULE.EXTENSION, MODULE.FACTS = old

    def test_an_unreadable_review_file_is_not_read_as_nothing_to_disclose(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = pathlib.Path(tmp) / "reviews.json"
            path.write_text(json.dumps({"kind": "whatever"}))
            old = MODULE.REVIEW_FILE
            MODULE.REVIEW_FILE = path
            try:
                with self.assertRaises(SystemExit):
                    MODULE.load_reviews()
            finally:
                MODULE.REVIEW_FILE = old

    def test_an_absent_review_file_means_no_reviews(self):
        """Paired control: absence is not an error, only unreadability is."""
        old = MODULE.REVIEW_FILE
        MODULE.REVIEW_FILE = pathlib.Path("/nonexistent/reviews.json")
        try:
            self.assertEqual(MODULE.load_reviews(), {})
        finally:
            MODULE.REVIEW_FILE = old


class DrawScopingTests(unittest.TestCase):
    def test_a_same_draw_development_family_counts_as_published(self):
        """A draw that publishes a subject in one partition and holds the same
        subject out in another is exactly the leak."""
        new = {
            "new-held": [row(f"Nat.h{i}", "Mathlib.Data.Nat.Widget",
                             "Nat.widget", "Eq") for i in range(10)],
            "new-dev": [row(f"Nat.d{i}", "Mathlib.Data.Nat.Widget",
                            "Nat.widget", "Eq") for i in range(10)],
        }
        pub, part = published()
        with self.assertRaises(MODULE.RefusalError):
            MODULE.assert_draw_lawful(
                new, {"new-held": "held-out", "new-dev": "development"},
                pub, part, env=(), reviews={})

    def test_a_dispatchable_family_is_not_screened(self):
        """False-positive control: R11 is about blindness. A development family
        may sit on published mathematics all it likes."""
        new = {"new-dev": [row(f"Nat.g{i}", "Mathlib.Data.Nat.GCD.Basic",
                               "Nat.gcd", "Eq") for i in range(10)]}
        pub, part = published()
        self.assertEqual(
            MODULE.assert_draw_lawful(new, {"new-dev": "development"},
                                      pub, part, env=(), reviews={}),
            [])


class GuardIntegrationTests(unittest.TestCase):
    """R11's CALL SITE in `guard()`, not just the screen it calls.

    Without these, deleting the `_adjacency_screen(...)` line from `guard()`
    leaves every test above green -- the screen would still be correct and
    still never run, which is precisely the shape ADR-0762 measured.

    These read the committed manifests, deliberately: the call site's job is to
    screen a draw against the real published corpus, and a fixture corpus would
    not exercise the join at all.
    """

    def _generator(self):
        from scripts.tests import test_gen_autogenesis_nursery_refill as G
        return G

    def test_a_topically_adjacent_new_held_out_family_is_refused(self):
        G = self._generator()
        G.Harness(self, {"a-new": "?", "b-new": "?", "c-new": "?", "d-new": "?"})
        rows = []
        for fam, part, module in (("a-new", "held-out", "Mathlib.Data.Nat.GCD.Basic"),
                                  ("b-new", "development", "Zzz.Alpha"),
                                  ("c-new", "train", "Zzz.Beta"),
                                  ("d-new", "held-out", "Zzz.Gamma")):
            e = G.entry(fam, part, f"Nat.{fam.replace('-', '_')}")
            e["module"] = module
            rows.append(e)
        with self.assertRaisesRegex(G.MODULE.RefillError, r"R11 1 new held-out"):
            G.MODULE.guard(rows, G.v1_nursery(), set(), G.validation([]))

    def test_a_screen_that_cannot_be_LOADED_refuses_the_draw(self):
        """A draw that could not run the screen has not passed it. Skipping on
        an import error would restore exactly the state ADR-0762 measured: the
        rule written down, nothing invoking it, and a green `GUARD PASSED`."""
        G = self._generator()
        old = G.MODULE.ROOT
        with tempfile.TemporaryDirectory() as tmp:
            G.MODULE.ROOT = pathlib.Path(tmp)
            try:
                with self.assertRaisesRegex(G.MODULE.RefillError,
                                            r"R11 the adjacency screen"):
                    G.MODULE._adjacency_screen(
                        [G.entry("a-new", "held-out", "Nat.x")], set())
            finally:
                G.MODULE.ROOT = old

    def test_an_unrelated_new_held_out_family_is_admitted(self):
        """False-positive control: R11 must not refuse every draw. Three
        consecutive draws have already been declined, so a screen with no
        accepting case is indistinguishable from a broken flywheel."""
        G = self._generator()
        G.Harness(self, {"a-new": "?", "b-new": "?", "c-new": "?", "d-new": "?"})
        rows = []
        for fam, part in (("a-new", "held-out"), ("b-new", "development"),
                          ("c-new", "train"), ("d-new", "held-out")):
            e = G.entry(fam, part, f"Nat.{fam.replace('-', '_')}")
            e["module"] = f"Zzz.{fam.replace('-', '_')}"
            rows.append(e)
        G.MODULE.guard(rows, G.v1_nursery(), set(), G.validation([]))


if __name__ == "__main__":
    unittest.main()
