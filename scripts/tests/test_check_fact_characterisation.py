"""Controls for `check-fact-characterisation.py` (ADR-1605).

Every guard below is driven to failure. Deleting any single guard from the
checker must kill exactly one test here; the mutation table is in ADR-1605 and
was run with `scripts/tests/mutation_controls.py`-style isolation (a copy of
the script under a scratch root), never in the shared worktree.

The checker's job is to make the ledger's SELF-CHARACTERISATION measurable:
how much of it says what a fact IS, rather than which declaration backs it.
Eight guards, each isolated to one assertion:

  A. `classify` returns `generated` for the generator's `[generated]` prefix.
  B. `classify` returns `transcribed` for a "Mathlib v4.30 source proposition"
     title -- the class `count-landmark-facts.py` collapses into `curated`,
     and the one where the audit's Stirling-number false absence hid.
  C. `classify` returns `curated` for anything else.
  D. `load_facts` raises on invalid JSON, naming the file.
  E. `load_facts` raises when a required field is missing, naming the field.
  F. `prose_disagreements` reports a `[generated]` title whose statement does
     not carry the generator's marker.
  G. `prose_disagreements` reports the converse -- the marker in a statement
     under a title that does not say so. This is the direction that was
     LIVE on `main`: `F-int-euler-totient-theorem.json` had a full curated
     characterisation of Euler's totient theorem under a "prose not curated"
     title, so both this checker and the landmark count scored it as
     uncharacterised prose.
  H. `run_check` is a RATCHET, not a pin: a curated count above the baseline
     passes, one below it fails and names the fragment.

Plus the end-to-end controls: a healthy fixture directory exits 0, a malformed
one exits 2, a disagreeing one exits 1 EVEN IN THE BARE REPORT MODE, and a
missing or unparseable baseline exits 1. Those are driven through `main` on a
real directory rather than against hand-built objects, because a suite that
only exercises the predicates proves the `if` statements work, not that the
script reads a ledger and can tell a broken one from a healthy one.
"""

from __future__ import annotations

import contextlib
import importlib.util
import io
import json
import pathlib
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "check_fact_characterisation", ROOT / "scripts" / "check-fact-characterisation.py"
)
assert SPEC and SPEC.loader
CFC = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CFC)

MARKER_STATEMENT = (
    "MECHANICALLY GENERATED, UNREVIEWED PROSE -- this sentence deliberately "
    "makes NO mathematical characterisation of the theorem."
)


def write_fact(directory: pathlib.Path, name: str, **fields) -> pathlib.Path:
    path = directory / f"{name}.json"
    path.write_text(json.dumps(fields), encoding="utf-8")
    return path


def generated_fact(directory: pathlib.Path, name: str, fragment: str = "Nat") -> pathlib.Path:
    return write_fact(
        directory,
        name,
        title=f"[generated] kernel theorem Nat.{name} (nat prelude, axiom-free, prose not curated)",
        statement=MARKER_STATEMENT,
        epistemic_status="proved",
        formal={"fragment": fragment},
    )


def curated_fact(directory: pathlib.Path, name: str, fragment: str = "Nat") -> pathlib.Path:
    return write_fact(
        directory,
        name,
        title=f"Wilson's theorem, in the form {name}",
        statement="A prime p divides (p-1)! + 1.",
        epistemic_status="proved",
        formal={"fragment": fragment},
    )


def transcribed_fact(directory: pathlib.Path, name: str, fragment: str = "Nat") -> pathlib.Path:
    return write_fact(
        directory,
        name,
        title=f"Mathlib v4.30 source proposition Nat.{name}",
        statement="Transcribed from Mathlib v4.30.",
        epistemic_status="proved",
        formal={"fragment": fragment},
    )


class ClassifyTests(unittest.TestCase):
    def test_generated_prefix_is_generated(self) -> None:
        """Guard A."""
        fact = {"title": "[generated] kernel theorem Rat.abs_nonneg (rat prelude)"}
        self.assertEqual(CFC.classify(fact), "generated")

    def test_mathlib_transcription_is_its_own_class(self) -> None:
        """Guard B -- NOT `curated`, which is what the landmark rule calls it."""
        fact = {"title": "Mathlib v4.30 source proposition Nat.stirlingFirst_self"}
        self.assertEqual(CFC.classify(fact), "transcribed")

    def test_written_prose_is_curated(self) -> None:
        """Guard C."""
        fact = {"title": "Uniqueness of prime factorization, as multiplicity agreement"}
        self.assertEqual(CFC.classify(fact), "curated")


class LoadFactsTests(unittest.TestCase):
    def test_invalid_json_raises_and_names_the_file(self) -> None:
        """Guard D."""
        with tempfile.TemporaryDirectory() as tmp:
            d = pathlib.Path(tmp)
            curated_fact(d, "good")
            (d / "broken.json").write_text("{not json", encoding="utf-8")
            with self.assertRaises(CFC.LedgerMalformed) as caught:
                CFC.load_facts(d)
            self.assertEqual(caught.exception.path.name, "broken.json")

    def test_missing_required_field_raises_and_names_it(self) -> None:
        """Guard E."""
        with tempfile.TemporaryDirectory() as tmp:
            d = pathlib.Path(tmp)
            write_fact(d, "headless", statement="s", epistemic_status="proved")
            with self.assertRaises(CFC.LedgerMalformed) as caught:
                CFC.load_facts(d)
            self.assertIn("title", caught.exception.reason)


class ProseDisagreementTests(unittest.TestCase):
    def test_generated_title_without_the_marker_is_reported(self) -> None:
        """Guard F."""
        facts = [
            (
                pathlib.Path("F-x.json"),
                {
                    "title": "[generated] kernel theorem Nat.x (nat prelude)",
                    "statement": "A real characterisation somebody wrote by hand.",
                    "epistemic_status": "proved",
                },
            )
        ]
        found = CFC.prose_disagreements(facts)
        self.assertEqual(len(found), 1)
        self.assertIn("F-x.json", found[0])

    def test_marker_under_a_curated_title_is_reported(self) -> None:
        """Guard G -- the direction that was live on `main`."""
        facts = [
            (
                pathlib.Path("F-y.json"),
                {
                    "title": "Euler's totient theorem over the constructed integers",
                    "statement": MARKER_STATEMENT,
                    "epistemic_status": "proved",
                },
            )
        ]
        found = CFC.prose_disagreements(facts)
        self.assertEqual(len(found), 1)
        self.assertIn("F-y.json", found[0])

    def test_agreeing_prose_is_not_reported(self) -> None:
        """The negative control: without it, a guard that reports EVERY fact passes."""
        with tempfile.TemporaryDirectory() as tmp:
            d = pathlib.Path(tmp)
            generated_fact(d, "g")
            curated_fact(d, "c")
            transcribed_fact(d, "t")
            self.assertEqual(CFC.prose_disagreements(CFC.load_facts(d)), [])


class RatchetTests(unittest.TestCase):
    """Guard H: a ratchet, not a pin."""

    def _measure(self, curated: int, fragment: str = "Nat") -> dict:
        with tempfile.TemporaryDirectory() as tmp:
            d = pathlib.Path(tmp)
            for i in range(curated):
                curated_fact(d, f"c{i}", fragment)
            generated_fact(d, "g", fragment)
            return CFC.measure(CFC.load_facts(d))

    def _baseline(self, tmp: pathlib.Path, floors: dict, total: int) -> pathlib.Path:
        p = tmp / "baseline.json"
        p.write_text(
            json.dumps({"curated_proved_by_fragment": floors, "curated_proved_total": total}),
            encoding="utf-8",
        )
        return p

    def test_more_curated_than_the_baseline_passes(self) -> None:
        m = self._measure(5)
        with tempfile.TemporaryDirectory() as tmp:
            base = self._baseline(pathlib.Path(tmp), {"Nat": 3}, 3)
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(CFC.run_check(m, base), 0)

    def test_fewer_curated_than_the_baseline_fails_and_names_the_fragment(self) -> None:
        m = self._measure(2)
        with tempfile.TemporaryDirectory() as tmp:
            base = self._baseline(pathlib.Path(tmp), {"Nat": 7}, 7)
            err = io.StringIO()
            with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(err):
                self.assertEqual(CFC.run_check(m, base), 1)
            self.assertIn("CHARACTERISATION_REGRESSION", err.getvalue())
            self.assertIn("Nat", err.getvalue())

    def test_missing_baseline_fails(self) -> None:
        m = self._measure(1)
        with tempfile.TemporaryDirectory() as tmp:
            missing = pathlib.Path(tmp) / "absent.json"
            with contextlib.redirect_stderr(io.StringIO()) as err:
                self.assertEqual(CFC.run_check(m, missing), 1)
            self.assertIn("BASELINE_MISSING", err.getvalue())

    def test_unparseable_baseline_fails(self) -> None:
        m = self._measure(1)
        with tempfile.TemporaryDirectory() as tmp:
            bad = pathlib.Path(tmp) / "bad.json"
            bad.write_text("{nope", encoding="utf-8")
            with contextlib.redirect_stderr(io.StringIO()) as err:
                self.assertEqual(CFC.run_check(m, bad), 1)
            self.assertIn("BASELINE_UNPARSEABLE", err.getvalue())


class EndToEndTests(unittest.TestCase):
    """Driven through `main` on a real directory, not against hand-built objects."""

    def test_healthy_ledger_reports_and_exits_zero(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            d = pathlib.Path(tmp)
            curated_fact(d, "c")
            generated_fact(d, "g")
            transcribed_fact(d, "t")
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                rc = CFC.main(["--facts-dir", str(d)])
            self.assertEqual(rc, 0)
            self.assertIn("curated=1", out.getvalue())
            self.assertIn("transcribed=1", out.getvalue())

    def test_malformed_ledger_exits_two_not_one(self) -> None:
        """The two failure kinds must never be confused."""
        with tempfile.TemporaryDirectory() as tmp:
            d = pathlib.Path(tmp)
            curated_fact(d, "c")
            (d / "broken.json").write_text("{", encoding="utf-8")
            with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(
                io.StringIO()
            ) as err:
                rc = CFC.main(["--facts-dir", str(d)])
            self.assertEqual(rc, 2)
            self.assertIn("MALFORMED", err.getvalue())

    def test_prose_disagreement_fails_the_BARE_REPORT_too(self) -> None:
        """A report mode in which nothing can fail is not a measurement."""
        with tempfile.TemporaryDirectory() as tmp:
            d = pathlib.Path(tmp)
            write_fact(
                d,
                "mismatched",
                title="[generated] kernel theorem Nat.q (nat prelude)",
                statement="Hand-written characterisation, no marker.",
                epistemic_status="proved",
                formal={"fragment": "Nat"},
            )
            with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(
                io.StringIO()
            ) as err:
                rc = CFC.main(["--facts-dir", str(d)])
            self.assertEqual(rc, 1)
            self.assertIn("PROSE_DISAGREEMENT", err.getvalue())


class ShippedLedgerTests(unittest.TestCase):
    """The guards are run against the ledger this repository actually ships.

    A control suite that only ever sees fixtures measures the fixtures. This
    one derives its subject from the authority -- `artifacts/facts/` -- so it
    fails when the real ledger regresses, which is the only failure anybody
    cares about.
    """

    def test_shipped_ledger_passes_every_guard(self) -> None:
        facts_dir = ROOT / "artifacts" / "facts"
        facts = CFC.load_facts(facts_dir)
        self.assertGreater(len(facts), 2000, "the ledger read as suspiciously small")
        self.assertEqual(CFC.prose_disagreements(facts), [])

    def test_shipped_ledger_meets_its_own_baseline(self) -> None:
        facts = CFC.load_facts(ROOT / "artifacts" / "facts")
        m = CFC.measure(facts)
        with contextlib.redirect_stdout(io.StringIO()):
            rc = CFC.run_check(m, ROOT / CFC.DEFAULT_BASELINE)
        self.assertEqual(rc, 0)


if __name__ == "__main__":
    unittest.main()
