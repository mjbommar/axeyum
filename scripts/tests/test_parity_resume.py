from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from scripts.parity_resume import ResumeError, canonical_resume_rows


class ParityResumeTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.population = self.root / "list.txt"
        self.sidecar = self.root / "detail.tsv"

    def tearDown(self) -> None:
        self.temp.cleanup()

    def write(self, population: str, sidecar: str) -> None:
        self.population.write_text(population)
        self.sidecar.write_text(sidecar)

    def test_exact_paths_distinguish_duplicate_basenames(self) -> None:
        self.write(
            "corpus/a/same.smt2\ncorpus/b/same.smt2\n",
            "file\taxeyum\treference\tdeclared\n"
            "corpus/a/same.smt2\tsat\tsat\tsat\n"
            "corpus/b/same.smt2\tunsat\tunsat\tunsat\n",
        )
        self.assertEqual(
            canonical_resume_rows(self.population, self.sidecar),
            [
                ("corpus/a/same.smt2", "sat", "sat", "sat"),
                ("corpus/b/same.smt2", "unsat", "unsat", "unsat"),
            ],
        )

    def test_unambiguous_legacy_basename_is_canonicalized(self) -> None:
        self.write(
            "corpus/a/one.smt2\ncorpus/b/two.smt2\n",
            "file\taxeyum\treference\tdeclared\none.smt2\tsat\tsat\tsat\n",
        )
        self.assertEqual(
            canonical_resume_rows(self.population, self.sidecar),
            [("corpus/a/one.smt2", "sat", "sat", "sat")],
        )

    def test_ambiguous_legacy_basename_fails_closed(self) -> None:
        self.write(
            "corpus/a/same.smt2\ncorpus/b/same.smt2\n",
            "file\taxeyum\treference\tdeclared\nsame.smt2\tsat\tsat\tsat\n",
        )
        with self.assertRaisesRegex(ResumeError, "legacy basename is ambiguous"):
            canonical_resume_rows(self.population, self.sidecar)

    def test_unknown_and_duplicate_rows_fail_closed(self) -> None:
        self.write(
            "corpus/a/one.smt2\n",
            "file\taxeyum\treference\tdeclared\nmissing.smt2\tsat\tsat\tsat\n",
        )
        with self.assertRaisesRegex(ResumeError, "outside the committed population"):
            canonical_resume_rows(self.population, self.sidecar)
        self.write(
            "corpus/a/one.smt2\n",
            "file\taxeyum\treference\tdeclared\n"
            "corpus/a/one.smt2\tsat\tsat\tsat\n"
            "one.smt2\tsat\tsat\tsat\n",
        )
        with self.assertRaisesRegex(ResumeError, "duplicate sidecar identity"):
            canonical_resume_rows(self.population, self.sidecar)


if __name__ == "__main__":
    unittest.main()
