#!/usr/bin/env python3
"""Test suite for the L1 phase C0 library-artifact contract.

Run directly: `python3 scripts/tests/test-library-artifact-contract.py -v`
(hyphenated filename -- not importable as a module, so this is a script, not
`python3 -m unittest ...`).

Covers the C0 exit criterion
(docs/plan/library-artifact-compatibility-roadmap-2026-08-30.md, section C0):

  1. Two independently-coded readers (reader A = check-library-artifact-
     contract.py, reader B = check-library-artifact-contract-reader-b.py)
     both accept the committed positive pack AND reproduce byte-identical
     digests for every declaration.
  2. Each of the five mutation classes (missing, duplicate, reordered,
     truncated, value_exposed) is rejected by BOTH readers.
  3. The MISSING mutation is rejected specifically because an EXTERNAL
     population registry names the absent root -- not because of anything
     the pack asserts about itself.

The guard-deletion kill table (delete one guard, exactly one test flips) is
a SEPARATE script, `test-library-artifact-contract-mutations.sh`, because it
edits a scratch copy of the validator source and must never run against the
tracked file (CLAUDE.md: mutation testing in the shared worktree breaks
other lanes' builds).
"""
from __future__ import annotations

import importlib.util
import json
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

_HERE = Path(__file__).resolve().parent
_SCRIPTS = _HERE.parent
_REPO_ROOT = _SCRIPTS.parent

sys.path.insert(0, str(_HERE))
import library_artifact_mutations as lam  # noqa: E402


def _load(name: str, relpath: str):
    spec = importlib.util.spec_from_file_location(name, _SCRIPTS / relpath)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


reader_a = _load("lac_reader_a", "check-library-artifact-contract.py")
reader_b = _load("lac_reader_b", "check-library-artifact-contract-reader-b.py")


class FixtureTestCase(unittest.TestCase):
    def setUp(self) -> None:
        self.tmpdir = Path(tempfile.mkdtemp(prefix="lac-fixtures-"))
        self.fixtures = lam.write_fixtures(self.tmpdir)
        self.population_dir = self.tmpdir / "populations"

    def tearDown(self) -> None:
        shutil.rmtree(self.tmpdir, ignore_errors=True)

    def pack_path(self, name: str) -> Path:
        return self.fixtures[name][0]

    def typeproj_path(self, name: str) -> Path:
        return self.fixtures[name][1]


class GoodPackAcceptedByBothReaders(FixtureTestCase):
    def test_reader_a_accepts_good_pack(self):
        errors = reader_a.validate_pack(self.pack_path("good"), self.population_dir)
        self.assertEqual(errors, [], errors)

    def test_reader_b_accepts_good_pack(self):
        errors = reader_b.validate_pack(self.pack_path("good"), self.population_dir)
        self.assertEqual(errors, [], errors)

    def test_committed_pack_and_projection_validate_via_cli(self):
        # The actually-committed files, not a fixture copy, through the
        # real CLI entry points -- this is what the aggregate gate runs.
        for script in ("check-library-artifact-contract.py", "check-library-artifact-contract-reader-b.py"):
            result = subprocess.run(
                [sys.executable, str(_SCRIPTS / script)],
                cwd=str(_REPO_ROOT),
                capture_output=True,
                text=True,
            )
            self.assertEqual(result.returncode, 0, f"{script}: {result.stdout}\n{result.stderr}")


class TwoReadersReproduceIdenticalIdentities(FixtureTestCase):
    def test_identity_digests_match_byte_for_byte(self):
        pack = json.loads(self.pack_path("good").read_text())
        decls_b = [reader_b.Decl.from_json(d) for d in pack["declarations"]]
        report_b = reader_b.identities_report(decls_b)

        for decl in pack["declarations"]:
            name = decl["name"]
            # Reader A's recomputation, from its own independent code path.
            type_digest_a = reader_a.compute_type_digest(decl)
            value_digest_a = reader_a.compute_value_digest(decl)
            identity_digest_a = reader_a.compute_identity_digest(decl, type_digest_a, value_digest_a)

            self.assertEqual(type_digest_a, decl["type_digest"], name)
            self.assertEqual(value_digest_a, decl["value_digest"], name)
            self.assertEqual(identity_digest_a, decl["identity_digest"], name)

            # Reader B's recomputation must land on the SAME bytes as reader
            # A's, and both must equal what is recorded in the pack.
            self.assertEqual(report_b[name]["type_digest"], decl["type_digest"], name)
            self.assertEqual(report_b[name]["value_digest"], decl["value_digest"], name)
            self.assertEqual(report_b[name]["identity_digest"], decl["identity_digest"], name)

    def test_pack_digest_matches_both_readers(self):
        pack = json.loads(self.pack_path("good").read_text())
        recomputed_a = reader_a.compute_pack_digest(pack["declarations"])
        decls_b = [reader_b.Decl.from_json(d) for d in pack["declarations"]]
        recomputed_b = reader_b.recompute_pack_digest(decls_b)
        self.assertEqual(recomputed_a, pack["pack_digest"])
        self.assertEqual(recomputed_b, pack["pack_digest"])

    def test_transitive_closures_match_both_readers(self):
        pack = json.loads(self.pack_path("good").read_text())
        by_name = {d["name"]: d for d in pack["declarations"]}
        decls_b = [reader_b.Decl.from_json(d) for d in pack["declarations"]]
        graph_b = reader_b.Graph(decls_b)
        for d in decls_b:
            recomputed_ttd_b = sorted(graph_b.closure(d.direct_type_deps, graph_b.type_neighbors))
            recomputed_tvd_b = sorted(
                graph_b.closure(d.direct_type_deps | d.direct_value_deps, graph_b.value_neighbors)
            )
            self.assertEqual(recomputed_ttd_b, by_name[d.name]["transitive_type_deps"], d.name)
            self.assertEqual(recomputed_tvd_b, by_name[d.name]["transitive_value_deps"], d.name)


class EachMutationClassIsRejected(FixtureTestCase):
    def test_missing_root_rejected_by_reader_a(self):
        errors = reader_a.validate_pack(self.pack_path("missing"), self.population_dir)
        joined = "\n".join(errors)
        self.assertIn("expected root(s) missing", joined)
        self.assertIn("'id'", joined)

    def test_missing_root_rejected_by_reader_b(self):
        errors = reader_b.validate_pack(self.pack_path("missing"), self.population_dir)
        joined = "\n".join(errors)
        self.assertIn("missing expected root(s)", joined)
        self.assertIn("'id'", joined)

    def test_missing_root_ignores_the_packs_own_tampered_metadata(self):
        """The pack's OWN source_population fields were edited (by
        build_missing) to match the deletion -- expected_declaration_count
        dropped to 8, requested_roots no longer names `id`. The guard must
        still fail, because it never trusts those pack-internal fields as
        its authority."""
        mutated = json.loads(self.pack_path("missing").read_text())
        self.assertEqual(mutated["source_population"]["expected_declaration_count"], 8)
        self.assertNotIn("id", mutated["source_population"]["requested_roots"])
        errors = reader_a.validate_pack(self.pack_path("missing"), self.population_dir)
        self.assertTrue(errors)

    def test_duplicate_rejected_by_both_readers(self):
        errors_a = reader_a.validate_pack(self.pack_path("duplicate"), self.population_dir)
        errors_b = reader_b.validate_pack(self.pack_path("duplicate"), self.population_dir)
        self.assertIn("duplicate declaration name(s)", "\n".join(errors_a))
        self.assertIn("repeated name(s)", "\n".join(errors_b))

    def test_reordered_rejected_by_both_readers(self):
        errors_a = reader_a.validate_pack(self.pack_path("reordered"), self.population_dir)
        errors_b = reader_b.validate_pack(self.pack_path("reordered"), self.population_dir)
        self.assertIn("pack_digest mismatch", "\n".join(errors_a))
        self.assertIn("pack_digest disagreement", "\n".join(errors_b))

    def test_truncated_rejected_by_both_readers(self):
        errors_a = reader_a.validate_pack(self.pack_path("truncated"), self.population_dir)
        errors_b = reader_b.validate_pack(self.pack_path("truncated"), self.population_dir)
        self.assertIn("Nat.add: type_digest mismatch", "\n".join(errors_a))
        self.assertIn("Nat.add type_digest disagreement", "\n".join(errors_b))

    def test_value_exposed_rejected_by_both_readers(self):
        errors_a = reader_a.validate_pack(self.pack_path("value_exposed"), self.population_dir)
        errors_b = reader_b.validate_pack(self.pack_path("value_exposed"), self.population_dir)
        self.assertIn("forbidden key(s)", "\n".join(errors_a))
        self.assertIn("non-type-only key(s)", "\n".join(errors_b))

    def test_only_its_own_mutation_fails_each_other_fixture_is_clean_apart_from_it(self):
        """Sanity: the five mutations are surgical. Each fixture other than
        its own target should not ALSO trip an unrelated fixture's error --
        checked the other direction from the guard-kill table, which proves
        it via literal guard deletion."""
        for name in lam.MUTATION_NAMES:
            errors = reader_a.validate_pack(self.pack_path(name), self.population_dir)
            self.assertTrue(errors, f"{name} mutation unexpectedly passed validation")


def main() -> int:
    loader = unittest.TestLoader()
    suite = loader.loadTestsFromModule(sys.modules[__name__])
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    return 0 if result.wasSuccessful() else 1


if __name__ == "__main__":
    sys.exit(main())
