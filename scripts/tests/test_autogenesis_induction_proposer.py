from __future__ import annotations

import importlib.util
import io
import json
import pathlib
import tempfile
import unittest
from contextlib import redirect_stdout
from unittest import mock


SCRIPT = pathlib.Path(__file__).parents[1] / "autogenesis-induction-proposer.py"
SPEC = importlib.util.spec_from_file_location("autogenesis_induction_proposer", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class InductionProposerTests(unittest.TestCase):
    def catalog(self, arity: int = 2) -> dict:
        return {
            "catalog_sha256": "catalog",
            "phase": "pre_b",
            "proof_bodies_included": False,
            "target": {"name": "E.B", "arity": arity, "canonical_type": "B"},
            "entries": [],
        }

    def run_proposer(self, catalog: dict) -> tuple[dict, str]:
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            catalog_path = root / "catalog.json"
            output = root / "output"
            output.mkdir()
            catalog_path.write_text(json.dumps(catalog))
            with mock.patch.object(
                MODULE.sys, "argv", [str(SCRIPT), str(catalog_path), str(output)]
            ):
                with redirect_stdout(io.StringIO()):
                    self.assertEqual(MODULE.main(), 0)
            return (
                json.loads((output / "induction-plans.json").read_text()),
                (output / "induction-plans.tsv").read_text(),
            )

    def test_enumeration_is_target_independent_and_deterministic(self):
        bundle, _tsv = self.run_proposer(self.catalog())
        self.assertEqual(
            [(plan["target_binder"], plan["step"]) for plan in bundle["plans"]],
            [
                (0, "exact-induction-hypothesis"),
                (0, "successor-congruence-induction-hypothesis"),
                (1, "exact-induction-hypothesis"),
                (1, "successor-congruence-induction-hypothesis"),
            ],
        )

    def test_json_and_tsv_are_bound_to_same_digest(self):
        bundle, tsv = self.run_proposer(self.catalog(1))
        unsigned = dict(bundle)
        unsigned.pop("bundle_sha256")
        self.assertEqual(bundle["bundle_sha256"], MODULE.digest(unsigned))
        self.assertEqual(tsv.splitlines()[0].split("\t")[1], bundle["bundle_sha256"])

    def test_nonpositive_or_boolean_arity_rejects(self):
        for arity in (0, -1, True):
            with self.subTest(arity=arity):
                with self.assertRaisesRegex(ValueError, "positive integer"):
                    MODULE.build_bundle(self.catalog(arity))

    def test_catalog_must_explicitly_exclude_proofs(self):
        catalog = self.catalog()
        catalog["proof_bodies_included"] = True
        with self.assertRaisesRegex(ValueError, "exclude proof bodies"):
            MODULE.build_bundle(catalog)


if __name__ == "__main__":
    unittest.main()
