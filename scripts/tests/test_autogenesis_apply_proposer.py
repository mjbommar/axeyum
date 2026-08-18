from __future__ import annotations

import importlib.util
import io
import json
import pathlib
import tempfile
import unittest
from contextlib import redirect_stdout
from unittest import mock


SCRIPT = pathlib.Path(__file__).parents[1] / "autogenesis-apply-proposer.py"
SPEC = importlib.util.spec_from_file_location("autogenesis_apply_proposer", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class ApplyProposerTests(unittest.TestCase):
    def catalog(self) -> dict:
        return {
            "catalog_sha256": "catalog",
            "phase": "post_b",
            "proof_bodies_included": False,
            "target": {"name": "E.A", "arity": 1, "canonical_type": "A"},
            "entries": [
                {"name": "Nat.Z", "arity": 1, "origin": "retained-visible"},
                {"name": "Nat.Nullary", "arity": 0, "origin": "retained-visible"},
                {"name": "E.B", "arity": 1, "origin": "accepted-episode"},
                {"name": "Nat.A", "arity": 1, "origin": "retained-visible"},
            ],
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
                json.loads((output / "apply-plans.json").read_text()),
                (output / "apply-plans.tsv").read_text(),
            )

    def test_episode_knowledge_is_first_and_wrong_arities_are_absent(self):
        bundle, _tsv = self.run_proposer(self.catalog())
        self.assertEqual(
            [plan["theorem"] for plan in bundle["plans"]], ["E.B", "Nat.A", "Nat.Z"]
        )
        self.assertEqual(bundle["plans"][0]["arguments"], [{"target_binder": 0}])

    def test_json_and_tsv_are_bound_to_same_digest(self):
        bundle, tsv = self.run_proposer(self.catalog())
        unsigned = dict(bundle)
        unsigned.pop("bundle_sha256")
        self.assertEqual(bundle["bundle_sha256"], MODULE.digest(unsigned))
        self.assertEqual(tsv.splitlines()[0].split("\t")[1], bundle["bundle_sha256"])

    def test_catalog_must_explicitly_exclude_proofs(self):
        catalog = self.catalog()
        catalog["proof_bodies_included"] = True
        with self.assertRaisesRegex(ValueError, "exclude proof bodies"):
            self.run_proposer(catalog)


if __name__ == "__main__":
    unittest.main()
