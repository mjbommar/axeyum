from __future__ import annotations

import importlib.util
import pathlib
import unittest


def load(name: str, filename: str):
    path = pathlib.Path(__file__).parents[1] / filename
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


PROPOSER = load("apply_proposer_for_verifier_test", "autogenesis-apply-proposer.py")
VERIFIER = load("verify_apply_proposals", "verify-autogenesis-apply-proposals.py")


class VerifyProposalTests(unittest.TestCase):
    def catalog(self):
        return {
            "catalog_sha256": "catalog",
            "phase": "post_b",
            "proof_bodies_included": False,
            "denied_theorems": ["Nat.secret"],
            "target": {"name": "E.A", "arity": 1, "canonical_type": "A"},
            "entries": [
                {"name": "E.B", "arity": 1, "origin": "accepted-episode"},
                {"name": "Nat.C", "arity": 1, "origin": "retained-visible"},
            ],
        }

    def test_exact_json_and_tsv_verify(self):
        catalog = self.catalog()
        bundle = PROPOSER.build_bundle(catalog)
        VERIFIER.verify(catalog, bundle, PROPOSER.render_tsv(bundle))

    def test_rehashed_plan_not_derived_from_catalog_rejects(self):
        catalog = self.catalog()
        bundle = PROPOSER.build_bundle(catalog)
        bundle["plans"][0]["theorem"] = "Nat.secret"
        unsigned = dict(bundle)
        unsigned.pop("bundle_sha256")
        bundle["bundle_sha256"] = PROPOSER.digest(unsigned)
        with self.assertRaisesRegex(VERIFIER.ProposalError, "not derived"):
            VERIFIER.verify(catalog, bundle, PROPOSER.render_tsv(bundle))

    def test_tsv_mutation_rejects(self):
        catalog = self.catalog()
        bundle = PROPOSER.build_bundle(catalog)
        with self.assertRaisesRegex(VERIFIER.ProposalError, "TSV"):
            VERIFIER.verify(catalog, bundle, PROPOSER.render_tsv(bundle) + "1\tNat.C\t1\n")


if __name__ == "__main__":
    unittest.main()
