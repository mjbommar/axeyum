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


PROPOSER = load("induction_proposer_for_verifier_test", "autogenesis-induction-proposer.py")
VERIFIER = load(
    "verify_induction_proposals", "verify-autogenesis-induction-proposals.py"
)


class VerifyInductionProposalTests(unittest.TestCase):
    def catalog(self):
        return {
            "catalog_sha256": "catalog",
            "phase": "pre_b",
            "proof_bodies_included": False,
            "target": {"name": "E.B", "arity": 1, "canonical_type": "B"},
            "entries": [],
        }

    def test_exact_json_and_tsv_verify(self):
        catalog = self.catalog()
        bundle = PROPOSER.build_bundle(catalog)
        VERIFIER.verify(catalog, bundle, PROPOSER.render_tsv(bundle))

    def test_rehashed_unenumerated_plan_rejects(self):
        catalog = self.catalog()
        bundle = PROPOSER.build_bundle(catalog)
        bundle["plans"][0]["step"] = "unregistered-step"
        unsigned = dict(bundle)
        unsigned.pop("bundle_sha256")
        bundle["bundle_sha256"] = PROPOSER.digest(unsigned)
        with self.assertRaisesRegex(VERIFIER.ProposalError, "not derived"):
            VERIFIER.verify(catalog, bundle, PROPOSER.render_tsv(bundle))

    def test_tsv_mutation_rejects(self):
        catalog = self.catalog()
        bundle = PROPOSER.build_bundle(catalog)
        with self.assertRaisesRegex(VERIFIER.ProposalError, "TSV"):
            VERIFIER.verify(catalog, bundle, PROPOSER.render_tsv(bundle) + "3\t0\tx\ty\n")


if __name__ == "__main__":
    unittest.main()
