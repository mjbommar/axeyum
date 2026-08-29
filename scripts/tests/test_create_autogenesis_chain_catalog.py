from __future__ import annotations

import copy
import importlib.util
import pathlib
import json
import tempfile
import unittest


SCRIPT = pathlib.Path(__file__).parents[1] / "create-autogenesis-chain-catalog.py"
SPEC = importlib.util.spec_from_file_location("autogenesis_chain_catalog", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def fact(fact_id: str, theorem: str, dependencies: list[str]) -> dict:
    return {
        "id": fact_id,
        "epistemic_status": "proved",
        "proof_route": "kernel-lean",
        "axiom_footprint": [],
        "depends_on": dependencies,
        "evidence": [{"theorem": theorem}],
    }


def theorem_of(value):
    return value["evidence"][0]["theorem"]


class ChainCatalogTests(unittest.TestCase):
    def inputs(self):
        facts = {
            "F:B": fact("F:B", "Nat.b", []),
            "F:A": fact("F:A", "Nat.a", ["F:B", "F:C"]),
            "F:C": fact("F:C", "Nat.c", []),
            "F:authored-only": fact("F:authored-only", "Nat.authored", ["F:B"]),
        }
        graph = {
            "Nat.b": [],
            "Nat.a": ["Nat.b"],
            "Nat.c": [],
            "Nat.authored": [],
        }
        return facts, graph

    def test_only_direct_kernel_dependency_becomes_a_candidate(self):
        facts, graph = self.inputs()
        catalog = MODULE.build_catalog(facts, graph, theorem_of)
        self.assertEqual(catalog["coverage"]["proof_derived_edges"], 1)
        candidate = catalog["candidates"][0]
        self.assertEqual(candidate["premise"]["fact_id"], "F:B")
        self.assertEqual(candidate["consequent"]["fact_id"], "F:A")
        self.assertEqual(candidate["consequent"]["other_dependencies"], ["F:C"])
        self.assertEqual(catalog["selection"]["selected_chain_id"], None)

    def test_missing_declared_edge_fails_closed(self):
        facts, graph = self.inputs()
        facts["F:A"]["depends_on"] = ["F:C"]
        with self.assertRaisesRegex(MODULE.ChainCatalogError, "absent"):
            MODULE.build_catalog(facts, graph, theorem_of)

    def test_catalog_is_deterministic_and_content_addressed(self):
        facts, graph = self.inputs()
        first = MODULE.build_catalog(facts, graph, theorem_of)
        second = MODULE.build_catalog(copy.deepcopy(facts), copy.deepcopy(graph), theorem_of)
        self.assertEqual(first, second)
        MODULE.verify_catalog(first, second)
        mutated = copy.deepcopy(first)
        mutated["candidates"][0]["axiom_free"] = False
        mutated["catalog_sha256"] = MODULE.digest(
            {key: value for key, value in mutated.items() if key != "catalog_sha256"}
        )
        with self.assertRaisesRegex(MODULE.ChainCatalogError, "stale"):
            MODULE.verify_catalog(mutated, second)

    def test_duplicate_theorem_mapping_resolves_deterministically(self):
        # ADR-0603 mirror facts are deliberately flipped onto an EXISTING
        # kernel declaration (measured 2026-08-29: Int.modEq_add_left,
        # Nat.coprime_of_lt_prime, Nat.descFactorial_of_lt all landed as two
        # facts naming one theorem -- see
        # docs/plan/status/284-autogenesis-gate-rot.md). This must resolve,
        # not raise: the old "reject on any duplicate" behaviour could not
        # tell that pattern apart from a genuine authorship bug and was red
        # for exactly that reason.
        facts, graph = self.inputs()
        facts["F:duplicate"] = fact("F:duplicate", "Nat.b", [])
        by_theorem, unnamed = MODULE.theorem_index(facts, theorem_of)
        self.assertEqual(unnamed, [])
        # Deterministic: among two equally-unpinned claimants, the first by
        # sorted fact id wins ("F:B" < "F:duplicate").
        self.assertEqual(by_theorem["Nat.b"], "F:B")
        # And the whole catalog still builds rather than raising.
        MODULE.build_catalog(facts, graph, theorem_of)

    def test_pinned_kernel_theorem_wins_over_regex_fallback(self):
        # A fact whose formal.kernel_theorem is explicitly pinned is a
        # deliberate assertion; one resolved only through theorem_of's
        # regex fallback is a guess. The pin must win regardless of sort
        # order.
        facts, graph = self.inputs()
        pinned = fact("F:z-pinned-duplicate", "Nat.b", [])
        pinned["formal"] = {"kernel_theorem": "Nat.b"}
        facts["F:z-pinned-duplicate"] = pinned
        by_theorem, _ = MODULE.theorem_index(facts, theorem_of)
        self.assertEqual(by_theorem["Nat.b"], "F:z-pinned-duplicate")

    def test_two_pinned_claimants_break_ties_by_fact_id(self):
        facts, graph = self.inputs()
        for extra_id in ("F:z-pinned-two", "F:a-pinned-one"):
            row = fact(extra_id, "Nat.b", [])
            row["formal"] = {"kernel_theorem": "Nat.b"}
            facts[extra_id] = row
        by_theorem, _ = MODULE.theorem_index(facts, theorem_of)
        # "F:B" (unpinned) loses to either pinned claimant; between the two
        # pinned claimants, "F:a-pinned-one" sorts first.
        self.assertEqual(by_theorem["Nat.b"], "F:a-pinned-one")

    def test_named_fact_outside_inventory_is_reported_not_inferred(self):
        facts, graph = self.inputs()
        graph.pop("Nat.authored")
        catalog = MODULE.build_catalog(facts, graph, theorem_of)
        self.assertEqual(
            catalog["coverage"]["missing_inventory_fact_ids"], ["F:authored-only"]
        )
        self.assertNotIn(
            "F:authored-only",
            [row["consequent"]["fact_id"] for row in catalog["candidates"]],
        )

    def qualification_files(self, root: pathlib.Path):
        snapshot = {
            "chain": {
                "premise": {"fact_id": "F:B", "retained_theorem": "Nat.b"},
                "consequent": {"fact_id": "F:A", "retained_theorem": "Nat.a"},
                "derived_direct_edge": "Nat.b -> Nat.a",
            },
            "controls": {
                "same_search_policy_and_budget_pre_and_post_b": True,
                "pre_b_requires_no_credit": True,
                "post_b_requires_new_premise_dependency": True,
                "retained_fact_evidence_never_becomes_visible": True,
                "proposer_must_not_receive_retained_proof_bodies": True,
            },
            "phases": {
                "post_b": {
                    "accepted_episode_facts": [
                        {"declaration": "Autogenesis.E.premise"}
                    ]
                }
            },
        }
        snapshot["snapshot_sha256"] = MODULE.digest(snapshot)
        readiness = {
            "newly_ready": ["F:A"],
            "cause": {
                "admitted_fact_id": "F:B",
                "derived_dependency_edge": "F:B -> F:A",
            },
            "target": {
                "fact_id": "F:A",
                "before": {"missing_dependencies": ["F:B"]},
                "after": {"eligible": True},
            },
            "authoritative_ledger_writes": 0,
            "fixture_writes": 1,
        }
        readiness["readiness_delta_sha256"] = MODULE.digest(readiness)
        evidence = {
            "identity": {"fact_id": "F:B"},
            "result": {"outcome": "proved"},
            "acceptance": {
                "independent_kernel_checked": True,
                "axiom_footprint": [],
                "retained_answer_dependencies": [],
            },
        }
        evidence["evidence_sha256"] = MODULE.digest(evidence)
        transaction = {"precondition": {"source_is_authoritative": False}}
        transaction["transaction_sha256"] = MODULE.digest(transaction)
        pre_catalog = {
            "target": {"source_fact_id": "F:A", "name": "Autogenesis.E.A"}
        }
        pre_catalog["catalog_sha256"] = MODULE.digest(pre_catalog)
        post_catalog = {
            "target": {"source_fact_id": "F:A", "name": "Autogenesis.E.A"}
        }
        post_catalog["catalog_sha256"] = MODULE.digest(post_catalog)
        post_bundle = {
            "plans": [
                {
                    "theorem": "Autogenesis.E.premise",
                    "catalog_origin": "accepted-episode",
                }
            ]
        }
        post_bundle["bundle_sha256"] = MODULE.digest(post_bundle)
        report = {
            "schema_version": 8,
            "kind": "axeyum-autogenesis-apply-experiment",
            "git_commit": "a" * 40,
            "snapshot_sha256": snapshot["snapshot_sha256"],
            "premise_fact_id": "F:B",
            "target_fact_id": "F:A",
            "same_target": True,
            "controls": {
                "denied_retained_answers": ["Nat.a", "Nat.b"],
                "proposer_isolated": True,
                "expected_outcome_mismatch_rejected": True,
                "after_fact_fault_recovered": True,
            },
            "premise": {
                "evidence_sha256": evidence["evidence_sha256"],
                "readiness_delta_sha256": readiness["readiness_delta_sha256"],
                "fact_transaction_sha256": transaction["transaction_sha256"],
                "result": "AUTOGENESIS_INDUCTION_RESULT|phase=pre_b|attempted=2|budget=2|outcome=proved|plan_rank=2",
            },
            "pre_a": {
                "catalog_sha256": pre_catalog["catalog_sha256"],
                "result": "AUTOGENESIS_APPLY_RESULT|phase=pre_a|attempted=3|budget=3|outcome=no-proof|theorem=-"
            },
            "post_b": {
                "catalog_sha256": post_catalog["catalog_sha256"],
                "bundle_sha256": post_bundle["bundle_sha256"],
                "result": "AUTOGENESIS_APPLY_RESULT|phase=post_b|attempted=1|budget=3|outcome=proved|theorem=Autogenesis.E.premise"
            },
        }
        report["experiment_sha256"] = MODULE.digest(report)
        values = {
            "snapshot.json": snapshot,
            "readiness-delta.json": readiness,
            "premise-evidence.json": evidence,
            "fact-transaction-proposal.json": transaction,
            "pre_a-catalog.json": pre_catalog,
            "post_b-catalog.json": post_catalog,
            "post_b-output/apply-plans.json": post_bundle,
            "experiment.json": report,
        }
        for relative, value in values.items():
            path = root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(json.dumps(value))

    def test_counterfactual_qualification_selects_but_grants_no_write_authority(self):
        facts, graph = self.inputs()
        structural = MODULE.build_catalog(facts, graph, theorem_of)
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            self.qualification_files(root)
            qualified = MODULE.apply_counterfactual_qualification(structural, root)
            self.assertEqual(
                qualified["selection"]["outcome"],
                "selected-qualified-counterfactual-chain",
            )
            self.assertFalse(qualified["selection"]["authoritative_write_authority"])

            report_path = root / "experiment.json"
            report = json.loads(report_path.read_text())
            report["pre_a"]["result"] = report["pre_a"]["result"].replace(
                "outcome=no-proof", "outcome=proved"
            )
            report["experiment_sha256"] = MODULE.digest(
                {key: value for key, value in report.items() if key != "experiment_sha256"}
            )
            report_path.write_text(json.dumps(report))
            with self.assertRaisesRegex(MODULE.ChainCatalogError, "sequence"):
                MODULE.apply_counterfactual_qualification(structural, root)


if __name__ == "__main__":
    unittest.main()
