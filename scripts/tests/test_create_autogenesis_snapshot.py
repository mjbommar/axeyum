from __future__ import annotations

import importlib.util
import pathlib
import unittest


SCRIPT = pathlib.Path(__file__).parents[1] / "create-autogenesis-snapshot.py"
SPEC = importlib.util.spec_from_file_location("create_autogenesis_snapshot", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def fact(ident: str, theorem: str, depends_on: list[str]) -> dict:
    return {
        "id": ident,
        "proof_route": "kernel-lean",
        "epistemic_status": "proved",
        "depends_on": depends_on,
        "evidence": [{"checker_command": f"inventory | grep '^%s '" % theorem}],
    }


class SnapshotTests(unittest.TestCase):
    def inputs(self):
        facts = {
            "F:B": fact("F:B", "Nat.zero_add", []),
            "F:A": fact("F:A", "Nat.mul_one", ["F:B"]),
            "F:C": fact("F:C", "Nat.add_comm", []),
        }
        return {
            "premise_id": "F:B",
            "consequent_id": "F:A",
            "facts": facts,
            "fact_hashes": {"F:B": "b", "F:A": "a", "F:C": "c"},
            "graph": {
                "Nat.zero_add": [],
                "Nat.mul_one": ["Nat.zero_add"],
                "Nat.add_comm": ["Nat.zero_add"],
            },
            "baseline": {"source_sha256": "source"},
            "baseline_sha256": "baseline",
        }

    def test_retained_answers_are_denied_in_both_phases(self):
        snapshot = MODULE.build_snapshot(**self.inputs())
        denied = ["Nat.mul_one", "Nat.zero_add"]
        self.assertEqual(snapshot["phases"]["pre_b"]["denied_theorems"], denied)
        self.assertEqual(snapshot["phases"]["post_b"]["denied_theorems"], denied)
        self.assertNotIn("F:B", snapshot["phases"]["pre_b"]["visible_fact_ids"])
        self.assertNotIn("F:B", snapshot["phases"]["post_b"]["visible_fact_ids"])

    def test_post_b_requires_episode_local_premise(self):
        snapshot = MODULE.build_snapshot(**self.inputs())
        post = snapshot["phases"]["post_b"]
        self.assertEqual(
            [item["declaration"] for item in post["accepted_episode_facts"]],
            post["required_dependencies"],
        )
        self.assertNotEqual(post["required_dependencies"], ["Nat.zero_add"])

    def test_snapshot_is_deterministic_and_content_sensitive(self):
        inputs = self.inputs()
        first = MODULE.build_snapshot(**inputs)
        second = MODULE.build_snapshot(**inputs)
        self.assertEqual(first, second)
        inputs["fact_hashes"]["F:B"] = "changed"
        changed = MODULE.build_snapshot(**inputs)
        self.assertNotEqual(first["episode_id"], changed["episode_id"])

    def test_ledger_only_edge_is_rejected(self):
        inputs = self.inputs()
        inputs["graph"]["Nat.mul_one"] = []
        with self.assertRaisesRegex(MODULE.SnapshotError, "does not directly reference"):
            MODULE.build_snapshot(**inputs)


if __name__ == "__main__":
    unittest.main()
