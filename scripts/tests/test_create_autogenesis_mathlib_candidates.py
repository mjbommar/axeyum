from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


SCRIPT = pathlib.Path(__file__).parents[1] / "create-autogenesis-mathlib-candidates.py"
SPEC = importlib.util.spec_from_file_location("create_autogenesis_mathlib_candidates", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def row(name: str, module: str, constants: int) -> dict:
    type_repr = " ".join(f"Lean.Expr.const `C{i} []" for i in range(constants))
    return {
        "level_params": [],
        "module": module,
        "name": name,
        "type": f"statement {name}",
        "type_repr": type_repr,
    }


class CandidateTests(unittest.TestCase):
    def inputs(self):
        source = {
            "schema_version": 1,
            "kind": "axeyum-autogenesis-external-statement-source",
            "external_artifact": {"sha256": "a" * 64},
        }
        source["manifest_sha256"] = MODULE.digest(source)
        policy = {
            "schema_version": 1,
            "kind": "axeyum-autogenesis-mathlib-candidate-policy",
            "source_manifest_sha256": source["manifest_sha256"],
            "candidate_count": 4,
            "quota_per_family": 2,
            "maximum_type_repr_bytes": 1000,
            "ranking": [
                "fewest-distinct-type-constants",
                "shortest-structural-type",
                "lexicographic-declaration-name",
            ],
            "families": [
                {"module": "Mathlib.A", "domain": "Nat", "theme": "a"},
                {"module": "Mathlib.B", "domain": "Int", "theme": "b"},
            ],
            "exclusions": {
                "name_segment_prefixes": ["_", "eq_", "inst", "match_"],
                "name_substrings": ["._@.", "._proof_", "._simp_", "._unary", "_hyg"],
                "type_substrings": ["✝", "_hyg"],
            },
            "authority": {"answers": "read statement-only input"},
        }
        rows = [
            row("Nat.a", "Mathlib.A", 1),
            row("Nat.b", "Mathlib.A", 2),
            row("Nat.c", "Mathlib.A", 3),
            row("Int.a", "Mathlib.B", 1),
            row("Int.b", "Mathlib.B", 2),
            row("Int.c", "Mathlib.B", 3),
        ]
        return rows, source, policy

    def test_selection_is_deterministic_and_ranked_by_statement_shape(self) -> None:
        rows, source, policy = self.inputs()
        first = MODULE.build_candidates(rows, source, policy)
        second = MODULE.build_candidates(copy.deepcopy(rows), copy.deepcopy(source), copy.deepcopy(policy))
        self.assertEqual(first, second)
        self.assertEqual([row["name"] for row in first["candidates"]], ["Nat.a", "Nat.b", "Int.a", "Int.b"])
        MODULE.verify(first, second)

    def test_generated_name_is_excluded(self) -> None:
        rows, source, policy = self.inputs()
        rows[0]["name"] = "Nat.eq_generated"
        result = MODULE.build_candidates(rows, source, policy)
        self.assertNotIn("Nat.eq_generated", [row["name"] for row in result["candidates"]])
        family = result["coverage"]["families"][0]
        self.assertEqual(family["rejected"], {"generated-name-segment": 1})

    def test_quota_failure_is_not_silently_shrunk(self) -> None:
        rows, source, policy = self.inputs()
        rows = [row for row in rows if row["module"] != "Mathlib.B" or row["name"] == "Int.a"]
        with self.assertRaisesRegex(MODULE.CandidateError, "only 1 eligible"):
            MODULE.build_candidates(rows, source, policy)

    def test_source_manifest_mismatch_fails(self) -> None:
        rows, source, policy = self.inputs()
        policy["source_manifest_sha256"] = "b" * 64
        with self.assertRaisesRegex(MODULE.CandidateError, "different statement source"):
            MODULE.build_candidates(rows, source, policy)

    def test_mutated_candidate_artifact_fails_verification(self) -> None:
        rows, source, policy = self.inputs()
        expected = MODULE.build_candidates(rows, source, policy)
        mutated = copy.deepcopy(expected)
        mutated["candidates"][0]["type"] = "weaker statement"
        mutated["candidates_sha256"] = MODULE.digest(
            {key: value for key, value in mutated.items() if key != "candidates_sha256"}
        )
        with self.assertRaisesRegex(MODULE.CandidateError, "stale or mutated"):
            MODULE.verify(mutated, expected)

    def test_committed_artifact_can_be_checked_without_bulk_source(self) -> None:
        rows, source, policy = self.inputs()
        actual = MODULE.build_candidates(rows, source, policy)
        MODULE.validate_committed(actual, source, policy)
        actual["candidates"][0]["module"] = "Mathlib.B"
        actual["candidates_sha256"] = MODULE.digest(
            {key: value for key, value in actual.items() if key != "candidates_sha256"}
        )
        with self.assertRaisesRegex(MODULE.CandidateError, "family quotas"):
            MODULE.validate_committed(actual, source, policy)


if __name__ == "__main__":
    unittest.main()
