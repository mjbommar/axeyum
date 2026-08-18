from __future__ import annotations

import copy
import importlib.util
import json
import pathlib
import tempfile
import unittest


SCRIPT = pathlib.Path(__file__).parents[1] / "create-autogenesis-mathlib-dependency-components.py"
SPEC = importlib.util.spec_from_file_location("create_autogenesis_mathlib_dependency_components", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class DependencyComponentTests(unittest.TestCase):
    def inputs(self):
        temporary = tempfile.TemporaryDirectory()
        root = pathlib.Path(temporary.name)
        extractor = root / "extractor.lean"
        extractor.write_text(
            'def x := theoremInfo.value.getUsedConstants\n'
            '"name"\n"module"\n"theorem_dependencies"\n'
        )
        rows = [
            {"module": "Mathlib.A", "name": "Int.c", "theorem_dependencies": ["Nat.a"]},
            {"module": "Mathlib.A", "name": "Nat.a", "theorem_dependencies": []},
            {"module": "Mathlib.B", "name": "Nat.b", "theorem_dependencies": ["Nat.a", "congrArg"]},
            {"module": "Mathlib.C", "name": "Nat.d", "theorem_dependencies": []},
        ]
        artifact_root = root / "external"
        artifact_root.mkdir()
        artifact = artifact_root / "dependencies.ndjson"
        artifact.write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in rows))
        candidates = {
            "source_manifest_sha256": "s" * 64,
            "candidates_sha256": "c" * 64,
            "candidates": [
                {"candidate_id": "ci", "module": "Mathlib.A", "name": "Int.c", "theme": "int"},
                {"candidate_id": "ca", "module": "Mathlib.A", "name": "Nat.a", "theme": "nat-a"},
                {"candidate_id": "cb", "module": "Mathlib.B", "name": "Nat.b", "theme": "nat-b"},
                {"candidate_id": "cd", "module": "Mathlib.C", "name": "Nat.d", "theme": "nat-d"},
            ],
        }
        manifest = {
            "schema_version": 1,
            "kind": "axeyum-autogenesis-external-theorem-dependency-source",
            "statement_source_manifest_sha256": candidates["source_manifest_sha256"],
            "candidate_set_sha256": candidates["candidates_sha256"],
            "source": {
                "commit": "c5ea00351c28e24afc9f0f84379aa41082b1188f",
                "tag": "v4.30.0",
            },
            "extractor": {"path": "extractor.lean", "sha256": MODULE.sha256_file(extractor)},
            "external_artifact": {
                "storage_root": str(artifact_root),
                "file": artifact.name,
                "sha256": MODULE.sha256_file(artifact),
                "bytes": artifact.stat().st_size,
                "records": len(rows),
                "content": "names-and-direct-theorem-edges-only-ndjson",
            },
            "isolation_policy": {"forbidden_consumers": "proposers and proof search"},
        }
        manifest["manifest_sha256"] = MODULE.digest(manifest)
        return temporary, root, candidates, manifest, extractor, artifact

    def test_component_projection_is_deterministic_and_whole(self) -> None:
        temporary, root, candidates, manifest, _, _ = self.inputs()
        self.addCleanup(temporary.cleanup)
        external, first = MODULE.check(manifest, candidates, root)
        _, second = MODULE.check(copy.deepcopy(manifest), copy.deepcopy(candidates), root)
        self.assertEqual(external, "verified")
        self.assertEqual(first, second)
        assert first is not None
        self.assertEqual(first["coverage"]["direct_edges"], 2)
        self.assertEqual(first["coverage"]["component_count"], 2)
        self.assertEqual(first["coverage"]["largest_component"], 3)
        self.assertEqual(first["coverage"]["cross_theme_edges"], 2)
        MODULE.validate_committed(first, candidates, manifest)

    def test_non_candidate_foundation_is_not_an_induced_edge(self) -> None:
        temporary, root, candidates, manifest, _, artifact = self.inputs()
        self.addCleanup(temporary.cleanup)
        rows = MODULE.read_rows(artifact, manifest["external_artifact"])
        result = MODULE.build(candidates, manifest, rows)
        edges = [edge for component in result["components"] for edge in component["edges"]]
        self.assertNotIn("congrArg", {edge["dependency"] for edge in edges})

    def test_proof_bearing_output_field_is_rejected(self) -> None:
        temporary, _, _, manifest, _, artifact = self.inputs()
        self.addCleanup(temporary.cleanup)
        rows = [json.loads(line) for line in artifact.read_text().splitlines()]
        rows[0]["proof"] = "answer"
        artifact.write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in rows))
        manifest["external_artifact"].update(
            sha256=MODULE.sha256_file(artifact), bytes=artifact.stat().st_size
        )
        with self.assertRaisesRegex(MODULE.DependencyError, "forbidden or missing fields"):
            MODULE.read_rows(artifact, manifest["external_artifact"])

    def test_unsorted_dependency_names_are_rejected(self) -> None:
        temporary, _, _, manifest, _, artifact = self.inputs()
        self.addCleanup(temporary.cleanup)
        rows = [json.loads(line) for line in artifact.read_text().splitlines()]
        rows[2]["theorem_dependencies"] = ["congrArg", "Nat.a", "Nat.a"]
        artifact.write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in rows))
        manifest["external_artifact"].update(
            sha256=MODULE.sha256_file(artifact), bytes=artifact.stat().st_size
        )
        with self.assertRaisesRegex(MODULE.DependencyError, "unsorted, duplicate"):
            MODULE.read_rows(artifact, manifest["external_artifact"])

    def test_cycle_is_rejected(self) -> None:
        temporary, _, candidates, manifest, _, artifact = self.inputs()
        self.addCleanup(temporary.cleanup)
        rows = [json.loads(line) for line in artifact.read_text().splitlines()]
        rows[1]["theorem_dependencies"] = ["Nat.b"]
        with self.assertRaisesRegex(MODULE.DependencyError, "cycle"):
            MODULE.build(candidates, manifest, rows)

    def test_edge_mutation_changes_projection_and_fails_exact_check(self) -> None:
        temporary, _, candidates, manifest, _, artifact = self.inputs()
        self.addCleanup(temporary.cleanup)
        rows = MODULE.read_rows(artifact, manifest["external_artifact"])
        expected = MODULE.build(candidates, manifest, rows)
        mutated_rows = copy.deepcopy(rows)
        mutated_rows[0]["theorem_dependencies"] = []
        mutated = MODULE.build(candidates, manifest, mutated_rows)
        self.assertNotEqual(expected["components_sha256"], mutated["components_sha256"])
        self.assertNotEqual(expected, mutated)
        rehashed = copy.deepcopy(expected)
        rehashed["components"][0]["edges"] = rehashed["components"][0]["edges"][1:]
        rehashed["coverage"]["direct_edges"] -= 1
        rehashed["components_sha256"] = MODULE.digest(
            {key: value for key, value in rehashed.items() if key != "components_sha256"}
        )
        with self.assertRaisesRegex(MODULE.DependencyError, "not weakly connected"):
            MODULE.validate_committed(rehashed, candidates, manifest)

    def test_extractor_output_schema_cannot_add_proof(self) -> None:
        temporary, root, candidates, manifest, extractor, _ = self.inputs()
        self.addCleanup(temporary.cleanup)
        extractor.write_text(
            'def x := theoremInfo.value.getUsedConstants\n'
            '"theorem_dependencies"\n("proof", Json.str "answer")\n'
        )
        manifest["extractor"]["sha256"] = MODULE.sha256_file(extractor)
        manifest["manifest_sha256"] = MODULE.digest(
            {key: value for key, value in manifest.items() if key != "manifest_sha256"}
        )
        with self.assertRaisesRegex(MODULE.DependencyError, "forbidden proof-bearing field"):
            MODULE.verify_manifest(manifest, candidates, root)


if __name__ == "__main__":
    unittest.main()
