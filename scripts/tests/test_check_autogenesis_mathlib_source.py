from __future__ import annotations

import copy
import importlib.util
import json
import pathlib
import tempfile
import unittest


SCRIPT = pathlib.Path(__file__).parents[1] / "check-autogenesis-mathlib-source.py"
SPEC = importlib.util.spec_from_file_location("check_autogenesis_mathlib_source", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class MathlibSourceTests(unittest.TestCase):
    def fixture(self):
        temporary = tempfile.TemporaryDirectory()
        root = pathlib.Path(temporary.name)
        extractor = root / "extractor.lean"
        extractor.write_text('def x := theoremInfo.type\n"type"\n"type_repr"\n')
        artifact_root = root / "external"
        artifact_root.mkdir()
        artifact_path = artifact_root / "rows.ndjson"
        rows = [
            {
                "level_params": [],
                "module": "Mathlib.Data.Int.Basic",
                "name": "Int.a",
                "type": "1 = 1",
                "type_repr": "Lean.Expr.const `Eq []",
            },
            {
                "level_params": [],
                "module": "Mathlib.Data.Nat.Basic",
                "name": "Nat.b",
                "type": "0 = 0",
                "type_repr": "Lean.Expr.const `Eq []",
            },
        ]
        artifact_path.write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in rows))
        manifest = {
            "schema_version": 1,
            "kind": "axeyum-autogenesis-external-statement-source",
            "source": {
                "commit": "c5ea00351c28e24afc9f0f84379aa41082b1188f",
                "tag": "v4.30.0",
            },
            "extractor": {
                "path": "extractor.lean",
                "sha256": MODULE.sha256_file(extractor),
            },
            "external_artifact": {
                "storage_root": str(artifact_root),
                "file": artifact_path.name,
                "sha256": MODULE.sha256_file(artifact_path),
                "bytes": artifact_path.stat().st_size,
                "records": len(rows),
                "content": "statement-only-ndjson",
            },
            "integration_policy": {
                "proof_isolation": "candidate selection must not read proof values"
            },
        }
        manifest["manifest_sha256"] = MODULE.digest(manifest)
        return temporary, root, manifest, extractor, artifact_path

    def test_statement_only_fixture_verifies(self) -> None:
        temporary, root, manifest, _, _ = self.fixture()
        self.addCleanup(temporary.cleanup)
        self.assertEqual(MODULE.check(manifest, root), "verified")

    def test_manifest_mutation_fails_digest(self) -> None:
        temporary, root, manifest, _, _ = self.fixture()
        self.addCleanup(temporary.cleanup)
        manifest["source"]["tag"] = "v4.33.0"
        with self.assertRaisesRegex(MODULE.SourceError, "manifest digest"):
            MODULE.check(manifest, root)

    def test_extractor_cannot_read_theorem_value(self) -> None:
        temporary, root, manifest, extractor, _ = self.fixture()
        self.addCleanup(temporary.cleanup)
        extractor.write_text('def x := theoremInfo.value\n"type"\n"type_repr"\n')
        manifest["extractor"]["sha256"] = MODULE.sha256_file(extractor)
        manifest["manifest_sha256"] = MODULE.digest(
            {key: value for key, value in manifest.items() if key != "manifest_sha256"}
        )
        with self.assertRaisesRegex(MODULE.SourceError, "proof value"):
            MODULE.check(manifest, root)

    def test_external_proof_field_is_rejected(self) -> None:
        temporary, root, manifest, _, artifact = self.fixture()
        self.addCleanup(temporary.cleanup)
        row = json.loads(artifact.read_text().splitlines()[0])
        row["value"] = "proof"
        artifact.write_text(json.dumps(row) + "\n")
        manifest["external_artifact"].update(
            sha256=MODULE.sha256_file(artifact), bytes=artifact.stat().st_size, records=1
        )
        manifest["manifest_sha256"] = MODULE.digest(
            {key: value for key, value in manifest.items() if key != "manifest_sha256"}
        )
        with self.assertRaisesRegex(MODULE.SourceError, "statement-only fields"):
            MODULE.check(manifest, root)

    def test_duplicate_or_unsorted_names_are_rejected(self) -> None:
        temporary, root, manifest, _, artifact = self.fixture()
        self.addCleanup(temporary.cleanup)
        rows = [json.loads(line) for line in artifact.read_text().splitlines()]
        artifact.write_text(json.dumps(rows[1]) + "\n" + json.dumps(rows[0]) + "\n")
        manifest["external_artifact"].update(
            sha256=MODULE.sha256_file(artifact), bytes=artifact.stat().st_size
        )
        manifest["manifest_sha256"] = MODULE.digest(
            {key: value for key, value in manifest.items() if key != "manifest_sha256"}
        )
        with self.assertRaisesRegex(MODULE.SourceError, "out of order"):
            MODULE.check(manifest, root)

    def test_missing_external_mount_is_reported_not_claimed(self) -> None:
        temporary, root, manifest, _, _ = self.fixture()
        self.addCleanup(temporary.cleanup)
        manifest = copy.deepcopy(manifest)
        manifest["external_artifact"]["storage_root"] = str(root / "absent")
        manifest["manifest_sha256"] = MODULE.digest(
            {key: value for key, value in manifest.items() if key != "manifest_sha256"}
        )
        self.assertEqual(MODULE.check(manifest, root), "unavailable")


if __name__ == "__main__":
    unittest.main()
