"""Unit and mutation tests for the ADR-0356 S3 official producer."""

from __future__ import annotations

import hashlib
import json
import tempfile
import textwrap
import unittest
from pathlib import Path

from scripts.smtcomp_repro.official_producer import (
    OfficialProducerError,
    authority_bundle_entries,
    locked_runtime_requirements,
    materialize_bundle,
    validate_repetition,
    validate_selected_output,
    verify_bundle,
)
from scripts.smtcomp_repro.official_producer_worker import load_official_cache_builder
from scripts.smtcomp_repro.official_selection import canonical_json_bytes


ROOT = Path(__file__).resolve().parents[3]
AUTHORITY_PATH = ROOT / "docs/plan/smtcomp-official-selection-authority-v1.json"


def identity(path: str, data: bytes) -> dict[str, object]:
    return {"bytes": len(data), "path": path, "sha256": hashlib.sha256(data).hexdigest()}


class OfficialProducerTests(unittest.TestCase):
    def test_authority_materializes_exact_88_file_bundle_contract(self) -> None:
        authority = json.loads(AUTHORITY_PATH.read_bytes())
        entries = authority_bundle_entries(authority)
        self.assertEqual(len(entries), 88)
        self.assertEqual(entries, sorted(entries, key=lambda row: row["path"]))
        self.assertIn("poetry.lock", {row["path"] for row in entries})
        self.assertIn("smtcomp/selection.py", {row["path"] for row in entries})
        self.assertIn("data/benchmarks-2026.json.gz", {row["path"] for row in entries})

    def test_bundle_copy_rejects_drift_extra_and_symlink(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "source"
            source.mkdir()
            payload = b"pinned\n"
            (source / "file.txt").write_bytes(payload)
            entries = [identity("file.txt", payload)]
            destination = root / "bundle"
            materialize_bundle(source, destination, entries)
            self.assertEqual(verify_bundle(destination, entries), entries)

            (destination / "extra").write_bytes(b"extra")
            with self.assertRaises(OfficialProducerError):
                verify_bundle(destination, entries)
            (destination / "extra").unlink()
            (destination / "file.txt").write_bytes(b"drift")
            with self.assertRaises(OfficialProducerError):
                verify_bundle(destination, entries)
            (destination / "file.txt").unlink()
            (destination / "file.txt").symlink_to(source / "file.txt")
            with self.assertRaises(OfficialProducerError):
                verify_bundle(destination, entries)

    def test_hash_locked_runtime_closure_is_deterministic(self) -> None:
        def package(name: str, version: str, dependencies: dict[str, str] | None = None) -> str:
            digest = hashlib.sha256(name.encode()).hexdigest()
            dependency_section = ""
            if dependencies:
                dependency_section = "\n[package.dependencies]\n" + "\n".join(
                    f'{key} = "{value}"' for key, value in dependencies.items()
                )
            return textwrap.dedent(
                f'''\
                [[package]]
                name = "{name}"
                version = "{version}"
                groups = ["main"]
                files = [{{file = "{name}.whl", hash = "sha256:{digest}"}}]
                {dependency_section}
                '''
            )

        lock = "".join(
            [
                package("email-validator", "1", {"shared": ">=1"}),
                package("polars", "1.39.2", {"polars-runtime-32": "1.39.2"}),
                package("polars-runtime-32", "1.39.2"),
                package("pydantic", "2", {"shared": ">=1"}),
                package("rich", "3", {"shared": ">=1"}),
                package("shared", "4"),
                '\n[metadata]\nlock-version = "2.1"\npython-versions = ">=3.11,<4.0"\n',
            ]
        ).encode()
        first, manifest = locked_runtime_requirements(lock)
        second, second_manifest = locked_runtime_requirements(lock)
        self.assertEqual(first, second)
        self.assertEqual(manifest, second_manifest)
        self.assertEqual([row["name"] for row in manifest], sorted(row["name"] for row in manifest))
        self.assertIn(b"polars==1.39.2 --hash=sha256:", first)
        self.assertEqual(first.count(b"shared==4"), 1)

        missing_hash = lock.replace(b"sha256:", b"sha512:", 1)
        with self.assertRaises(OfficialProducerError):
            locked_runtime_requirements(missing_hash)

    def test_cache_builder_is_extracted_from_pinned_ast_without_decorator(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            bundle = Path(temporary)
            package = bundle / "smtcomp"
            package.mkdir()
            (package / "main.py").write_text(
                "@app.command()\ndef create_cache(data: Path, only_current: bool = False) -> None:\n"
                "    data.append(only_current)\n"
            )
            namespace: dict[str, object] = {"Path": Path}
            builder, digest = load_official_cache_builder(bundle, namespace)
            observed: list[bool] = []
            builder(observed)
            self.assertEqual(observed, [False])
            self.assertEqual(len(digest), 64)

    def test_repetition_rejects_order_path_and_per_logic_drift(self) -> None:
        paths = [
            "non-incremental/QF_BV/family/a.smt2",
            "non-incremental/QF_BV/family/b.smt2",
        ]
        selected = ("\n".join(paths) + "\n").encode()
        logic = canonical_json_bytes({"logics": [{"logic": "QF_BV", "selected": 2}], "selected": 2})
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            first = root / "first"
            second = root / "second"
            first.mkdir()
            second.mkdir()
            for output in (first, second):
                (output / "official-selected.txt").write_bytes(selected)
                (output / "per-logic.json").write_bytes(logic)
            result = validate_repetition(first, second)
            self.assertEqual(len(result["official_selected_sha256"]), 64)

            (second / "official-selected.txt").write_bytes(("\n".join(reversed(paths)) + "\n").encode())
            with self.assertRaises(OfficialProducerError):
                validate_repetition(first, second)
            (second / "official-selected.txt").write_bytes(selected)
            (second / "per-logic.json").write_bytes(canonical_json_bytes({"selected": 1}))
            with self.assertRaises(OfficialProducerError):
                validate_repetition(first, second)

        with self.assertRaises(OfficialProducerError):
            validate_selected_output(b"../escape.smt2\n")
        with self.assertRaises(OfficialProducerError):
            validate_selected_output(b"non-incremental/QF_BV/family\\escape.smt2\n")
        with self.assertRaises(OfficialProducerError):
            validate_selected_output(b"non-incremental//QF_BV/family/escape.smt2\n")


if __name__ == "__main__":
    unittest.main()
