import hashlib
import importlib.util
import json
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).parents[1] / "materialize-glaurung-proof-holdout.py"
SPEC = importlib.util.spec_from_file_location("materialize_glaurung_proof_holdout", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def digest(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def entry(path: str, raw: bytes, *, tier: str) -> dict:
    return {
        "path": path,
        "content_hash": f"sha256:{digest(raw)}",
        "expected": "sat",
        "family": "fixture",
        "tiers": [tier],
    }


def manifest(name: str, files: list[dict]) -> dict:
    return {
        "version": 1,
        "name": name,
        "logic": "QF_BV",
        "source": "fixture",
        "files": files,
    }


class ProofHoldoutMaterializationTests(unittest.TestCase):
    def fixture(self, root: Path) -> tuple[Path, Path, Path, bytes]:
        source = root / "source"
        query = source / "queries" / ("a" * 64 + ".smt2")
        query.parent.mkdir(parents=True)
        raw = b"(set-logic QF_BV)\n(check-sat)\n"
        query.write_bytes(raw)
        full = manifest("full", [entry(f"queries/{query.name}", raw, tier="full")])
        selected = manifest(
            "selected", [entry(f"queries/{query.name}", raw, tier="proof-holdout-v1")]
        )
        full_path = source / "manifest-v1.json"
        selected_path = root / "selected.json"
        full_path.write_text(json.dumps(full, indent=2) + "\n", encoding="utf-8")
        selected_path.write_text(json.dumps(selected, indent=2) + "\n", encoding="utf-8")
        return source, full_path, selected_path, raw

    def test_materializes_exact_selected_membership_and_bytes(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source, full_path, selected_path, raw = self.fixture(root)
            out = root / "out"
            report = MODULE.materialize(
                source,
                full_path,
                selected_path,
                out,
                expected_full_sha256=digest(full_path.read_bytes()),
                expected_selected_sha256=digest(selected_path.read_bytes()),
            )
            copied = out / "queries" / ("a" * 64 + ".smt2")
            self.assertEqual(copied.read_bytes(), raw)
            self.assertEqual((out / "manifest-v1.json").read_bytes(), selected_path.read_bytes())
            self.assertEqual(report["selected_entries"], 1)
            self.assertEqual(report["copied_bytes"], len(raw))
            self.assertEqual(
                sorted(path.relative_to(out).as_posix() for path in out.rglob("*.smt2")),
                [f"queries/{'a' * 64}.smt2"],
            )

    def test_rejects_source_content_drift_without_creating_destination(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source, full_path, selected_path, _ = self.fixture(root)
            (source / "queries" / ("a" * 64 + ".smt2")).write_text("drift")
            out = root / "out"
            with self.assertRaisesRegex(ValueError, "content hash"):
                MODULE.materialize(
                    source,
                    full_path,
                    selected_path,
                    out,
                    expected_full_sha256=digest(full_path.read_bytes()),
                    expected_selected_sha256=digest(selected_path.read_bytes()),
                )
            self.assertFalse(out.exists())

    def test_rejects_nonmember_selection_and_manifest_hash_drift(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source, full_path, selected_path, _ = self.fixture(root)
            selected = json.loads(selected_path.read_bytes())
            selected["files"][0]["family"] = "not-the-full-member"
            selected_path.write_text(json.dumps(selected, indent=2) + "\n")
            with self.assertRaisesRegex(ValueError, "exact full-manifest member"):
                MODULE.materialize(
                    source,
                    full_path,
                    selected_path,
                    root / "out",
                    expected_full_sha256=digest(full_path.read_bytes()),
                    expected_selected_sha256=digest(selected_path.read_bytes()),
                )
            with self.assertRaisesRegex(ValueError, "selected manifest SHA-256"):
                MODULE.materialize(
                    source,
                    full_path,
                    selected_path,
                    root / "out-two",
                    expected_full_sha256=digest(full_path.read_bytes()),
                    expected_selected_sha256="0" * 64,
                )

    def test_refuses_existing_destination(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source, full_path, selected_path, _ = self.fixture(root)
            out = root / "out"
            out.mkdir()
            with self.assertRaisesRegex(ValueError, "refusing to overwrite"):
                MODULE.materialize(
                    source,
                    full_path,
                    selected_path,
                    out,
                    expected_full_sha256=digest(full_path.read_bytes()),
                    expected_selected_sha256=digest(selected_path.read_bytes()),
                )


if __name__ == "__main__":
    unittest.main()
