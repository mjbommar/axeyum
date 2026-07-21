from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
CHECKER = ROOT / "scripts" / "check-reflection-semantics-gate.py"
BINARIES = [
    "reflection_semantics_gate",
    "llvm_ctlz",
    "cross_ir_equivalence",
    "cross_ir_refutation",
    "llvm_checked_cfg",
    "llvm_checked_memory",
    "mir_checked_memory",
    "checked_bounds",
    "llvm_checked_loop",
    "llvm_direct_calls",
    "checksum_module",
    "source_contract_bridge",
]


class ReflectionSemanticsGateTest(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        (self.root / "src").mkdir()
        (self.root / "tests").mkdir()
        (self.root / "docs").mkdir()
        (self.root / "src" / "surface.rs").write_text(
            "pub enum Op {\n"
            "    /// Scalar.\n"
            "    Add,\n"
            "    Pair(u8, u8),\n"
            "    Record { values: Vec<u8> },\n"
            "}\n",
            encoding="utf-8",
        )
        (self.root / "tests" / "evidence.rs").write_text(
            "#[test]\nfn proof() {}\n\n#[test]\nfn fuzz() {}\n",
            encoding="utf-8",
        )
        self.manifest = {
            "schema": "axeyum.reflection-semantics-gate.v1",
            "surfaces": [
                {"id": "demo.op", "source": "src/surface.rs", "enum": "Op"}
            ],
            "evidence_groups": [
                {
                    "id": "demo",
                    "members": ["demo.op::Add", "demo.op::Pair", "demo.op::Record"],
                    "proof_tests": ["tests/evidence.rs::proof"],
                    "fuzz_tests": ["tests/evidence.rs::fuzz"],
                }
            ],
            "test_binaries": BINARIES,
        }
        self.write_manifest()

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def write_manifest(self) -> None:
        (self.root / "docs" / "manifest.json").write_text(
            json.dumps(self.manifest, indent=2) + "\n", encoding="utf-8"
        )

    def run_checker(self) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [
                sys.executable,
                str(CHECKER),
                "--root",
                str(self.root),
                "--manifest",
                "docs/manifest.json",
            ],
            check=False,
            text=True,
            capture_output=True,
        )

    def assert_fails(self, fragment: str) -> None:
        self.write_manifest()
        result = self.run_checker()
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn(fragment, result.stderr)

    def test_valid_manifest_reports_exact_inventory(self) -> None:
        result = self.run_checker()
        self.assertEqual(result.returncode, 0, result.stderr)
        report = json.loads(result.stdout)
        self.assertEqual(report["surfaces"], 1)
        self.assertEqual(report["variants"], 3)
        self.assertEqual(report["status"], "pass")

    def test_new_source_variant_fails_uncovered(self) -> None:
        path = self.root / "src" / "surface.rs"
        path.write_text(path.read_text().replace("    Add,", "    Add,\n    NewOp,"))
        self.assert_fails("uncovered semantic keys")

    def test_removed_evidence_member_fails_uncovered(self) -> None:
        self.manifest["evidence_groups"][0]["members"].remove("demo.op::Pair")
        self.assert_fails("uncovered semantic keys")

    def test_duplicate_evidence_member_fails(self) -> None:
        self.manifest["evidence_groups"].append(
            {
                "id": "duplicate",
                "members": ["demo.op::Add"],
                "proof_tests": ["tests/evidence.rs::proof"],
                "fuzz_tests": ["tests/evidence.rs::fuzz"],
            }
        )
        self.assert_fails("already owned")

    def test_orphan_evidence_member_fails(self) -> None:
        self.manifest["evidence_groups"][0]["members"].append("demo.op::Missing")
        self.assert_fails("orphan semantic key")

    def test_missing_proof_or_fuzz_side_fails(self) -> None:
        self.manifest["evidence_groups"][0]["proof_tests"] = []
        self.assert_fails("proof_tests: must not be empty")

    def test_nonexistent_or_ignored_test_fails(self) -> None:
        self.manifest["evidence_groups"][0]["fuzz_tests"] = [
            "tests/evidence.rs::missing"
        ]
        self.assert_fails("active `#[test] fn missing` not found")

    def test_escaping_source_path_fails(self) -> None:
        self.manifest["surfaces"][0]["source"] = "../outside.rs"
        self.assert_fails("without `..`")

    def test_duplicate_group_id_fails(self) -> None:
        duplicate = dict(self.manifest["evidence_groups"][0])
        duplicate["members"] = []
        self.manifest["evidence_groups"].append(duplicate)
        self.assert_fails("duplicate evidence group")

    def test_command_list_drift_fails(self) -> None:
        self.manifest["test_binaries"] = BINARIES[:-1]
        self.assert_fails("command-list drift")


if __name__ == "__main__":
    unittest.main()
