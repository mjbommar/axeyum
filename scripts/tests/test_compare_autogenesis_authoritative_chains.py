import copy
import hashlib
import importlib.util
import json
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).resolve().parents[1] / "compare-autogenesis-authoritative-chains.py"
SPEC = importlib.util.spec_from_file_location("compare_autogenesis_chains", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class CompareAuthoritativeChainsTests(unittest.TestCase):
    def fixture(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name)
        artifact = root / "evidence.json"
        artifact.write_text("{}\n", encoding="utf-8")
        value = {
            "schema_version": 1,
            "kind": "axeyum-autogenesis-authoritative-two-write-run",
            "source_commit": "source",
            "reconstructed_prestate_commit": "prestate",
            "pre_a_state_commit": "state",
            "chain": {"premise": "F:b", "consequent": "F:a"},
            "budgets": {"b": 2, "a": 1},
            "intervention_audit": {"human_interventions_after_launch": 0},
            "trusted_base_audit": {"trusted_base_files_changed": []},
            "fault_injection": {"b": {"recovered": True}, "a": {"recovered": True}},
            "checks": {"closed": True},
            "artifacts": {"evidence.json": hashlib.sha256(b"{}\n").hexdigest()},
        }
        value["run_sha256"] = MODULE.canonical_digest(value)
        (root / "run.json").write_text(json.dumps(value) + "\n", encoding="utf-8")
        return root, value

    def test_valid_manifest_loads_and_projects(self):
        root, value = self.fixture()
        loaded = MODULE.load_run(root)
        self.assertEqual(MODULE.comparison_identity(loaded), MODULE.comparison_identity(value))

    def test_tampered_artifact_fails(self):
        root, _ = self.fixture()
        (root / "evidence.json").write_text("tampered\n", encoding="utf-8")
        with self.assertRaisesRegex(MODULE.CompareError, "artifact digest mismatch"):
            MODULE.load_run(root)

    def test_failed_check_fails(self):
        root, value = self.fixture()
        changed = copy.deepcopy(value)
        changed["checks"]["closed"] = False
        changed.pop("run_sha256")
        changed["run_sha256"] = MODULE.canonical_digest(changed)
        (root / "run.json").write_text(json.dumps(changed) + "\n", encoding="utf-8")
        with self.assertRaisesRegex(MODULE.CompareError, "failed semantic check"):
            MODULE.load_run(root)

    def test_changed_budget_changes_reproduction_identity(self):
        _, first = self.fixture()
        second = copy.deepcopy(first)
        second["budgets"]["a"] = 2
        self.assertNotEqual(
            MODULE.comparison_identity(first), MODULE.comparison_identity(second)
        )
