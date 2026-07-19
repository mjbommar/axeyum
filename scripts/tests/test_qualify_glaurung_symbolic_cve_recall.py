import importlib.util
import pathlib
import unittest


SCRIPT = (
    pathlib.Path(__file__).resolve().parents[1]
    / "qualify-glaurung-symbolic-cve-recall.py"
)
SPEC = importlib.util.spec_from_file_location("qualify_symbolic_cve", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


CORPUS_SHA = "a" * 64
RECALL_SHA = "b" * 64


def corpus() -> list[dict]:
    return [
        {
            "cve": "CVE-TEST-0001",
            "file": "drivers/test/direct.c",
            "handler_fn": "direct_ioctl",
            "ioctl_cmd": "TEST_DIRECT",
            "unprivileged_reachable": True,
            "fixing_commit": "111111111111",
            "vuln_class": "int-overflow",
            "fix_summary": "test: prevent integer overflow",
            "source": "https://example.invalid/111111111111",
            "subsystem": "drivers/test",
            "year": 2026,
            "confirmed_in_tree": True,
        },
        {
            "cve": "CVE-TEST-0002",
            "file": "drivers/test/stale-name.c",
            "handler_fn": "race_ioctl",
            "ioctl_cmd": "TEST_RACE",
            "unprivileged_reachable": False,
            "fixing_commit": "222222222222",
            "vuln_class": "uaf",
            "fix_summary": "test: serialize lifetime",
            "source": "https://example.invalid/222222222222",
            "subsystem": "drivers/test",
            "year": 2026,
            "confirmed_in_tree": True,
        },
    ]


def recall() -> dict:
    return {
        "n_cves": 2,
        "summary": {"n_total": 2},
        "rows": [
            {"cve": "CVE-TEST-0001", "handler_found": True},
            {"cve": "CVE-TEST-0002", "handler_found": False},
        ],
    }


def classification() -> dict:
    return {
        "schema": "axeyum.glaurung-symbolic-cve-qualification.v1",
        "cve_corpus_sha256": CORPUS_SHA,
        "cve_recall_sha256": RECALL_SHA,
        "expected_rows": 2,
        "expected_partition": {
            "direct-scalar-address-safety": 1,
            "lifetime-concurrency": 1,
        },
        "rows": [
            {
                "cve": "CVE-TEST-0001",
                "qualification_class": "direct-scalar-address-safety",
                "current_fragment_candidate": True,
                "rationale": "Direct checked arithmetic in the handler path.",
            },
            {
                "cve": "CVE-TEST-0002",
                "qualification_class": "lifetime-concurrency",
                "current_fragment_candidate": False,
                "source_file_override": "drivers/test/actual.c",
                "rationale": "Requires concurrent lifetime semantics.",
            },
        ],
    }


def resolved() -> dict[str, dict]:
    return {
        "111111111111": {
            "full_commit": "1" * 40,
            "parent_commit": "3" * 40,
            "changed_files": ["drivers/test/direct.c"],
            "handler_files": ["drivers/test/direct.c"],
            "patch_sha256": "c" * 64,
        },
        "222222222222": {
            "full_commit": "2" * 40,
            "parent_commit": "4" * 40,
            "changed_files": ["drivers/test/actual.c"],
            "handler_files": ["drivers/test/actual.c"],
            "patch_sha256": "d" * 64,
        },
    }


class SymbolicCveQualificationTests(unittest.TestCase):
    def test_accepts_complete_partition_and_records_candidates_separately(self) -> None:
        report = MODULE.validate_qualification(
            corpus(),
            recall(),
            classification(),
            resolved(),
            corpus_sha256=CORPUS_SHA,
            recall_sha256=RECALL_SHA,
        )
        self.assertTrue(report["valid"])
        self.assertEqual(report["summary"]["rows"], 2)
        self.assertEqual(report["summary"]["current_fragment_candidates"], 1)
        self.assertEqual(report["summary"]["not_currently_admitted"], 1)
        self.assertEqual(
            report["rows"][1]["effective_source_file"],
            "drivers/test/actual.c",
        )
        self.assertFalse(report["rows"][1]["current_fragment_candidate"])

    def test_rejects_source_hash_drift(self) -> None:
        with self.assertRaisesRegex(ValueError, "cve corpus SHA-256"):
            MODULE.validate_qualification(
                corpus(),
                recall(),
                classification(),
                resolved(),
                corpus_sha256="e" * 64,
                recall_sha256=RECALL_SHA,
            )

    def test_rejects_missing_or_extra_classification_rows(self) -> None:
        bad = classification()
        bad["rows"].pop()
        with self.assertRaisesRegex(ValueError, "classification CVEs"):
            MODULE.validate_qualification(
                corpus(),
                recall(),
                bad,
                resolved(),
                corpus_sha256=CORPUS_SHA,
                recall_sha256=RECALL_SHA,
            )

    def test_rejects_candidate_outside_direct_safety_class(self) -> None:
        bad = classification()
        bad["rows"][1]["current_fragment_candidate"] = True
        with self.assertRaisesRegex(ValueError, "candidate"):
            MODULE.validate_qualification(
                corpus(),
                recall(),
                bad,
                resolved(),
                corpus_sha256=CORPUS_SHA,
                recall_sha256=RECALL_SHA,
            )

    def test_rejects_patch_path_mismatch_without_explicit_override(self) -> None:
        bad = classification()
        del bad["rows"][1]["source_file_override"]
        with self.assertRaisesRegex(ValueError, "changed files"):
            MODULE.validate_qualification(
                corpus(),
                recall(),
                bad,
                resolved(),
                corpus_sha256=CORPUS_SHA,
                recall_sha256=RECALL_SHA,
            )

    def test_rejects_handler_absent_from_vulnerable_parent(self) -> None:
        bad_resolved = resolved()
        bad_resolved["111111111111"]["handler_files"] = []
        with self.assertRaisesRegex(ValueError, "handler"):
            MODULE.validate_qualification(
                corpus(),
                recall(),
                classification(),
                bad_resolved,
                corpus_sha256=CORPUS_SHA,
                recall_sha256=RECALL_SHA,
            )

    def test_rejects_partition_count_drift(self) -> None:
        bad = classification()
        bad["expected_partition"] = {"direct-scalar-address-safety": 2}
        with self.assertRaisesRegex(ValueError, "partition"):
            MODULE.validate_qualification(
                corpus(),
                recall(),
                bad,
                resolved(),
                corpus_sha256=CORPUS_SHA,
                recall_sha256=RECALL_SHA,
            )


if __name__ == "__main__":
    unittest.main()
