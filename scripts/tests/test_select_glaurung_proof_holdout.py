import importlib.util
import hashlib
import json
import unittest
from pathlib import Path


SCRIPT = Path(__file__).parents[1] / "select-glaurung-proof-holdout.py"
SPEC = importlib.util.spec_from_file_location("select_glaurung_proof_holdout", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def entry(index: int, family: str, expected: str) -> dict:
    digest = f"{index:064x}"
    return {
        "path": f"queries/{digest}.smt2",
        "content_hash": f"sha256:{digest}",
        "expected": expected,
        "family": family,
        "tiers": ["full"],
    }


def manifest(files: list[dict]) -> dict:
    return {
        "version": 1,
        "name": "source",
        "logic": "QF_BV",
        "source": "fixture",
        "files": files,
    }


class ProofHoldoutSelectionTests(unittest.TestCase):
    def test_selects_hash_first_strata_after_excluding_representative(self) -> None:
        full = manifest(
            [
                entry(5, "arithmetic", "sat"),
                entry(2, "arithmetic", "sat"),
                entry(3, "arithmetic", "sat"),
                entry(8, "register-slice", "unsat"),
                entry(7, "register-slice", "unsat"),
            ]
        )
        representative = manifest([entry(2, "arithmetic", "sat")])
        selected = MODULE.select_manifest(
            full,
            representative,
            quotas={
                ("arithmetic", "sat"): 2,
                ("register-slice", "unsat"): 1,
            },
            output_name="holdout",
            tier="proof-holdout-v1",
        )
        self.assertEqual(
            [row["content_hash"] for row in selected["files"]],
            [
                entry(3, "arithmetic", "sat")["content_hash"],
                entry(5, "arithmetic", "sat")["content_hash"],
                entry(7, "register-slice", "unsat")["content_hash"],
            ],
        )
        self.assertTrue(
            all(row["tiers"] == ["proof-holdout-v1"] for row in selected["files"])
        )

    def test_rejects_short_strata_or_nonmember_representative(self) -> None:
        full = manifest([entry(1, "arithmetic", "sat")])
        with self.assertRaisesRegex(ValueError, "quota"):
            MODULE.select_manifest(
                full,
                manifest([]),
                quotas={("arithmetic", "sat"): 2},
                output_name="holdout",
                tier="proof-holdout-v1",
            )
        malformed = manifest([entry(1, "arithmetic", "sat")])
        malformed["logic"] = "QF_UF"
        with self.assertRaisesRegex(ValueError, "logic"):
            MODULE.select_manifest(
                malformed,
                manifest([]),
                quotas={("arithmetic", "sat"): 1},
                output_name="holdout",
                tier="proof-holdout-v1",
            )
        with self.assertRaisesRegex(ValueError, "not an exact full-manifest member"):
            MODULE.select_manifest(
                full,
                manifest([entry(2, "arithmetic", "sat")]),
                quotas={("arithmetic", "sat"): 1},
                output_name="holdout",
                tier="proof-holdout-v1",
            )

    def test_rejects_duplicate_hashes_and_invalid_manifest_shape(self) -> None:
        duplicate = entry(1, "arithmetic", "sat")
        with self.assertRaisesRegex(ValueError, "duplicate content hash"):
            MODULE.select_manifest(
                manifest([duplicate, duplicate]),
                manifest([]),
                quotas={("arithmetic", "sat"): 1},
                output_name="holdout",
                tier="proof-holdout-v1",
            )

    def test_committed_registration_matches_selector_and_manifest(self) -> None:
        root = Path(__file__).parents[2]
        registration_path = (
            root
            / "corpus/glaurung-proof-populations/"
            "corrected-wide-v3-proof-holdout-v1-registration.json"
        )
        manifest_path = (
            root
            / "corpus/glaurung-proof-populations/"
            "corrected-wide-v3-proof-holdout-v1.json"
        )
        registration = json.loads(registration_path.read_bytes())
        selected = json.loads(manifest_path.read_bytes())
        selection = registration["selection"]
        self.assertEqual(
            selection["selector_sha256"], hashlib.sha256(SCRIPT.read_bytes()).hexdigest()
        )
        self.assertEqual(
            selection["manifest_sha256"],
            hashlib.sha256(manifest_path.read_bytes()).hexdigest(),
        )
        self.assertEqual(selection["selected_entries"], len(selected["files"]))
        self.assertEqual(
            selection["quotas"],
            {
                f"{family}/{expected}": quota
                for (family, expected), quota in sorted(MODULE.QUOTAS.items())
            },
        )
        self.assertEqual(
            sum(row["expected"] == "sat" for row in selected["files"]),
            selection["expected_sat"],
        )
        self.assertEqual(
            sum(row["expected"] == "unsat" for row in selected["files"]),
            selection["expected_unsat"],
        )


if __name__ == "__main__":
    unittest.main()
