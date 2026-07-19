from __future__ import annotations

import importlib.util
import unittest
from pathlib import Path


SCRIPT = (
    Path(__file__).parents[1]
    / "validate-glaurung-policy-difference-adjudication.py"
)
SPEC = importlib.util.spec_from_file_location(
    "validate_glaurung_policy_difference_adjudication", SCRIPT
)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


ROW_A = "    arbitrary-read  va=0x1010  [dispatch] fn=f @ 0x1000  sev=Arbitrary  taint=[\"*Arg1\"]"
ROW_B = "        null-deref  va=0x1010  [dispatch] fn=f @ 0x1000  sev=Arbitrary  taint=[\"*Arg1\"]"


def frozen() -> dict:
    return {
        "schema": "axeyum.glaurung-policy-difference-population.v1",
        "finding_count": 2,
        "site_count": 1,
        "driver_count": 1,
        "policy_order": [
            "any-model",
            "min-unsigned",
            "max-unsigned",
            "site-hash-0",
            "site-hash-1",
        ],
        "drivers": [
            {
                "name": "fixture.sys",
                "binary_path": "test_drivers/fixture.sys",
                "sha256": "binary-sha",
                "source": {
                    "path": "test_drivers/fixture.c",
                    "repository_revision": "source-rev",
                    "sha256": "source-sha",
                },
                "rows": [
                    {
                        "finding": ROW_A,
                        "kind": "arbitrary-read",
                        "va": "0x1010",
                        "taint": ["*Arg1"],
                        "present_policies": ["any-model"],
                        "adjudication": {"status": "pending"},
                    },
                    {
                        "finding": ROW_B,
                        "kind": "null-deref",
                        "va": "0x1010",
                        "taint": ["*Arg1"],
                        "present_policies": ["any-model", "min-unsigned"],
                        "adjudication": {"status": "pending"},
                    },
                ],
            }
        ],
    }


def review() -> dict:
    return {
        "schema": "axeyum.glaurung-policy-difference-adjudication-review.v1",
        "frozen_population_sha256": "frozen-sha",
        "source_repository_revision": "source-rev",
        "sites": [
            {
                "driver": "fixture.sys",
                "va": "0x1010",
                "applies_to_all_frozen_rows_at_site": True,
                "classification": "ordinary-irp-request-plumbing",
                "source_lines": "10-12",
                "machine_evidence": "Loads a fixed request field, not an attacker-selected address.",
            }
        ],
    }


class PolicyDifferenceAdjudicationTests(unittest.TestCase):
    def test_accepts_exact_complete_review_and_computes_no_validated_gap(self) -> None:
        result = MODULE.validate_adjudication(
            frozen(),
            review(),
            frozen_sha256="frozen-sha",
            evidence={
                ("fixture.sys", "0x1010"): {
                    "instruction": "mov eax, dword ptr [rax + 0x18]",
                    "source_excerpt": "10:line ten\n11:line eleven\n12:line twelve",
                }
            },
        )
        self.assertTrue(result["accepted"])
        self.assertEqual(result["adjudicated_finding_count"], 2)
        self.assertEqual(result["adjudicated_site_count"], 1)
        self.assertEqual(
            result["classification_counts"],
            {"ordinary-irp-request-plumbing": 2},
        )
        self.assertFalse(result["validated_policy_difference"])
        self.assertFalse(result["validated_residual_gap"])
        self.assertEqual(result["indeterminate_count"], 0)
        self.assertEqual(
            result["rows"][0]["instruction"],
            "mov eax, dword ptr [rax + 0x18]",
        )

    def test_rejects_missing_or_extra_exact_rows(self) -> None:
        missing_review = review()
        missing_review["sites"] = []
        missing = MODULE.validate_adjudication(
            frozen(), missing_review, frozen_sha256="frozen-sha", evidence={}
        )
        self.assertFalse(missing["accepted"])
        self.assertTrue(any("does not exactly cover" in row for row in missing["failures"]))

        extra_review = review()
        extra_review["sites"].append(
            {
                "driver": "fixture.sys",
                "va": "0x2020",
                "applies_to_all_frozen_rows_at_site": True,
                "classification": "ordinary-irp-request-plumbing",
                "source_lines": "10-12",
                "machine_evidence": "Not a frozen site.",
            }
        )
        extra = MODULE.validate_adjudication(
            frozen(), extra_review, frozen_sha256="frozen-sha", evidence={}
        )
        self.assertFalse(extra["accepted"])
        self.assertTrue(any("does not exactly cover" in row for row in extra["failures"]))

    def test_rejects_identity_evidence_and_classification_drift(self) -> None:
        wrong_hash = MODULE.validate_adjudication(
            frozen(), review(), frozen_sha256="other", evidence={}
        )
        self.assertFalse(wrong_hash["accepted"])
        self.assertTrue(any("frozen population SHA-256" in row for row in wrong_hash["failures"]))

        wrong_revision = review()
        wrong_revision["source_repository_revision"] = "other"
        revision = MODULE.validate_adjudication(
            frozen(), wrong_revision, frozen_sha256="frozen-sha", evidence={}
        )
        self.assertFalse(revision["accepted"])
        self.assertTrue(any("source revision" in row for row in revision["failures"]))

        unknown = review()
        unknown["sites"][0]["classification"] = "looks-safe"
        classification = MODULE.validate_adjudication(
            frozen(), unknown, frozen_sha256="frozen-sha", evidence={}
        )
        self.assertFalse(classification["accepted"])
        self.assertTrue(any("classification" in row for row in classification["failures"]))

        no_instruction = MODULE.validate_adjudication(
            frozen(), review(), frozen_sha256="frozen-sha", evidence={}
        )
        self.assertFalse(no_instruction["accepted"])
        self.assertTrue(any("instruction evidence" in row for row in no_instruction["failures"]))

    def test_real_primitive_difference_opens_the_residual_gap(self) -> None:
        candidate = review()
        candidate["sites"][0]["classification"] = "real-vulnerability-primitive"
        result = MODULE.validate_adjudication(
            frozen(),
            candidate,
            frozen_sha256="frozen-sha",
            evidence={
                ("fixture.sys", "0x1010"): {
                    "instruction": "call rax",
                    "source_excerpt": "10:call callback",
                }
            },
        )
        self.assertTrue(result["accepted"])
        self.assertTrue(result["validated_policy_difference"])
        self.assertTrue(result["validated_residual_gap"])
        self.assertEqual(
            result["real_primitive_counts_by_policy"],
            {
                "any-model": 2,
                "min-unsigned": 1,
                "max-unsigned": 0,
                "site-hash-0": 0,
                "site-hash-1": 0,
            },
        )


if __name__ == "__main__":
    unittest.main()
