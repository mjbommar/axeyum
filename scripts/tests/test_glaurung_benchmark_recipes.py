import subprocess
import unittest
from pathlib import Path


ROOT = Path(__file__).parents[2]


def dry_run(recipe: str, *args: str) -> str:
    completed = subprocess.run(
        ["just", "--dry-run", recipe, *args],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    return completed.stdout + completed.stderr


class GlaurungBenchmarkRecipeTests(unittest.TestCase):
    def assert_policy(self, recipe: str, expected: str) -> None:
        output = dry_run(recipe, "corpus", "manifest", "representative")
        self.assertIn("--backend sat-bv", output)
        self.assertIn("--require-in-process-z3", output)
        self.assertIn("--require-reproducible-run", output)
        self.assertIn("--require-deterministic-resources", output)
        self.assertIn("--min-decided-percent 100", output)
        if expected == "raw":
            self.assertIn("--rewrite off", output)
            self.assertNotIn("--preprocess", output)
        elif expected == "canonical":
            self.assertIn("--rewrite default", output)
            self.assertNotIn("--preprocess", output)
        elif expected == "configured":
            self.assertIn("--rewrite off --preprocess", output)
        else:
            self.fail(f"unknown expected policy {expected}")

    def test_single_run_policies_are_distinct(self) -> None:
        self.assert_policy("bench-glaurung-qfbv-raw", "raw")
        self.assert_policy("bench-glaurung-qfbv-canonical", "canonical")
        self.assert_policy("bench-glaurung-qfbv-configured", "configured")

    def test_demand_slicing_has_whole_tier_and_register_slice_recipes(self) -> None:
        whole = dry_run("bench-glaurung-qfbv-demand", "corpus", "manifest")
        register = dry_run(
            "bench-glaurung-qfbv-demand-register-slice", "corpus", "manifest"
        )
        for output in (whole, register):
            self.assertIn("--backend sat-bv", output)
            self.assertIn("--rewrite off", output)
            self.assertIn("--demand-bit-slicing", output)
            self.assertNotIn("--profile-bit-demand", output)
            self.assertIn("--require-reproducible-run", output)
            self.assertIn("--min-decided-percent 100", output)
        self.assertNotIn("--families", whole)
        self.assertIn("--families register-slice", register)

    def test_proof_companions_preserve_the_word_policy(self) -> None:
        self.assert_policy("bench-glaurung-qfbv-raw-proof-check", "raw")
        self.assert_policy("bench-glaurung-qfbv-canonical-proof-check", "canonical")
        self.assert_policy("bench-glaurung-qfbv-configured-proof-check", "configured")
        for recipe in [
            "bench-glaurung-qfbv-raw-proof-check",
            "bench-glaurung-qfbv-canonical-proof-check",
            "bench-glaurung-qfbv-configured-proof-check",
        ]:
            self.assertIn("--prove-unsat", dry_run(recipe, "corpus", "manifest"))

    def test_repeated_wrappers_select_separate_policy_series(self) -> None:
        expected = {
            "bench-glaurung-qfbv-raw-repeated": "raw",
            "bench-glaurung-qfbv-canonical-repeated": "canonical",
            "bench-glaurung-qfbv-configured-repeated": "configured",
        }
        for recipe, policy in expected.items():
            output = dry_run(recipe, "corpus", "manifest", "representative")
            self.assertIn("_bench-glaurung-qfbv-repeated", output)
            self.assertTrue(output.rstrip().endswith(policy), output)
            self.assertIn(f"glaurung-qfbv-{policy}-repeated", output)

    def test_range_demand_recipes_pin_distinct_policy_and_thresholds(self) -> None:
        for recipe in [
            "bench-glaurung-qfbv-range-demand",
            "bench-glaurung-qfbv-range-demand-register-slice",
        ]:
            output = dry_run(recipe, "corpus", "manifest")
            self.assertIn("--range-demand-slicing", output)
            self.assertNotIn("--demand-bit-slicing", output)
            self.assertIn("--range-demand-min-term-bits", output)
            self.assertIn("--range-demand-min-estimated-percent", output)
            self.assertIn("--range-demand-min-exact-percent", output)
            self.assertIn("--range-demand-work-budget", output)
        register = dry_run(
            "bench-glaurung-qfbv-range-demand-register-slice",
            "corpus",
            "manifest",
        )
        self.assertIn("--families register-slice", register)

    def test_unsuffixed_compatibility_entries_follow_raw(self) -> None:
        single = dry_run("bench-glaurung-qfbv", "corpus", "manifest")
        repeated = dry_run("bench-glaurung-qfbv-repeated", "corpus", "manifest")
        proof = dry_run("bench-glaurung-qfbv-proof-check", "corpus", "manifest")
        self.assertIn("bench-glaurung-qfbv-raw", single)
        self.assertIn("bench-glaurung-qfbv-raw-repeated", repeated)
        self.assertIn("bench-glaurung-qfbv-raw-proof-check", proof)

    def test_guarded_comparison_pins_full_tier_thresholds(self) -> None:
        output = dry_run(
            "compare-glaurung-qfbv-repeated-guarded",
            "baseline.json",
            "candidate.json",
            "comparison.json",
        )
        self.assertIn("--max-ratio-regression-percent 3", output)
        self.assertIn("--max-axeyum-regression-percent 3", output)
        self.assertIn("--max-z3-drift-percent 2", output)

    def test_rewrite_guard_requires_the_exact_manifest_delta(self) -> None:
        output = dry_run(
            "compare-glaurung-qfbv-repeated-rewrite-guarded",
            "baseline.json",
            "candidate.json",
            "axeyum-rewrite-default-v2",
            "axeyum-rewrite-default-v3",
            "bv.add_constant_chain.v1",
            "comparison.json",
        )
        self.assertIn("--expected-baseline-rule-set", output)
        self.assertIn("--expected-candidate-rule-set", output)
        self.assertIn("--expected-added-rewrite-rule", output)
        self.assertIn("--max-ratio-regression-percent 3", output)


if __name__ == "__main__":
    unittest.main()
