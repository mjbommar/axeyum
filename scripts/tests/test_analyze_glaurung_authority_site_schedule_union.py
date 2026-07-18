import importlib.util
import unittest
from pathlib import Path


SCRIPTS = Path(__file__).parents[1]
SCRIPT = SCRIPTS / "analyze-glaurung-authority-site-schedule-union.py"
FIXTURE_SCRIPT = Path(__file__).with_name(
    "test_analyze_glaurung_authority_coverage_union.py"
)

SPEC = importlib.util.spec_from_file_location(
    "analyze_glaurung_authority_site_schedule_union", SCRIPT
)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)

FIXTURE_SPEC = importlib.util.spec_from_file_location(
    "authority_coverage_union_fixture", FIXTURE_SCRIPT
)
assert FIXTURE_SPEC and FIXTURE_SPEC.loader
FIXTURE = importlib.util.module_from_spec(FIXTURE_SPEC)
FIXTURE_SPEC.loader.exec_module(FIXTURE)


class AuthoritySiteScheduleUnionTests(unittest.TestCase):
    def test_accepts_stable_four_policy_union_and_preserves_all_partitions(self) -> None:
        analyzed = MODULE.analyze_reports(
            FIXTURE.report(None, ["a", "arbitrary-only", "z3-only"], ["a", "arbitrary-only"]),
            FIXTURE.report("min-unsigned", ["a", "min-only"]),
            FIXTURE.report("max-unsigned", ["a", "max-only"]),
            FIXTURE.report("site-hash-0", ["a", "mixed-zero", "z3-only"]),
            FIXTURE.report("site-hash-1", ["a", "mixed-one"]),
        )
        self.assertTrue(analyzed["accepted"])
        self.assertEqual(
            analyzed["four_schedule_union"]["ordered_findings"],
            [
                "a",
                "max-only",
                "min-only",
                "mixed-one",
                "mixed-zero",
                "z3-only",
            ],
        )
        self.assertEqual(
            analyzed["extension_over_two_extrema"]["site_schedule_only"],
            ["mixed-one", "mixed-zero", "z3-only"],
        )
        self.assertEqual(
            analyzed["four_schedule_vs_any_model_combined_union"]["any_model_only"],
            ["arbitrary-only"],
        )
        self.assertEqual(
            analyzed["four_schedule_vs_any_model_combined_union"]["four_schedule_only"],
            ["max-only", "min-only", "mixed-one", "mixed-zero"],
        )

    def test_rejects_mixed_policy_authority_divergence(self) -> None:
        with self.assertRaisesRegex(RuntimeError, "site-hash-1 authority findings differ"):
            MODULE.analyze_reports(
                FIXTURE.report(None, ["a", "z3-only"], ["a"]),
                FIXTURE.report("min-unsigned", ["a"]),
                FIXTURE.report("max-unsigned", ["a"]),
                FIXTURE.report("site-hash-0", ["a"]),
                FIXTURE.report("site-hash-1", ["a"], ["b"]),
            )

    def test_rejects_cross_cell_source_drift(self) -> None:
        mixed_one = FIXTURE.report("site-hash-1", ["a"])
        mixed_one["glaurung"]["revision"] = "different"
        with self.assertRaisesRegex(RuntimeError, "glaurung identity drift"):
            MODULE.analyze_reports(
                FIXTURE.report(None, ["a", "z3-only"], ["a"]),
                FIXTURE.report("min-unsigned", ["a"]),
                FIXTURE.report("max-unsigned", ["a"]),
                FIXTURE.report("site-hash-0", ["a"]),
                mixed_one,
            )

    def test_rejects_an_accepted_any_model_baseline(self) -> None:
        with self.assertRaisesRegex(RuntimeError, "must preserve a stable divergence"):
            MODULE.analyze_reports(
                FIXTURE.report(None, ["a"]),
                FIXTURE.report("min-unsigned", ["a"]),
                FIXTURE.report("max-unsigned", ["a"]),
                FIXTURE.report("site-hash-0", ["a"]),
                FIXTURE.report("site-hash-1", ["a"]),
            )


if __name__ == "__main__":
    unittest.main()
