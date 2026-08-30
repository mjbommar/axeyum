from __future__ import annotations

import copy
import importlib.util
import json
from pathlib import Path
import unittest


SCRIPT = Path(__file__).parents[1] / "check-autogenesis-nursery.py"
SPEC = importlib.util.spec_from_file_location("check_autogenesis_nursery", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def fact(fact_id: str, dependencies: list[str] | None = None) -> dict:
    return {"id": fact_id, "depends_on": dependencies or []}


def entry(
    fact_id: str,
    partition: str,
    *,
    provenance: str = "project-constructed",
    routes: list[str] | None = None,
    mutation_of: str | None = None,
) -> dict:
    return {
        "fact_id": fact_id,
        "partition": partition,
        "provenance_class": provenance,
        "family": "family",
        "proof_shape": "shape",
        "source_group": fact_id,
        "route_hypotheses": routes or ["kernel"],
        "mutation_of": mutation_of,
        "answer_access": "withheld-during-episode",
    }


def unshared_entry(fact_id: str, partition: str) -> dict:
    """An entry() whose family/proof_shape/source_group are all UNIQUE to it.

    `entry()`'s defaults share `family="family"` / `proof_shape="shape"`
    across every call, so two entries in different partitions always ALSO
    trip the family- and proof-shape-leak checks. That is fine for tests
    that only assert on the substring "crosses evaluation partitions" (every
    leak header contains it), but it pollutes an exemption test's message
    with unrelated, unexempted violations. Use this helper whenever a test
    wants to isolate exactly the COMPONENT-split (or longitudinal-overlap)
    check.
    """
    row = entry(fact_id, partition)
    row["family"] = f"family-{fact_id}"
    row["proof_shape"] = f"shape-{fact_id}"
    return row


class NurseryTests(unittest.TestCase):
    def setUp(self) -> None:
        repository = json.loads(MODULE.NURSERY.read_text())
        self.nursery = copy.deepcopy(repository)
        self.nursery["state"] = "foundation-only"
        self.nursery["entries"] = [
            row for row in repository["entries"] if row["partition"] == "longitudinal"
        ]
        # The real nursery-v1.json carries component_split_exemptions naming
        # real fact ids that are not part of this test's slimmed-down
        # synthetic population; each test builds its own tiny scenario and
        # exercises exemptions explicitly where it needs to.
        self.nursery["component_split_exemptions"] = []
        self.result = {"verdict": "autogenesis-1-passed"}
        self.facts = {
            "F:nat-zero-add": fact("F:nat-zero-add"),
            "F:nat-mul-one": fact("F:nat-mul-one", ["F:nat-zero-add"]),
        }

    def test_repository_foundation_is_truthfully_not_ready(self) -> None:
        report = MODULE.build_report(self.nursery, self.facts, self.result)
        self.assertFalse(report["ready"])
        self.assertEqual(report["population"]["evaluation_entries"], 0)
        self.assertIn("empty-partition:held-out", report["blockers"])
        self.assertTrue(report["controls"]["admission_edges_require_proof_derivation"])

    def test_component_leakage_fails_closed(self) -> None:
        self.facts.update(
            {
                "F:train": fact("F:train"),
                "F:held": fact("F:held", ["F:train"]),
            }
        )
        self.nursery["entries"].extend(
            [entry("F:train", "train"), entry("F:held", "held-out")]
        )
        with self.assertRaisesRegex(MODULE.NurseryError, "crosses evaluation partitions"):
            MODULE.build_report(self.nursery, self.facts, self.result)

    def test_longitudinal_component_cannot_be_reused_for_evaluation(self) -> None:
        self.facts["F:leak"] = fact("F:leak", ["F:nat-mul-one"])
        self.nursery["entries"].append(entry("F:leak", "development"))
        with self.assertRaisesRegex(MODULE.NurseryError, "shares a component"):
            MODULE.build_report(self.nursery, self.facts, self.result)

    def test_route_hypotheses_never_become_authority(self) -> None:
        self.facts["F:isolated"] = fact("F:isolated")
        self.nursery["entries"].append(
            entry("F:isolated", "held-out", routes=["cas", "solver"])
        )
        report = MODULE.build_report(self.nursery, self.facts, self.result)
        self.assertEqual(report["population"]["route_hypothesis_families"], ["cas", "solver"])
        self.assertTrue(
            report["controls"]["route_hypotheses_grant_no_dispatch_or_admission_authority"]
        )

    def test_family_and_shape_leakage_fail_closed(self) -> None:
        self.facts.update({"F:train": fact("F:train"), "F:held": fact("F:held")})
        self.nursery["entries"].extend(
            [entry("F:train", "train"), entry("F:held", "held-out")]
        )
        with self.assertRaisesRegex(MODULE.NurseryError, "theorem family crosses"):
            MODULE.build_report(self.nursery, self.facts, self.result)

        self.nursery["entries"][-1]["family"] = "other-family"
        with self.assertRaisesRegex(MODULE.NurseryError, "proof shape crosses"):
            MODULE.build_report(self.nursery, self.facts, self.result)

    def test_source_review_group_leakage_fails_closed(self) -> None:
        self.facts.update({"F:train": fact("F:train"), "F:held": fact("F:held")})
        train = entry("F:train", "train")
        held = entry("F:held", "held-out")
        train["family"], held["family"] = "train-family", "held-family"
        train["proof_shape"], held["proof_shape"] = "train-shape", "held-shape"
        train["source_group"] = held["source_group"] = "review-group"
        self.nursery["entries"].extend([train, held])
        with self.assertRaisesRegex(MODULE.NurseryError, "source review group crosses"):
            MODULE.build_report(self.nursery, self.facts, self.result)

    def test_mutation_must_reference_a_nursery_entry(self) -> None:
        self.facts["F:mutation"] = fact("F:mutation")
        self.nursery["entries"].append(
            entry("F:mutation", "development", mutation_of="F:outside")
        )
        with self.assertRaisesRegex(MODULE.NurseryError, "mutation target is outside"):
            MODULE.build_report(self.nursery, self.facts, self.result)

    def test_mutation_classification_and_partition_are_coupled(self) -> None:
        self.facts.update({"F:base": fact("F:base"), "F:mutation": fact("F:mutation")})
        self.nursery["entries"].extend(
            [entry("F:base", "development"), entry("F:mutation", "development")]
        )
        self.nursery["entries"][-1]["mutation_of"] = "F:base"
        with self.assertRaisesRegex(MODULE.NurseryError, "provenance and mutation_of"):
            MODULE.build_report(self.nursery, self.facts, self.result)
        self.nursery["entries"][-1]["provenance_class"] = "generated-mutation"
        self.nursery["entries"][-1]["source_group"] = self.nursery["entries"][-2]["source_group"]
        self.nursery["entries"][-1]["partition"] = "held-out"
        with self.assertRaisesRegex(MODULE.NurseryError, "target partition, family, and source group"):
            MODULE.build_report(self.nursery, self.facts, self.result)

    def test_policy_floor_mutation_is_rejected(self) -> None:
        mutated = copy.deepcopy(self.nursery)
        mutated["policy"]["evaluation_fact_count"]["minimum"] = 2
        with self.assertRaisesRegex(MODULE.NurseryError, "100..300"):
            MODULE.build_report(mutated, self.facts, self.result)

    def test_complete_component_safe_population_can_be_frozen(self) -> None:
        for index in range(100):
            fact_id = f"F:e-{index}"
            dependencies = ["F:e-0"] if index == 1 else []
            self.facts[fact_id] = fact(fact_id, dependencies)
            partition = "train" if index < 34 else "development" if index < 67 else "held-out"
            row = entry(
                fact_id,
                partition,
                provenance="external-transcribed" if index % 2 else "project-constructed",
                routes=["cas"] if index % 2 else ["kernel"],
            )
            row["family"] = f"family-{index}"
            row["proof_shape"] = f"shape-{index}"
            self.nursery["entries"].append(row)
        mutation = self.nursery["entries"][3]
        mutation["provenance_class"] = "generated-mutation"
        mutation["mutation_of"] = "F:e-0"
        mutation["family"] = self.nursery["entries"][2]["family"]
        mutation["proof_shape"] = self.nursery["entries"][2]["proof_shape"]
        mutation["source_group"] = self.nursery["entries"][2]["source_group"]
        self.nursery["state"] = "frozen-evaluation"

        report = MODULE.build_report(self.nursery, self.facts, self.result)
        self.assertTrue(report["ready"])
        self.assertEqual(report["blockers"], [])
        self.assertEqual(report["population"]["maximum_declared_dependency_depth"], 2)
        self.assertEqual(report["population"]["held_out_components"], 33)

    def test_report_is_deterministic_and_addressed(self) -> None:
        first = MODULE.build_report(self.nursery, self.facts, self.result)
        second = MODULE.build_report(
            copy.deepcopy(self.nursery), copy.deepcopy(self.facts), copy.deepcopy(self.result)
        )
        self.assertEqual(first, second)
        unsigned = dict(first)
        claimed = unsigned.pop("report_sha256")
        self.assertEqual(claimed, MODULE.digest(unsigned))

    def test_component_leak_message_names_members_and_partitions(self) -> None:
        # Regression guard for the 2026-08-30 defect: the gate used to raise
        # a bare header naming no component, no fact, and no partition.
        self.facts.update(
            {
                "F:train": fact("F:train"),
                "F:held": fact("F:held", ["F:train"]),
            }
        )
        self.nursery["entries"].extend(
            [entry("F:train", "train"), entry("F:held", "held-out")]
        )
        with self.assertRaises(MODULE.NurseryError) as ctx:
            MODULE.build_report(self.nursery, self.facts, self.result)
        message = str(ctx.exception)
        self.assertIn("F:train -> train", message)
        self.assertIn("F:held -> held-out", message)
        self.assertIn("partitions=", message)

    def test_multiple_violation_types_are_all_reported_at_once(self) -> None:
        # The gate used to raise on the FIRST violation type only, masking
        # any other violation until the first was fixed. Engineer both a
        # component leak and a family leak simultaneously and confirm the
        # single raised message names both.
        self.facts.update({"F:train": fact("F:train"), "F:held": fact("F:held")})
        train = entry("F:train", "train")
        held = entry("F:held", "held-out")
        train["family"] = "shared-family"
        held["family"] = "shared-family"
        self.nursery["entries"].extend([train, held])
        with self.assertRaises(MODULE.NurseryError) as ctx:
            MODULE.build_report(self.nursery, self.facts, self.result)
        message = str(ctx.exception)
        self.assertIn("theorem family crosses evaluation partitions", message)
        self.assertIn("2 partition-leak violation type(s) found", message)

    def test_exemption_naming_a_non_nursery_fact_is_rejected(self) -> None:
        self.nursery["component_split_exemptions"] = [
            {
                "component_fact_ids": ["F:not-in-nursery"],
                "reason": "test",
                "authority": "test",
                "date": "2026-08-30",
            }
        ]
        with self.assertRaisesRegex(MODULE.NurseryError, "which is not a nursery entry"):
            MODULE.build_report(self.nursery, self.facts, self.result)

    def test_duplicate_exemption_is_rejected(self) -> None:
        self.facts.update({"F:train": fact("F:train"), "F:held": fact("F:held", ["F:train"])})
        self.nursery["entries"].extend(
            [unshared_entry("F:train", "train"), unshared_entry("F:held", "held-out")]
        )
        exemption = {
            "component_fact_ids": ["F:held", "F:train"],
            "reason": "test",
            "authority": "test",
            "date": "2026-08-30",
        }
        self.nursery["component_split_exemptions"] = [exemption, dict(exemption)]
        with self.assertRaisesRegex(MODULE.NurseryError, "duplicates an already-exempted"):
            MODULE.build_report(self.nursery, self.facts, self.result)

    def test_malformed_exemption_fact_ids_are_rejected(self) -> None:
        self.nursery["component_split_exemptions"] = [
            {
                # Not sorted -- must be rejected before it can silently
                # produce a different digest than the checker's own.
                "component_fact_ids": ["F:nat-mul-one", "F:nat-zero-add"][::-1],
                "reason": "test",
                "authority": "test",
                "date": "2026-08-30",
            }
        ]
        with self.assertRaisesRegex(MODULE.NurseryError, "sorted, deduplicated"):
            MODULE.build_report(self.nursery, self.facts, self.result)

    def test_exemption_suppresses_exactly_the_named_component(self) -> None:
        self.facts.update({"F:train": fact("F:train"), "F:held": fact("F:held", ["F:train"])})
        self.nursery["entries"].extend(
            [unshared_entry("F:train", "train"), unshared_entry("F:held", "held-out")]
        )
        self.nursery["component_split_exemptions"] = [
            {
                "component_fact_ids": sorted(["F:train", "F:held"]),
                "reason": "test exemption",
                "authority": "test",
                "date": "2026-08-30",
            }
        ]
        report = MODULE.build_report(self.nursery, self.facts, self.result)
        self.assertEqual(report["controls"]["component_split_leaks"], [])
        exempted = report["controls"]["component_split_leaks_exempted"]
        self.assertEqual(len(exempted), 1)
        member_ids = sorted(m["fact_id"] for m in exempted[0]["members"])
        self.assertEqual(member_ids, ["F:held", "F:train"])
        self.assertEqual(report["controls"]["component_split_exemptions_unused"], [])

    def test_exemption_stops_matching_once_the_component_grows(self) -> None:
        # The self-invalidation property: an exemption names an EXACT fact-id
        # set, and its digest is recomputed against the CURRENT declared
        # dependency graph on every run. If a later fact starts depending on
        # a member of an exempted component, the component's digest changes
        # and the exemption must stop applying -- the gate must go red again
        # on the now-larger, unreviewed component.
        self.facts.update({"F:train": fact("F:train"), "F:held": fact("F:held", ["F:train"])})
        self.nursery["entries"].extend(
            [unshared_entry("F:train", "train"), unshared_entry("F:held", "held-out")]
        )
        self.nursery["component_split_exemptions"] = [
            {
                "component_fact_ids": sorted(["F:train", "F:held"]),
                "reason": "test exemption",
                "authority": "test",
                "date": "2026-08-30",
            }
        ]
        # Sanity: the exemption applies as-is.
        report = MODULE.build_report(self.nursery, self.facts, self.result)
        self.assertEqual(report["controls"]["component_split_leaks"], [])

        # Now grow the component: a new development-partition fact starts
        # depending on F:train, joining the same weakly-connected component
        # without being named in the exemption.
        self.facts["F:new-dependent"] = fact("F:new-dependent", ["F:train"])
        self.nursery["entries"].append(unshared_entry("F:new-dependent", "development"))
        with self.assertRaisesRegex(MODULE.NurseryError, "crosses evaluation partitions"):
            MODULE.build_report(self.nursery, self.facts, self.result)

    def test_exemption_also_suppresses_matching_longitudinal_overlap(self) -> None:
        self.facts["F:leak"] = fact("F:leak", ["F:nat-mul-one"])
        self.nursery["entries"].append(entry("F:leak", "development"))
        longitudinal_component = sorted(["F:leak", "F:nat-mul-one", "F:nat-zero-add"])
        self.nursery["component_split_exemptions"] = [
            {
                "component_fact_ids": longitudinal_component,
                "reason": "test exemption",
                "authority": "test",
                "date": "2026-08-30",
            }
        ]
        report = MODULE.build_report(self.nursery, self.facts, self.result)
        self.assertEqual(report["controls"]["evaluation_longitudinal_component_overlap"], [])
        self.assertEqual(
            report["controls"]["evaluation_longitudinal_component_overlap_exempted"],
            ["F:leak"],
        )


if __name__ == "__main__":
    unittest.main()
