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


def v2_extension(entries: list[dict]) -> dict:
    return {
        "kind": "axeyum-autogenesis-nursery-extension",
        "extends": "artifacts/autogenesis/nursery-v1.json",
        "entries": entries,
    }


class CrossPopulationTests(unittest.TestCase):
    """`build_cross_population_report` -- the union-of-v1-and-v2 component
    check. `check-autogenesis-nursery.py` used to only ever read
    nursery-v1.json, so a crossing entirely within nursery-v2-extension, or
    one formed only by a real dependency edge BETWEEN the two files, was
    invisible to every gate. See docs/plan/status/nursery-v2-component-coverage.md
    and ADR-0855.
    """

    def setUp(self) -> None:
        self.facts: dict[str, dict] = {}
        self.v1 = {"entries": []}
        self.v2 = v2_extension([])

    def test_wrong_extension_kind_is_rejected(self) -> None:
        self.v2["kind"] = "something-else"
        with self.assertRaisesRegex(MODULE.NurseryError, "schema identity is invalid"):
            MODULE.build_cross_population_report(self.v1, self.v2, self.facts)

    def test_extension_must_still_declare_its_base(self) -> None:
        self.v2["extends"] = "artifacts/autogenesis/nursery-v0.json"
        with self.assertRaisesRegex(MODULE.NurseryError, "no longer declares nursery-v1"):
            MODULE.build_cross_population_report(self.v1, self.v2, self.facts)

    def test_overlapping_fact_ids_across_files_are_rejected(self) -> None:
        self.facts["F:shared"] = fact("F:shared")
        self.v1["entries"] = [unshared_entry("F:shared", "train")]
        self.v2["entries"] = [unshared_entry("F:shared", "development")]
        with self.assertRaisesRegex(MODULE.NurseryError, "overlapping fact ids"):
            MODULE.build_cross_population_report(self.v1, self.v2, self.facts)

    def test_v2_internal_component_leak_fails_closed(self) -> None:
        # A crossing entirely WITHIN nursery-v2-extension -- invisible to
        # build_report, which never reads this file at all.
        self.facts.update(
            {
                "F:v1-unrelated": fact("F:v1-unrelated"),
                "F:v2-train": fact("F:v2-train"),
                "F:v2-dev": fact("F:v2-dev", ["F:v2-train"]),
            }
        )
        self.v1["entries"] = [unshared_entry("F:v1-unrelated", "train")]
        self.v2["entries"] = [
            unshared_entry("F:v2-train", "train"),
            unshared_entry("F:v2-dev", "development"),
        ]
        with self.assertRaisesRegex(
            MODULE.NurseryError, "cross-population: nursery-v1 union nursery-v2-extension"
        ):
            MODULE.build_cross_population_report(self.v1, self.v2, self.facts)

    def test_cross_file_dependency_edge_creates_a_leak_invisible_to_either_file_alone(
        self,
    ) -> None:
        # F:v1-train (v1, train) and F:v2-dev (v2, development) are each a
        # singleton, non-leaking component within their OWN file. The
        # dependency edge between them only exists once the files are
        # unioned -- exactly the ADR-0855 finding.
        self.facts.update(
            {"F:v1-train": fact("F:v1-train"), "F:v2-dev": fact("F:v2-dev", ["F:v1-train"])}
        )
        self.v1["entries"] = [unshared_entry("F:v1-train", "train")]
        self.v2["entries"] = [unshared_entry("F:v2-dev", "development")]
        with self.assertRaises(MODULE.NurseryError) as ctx:
            MODULE.build_cross_population_report(self.v1, self.v2, self.facts)
        message = str(ctx.exception)
        self.assertIn("F:v1-train -> train [v1]", message)
        self.assertIn("F:v2-dev -> development [v2]", message)

    def test_exemption_suppresses_exactly_the_named_cross_population_component(self) -> None:
        self.facts.update(
            {"F:v1-train": fact("F:v1-train"), "F:v2-dev": fact("F:v2-dev", ["F:v1-train"])}
        )
        self.v1["entries"] = [unshared_entry("F:v1-train", "train")]
        self.v2["entries"] = [unshared_entry("F:v2-dev", "development")]
        self.v2["cross_population_component_split_exemptions"] = [
            {
                "component_fact_ids": sorted(["F:v1-train", "F:v2-dev"]),
                "reason": "test exemption",
                "authority": "test",
                "date": "2026-08-30",
            }
        ]
        report = MODULE.build_cross_population_report(self.v1, self.v2, self.facts)
        self.assertEqual(report["controls"]["component_split_leaks"], [])
        exempted = report["controls"]["component_split_leaks_exempted"]
        self.assertEqual(len(exempted), 1)
        origins = {m["fact_id"]: m["origin"] for m in exempted[0]["members"]}
        self.assertEqual(origins, {"F:v1-train": "v1", "F:v2-dev": "v2"})
        self.assertEqual(report["controls"]["cross_population_component_split_exemptions_unused"], [])

    def test_exemption_stops_matching_once_the_cross_population_component_grows(self) -> None:
        # The self-invalidating property ADR-0850 established, preserved here:
        # an exemption names an EXACT fact-id set, and stops applying the
        # moment the live union graph enlarges the component it names.
        self.facts.update(
            {"F:v1-train": fact("F:v1-train"), "F:v2-dev": fact("F:v2-dev", ["F:v1-train"])}
        )
        self.v1["entries"] = [unshared_entry("F:v1-train", "train")]
        self.v2["entries"] = [unshared_entry("F:v2-dev", "development")]
        self.v2["cross_population_component_split_exemptions"] = [
            {
                "component_fact_ids": sorted(["F:v1-train", "F:v2-dev"]),
                "reason": "test exemption",
                "authority": "test",
                "date": "2026-08-30",
            }
        ]
        report = MODULE.build_cross_population_report(self.v1, self.v2, self.facts)
        self.assertEqual(report["controls"]["component_split_leaks"], [])

        # A new v2 fact starts depending on F:v1-train, joining the same
        # weakly-connected component without being named in the exemption.
        self.facts["F:v2-new"] = fact("F:v2-new", ["F:v1-train"])
        self.v2["entries"].append(unshared_entry("F:v2-new", "development"))
        with self.assertRaisesRegex(MODULE.NurseryError, "cross-population"):
            MODULE.build_cross_population_report(self.v1, self.v2, self.facts)

    def test_cross_population_longitudinal_overlap_fails_closed_and_can_be_exempted(self) -> None:
        self.facts.update(
            {
                "F:nat-zero-add": fact("F:nat-zero-add"),
                "F:nat-mul-one": fact("F:nat-mul-one", ["F:nat-zero-add"]),
                "F:v2-leak": fact("F:v2-leak", ["F:nat-mul-one"]),
            }
        )
        self.v1["entries"] = [
            entry("F:nat-zero-add", "longitudinal"),
            entry("F:nat-mul-one", "longitudinal"),
        ]
        self.v2["entries"] = [unshared_entry("F:v2-leak", "development")]
        with self.assertRaisesRegex(MODULE.NurseryError, "shares a component with Autogenesis-1"):
            MODULE.build_cross_population_report(self.v1, self.v2, self.facts)

        longitudinal_component = sorted(["F:v2-leak", "F:nat-mul-one", "F:nat-zero-add"])
        self.v2["cross_population_component_split_exemptions"] = [
            {
                "component_fact_ids": longitudinal_component,
                "reason": "test exemption",
                "authority": "test",
                "date": "2026-08-30",
            }
        ]
        report = MODULE.build_cross_population_report(self.v1, self.v2, self.facts)
        self.assertEqual(report["controls"]["evaluation_longitudinal_component_overlap"], [])
        self.assertEqual(
            report["controls"]["evaluation_longitudinal_component_overlap_exempted"],
            ["F:v2-leak"],
        )

    def test_clean_union_report_is_deterministic_and_addressed(self) -> None:
        self.facts.update({"F:v1-a": fact("F:v1-a"), "F:v2-a": fact("F:v2-a")})
        self.v1["entries"] = [unshared_entry("F:v1-a", "train")]
        self.v2["entries"] = [unshared_entry("F:v2-a", "development")]
        first = MODULE.build_cross_population_report(self.v1, self.v2, self.facts)
        second = MODULE.build_cross_population_report(
            copy.deepcopy(self.v1), copy.deepcopy(self.v2), copy.deepcopy(self.facts)
        )
        self.assertEqual(first, second)
        self.assertEqual(first["population"]["v1_entries"], 1)
        self.assertEqual(first["population"]["v2_entries"], 1)
        self.assertEqual(first["population"]["union_entries"], 2)
        unsigned = dict(first)
        claimed = unsigned.pop("report_sha256")
        self.assertEqual(claimed, MODULE.digest(unsigned))

    def test_stale_exemption_matching_no_live_component_is_reported_as_unused(self) -> None:
        # Regression guard: a first cut of this reporting field hardcoded []
        # and NO test in this suite caught it, because every exemption test
        # so far named an exemption that DOES match a live crossing. An
        # exemption whose fact ids no longer form the component it once
        # named (e.g. after an unrelated ledger edit severs the dependency
        # edge) must show up here, not vanish silently.
        self.facts.update({"F:v1-a": fact("F:v1-a"), "F:v2-a": fact("F:v2-a")})
        self.v1["entries"] = [unshared_entry("F:v1-a", "train")]
        self.v2["entries"] = [unshared_entry("F:v2-a", "development")]
        # F:v1-a and F:v2-a are NOT connected by any depends_on edge, so this
        # named pair's digest never matches any live weakly-connected
        # component (each is its own singleton component instead).
        self.v2["cross_population_component_split_exemptions"] = [
            {
                "component_fact_ids": sorted(["F:v1-a", "F:v2-a"]),
                "reason": "stale test exemption",
                "authority": "test",
                "date": "2026-08-30",
            }
        ]
        report = MODULE.build_cross_population_report(self.v1, self.v2, self.facts)
        self.assertEqual(report["controls"]["component_split_leaks"], [])
        self.assertEqual(report["controls"]["component_split_leaks_exempted"], [])
        unused = report["controls"]["cross_population_component_split_exemptions_unused"]
        self.assertEqual(len(unused), 1)
        self.assertEqual(unused[0]["component_fact_ids"], ["F:v1-a", "F:v2-a"])


if __name__ == "__main__":
    unittest.main()
