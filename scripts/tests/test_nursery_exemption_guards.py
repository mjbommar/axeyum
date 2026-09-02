"""Controls for the two nursery split-exemption guards added 2026-09-01.

`check-autogenesis-nursery.py`'s `component_split_exemptions` (ADR-0850) let a
reviewer record that one declared-dependency component's partition crossing is
benign. Two properties that every producer already respected were never
ENFORCED by the gate, and both are the exact shape this repository keeps
finding it does not have -- a guard nobody wrote, which mutation testing cannot
report because there is nothing to delete:

* **No exemption may name a `held-out` row.** ADR-0850's whole safety argument
  is "no held-out member"; every recorded reason asserts it and
  `rescope-nursery-exemption.py` exits 2 rather than write one. The gate would
  have accepted a hand-written exemption suppressing a train/held-out crossing
  with a plausible reason string and gone green. Held-out blindness, once
  spent, cannot be un-spent: such a crossing is a finding and an ADR-0542
  amendment, never a suppression.

* **A recorded exemption must match a live crossing component.** The digest
  pinning is what makes an exemption self-invalidating, but until this change
  the invalidation was observable only in `--json` output. Measured
  2026-09-01: the committed 10-member factorial exemption had gone stale at a
  live 11 and the 258-member cross-population one at a live 274, and in both
  cases the operator saw only "component crosses evaluation partitions" -- no
  indication that a reviewed decision no longer applied to anything.

Why these live in their own module rather than beside their siblings in
`test_check_autogenesis_nursery.py`: `scripts/tests/mutation_controls.py`
refuses to measure a suite whose BASELINE is not green, and that suite's
`LiveManifestTests` reads the committed `nursery-v2-extension.json`, whose
cross-population exemption is stale for a reason outside this lane's remit.
Registering the whole module for mutation would have reported
`BASELINE IS NOT GREEN` and measured nothing. This module depends on no
committed manifest, so each guard here is mutation-verified to kill exactly
one test.

Every guard case is paired with a POSITIVE CONTROL that must still pass: a
guard which rejected every exemption, or every population, would satisfy the
negative case alone and measure nothing.
"""

from __future__ import annotations

import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest


SCRIPT = Path(__file__).parents[1] / "check-autogenesis-nursery.py"
SPEC = importlib.util.spec_from_file_location("check_autogenesis_nursery_guards", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


# THE FIXTURE POLICY IS PINNED TO THE PREREGISTERED ROLES, not inherited from
# the committed manifest.
#
# Every scenario in this module uses a `train`/`development` component as its
# crossing, and ADR-1564 made that pair legal: `train` is now the TRAINING
# partition. Reading the live policy would silently turn each exemption
# scenario into a population with no crossing at all -- the guard would still
# be there and nothing would be exercising it, which is the shape this whole
# module exists to prevent. Pinning the ORIGINAL roles keeps each test's
# subject the exemption guard; `AmendedPartitionRoleTests` below is where the
# roles themselves are the subject.
PREREGISTERED_ROLES = {
    "required_evaluation_partitions": ["train", "development", "held-out"],
    "training_partitions": [],
    "blind_partitions": ["held-out"],
}


def with_preregistered_roles(nursery: dict) -> dict:
    """`nursery`, with its policy pinned to the preregistered roles."""
    nursery["policy"] = {**nursery["policy"], **PREREGISTERED_ROLES}
    return nursery


def fact(fact_id: str, dependencies: list[str] | None = None) -> dict:
    return {"id": fact_id, "depends_on": dependencies or []}


def entry(fact_id: str, partition: str) -> dict:
    """A nursery row whose family/proof_shape/source_group are UNIQUE to it.

    Sharing any of the three across partitions trips the family-, shape- and
    source-group-leak checks as well, which would pollute an exemption test's
    message with unrelated, unexempted violations.
    """
    return {
        "fact_id": fact_id,
        "partition": partition,
        "provenance_class": "project-constructed",
        "family": f"family-{fact_id}",
        "proof_shape": f"shape-{fact_id}",
        "source_group": f"group-{fact_id}",
        "route_hypotheses": ["kernel"],
        "mutation_of": None,
        "answer_access": "withheld-during-episode",
    }


def exemption(fact_ids: list[str], reason: str = "test exemption") -> dict:
    return {
        "component_fact_ids": sorted(fact_ids),
        "reason": reason,
        "authority": "scripts/tests/test_nursery_exemption_guards.py",
        "date": "2026-09-01",
    }


class ExemptionGuardTests(unittest.TestCase):
    """One-file population, no committed manifest, so the baseline is green."""

    def setUp(self) -> None:
        repository = json.loads(MODULE.NURSERY.read_text())
        self.nursery = with_preregistered_roles(copy.deepcopy(repository))
        self.nursery["state"] = "foundation-only"
        self.nursery["entries"] = [
            row for row in repository["entries"] if row["partition"] == "longitudinal"
        ]
        self.nursery["component_split_exemptions"] = []
        self.result = {"verdict": "autogenesis-1-passed"}
        self.facts = {
            "F:nat-zero-add": fact("F:nat-zero-add"),
            "F:nat-mul-one": fact("F:nat-mul-one", ["F:nat-zero-add"]),
        }

    def _train_held_crossing(self) -> None:
        self.facts.update(
            {"F:train": fact("F:train"), "F:held": fact("F:held", ["F:train"])}
        )
        self.nursery["entries"].extend(
            [entry("F:train", "train"), entry("F:held", "held-out")]
        )

    def _train_dev_crossing(self) -> None:
        self.facts.update(
            {"F:train": fact("F:train"), "F:dev": fact("F:dev", ["F:train"])}
        )
        self.nursery["entries"].extend(
            [entry("F:train", "train"), entry("F:dev", "development")]
        )

    # -- guard 1: an exemption may never name a held-out row ----------------

    def test_exemption_naming_a_held_out_row_is_refused(self) -> None:
        self._train_held_crossing()
        self.nursery["component_split_exemptions"] = [
            exemption(
                ["F:train", "F:held"],
                "a plausible reason, which must not be enough on its own",
            )
        ]
        with self.assertRaisesRegex(MODULE.NurseryError, "may never cover a held-out fact"):
            MODULE.build_report(self.nursery, self.facts, self.result)

    def test_an_equivalent_exemption_over_train_and_development_is_accepted(self) -> None:
        # POSITIVE CONTROL for the guard above. The identical mechanism, with
        # the held-out row replaced by a development one, must still work --
        # otherwise a guard rejecting every exemption would pass the test
        # above while destroying ADR-0850's mechanism.
        self._train_dev_crossing()
        self.nursery["component_split_exemptions"] = [exemption(["F:train", "F:dev"])]
        report = MODULE.build_report(self.nursery, self.facts, self.result)
        self.assertEqual(report["controls"]["component_split_leaks"], [])
        members = sorted(
            m["fact_id"]
            for m in report["controls"]["component_split_leaks_exempted"][0]["members"]
        )
        self.assertEqual(members, ["F:dev", "F:train"])

    def test_a_held_out_crossing_still_fails_when_nothing_is_exempted(self) -> None:
        # SECOND POSITIVE CONTROL: the held-out crossing must be reported as a
        # crossing when no exemption is present, so the test above is measuring
        # the exemption guard rather than the crossing check it sits behind.
        self._train_held_crossing()
        with self.assertRaisesRegex(MODULE.NurseryError, "crosses evaluation partitions"):
            MODULE.build_report(self.nursery, self.facts, self.result)

    # -- guard 2: a recorded exemption must match a live crossing -----------

    def test_stale_exemption_matching_no_live_component_fails_the_gate(self) -> None:
        # `F:lonely` depends on nothing and nothing depends on it, so it is its
        # own singleton component and crosses no partition. An exemption naming
        # it therefore matches no live CROSSING component: a reviewed claim
        # about a set of facts that is not the set the gate sees.
        self._train_dev_crossing()
        self.facts["F:lonely"] = fact("F:lonely")
        self.nursery["entries"].append(entry("F:lonely", "development"))
        self.nursery["component_split_exemptions"] = [
            exemption(["F:train", "F:dev"], "current, must stay silent"),
            exemption(["F:lonely"], "stale: F:lonely crosses nothing"),
        ]
        with self.assertRaisesRegex(
            MODULE.NurseryError, "matches no live crossing component"
        ):
            MODULE.build_report(self.nursery, self.facts, self.result)

    def test_the_same_population_passes_once_the_stale_entry_is_dropped(self) -> None:
        # POSITIVE CONTROL for the guard above: identical population, only the
        # stale entry removed. A guard that fired on any exemptions array at
        # all -- or on any population with a non-crossing fact in it -- would
        # pass the test above and fail this one.
        self._train_dev_crossing()
        self.facts["F:lonely"] = fact("F:lonely")
        self.nursery["entries"].append(entry("F:lonely", "development"))
        self.nursery["component_split_exemptions"] = [
            exemption(["F:train", "F:dev"], "current, must stay silent")
        ]
        report = MODULE.build_report(self.nursery, self.facts, self.result)
        self.assertEqual(report["controls"]["component_split_leaks"], [])
        self.assertEqual(report["controls"]["component_split_exemptions_unused"], [])

    def test_a_grown_component_reports_BOTH_the_crossing_and_the_void_exemption(
        self,
    ) -> None:
        # This is the incident shape, and the reason the stale check is fatal
        # rather than a JSON field. On 2026-09-01 a `depends_on` repair grew an
        # exempted component by one member: the digest stopped matching, so the
        # gate reported the ENLARGED crossing -- correctly -- and said nothing
        # at all about the reviewed decision that had just been voided. Both
        # facts have to reach the operator, because the second one is what says
        # the first is a re-review rather than a new finding.
        self._train_dev_crossing()
        self.nursery["component_split_exemptions"] = [exemption(["F:train", "F:dev"])]
        MODULE.build_report(self.nursery, self.facts, self.result)  # green as-is

        self.facts["F:grown"] = fact("F:grown", ["F:train"])
        self.nursery["entries"].append(entry("F:grown", "development"))
        with self.assertRaises(MODULE.NurseryError) as caught:
            MODULE.build_report(self.nursery, self.facts, self.result)
        message = str(caught.exception)
        self.assertIn("crosses evaluation partitions", message)
        self.assertIn("matches no live crossing component", message)


def v2_extension(entries: list[dict], exemptions: list[dict] | None = None) -> dict:
    extension = {
        "kind": "axeyum-autogenesis-nursery-extension",
        "extends": "artifacts/autogenesis/nursery-v1.json",
        "entries": entries,
    }
    if exemptions is not None:
        extension["cross_population_component_split_exemptions"] = exemptions
    return extension


class CrossPopulationExemptionGuardTests(unittest.TestCase):
    """The same two guards over the v1-union-v2 report, which validates its
    exemptions through the same `validate_exemptions` and had the same gap."""

    def setUp(self) -> None:
        repository = json.loads(MODULE.NURSERY.read_text())
        self.v1 = with_preregistered_roles(copy.deepcopy(repository))
        self.v1["entries"] = [
            row for row in repository["entries"] if row["partition"] == "longitudinal"
        ]
        self.v1["component_split_exemptions"] = []
        self.facts = {
            "F:nat-zero-add": fact("F:nat-zero-add"),
            "F:nat-mul-one": fact("F:nat-mul-one", ["F:nat-zero-add"]),
        }

    def test_cross_population_exemption_naming_a_held_out_row_is_refused(self) -> None:
        self.facts.update(
            {"F:v1-a": fact("F:v1-a"), "F:v2-a": fact("F:v2-a", ["F:v1-a"])}
        )
        self.v1["entries"] = [entry("F:v1-a", "train")]
        v2 = v2_extension(
            [entry("F:v2-a", "held-out")], [exemption(["F:v1-a", "F:v2-a"])]
        )
        with self.assertRaisesRegex(MODULE.NurseryError, "may never cover a held-out fact"):
            MODULE.build_cross_population_report(self.v1, v2, self.facts)

    def test_cross_population_exemption_over_train_and_development_is_accepted(self) -> None:
        # POSITIVE CONTROL: same shape, development instead of held-out.
        self.facts.update(
            {"F:v1-a": fact("F:v1-a"), "F:v2-a": fact("F:v2-a", ["F:v1-a"])}
        )
        self.v1["entries"] = [entry("F:v1-a", "train")]
        v2 = v2_extension(
            [entry("F:v2-a", "development")], [exemption(["F:v1-a", "F:v2-a"])]
        )
        report = MODULE.build_cross_population_report(self.v1, v2, self.facts)
        self.assertEqual(report["controls"]["component_split_leaks"], [])

    def test_stale_cross_population_exemption_fails_the_gate(self) -> None:
        # F:v1-a and F:v2-a share no depends_on edge, so the named pair is not
        # a live component at all -- each is its own singleton.
        self.facts.update({"F:v1-a": fact("F:v1-a"), "F:v2-a": fact("F:v2-a")})
        self.v1["entries"] = [entry("F:v1-a", "train")]
        v2 = v2_extension(
            [entry("F:v2-a", "development")], [exemption(["F:v1-a", "F:v2-a"])]
        )
        with self.assertRaisesRegex(
            MODULE.NurseryError, "matches no live crossing component"
        ):
            MODULE.build_cross_population_report(self.v1, v2, self.facts)

    def test_the_same_union_passes_with_no_exemption_recorded(self) -> None:
        # POSITIVE CONTROL for the guard above.
        self.facts.update({"F:v1-a": fact("F:v1-a"), "F:v2-a": fact("F:v2-a")})
        self.v1["entries"] = [entry("F:v1-a", "train")]
        v2 = v2_extension([entry("F:v2-a", "development")], [])
        report = MODULE.build_cross_population_report(self.v1, v2, self.facts)
        self.assertEqual(report["controls"]["component_split_leaks"], [])
        self.assertEqual(
            report["controls"]["cross_population_component_split_exemptions_unused"], []
        )


class AmendedEdgeContractionTests(unittest.TestCase):
    """Controls for the per-edge amendment contraction (ADR-1563).

    `components` skips the adjacency of any edge `check-partition-edges.py`
    honours as an amendment. That is what lets the 45 edges into the two pinned
    longitudinal bootstrap lemmas stop fusing the regression chain into the
    evaluation population WITHOUT a hardcoded rule in this file -- a hardcoded
    rule would have made the longitudinal-overlap check structurally unable to
    fail, and a check that cannot fail is worse than no check.

    So the pair that matters is `..._is_a_leak_without_the_amendment` and
    `..._is_contracted_by_the_amendment`: identical populations, differing only
    in whether one reviewed line exists. The third test drives the DIRECTION
    argument -- longitudinal DEPENDING ON an evaluation fact is a real leak and
    the class cannot cover it -- and the fourth is that a refused amendment
    stops the report rather than silently restoring every edge.

    The DATA root is a throwaway tree; the shipped `check-partition-edges.py`
    is still the implementation under test, loaded from the real checkout by
    `amended_edges`.
    """

    BOOTSTRAP = {"from": "F:dev", "to": "F:nat-zero-add",
                 "class": "depends-on-longitudinal-bootstrap",
                 "reason": "the bootstrap lemma is shared by every partition",
                 "date": "2026-09-02"}

    def setUp(self) -> None:
        repository = json.loads(MODULE.NURSERY.read_text())
        self.nursery = with_preregistered_roles(copy.deepcopy(repository))
        self.nursery["state"] = "foundation-only"
        self.nursery["entries"] = [
            row for row in repository["entries"] if row["partition"] == "longitudinal"
        ]
        self.nursery["component_split_exemptions"] = []
        self.result = {"verdict": "autogenesis-1-passed"}
        self.facts = {
            "F:nat-zero-add": fact("F:nat-zero-add"),
            "F:nat-mul-one": fact("F:nat-mul-one", ["F:nat-zero-add"]),
        }
        scratch = Path("/data0/axeyum/scratch")
        self._tmp = tempfile.TemporaryDirectory(
            dir=scratch if scratch.is_dir() else None)
        self.addCleanup(self._tmp.cleanup)
        self.data_root = Path(self._tmp.name) / "tree"
        (self.data_root / "artifacts/autogenesis").mkdir(parents=True)
        saved = MODULE.PARTITION_EDGE_ROOT
        MODULE.PARTITION_EDGE_ROOT = self.data_root
        self.addCleanup(setattr, MODULE, "PARTITION_EDGE_ROOT", saved)

    def install(self, amendments: list[dict]) -> None:
        """Mirror this fixture's rows into the data root the amendments read."""
        (self.data_root / "artifacts/autogenesis/nursery-v1.json").write_text(
            json.dumps({"kind": "axeyum-autogenesis-nursery",
                        "entries": [{"fact_id": row["fact_id"],
                                     "partition": row["partition"]}
                                    for row in self.nursery["entries"]]})
        )
        (self.data_root
         / "artifacts/autogenesis/partition-edge-amendments-v1.json").write_text(
            json.dumps({"kind": "axeyum-partition-edge-amendments",
                        "amendments": amendments})
        )
        facts_dir = self.data_root / "artifacts/facts"
        facts_dir.mkdir(parents=True, exist_ok=True)
        for fact_id, body in self.facts.items():
            (facts_dir / f"{fact_id.replace(':', '-')}.json").write_text(
                json.dumps(body))

    def _dev_depends_on_bootstrap(self) -> None:
        """`F:dev` [development] depends on `F:nat-zero-add` [longitudinal]."""
        self.facts["F:dev"] = fact("F:dev", ["F:nat-zero-add"])
        self.nursery["entries"].append(entry("F:dev", "development"))

    def test_an_edge_into_the_bootstrap_lemma_is_a_leak_without_the_amendment(
        self,
    ) -> None:
        # THE NEGATIVE HALF. Without it, the accept case below is satisfied by
        # a graph in which nothing was ever fused, and the contraction would be
        # measuring nothing.
        self._dev_depends_on_bootstrap()
        self.install([])
        with self.assertRaisesRegex(
            MODULE.NurseryError, "shares a component with Autogenesis-1"
        ):
            MODULE.build_report(self.nursery, self.facts, self.result)

    def test_an_edge_into_the_bootstrap_lemma_is_contracted_by_the_amendment(
        self,
    ) -> None:
        # THE ACCEPT HALF. Identical population, one reviewed amendment.
        self._dev_depends_on_bootstrap()
        self.install([self.BOOTSTRAP])
        report = MODULE.build_report(self.nursery, self.facts, self.result)
        self.assertEqual(
            report["controls"]["evaluation_longitudinal_component_overlap"], [])
        self.assertEqual(report["controls"]["component_split_leaks"], [])

    def test_the_contraction_is_directed_and_the_reverse_edge_still_leaks(
        self,
    ) -> None:
        # THE DIRECTION ARGUMENT, driven in ONE fixture rather than asserted.
        # `F:dev` -> `F:nat-zero-add` is amended and contracted. `F:nat-mul-one`
        # -> `F:dev2` is the REVERSE shape -- the bootstrap lemma depending on a
        # drawn development fact, which pulls a drawn result into the regression
        # chain -- and no amendment can cover it, because the class is
        # re-derived from the TARGET's partition and `F:dev2` is development.
        # So the gate stays red on the leaking direction while the benign one is
        # gone. A contraction that ignored direction would clear both, and this
        # test is the only thing that would notice.
        #
        # BOTH DIRECTIONS BETWEEN THE SAME PAIR, deliberately. That is the only
        # fixture an undirected contraction can be caught by, and it is not a
        # contrivance: `check-partition-edges.py` treats `a depends_on b` and
        # `b depends_on a` as two separate things somebody did, so an amendment
        # for one says nothing whatever about the other.
        self._dev_depends_on_bootstrap()
        self.facts["F:nat-zero-add"] = fact("F:nat-zero-add", ["F:dev"])
        self.install([self.BOOTSTRAP])
        with self.assertRaisesRegex(
            MODULE.NurseryError, "shares a component with Autogenesis-1"
        ):
            MODULE.build_report(self.nursery, self.facts, self.result)

    def test_a_refused_amendment_stops_the_report_rather_than_restoring_edges(
        self,
    ) -> None:
        # A malformed amendment must not read as "no amendments". Swallowing it
        # would restore every edge and print a STRICTER-looking report, which is
        # the one direction a reader does not question.
        self._dev_depends_on_bootstrap()
        self.install([{"from": "F:dev", "to": "F:nat-zero-add",
                       "date": "2026-09-02"}])
        with self.assertRaisesRegex(MODULE.NurseryError, "NOT honoured"):
            MODULE.build_report(self.nursery, self.facts, self.result)


class AmendedPartitionRoleTests(unittest.TestCase):
    """Controls for ADR-1564: the evaluated partitions come from the POLICY.

    `check-autogenesis-nursery.py` used to hold `EVALUATION_PARTITIONS =
    {"train", "development", "held-out"}` as a module literal three lines from
    a `validate_policy` that separately asserted the manifest said the same
    triple -- two copies of one decision, with the gate answering from the copy
    that was never the authority. These tests hand the SAME population two
    different policies and require two different answers, which is the only
    way to distinguish a derived set from a literal that happens to agree.
    """

    def setUp(self) -> None:
        repository = json.loads(MODULE.NURSERY.read_text())
        self.nursery = copy.deepcopy(repository)
        self.nursery["state"] = "foundation-only"
        self.nursery["entries"] = [
            row for row in repository["entries"] if row["partition"] == "longitudinal"
        ]
        self.nursery["component_split_exemptions"] = []
        self.result = {"verdict": "autogenesis-1-passed"}
        self.facts = {
            "F:nat-zero-add": fact("F:nat-zero-add"),
            "F:nat-mul-one": fact("F:nat-mul-one", ["F:nat-zero-add"]),
            "F:train": fact("F:train"),
            "F:dev": fact("F:dev", ["F:train"]),
        }
        self.nursery["entries"].extend(
            [entry("F:train", "train"), entry("F:dev", "development")]
        )

    def roles(self, **overrides: object) -> None:
        self.nursery["policy"] = {**self.nursery["policy"], **overrides}

    def test_a_train_development_component_leaks_under_the_preregistered_roles(
        self,
    ) -> None:
        """The BEFORE half of the pair. With train evaluated, the component is
        a leak -- which is what makes the AFTER half a measurement of the
        policy rather than of the fixture."""
        self.roles(**PREREGISTERED_ROLES)
        with self.assertRaisesRegex(
            MODULE.NurseryError, "crosses evaluation partitions"
        ):
            MODULE.build_report(self.nursery, self.facts, self.result)

    def test_the_same_component_does_not_leak_once_train_is_a_training_partition(
        self,
    ) -> None:
        """THE AFTER HALF. Identical facts, identical entries, identical
        `depends_on` edge; only `required_evaluation_partitions` differs. A
        literal evaluation set in the gate keeps this red."""
        self.roles(required_evaluation_partitions=["development", "held-out"],
                   training_partitions=["train"],
                   blind_partitions=["held-out"])
        report = MODULE.build_report(self.nursery, self.facts, self.result)
        self.assertEqual(report["controls"]["component_split_leaks"], [])
        self.assertEqual(
            report["population"]["partitions"]["train"], 1,
            "the train row is still DRAWN; it is just not evaluated")

    def test_a_development_held_out_component_still_leaks_after_the_amendment(
        self,
    ) -> None:
        """The seal ADR-1564 does not touch. Two evaluation partitions fused
        by a real `depends_on` edge is the same finding it always was."""
        self.facts["F:held"] = fact("F:held", ["F:dev"])
        self.nursery["entries"].append(entry("F:held", "held-out"))
        self.roles(required_evaluation_partitions=["development", "held-out"],
                   training_partitions=["train"],
                   blind_partitions=["held-out"])
        with self.assertRaisesRegex(
            MODULE.NurseryError, "crosses evaluation partitions"
        ):
            MODULE.build_report(self.nursery, self.facts, self.result)

    def test_a_held_out_train_component_still_leaks_after_the_amendment(
        self,
    ) -> None:
        """THE SEAL ADR-1564 DROPPED BY ACCIDENT, and the reason this test
        exists at all.

        ADR-1564's own table marks `held-out -> train` in bold as a crossing
        that SURVIVES the amendment ("blind seal"), and
        `check-partition-edges.py` does apply it -- the six edges baselined in
        `partition-edge-baseline-v1.json` are exactly this shape. This gate
        did not. Its leak check filtered `entries` down to the EVALUATED rows
        before counting a component's partitions, so once `train` left the
        evaluation set a component holding only `held-out` and `train` rows
        collapsed to one evaluated partition and raised nothing. Measured
        2026-09-02, before the repair: this population passed.

        The component here is ISOLATED from `setUp`'s `F:dev -> F:train` one
        on purpose. Were it fused, the leak would be reported for the
        ordinary reason -- two evaluation partitions, `development` and
        `held-out`, in one component -- and this test would pass with the
        blind seal deleted, measuring the confound instead of the subject.

        Its positive control is
        `test_the_same_component_does_not_leak_once_train_is_a_training_partition`
        above: the same roles over a `train`/`development` component must
        still come back CLEAN, so a rule that simply called every
        train-touching component a leak fails that one.
        """
        self.facts["F:trainB"] = fact("F:trainB")
        self.facts["F:heldB"] = fact("F:heldB", ["F:trainB"])
        self.nursery["entries"].extend(
            [entry("F:trainB", "train"), entry("F:heldB", "held-out")]
        )
        self.roles(required_evaluation_partitions=["development", "held-out"],
                   training_partitions=["train"],
                   blind_partitions=["held-out"])
        with self.assertRaisesRegex(
            MODULE.NurseryError, "crosses evaluation partitions"
        ) as raised:
            MODULE.build_report(self.nursery, self.facts, self.result)
        message = str(raised.exception)
        # The finding must name the BLIND row, not merely fire somewhere.
        self.assertIn("F:heldB", message)
        self.assertIn("F:trainB", message)
        # ...and it must not have fired on the benign train/development
        # component that `setUp` builds, which the positive control above
        # requires to stay clean.
        self.assertNotIn("F:dev ", message)

    def test_a_policy_naming_no_evaluation_partition_is_refused(self) -> None:
        """A gate that cannot fail is worse than no gate. With nothing
        evaluated, every component sits in at most one evaluation partition and
        this report would be clean over a split it never looked at."""
        self.roles(required_evaluation_partitions=[],
                   training_partitions=["train"],
                   blind_partitions=["held-out"])
        with self.assertRaisesRegex(
            MODULE.NurseryError,
            "required_evaluation_partitions must be a non-empty"
        ):
            MODULE.build_report(self.nursery, self.facts, self.result)

    def test_a_policy_that_seals_no_blind_partition_is_refused(self) -> None:
        """`blind_partitions: []` unseals the held-out population by data
        edit. Blindness once spent cannot be un-spent, so the seal is not a
        field a producer may empty."""
        self.roles(required_evaluation_partitions=["development", "held-out"],
                   training_partitions=["train"],
                   blind_partitions=[])
        with self.assertRaisesRegex(
            MODULE.NurseryError, "blind_partitions must be a non-empty subset"
        ):
            MODULE.build_report(self.nursery, self.facts, self.result)

    def test_a_partition_that_is_both_training_and_evaluation_is_refused(
        self,
    ) -> None:
        """A partition cannot be what producers build on AND what they are
        scored against; reading it as either silently picks a side."""
        self.roles(required_evaluation_partitions=["train", "development",
                                                   "held-out"],
                   training_partitions=["train"],
                   blind_partitions=["held-out"])
        with self.assertRaisesRegex(
            MODULE.NurseryError,
            "is both a training and an evaluation partition"
        ):
            MODULE.build_report(self.nursery, self.facts, self.result)


class ScoredResidueContractionTests(unittest.TestCase):
    """The nursery gate honours `scored-evaluation-residue` (ADR-1566).

    ADR-1565 left this gate red on ONE component, whose held-out members are
    all rows of one family that was SCORED against a preregistered protocol.
    ADR-1566 contracts those edges out through the same mechanism ADR-1563
    used -- `check-partition-edges.py`'s own `load_amendments` and
    `edge_is_amended`, never a rule written twice -- and this class is what
    keeps the mechanism from becoming a hole.

    THE BLIND SEAL MUST SURVIVE. Three refusals, each a synthetic population
    that differs from the accept case in exactly one thing:

      * the record does not exist (nothing was scored, so there is no
        evaluation whose residue this could be);
      * the edge runs INTO the blind row (blindness spent, not recorded);
      * the edge PREDATES the preregistration (not created by the evaluation).

    Each of the three must fail this gate, not merely fail the edge gate: a
    refused amendment raises here rather than silently restoring the edge, and
    that is the property that makes the two gates describe one tree.

    THE DATA ROOT IS A REAL GIT REPOSITORY. The preregistration clause is a
    question about the commit graph, and a fixture that could not answer it
    would turn `strictly_precedes` into an unconditional refusal -- which
    would pass every test here for the wrong reason and hide the accept case
    being impossible.
    """

    # WHAT A SEAL TEST ASSERTS, AND WHY IT IS NOT THE REFUSAL MESSAGE.
    #
    # The property is "this population does not go green". Whether the gate
    # refuses the amendment (`NOT honoured`) or reports the restored component
    # (`crosses evaluation partitions`) is a detail of WHICH mechanism caught
    # it, and pinning that here would make N3 -- whose subject is that a
    # refused amendment stops the report rather than restoring edges -- kill
    # all four tests instead of the one it is about. WHICH clause refuses each
    # of these three shapes is measured where it belongs, in
    # `scripts/tests/test_check_partition_edges.py`, at one kill each
    # (M24/M26/M27).
    STILL_RED = "NOT honoured|crosses evaluation partitions"

    SALT = "fedcba9876543210" * 4
    RECORD_ID = "test-evaluation-1"
    FAMILY = "scored-fixture-family"
    AMENDED_ROLES = {
        "required_evaluation_partitions": ["development", "held-out"],
        "training_partitions": ["train"],
        "blind_partitions": ["held-out"],
    }

    def setUp(self) -> None:
        repository = json.loads(MODULE.NURSERY.read_text())
        self.nursery = copy.deepcopy(repository)
        self.nursery["policy"] = {**self.nursery["policy"], **self.AMENDED_ROLES}
        self.nursery["state"] = "foundation-only"
        self.nursery["entries"] = [
            row for row in repository["entries"] if row["partition"] == "longitudinal"
        ]
        self.nursery["component_split_exemptions"] = []
        self.result = {"verdict": "autogenesis-1-passed"}
        self.facts = {
            "F:nat-zero-add": fact("F:nat-zero-add"),
            "F:nat-mul-one": fact("F:nat-mul-one", ["F:nat-zero-add"]),
            "F:dev": fact("F:dev"),
            "F:blind": fact("F:blind"),
        }
        blind_row = entry("F:blind", "held-out")
        blind_row["family"] = self.FAMILY
        self.nursery["entries"].extend([entry("F:dev", "development"), blind_row])

        scratch = Path("/data0/axeyum/scratch")
        self._tmp = tempfile.TemporaryDirectory(
            dir=scratch if scratch.is_dir() else None)
        self.addCleanup(self._tmp.cleanup)
        self.data_root = Path(self._tmp.name) / "tree"
        (self.data_root / "artifacts/autogenesis").mkdir(parents=True)
        (self.data_root / "artifacts/facts").mkdir(parents=True)
        saved = MODULE.PARTITION_EDGE_ROOT
        MODULE.PARTITION_EDGE_ROOT = self.data_root
        self.addCleanup(setattr, MODULE, "PARTITION_EDGE_ROOT", saved)
        self.git("init", "-q", "-b", "main")
        self.git("config", "user.email", "fixture@example.invalid")
        self.git("config", "user.name", "fixture")

    # -- fixture construction ----------------------------------------------

    def git(self, *args: str) -> subprocess.CompletedProcess:
        done = subprocess.run(["git", *args], cwd=self.data_root,
                              capture_output=True, text=True, timeout=60)
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        return done

    def commit(self, message: str) -> str:
        self.git("add", "-A")
        self.git("commit", "-q", "-m", message)
        return self.git("rev-parse", "HEAD").stdout.strip()

    def digest_of(self, fact_id: str) -> str:
        return hashlib.sha256(f"{self.SALT}:{fact_id}".encode()).hexdigest()

    def sync(self) -> None:
        """Mirror the in-memory fixture into the git-backed data root.

        The manifest carries the FAMILY column, because clause (a) is
        re-derived from the live manifests and a fixture that omitted it would
        make the accept case impossible for a reason no message would name.
        """
        root = self.data_root
        (root / "artifacts/autogenesis/nursery-v1.json").write_text(
            json.dumps({"kind": "axeyum-autogenesis-nursery",
                        "policy": self.AMENDED_ROLES,
                        "entries": [{"fact_id": row["fact_id"],
                                     "partition": row["partition"],
                                     "family": row.get("family", "other")}
                                    for row in self.nursery["entries"]]},
                       indent=2, sort_keys=True))
        (root / "artifacts/autogenesis/partition-edge-baseline-v1.json").write_text(
            json.dumps({"kind": "axeyum-partition-edge-baseline",
                        "schema_version": 1, "held_out_salt": self.SALT,
                        "edges": []}, indent=2, sort_keys=True))
        for fact_id, body in self.facts.items():
            (root / f"artifacts/facts/{fact_id.replace(':', '-')}.json"
             ).write_text(json.dumps(body, indent=2, sort_keys=True))

    def write_record(self, protocol_commit: str = "",
                     record_id: str | None = None) -> None:
        (self.data_root
         / "artifacts/autogenesis/holdout-evaluation-v1.json").write_text(
            json.dumps({"kind": "axeyum-holdout-evaluation-record",
                        "record_id": record_id or self.RECORD_ID,
                        "family": self.FAMILY,
                        "state": "scored",
                        "protocol_commit": protocol_commit,
                        "outcomes": [{"fact_id": "F:blind"}]},
                       indent=2, sort_keys=True))

    def write_amendments(self, items: list[dict]) -> None:
        (self.data_root
         / "artifacts/autogenesis/partition-edge-amendments-v1.json").write_text(
            json.dumps({"kind": "axeyum-partition-edge-amendments",
                        "amendments": items}, indent=2, sort_keys=True))

    def residue(self, frm: str, to: str, **overrides: object) -> dict:
        item = {"class": "scored-evaluation-residue",
                "evaluation_record": self.RECORD_ID,
                "from": frm, "to": to,
                "reason": "the residue of a scored evaluation",
                "date": "2026-09-02"}
        item.update(overrides)
        return item

    def build_after(self, amendments: list[dict]) -> dict:
        self.write_amendments(amendments)
        return MODULE.build_report(self.nursery, self.facts, self.result)

    # -- the two commit orders ---------------------------------------------

    def preregister_then_edge(self) -> None:
        """Population, then the protocol commit, THEN the crossing edge."""
        self.write_record()
        self.write_amendments([])
        self.sync()
        head = self.commit("the drawn population, no edges")
        self.write_record(protocol_commit=head)
        self.commit("preregister the scoring protocol")
        self.facts["F:blind"] = fact("F:blind", ["F:dev"])
        self.sync()
        self.commit("close the evaluation")

    def edge_then_preregister(self) -> None:
        """The crossing edge FIRST, the preregistration after it."""
        self.facts["F:blind"] = fact("F:blind", ["F:dev"])
        self.write_record()
        self.write_amendments([])
        self.sync()
        self.commit("the population WITH the edge already in it")
        head = self.git("rev-parse", "HEAD").stdout.strip()
        self.write_record(protocol_commit=head)
        self.commit("preregister the scoring protocol, too late")

    # -- the pair the contraction is measured by ---------------------------

    def test_the_crossing_is_a_leak_without_the_amendment(self) -> None:
        """THE NEGATIVE HALF. Without it the accept case below is satisfied by
        a population in which nothing ever crossed."""
        self.preregister_then_edge()
        with self.assertRaisesRegex(
            MODULE.NurseryError, "crosses evaluation partitions"
        ):
            self.build_after([])

    def test_the_scored_residue_is_contracted_out_of_the_component_graph(
        self,
    ) -> None:
        """THE ACCEPT HALF. Identical population, one reviewed amendment whose
        four clauses all re-derive."""
        self.preregister_then_edge()
        report = self.build_after(
            [self.residue(self.digest_of("F:blind"), "F:dev")])
        self.assertEqual(report["controls"]["component_split_leaks"], [])

    # -- the three seals -----------------------------------------------------

    def test_a_blind_row_citing_a_drawn_row_with_no_record_still_fails(
        self,
    ) -> None:
        """SEAL 1. There is no evaluation, so there is no residue.

        The amendment names a record id `holdout-evaluation-v1.json` does not
        contain -- the shape a lane would write to clear this gate without
        having scored anything. It is refused, and the refusal STOPS the
        report rather than silently restoring the edge.
        """
        self.preregister_then_edge()
        with self.assertRaisesRegex(MODULE.NurseryError, self.STILL_RED):
            self.build_after([self.residue(self.digest_of("F:blind"), "F:dev",
                                           evaluation_record="no-such-record")])

    def test_an_edge_into_the_scored_blind_row_still_fails(self) -> None:
        """SEAL 2. Every other clause holds; only the direction is wrong.

        A drawn row whose proof cites the blind row spends blindness, and no
        evaluation record licenses that retroactively -- the record says what
        was scored, not what may be read.
        """
        self.write_record()
        self.write_amendments([])
        self.sync()
        head = self.commit("the drawn population, no edges")
        self.write_record(protocol_commit=head)
        self.commit("preregister the scoring protocol")
        self.facts["F:dev"] = fact("F:dev", ["F:blind"])
        self.sync()
        self.commit("a drawn row's proof cites the blind row")
        with self.assertRaisesRegex(MODULE.NurseryError, self.STILL_RED):
            self.build_after([self.residue("F:dev", self.digest_of("F:blind"))])

    def test_an_edge_predating_the_preregistration_still_fails(self) -> None:
        """SEAL 3. ADR-1565's argument, inverted.

        Same population, same record, same direction; the edge was simply in
        the tree before the protocol was committed, so it was not created by
        the evaluation and the row was not blind when it was scored.
        """
        self.edge_then_preregister()
        with self.assertRaisesRegex(MODULE.NurseryError, self.STILL_RED):
            self.build_after(
                [self.residue(self.digest_of("F:blind"), "F:dev")])


if __name__ == "__main__":
    unittest.main()
