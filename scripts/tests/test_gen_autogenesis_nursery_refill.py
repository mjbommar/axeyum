"""Controls for scripts/gen-autogenesis-nursery-refill.py (ADR-0615).

One case per guard, each written so that deleting exactly that guard kills
exactly this case. Case 0 is the false-positive control and runs against the
REAL repository: a generator that refuses its own committed manifest is the
same end state as no generator.

The three defects these pin were all live on 2026-08-29 and none of them was
the ceiling arithmetic that a lane had refused on:

  * `reconcile_facts` -- the generator rewrote every fact file it had ever
    emitted, so `--check` reported `39 generated file(s) are stale` and its own
    advice would have overwritten 39 `proved` facts with `open` stubs.
  * `assign_partitions` -- one cycle over the whole family set, so adding four
    families moved SEVEN of the first eight, including a train family with 8 of
    10 mirrors proved into `held-out`.
  * R9 -- 4 of 10 rows in a family preregistered `held-out` today already had a
    declaration of the same Mathlib name in the kernel environment.
"""

from __future__ import annotations

import copy
import importlib.util
import json
import pathlib
import tempfile
import unittest
from unittest import mock

ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/gen-autogenesis-nursery-refill.py"

_spec = importlib.util.spec_from_file_location("gen_nursery_refill", SCRIPT)
MODULE = importlib.util.module_from_spec(_spec)
assert _spec.loader is not None
_spec.loader.exec_module(MODULE)


def entry(family: str, partition: str, name: str, index: int = 0) -> dict:
    return {
        "family": family,
        "partition": partition,
        "source_name": name,
        "fact_id": f"F:test-{family}-{index}",
        "proof_shape": f"{family}:unconditional-equality",
        "source_group": f"Test.{family}",
        "statement": f"statement for {name}",
        "fragment": "Nat",
        "constants": [],
        "module": f"Test.{family}",
    }


def v1_nursery(count: int = MODULE.V1_EVALUATION_ENTRIES) -> dict:
    entries = [{"family": "v1-family", "partition": "train"} for _ in range(count)]
    entries.append({"family": "v1-longitudinal", "partition": "longitudinal"})
    return {"entries": entries}


def frozen_manifest(partitions: dict[str, str]) -> dict:
    entries = [entry(f, p, f"Test.{f}_lemma") for f, p in sorted(partitions.items())]
    body = {"family_partitions": dict(partitions), "entries": entries}
    body["extension_sha256"] = MODULE.digest(
        {k: v for k, v in body.items() if k != "extension_sha256"})
    return body


class Harness:
    """Point the module at a temporary manifest and a synthetic family set."""

    def __init__(self, test: unittest.TestCase, families: dict[str, str],
                 frozen: dict[str, str] | None = None):
        self.dir = pathlib.Path(tempfile.mkdtemp())
        test.addCleanup(lambda: None)
        modules = {f: (f"Test.{f}",) for f in families}
        routes = {f: ("kernel-induction", "kernel-library-application")
                  for f in families}
        extension = self.dir / "nursery-v2-extension.json"
        if frozen is not None:
            extension.write_text(json.dumps(frozen_manifest(frozen)))
        patches = [
            mock.patch.object(MODULE, "FAMILY_MODULES", modules),
            mock.patch.object(MODULE, "FAMILY_ROUTES", routes),
            mock.patch.object(MODULE, "EXTENSION", extension),
        ]
        for patch in patches:
            patch.start()
            test.addCleanup(patch.stop)
        self.extension = extension


class FalsePositiveControl(unittest.TestCase):
    """Case 0 -- the committed manifest must survive every guard."""

    def test_real_manifest_passes_every_guard(self):
        manifest = json.loads(
            (ROOT / "artifacts/autogenesis/nursery-v2-extension.json").read_text())
        real_v1 = json.loads(
            (ROOT / "artifacts/autogenesis/nursery-v1.json").read_text())
        snapshot = json.loads(
            (ROOT / "artifacts/autogenesis/kernel-environment-snapshot-v1.json"
             ).read_text())
        MODULE.guard(manifest["entries"], real_v1, set(snapshot["declarations"]))

    def test_real_manifest_is_its_own_freeze(self):
        frozen = MODULE.frozen_partitions()
        self.assertEqual(frozen, MODULE.assign_partitions())
        self.assertGreater(len(frozen), 0)


class CeilingTests(unittest.TestCase):
    def test_quoted_cohort_over_its_own_ceiling_is_refused(self):
        Harness(self, {"a": "held-out"})
        rows = [entry("a", "held-out", f"Test.a_{i}", i)
                for i in range(MODULE.EXTENSION_CEILING + 1)]
        with self.assertRaisesRegex(MODULE.RefillError, r"R3 the quoted cohort"):
            MODULE.guard(rows, v1_nursery(), set())

    def test_attested_cohort_moving_is_refused(self):
        Harness(self, {"a": "held-out", "b": "development"})
        rows = [entry("a", "held-out", "Test.a_x"),
                entry("b", "development", "Test.b_x")]
        with self.assertRaisesRegex(MODULE.RefillError, r"R3 nursery-v1 holds"):
            MODULE.guard(rows, v1_nursery(MODULE.V1_EVALUATION_ENTRIES - 1), set())

    def test_ceiling_is_the_attested_cohort_not_a_free_number(self):
        self.assertEqual(MODULE.EXTENSION_CEILING, MODULE.V1_EVALUATION_ENTRIES)
        low, high = MODULE.V1_POLICY_RANGE
        self.assertEqual((low, high), (100, 300))


class FreezeTests(unittest.TestCase):
    """R8 and assign_partitions -- the repartition hazard."""

    def test_adding_families_does_not_move_a_frozen_one(self):
        frozen = {"m-alpha": "held-out", "m-bravo": "development",
                  "m-charlie": "train"}
        Harness(self, {**frozen, "a-new": "?", "b-new": "?"}, frozen=frozen)
        assignment = MODULE.assign_partitions()
        for family, partition in frozen.items():
            self.assertEqual(assignment[family], partition, family)
        # ...and the new families get the cycle, restarted at held-out.
        self.assertEqual(assignment["a-new"], "held-out")
        self.assertEqual(assignment["b-new"], "development")

    def test_a_moved_frozen_partition_is_refused(self):
        """The real hazard: the emitted rows AGREE with a shifted assignment,
        so R6 is satisfied and only the freeze can see it. This is what adding
        four families to `FAMILY_MODULES` did on 2026-08-29 -- it moved seven
        of eight -- and it is why R6 is not a substitute for R8."""
        frozen = {"m-alpha": "held-out", "m-bravo": "development"}
        Harness(self, frozen, frozen=frozen)
        shifted = {"m-alpha": "train", "m-bravo": "held-out"}
        rows = [entry("m-alpha", "train", "Test.m-alpha_x"),
                entry("m-bravo", "held-out", "Test.m-bravo_x")]
        with mock.patch.object(MODULE, "assign_partitions", lambda: shifted):
            with self.assertRaisesRegex(MODULE.RefillError, r"R8 'm-alpha' was pre"):
                MODULE.guard(rows, v1_nursery(), set())

    def test_dropping_a_preregistered_family_is_refused(self):
        frozen = {"m-alpha": "held-out", "m-bravo": "development"}
        Harness(self, {"m-alpha": "held-out"}, frozen=frozen)
        rows = [entry("m-alpha", "held-out", "Test.m-alpha_x")]
        with self.assertRaisesRegex(MODULE.RefillError, r"R8 preregistered fam"):
            MODULE.guard(rows, v1_nursery(), set())

    def test_a_hand_edited_manifest_cannot_become_the_freeze(self):
        frozen = {"m-alpha": "held-out", "m-bravo": "development"}
        harness = Harness(self, frozen, frozen=frozen)
        tampered = json.loads(harness.extension.read_text())
        tampered["family_partitions"]["m-alpha"] = "train"
        harness.extension.write_text(json.dumps(tampered))
        with self.assertRaisesRegex(MODULE.RefillError, r"extension_sha256"):
            MODULE.frozen_partitions()

    def test_a_manifest_disagreeing_with_its_own_entries_is_refused(self):
        frozen = {"m-alpha": "held-out", "m-bravo": "development"}
        harness = Harness(self, frozen, frozen=frozen)
        body = frozen_manifest(frozen)
        body["entries"][0]["partition"] = "train"
        body["extension_sha256"] = MODULE.digest(
            {k: v for k, v in body.items() if k != "extension_sha256"})
        harness.extension.write_text(json.dumps(body))
        with self.assertRaisesRegex(MODULE.RefillError, r"disagreeing with its own"):
            MODULE.frozen_partitions()


class BlindnessTests(unittest.TestCase):
    """R9 -- a held-out row whose Mathlib name we already declare is not blind."""

    def test_already_declared_held_out_candidate_is_refused(self):
        Harness(self, {"a-new": "?", "b-new": "?", "c-new": "?", "d-new": "?"})
        rows = [entry("a-new", "held-out", "Nat.dvd_add"),
                entry("b-new", "development", "Nat.brand_new"),
                entry("c-new", "train", "Nat.also_new"),
                entry("d-new", "held-out", "Nat.still_new")]
        with self.assertRaisesRegex(MODULE.RefillError, r"R9 1 held-out cand"):
            MODULE.guard(rows, v1_nursery(), {"Nat.dvd_add"})

    def test_a_declared_name_in_a_DISPATCHABLE_row_is_admitted(self):
        """False-positive control: R9 is about blindness, not about novelty."""
        Harness(self, {"a-new": "?", "b-new": "?", "c-new": "?", "d-new": "?"})
        rows = [entry("a-new", "held-out", "Nat.brand_new"),
                entry("b-new", "development", "Nat.dvd_add"),
                entry("c-new", "train", "Nat.also_declared"),
                entry("d-new", "held-out", "Nat.still_new")]
        MODULE.guard(rows, v1_nursery(), {"Nat.dvd_add", "Nat.also_declared"})

    def test_a_frozen_held_out_row_is_not_re_judged(self):
        """Grandfathering: repairing an earlier draw is an ADR-0542 amendment,
        not something a regeneration may do."""
        frozen = {"m-alpha": "held-out"}
        Harness(self, frozen, frozen=frozen)
        rows = [entry("m-alpha", "held-out", "Nat.dvd_add")]
        MODULE.guard(rows, v1_nursery(), {"Nat.dvd_add"})


class RefillMustRefillTests(unittest.TestCase):
    def test_a_draw_with_no_dispatchable_row_is_refused(self):
        Harness(self, {"a-new": "?", "b-new": "?"})
        rows = [entry("a-new", "held-out", "Nat.x"),
                entry("b-new", "development", "Nat.y")]
        rows[1]["partition"] = "held-out"
        with mock.patch.object(MODULE, "assign_partitions",
                               lambda: {"a-new": "held-out", "b-new": "held-out"}):
            with self.assertRaisesRegex(MODULE.RefillError, r"R4 every refill row"):
                MODULE.guard(rows, v1_nursery(), set())

    def test_a_draw_adding_one_held_out_family_is_refused(self):
        Harness(self, {"a-new": "?", "b-new": "?"})
        rows = [entry("a-new", "held-out", "Nat.x"),
                entry("b-new", "development", "Nat.y")]
        with self.assertRaisesRegex(MODULE.RefillError, r"R5 the refill adds 1"):
            MODULE.guard(rows, v1_nursery(), set())

    def test_a_reproduction_adding_nothing_is_not_judged_as_a_draw(self):
        """--check re-derives the committed manifest and adds no family; R4/R5
        have no draw to be about, and firing there would make --check
        unrunnable forever."""
        frozen = {"m-alpha": "held-out"}
        Harness(self, frozen, frozen=frozen)
        MODULE.guard([entry("m-alpha", "held-out", "Nat.x")], v1_nursery(), set())


class FactReconciliationTests(unittest.TestCase):
    """The catastrophic one: a regeneration must not revert a closed fact."""

    def setUp(self):
        self.facts = pathlib.Path(tempfile.mkdtemp())
        patch = mock.patch.object(MODULE, "FACTS", self.facts)
        patch.start()
        self.addCleanup(patch.stop)
        self.entry = entry("a-new", "train", "Nat.some_lemma")

    def test_a_missing_fact_is_created(self):
        MODULE.reconcile_facts([self.entry], check=False)
        path = MODULE.fact_path(self.entry["fact_id"])
        self.assertTrue(path.exists())
        self.assertEqual(json.loads(path.read_text())["epistemic_status"], "open")

    def test_a_closed_fact_is_not_reverted(self):
        path = MODULE.fact_path(self.entry["fact_id"])
        closed = MODULE.fact_for(self.entry)
        closed["epistemic_status"] = "proved"
        closed["evidence"] = [{"kind": "kernel", "status": "checked"}]
        path.write_text(MODULE.render_fact(closed))
        problems = MODULE.reconcile_facts([self.entry], check=False)
        self.assertEqual(problems, [])
        after = json.loads(path.read_text())
        self.assertEqual(after["epistemic_status"], "proved")
        self.assertEqual(len(after["evidence"]), 1)

    def test_a_rewritten_preregistered_statement_is_reported(self):
        path = MODULE.fact_path(self.entry["fact_id"])
        drifted = copy.deepcopy(MODULE.fact_for(self.entry))
        drifted["formal"]["statement"] = "theorem Whatever : AxNat"
        path.write_text(MODULE.render_fact(drifted))
        problems = MODULE.reconcile_facts([self.entry], check=False)
        self.assertEqual(len(problems), 1)
        self.assertIn("formal.statement", problems[0])

    def test_a_missing_fact_under_check_is_a_reproduction_failure(self):
        problems = MODULE.reconcile_facts([self.entry], check=True)
        self.assertEqual(len(problems), 1)
        self.assertIn("is missing", problems[0])
        self.assertFalse(MODULE.fact_path(self.entry["fact_id"]).exists())


if __name__ == "__main__":
    unittest.main()
