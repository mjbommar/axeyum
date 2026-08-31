"""Controls for scripts/gen-autogenesis-nursery-refill.py (ADR-0615, ADR-0616).

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


def validation(rows: list[dict], *, attested: int = 0, rejected: int = 0) -> dict:
    """A `surface_validation` block covering `rows`, split three ways.

    The first `attested` ids are accepted, the next `rejected` were REFUSED by
    Lean, the rest have had no run at all. ADR-0616: R3 compares the union of
    the last two against the first plus nursery-v1's 214.
    """
    ids = [r["fact_id"] for r in rows]
    return {
        "attested": sorted(ids[:attested]),
        "not_elaborable": [{"fact_id": i, "source_name": None, "lean": "no"}
                           for i in ids[attested:attested + rejected]],
        "unattested": sorted(ids[attested + rejected:]),
    }


def real_validation() -> dict:
    """What the committed manifest actually records about its own rows."""
    manifest = json.loads(
        (ROOT / "artifacts/autogenesis/nursery-v2-extension.json").read_text())
    return manifest["surface_validation"]


def frozen_manifest(partitions: dict[str, str],
                    preregistered: dict[str, str] | None = None) -> dict:
    """A manifest whose EFFECTIVE partitions are `partitions`.

    `preregistered` defaults to the same dict, which is the unamended case. Pass
    a different one to model a family the ADR-0542 ledger has moved.
    """
    entries = [entry(f, p, f"Test.{f}_lemma") for f, p in sorted(partitions.items())]
    body = {
        "family_partitions": dict(partitions),
        "preregistered_family_partitions": dict(preregistered or partitions),
        "entries": entries,
    }
    body["extension_sha256"] = MODULE.digest(
        {k: v for k, v in body.items() if k != "extension_sha256"})
    return body


def ledger(*amendments: dict) -> mock._patch:
    """Patch the ADR-0542 ledger to exactly these amendments."""
    return mock.patch.object(MODULE, "amendments",
                             lambda: {a["family"]: a for a in amendments})


def amendment(family: str, was: str, now: str) -> dict:
    return {"family": family, "from": was, "to": now}


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
        MODULE.guard(manifest["entries"], real_v1, set(snapshot["declarations"]),
                     real_validation())

    def test_real_manifest_is_its_own_freeze(self):
        """The freeze is the PREREGISTERED assignment, and the effective one
        differs from it at exactly the families the ADR-0542 ledger names."""
        frozen = MODULE.frozen_partitions()
        self.assertGreater(len(frozen), 0)
        self.assertEqual(frozen, MODULE.assign_partitions())
        preregistered = MODULE.preregistered_assignment()
        moved = {f for f in frozen if preregistered[f] != frozen[f]}
        amended = set(MODULE.amendments()) & set(frozen)
        self.assertEqual(moved, amended)
        # ...and this is not vacuous: the natural-divisibility spend is real.
        self.assertIn("natural-divisibility", moved)
        self.assertEqual(preregistered["natural-divisibility"], "held-out")
        self.assertEqual(frozen["natural-divisibility"], "development")


class CeilingTests(unittest.TestCase):
    """R3 -- ADR-0616 counts the ceiling by ATTESTATION, not by membership."""

    def _rows(self, count: int) -> list[dict]:
        """`count` rows over a family set that satisfies every rule but R3.

        Four families, so the module-path cycle yields two held-out (R5) and two
        dispatchable (R4), and each row carries the partition the rule assigns
        it (R6). Isolating R3 this way is what lets the refusal case and the
        promotion case differ ONLY in which attestation bucket a row sits in.
        """
        names = ["a", "b", "c", "d"]
        Harness(self, {n: "" for n in names})
        assigned = MODULE.assign_partitions()
        self.assertGreaterEqual(
            sum(1 for p in assigned.values() if p == "held-out"), 2)
        self.assertGreaterEqual(
            sum(1 for p in assigned.values() if p != "held-out"), 1)
        return [entry(names[i % len(names)],
                      assigned[names[i % len(names)]],
                      f"Test.{names[i % len(names)]}_{i}", i)
                for i in range(count)]

    # Each case below is sized so it dies under EXACTLY ONE mutation of R3,
    # which needed arithmetic rather than intuition. With `n` rows of which `a`
    # are attested, the extension contributes `n - a` to the unattested side
    # (`not_elaborable` rows are unattested too, so `r` does not change that
    # total) and `a` to the attested side, against v1's 214. R3 refuses when
    #
    #     n - a  >  214 + a
    #
    # The first draft used n = 215, a = 1 for the promotion case: 214 vs 215,
    # which passes -- but ALSO passes with the extension's attested rows dropped
    # from the sum (214 vs 214), so the mutant that reverts the promotion
    # SURVIVED. The sizes below are chosen against the mutants, not against the
    # rule as I imagined it.
    OVER = MODULE.V1_EVALUATION_ENTRIES + 4    # 218
    OVER_PLUS = MODULE.V1_EVALUATION_ENTRIES + 5   # 219

    def test_unattested_cohort_outweighing_the_attested_one_is_refused(self):
        # 218 rows nobody has run against 214 attested. Refused either way, so
        # this case pins that a comparison exists and nothing finer.
        rows = self._rows(self.OVER)
        with self.assertRaisesRegex(MODULE.RefillError,
                                    r"R3 the unattested cohort"):
            MODULE.guard(rows, v1_nursery(), set(), validation(rows))

    def test_an_attested_row_is_not_counted_as_scaffolding(self):
        # THE PROMOTION. The identical population, with two rows moved from
        # `unattested` to `attested`: 216 against 216, so it passes. Count the
        # extension's attested rows as scaffolding (a flat `len(entries)`, or
        # `attested_cohort` returning v1's 214 alone) and it becomes 216 > 214
        # and refuses. This case is what makes ADR-0615's stated exit work, and
        # it is the ONLY one that dies when the promotion is reverted.
        rows = self._rows(self.OVER)
        MODULE.guard(rows, v1_nursery(), set(), validation(rows, attested=2))

    def test_a_lean_refused_row_never_buys_headroom(self):
        # `not_elaborable` is a preregistered string Lean says is not a
        # proposition. It HAS been through the round trip, so a checker counting
        # "covered by a run" would promote it. 219 rows, 2 attested, 1 refused:
        # 217 unattested against 216 attested, refused. Drop the refused row
        # from the unattested side and it is 216 against 216 and passes.
        rows = self._rows(self.OVER_PLUS)
        with self.assertRaisesRegex(MODULE.RefillError,
                                    r"R3 the unattested cohort"):
            MODULE.guard(rows, v1_nursery(), set(),
                         validation(rows, attested=2, rejected=1))

    def test_attested_cohort_moving_is_refused(self):
        Harness(self, {"a": "held-out", "b": "development"})
        rows = [entry("a", "held-out", "Test.a_x"),
                entry("b", "development", "Test.b_x")]
        with self.assertRaisesRegex(MODULE.RefillError, r"R3 nursery-v1 holds"):
            MODULE.guard(rows, v1_nursery(MODULE.V1_EVALUATION_ENTRIES - 1),
                         set(), validation(rows))

    def test_v1_keeps_its_own_policy_range(self):
        low, high = MODULE.V1_POLICY_RANGE
        self.assertEqual((low, high), (100, 300))
        self.assertEqual(MODULE.V1_EVALUATION_ENTRIES, 214)


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

    def test_dropping_a_preregistered_family_is_refused(self):
        frozen = {"m-alpha": "held-out", "m-bravo": "development"}
        Harness(self, {"m-alpha": "held-out"}, frozen=frozen)
        rows = [entry("m-alpha", "held-out", "Test.m-alpha_x")]
        with self.assertRaisesRegex(MODULE.RefillError, r"R8 preregistered fam"):
            MODULE.guard(rows, v1_nursery(), set(), validation([]))

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


class AmendmentTests(unittest.TestCase):
    """R10 -- an effective partition may leave its preregistered one only
    through a recorded ADR-0542 breach.

    The hole this closes: `frozen_partitions` used to freeze
    `family_partitions`, so a hand edit that moved a family AND recomputed
    `extension_sha256` made itself the freeze and regenerated clean. The digest
    catches a careless edit, never a deliberate one, and until 2026-08-30
    nothing tied this manifest to the ledger at all.
    """

    def _harness(self, effective, preregistered):
        harness = Harness(self, effective, frozen=preregistered)
        harness.extension.write_text(
            json.dumps(frozen_manifest(effective, preregistered)))
        return [entry(f, p, f"Test.{f}_x") for f, p in sorted(effective.items())]

    def test_a_moved_partition_with_no_amendment_is_refused(self):
        """The hazard R8's freeze-comparison used to cover, and the one a
        digest cannot: the manifest agrees with itself in every direction."""
        rows = self._harness({"m-alpha": "train", "m-bravo": "development"},
                             {"m-alpha": "held-out", "m-bravo": "development"})
        with ledger():
            with self.assertRaisesRegex(
                    MODULE.RefillError, r"R10 'm-alpha' was preregistered"):
                MODULE.guard(rows, v1_nursery(), set(), validation([]))

    def test_a_moved_partition_with_a_matching_amendment_is_accepted(self):
        """The same manifest, one ledger row different. Without this pair the
        guard above could be satisfied by refusing every move."""
        rows = self._harness({"m-alpha": "development", "m-bravo": "development"},
                             {"m-alpha": "held-out", "m-bravo": "development"})
        with ledger(amendment("m-alpha", "held-out", "development")):
            MODULE.guard(rows, v1_nursery(), set(), validation([]))

    def test_an_amendment_recording_the_wrong_origin_is_refused(self):
        rows = self._harness({"m-alpha": "development", "m-bravo": "development"},
                             {"m-alpha": "held-out", "m-bravo": "development"})
        with ledger(amendment("m-alpha", "train", "development")):
            with self.assertRaisesRegex(MODULE.RefillError, r"R10 the 'm-alpha' amend"):
                MODULE.guard(rows, v1_nursery(), set(), validation([]))

    def test_an_amendment_recording_the_wrong_destination_is_refused(self):
        rows = self._harness({"m-alpha": "development", "m-bravo": "development"},
                             {"m-alpha": "held-out", "m-bravo": "development"})
        with ledger(amendment("m-alpha", "held-out", "train")):
            with self.assertRaisesRegex(MODULE.RefillError, r"R10 the 'm-alpha' amend"):
                MODULE.guard(rows, v1_nursery(), set(), validation([]))

    def test_an_amended_family_cannot_be_recycled_into_held_out(self):
        """ADR-0542: the spend is irreversible. A family whose blind value is
        gone may not be put back into the blind population, even with a ledger
        row that describes the move accurately."""
        rows = self._harness({"m-alpha": "held-out", "m-bravo": "development"},
                             {"m-alpha": "development", "m-bravo": "development"})
        with ledger(amendment("m-alpha", "development", "held-out")):
            with self.assertRaisesRegex(
                    MODULE.RefillError, r"R10 amended family 'm-alpha'"):
                MODULE.guard(rows, v1_nursery(), set(), validation([]))

    def test_a_manifest_without_a_preregistered_freeze_is_refused(self):
        """No fall back to `family_partitions`: a manifest that dropped the key
        would otherwise make its own amended partitions the freeze."""
        harness = Harness(self, {"m-alpha": "held-out"},
                          frozen={"m-alpha": "held-out"})
        body = frozen_manifest({"m-alpha": "held-out"})
        del body["preregistered_family_partitions"]
        body["extension_sha256"] = MODULE.digest(
            {k: v for k, v in body.items() if k != "extension_sha256"})
        harness.extension.write_text(json.dumps(body))
        with self.assertRaisesRegex(
                MODULE.RefillError, r"no preregistered_family_partitions"):
            MODULE.preregistered_freeze()

    def test_a_missing_ledger_is_an_error_not_a_quiet_pass(self):
        with mock.patch.object(MODULE, "SPLIT_POLICY",
                               pathlib.Path("/nonexistent/ledger.json")):
            with self.assertRaisesRegex(
                    MODULE.RefillError, r"amendment ledger is missing"):
                MODULE.amendments()

    def test_a_family_amended_twice_is_refused(self):
        """A held-out spend is irreversible, so a second move has no defined
        `from` and R10's origin check would silently read whichever row won."""
        policy = pathlib.Path(tempfile.mkdtemp()) / "policy.json"
        policy.write_text(json.dumps({"amendments": [
            amendment("m-alpha", "held-out", "development"),
            amendment("m-alpha", "development", "train"),
        ]}))
        with mock.patch.object(MODULE, "SPLIT_POLICY", policy):
            with self.assertRaisesRegex(MODULE.RefillError, r"amends 'm-alpha' twice"):
                MODULE.amendments()


class BlindnessTests(unittest.TestCase):
    """R9 -- a held-out row whose Mathlib name we already declare is not blind."""

    def test_already_declared_held_out_candidate_is_refused(self):
        Harness(self, {"a-new": "?", "b-new": "?", "c-new": "?", "d-new": "?"})
        rows = [entry("a-new", "held-out", "Nat.dvd_add"),
                entry("b-new", "development", "Nat.brand_new"),
                entry("c-new", "train", "Nat.also_new"),
                entry("d-new", "held-out", "Nat.still_new")]
        with self.assertRaisesRegex(MODULE.RefillError, r"R9 1 held-out cand"):
            MODULE.guard(rows, v1_nursery(), {"Nat.dvd_add"}, validation([]))

    def test_a_declared_name_in_a_DISPATCHABLE_row_is_admitted(self):
        """False-positive control: R9 is about blindness, not about novelty."""
        Harness(self, {"a-new": "?", "b-new": "?", "c-new": "?", "d-new": "?"})
        rows = [entry("a-new", "held-out", "Nat.brand_new"),
                entry("b-new", "development", "Nat.dvd_add"),
                entry("c-new", "train", "Nat.also_declared"),
                entry("d-new", "held-out", "Nat.still_new")]
        MODULE.guard(rows, v1_nursery(), {"Nat.dvd_add", "Nat.also_declared"}, validation([]))

    def test_a_frozen_held_out_row_is_not_re_judged(self):
        """Grandfathering: repairing an earlier draw is an ADR-0542 amendment,
        not something a regeneration may do."""
        frozen = {"m-alpha": "held-out"}
        Harness(self, frozen, frozen=frozen)
        rows = [entry("m-alpha", "held-out", "Nat.dvd_add")]
        MODULE.guard(rows, v1_nursery(), {"Nat.dvd_add"}, validation([]))


class ClosedEvaluationScreenTests(unittest.TestCase):
    """R12 (ADR-0695/ADR-0950) -- a NEW held-out row already decided by
    reduction over declared constants is not blind.

    `test_the_real_spent_statements_are_refused_as_a_new_draw` is not a
    synthetic fixture: it replays the exact two statements ADR-0950 amended
    (`Nat.bit false 0 = 0`, `Nat.size 1 = 1`) against the REAL committed
    kernel-environment snapshot. Draw 11 (882ae1a52, 2026-08-30) preregistered
    `natural-bit-decode` held-out even though `Nat.bit` (2facd789, 2026-08-28)
    and `Nat.size` (a7ac623d7, 2026-08-24) were already admitted -- both
    confirmed ancestors of the draw commit. If this screen or the snapshot
    ever stopped seeing those two declarations, this test would go green for
    the wrong reason, so it is paired with a false-positive control using the
    real env below.
    """

    def _snapshot_env(self) -> set[str]:
        snap = json.loads(
            (ROOT / "artifacts/autogenesis/kernel-environment-snapshot-v1.json"
             ).read_text())
        return set(snap["declarations"])

    def test_the_real_spent_statements_are_refused_as_a_new_draw(self):
        env = self._snapshot_env()
        rows = [entry("bit-decode-replay", "held-out", "Nat.bit_false_zero"),
                entry("bit-decode-replay", "held-out", "Nat.size_one")]
        rows[0]["statement"] = "Nat.bit false 0 = 0"
        rows[1]["statement"] = "Nat.size 1 = 1"
        with self.assertRaisesRegex(MODULE.RefillError, r"R12 2 held-out cand"):
            MODULE._closed_evaluation_screen(rows, env)

    def test_a_quantified_sibling_from_the_same_family_is_admitted(self):
        """False-positive control: R12 is about closed evaluation, not about
        the family's name. Uses the REAL env so a screen that started
        refusing everything from this family would still be caught."""
        env = self._snapshot_env()
        rows = [entry("bit-decode-replay", "held-out", "Nat.bit_le")]
        rows[0]["statement"] = (
            "∀ (b : Bool) {m n : ℕ}, m ≤ n → "
            "Nat.bit b m ≤ Nat.bit b n")
        MODULE._closed_evaluation_screen(rows, env)  # must not raise

    def test_a_closed_row_over_an_undeclared_constant_is_admitted(self):
        """A row SHAPED like a closed evaluation but over a constant this
        kernel does not declare is genuinely blind; R12 must not refuse it.

        The made-up tail must not appear as a source-fallback false positive
        (`source_declares` over-approximates on purpose, see its docstring),
        so it is deliberately long and implausible rather than a short word
        like `bar` that collides with ordinary Rust identifiers.
        """
        rows = [entry("undeclared-family", "held-out", "Foo.zzzquxxNotarealthing")]
        rows[0]["statement"] = "Foo.zzzquxxNotarealthing 0 = 0"
        MODULE._closed_evaluation_screen(rows, set())  # must not raise

    def test_a_dispatchable_row_is_not_screened(self):
        """R12 is about BLINDNESS; a `development` row may restate a closed
        fact freely -- development is where looking is allowed."""
        env = self._snapshot_env()
        rows = [entry("bit-decode-replay", "development", "Nat.size_one")]
        rows[0]["statement"] = "Nat.size 1 = 1"
        MODULE._closed_evaluation_screen(rows, env)  # must not raise

    def test_a_ground_inequality_is_not_a_closed_evaluation(self):
        """R12 must defer to the STANDING classifier's shape rule (binder-free
        EQUATION, not any ground relation), not just check whether a row's
        names are all declared.

        Without the `is_closed_evaluation` call this row -- ground, both
        sides the same declared constant, no bound variables at all -- has no
        undeclared name to save it, so it would be flagged even though it
        carries no `=` and the standing gate does not classify it as a closed
        evaluation. Kills the mutation that drops the shape check and keeps
        only the undeclared-name filter, which the bound-variable case above
        cannot kill because a quantifier's own bound names (`m`, `n`, ...)
        happen to look undeclared too."""
        env = self._snapshot_env()
        self.assertIn("Nat.size", env)
        rows = [entry("bit-decode-replay", "held-out", "Nat.size_le_size_refl")]
        rows[0]["statement"] = "Nat.size 1 ≤ Nat.size 1"
        MODULE._closed_evaluation_screen(rows, env)  # must not raise

    def test_guard_integration_refuses_via_r12(self):
        """The screen is wired into `guard()`, not just callable standalone.
        Mirrors `BlindnessTests`' R9 harness shape so R4/R5/R6 are satisfied
        and the only new failure is R12."""
        Harness(self, {"a-new": "?", "b-new": "?", "c-new": "?", "d-new": "?"})
        rows = [entry("a-new", "held-out", "Nat.bit_false_zero"),
                entry("b-new", "development", "Nat.brand_new"),
                entry("c-new", "train", "Nat.also_new"),
                entry("d-new", "held-out", "Nat.still_new")]
        rows[0]["statement"] = "Nat.bit false 0 = 0"
        with self.assertRaisesRegex(MODULE.RefillError, r"R12"):
            MODULE.guard(rows, v1_nursery(), {"Nat.bit"}, validation([]))


class RefillMustRefillTests(unittest.TestCase):
    def test_a_draw_with_no_dispatchable_row_is_refused(self):
        Harness(self, {"a-new": "?", "b-new": "?"})
        rows = [entry("a-new", "held-out", "Nat.x"),
                entry("b-new", "development", "Nat.y")]
        rows[1]["partition"] = "held-out"
        with mock.patch.object(MODULE, "assign_partitions",
                               lambda: {"a-new": "held-out", "b-new": "held-out"}):
            with self.assertRaisesRegex(MODULE.RefillError, r"R4 every refill row"):
                MODULE.guard(rows, v1_nursery(), set(), validation([]))

    def test_a_draw_adding_one_held_out_family_is_refused(self):
        Harness(self, {"a-new": "?", "b-new": "?"})
        rows = [entry("a-new", "held-out", "Nat.x"),
                entry("b-new", "development", "Nat.y")]
        with self.assertRaisesRegex(MODULE.RefillError, r"R5 the refill adds 1"):
            MODULE.guard(rows, v1_nursery(), set(), validation([]))

    def test_a_reproduction_adding_nothing_is_not_judged_as_a_draw(self):
        """--check re-derives the committed manifest and adds no family; R4/R5
        have no draw to be about, and firing there would make --check
        unrunnable forever."""
        frozen = {"m-alpha": "held-out"}
        Harness(self, frozen, frozen=frozen)
        MODULE.guard([entry("m-alpha", "held-out", "Nat.x")], v1_nursery(), set(),
                     validation([]))


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


class AttestationProvenanceTests(unittest.TestCase):
    """ADR-0616 -- an accepted row buys ceiling headroom, so WHICH Mathlib
    the run read stopped being descriptive and became load-bearing."""

    def _record(self, commit: str) -> pathlib.Path:
        path = pathlib.Path(tempfile.mkdtemp()) / "run.json"
        path.write_text(json.dumps({
            "host": "s5",
            "mathlib_commit": commit,
            "lean_version": "Lean (version 4.30.0)",
            "module_sha256": "0" * 64,
            "negative_control_rejected": True,
            "attested_fact_ids": ["F:test-a-0"],
            "elapsed_seconds": 1.0,
            "failures": [],
        }))
        return path

    def test_a_run_against_another_mathlib_commit_is_refused(self):
        rows = [entry("a", "held-out", "Test.a_x")]
        with self.assertRaisesRegex(MODULE.RefillError, r"not the pinned"):
            MODULE.surface_validation(rows, self._record("deadbeef" * 5))

    def test_a_run_at_the_pinned_commit_attests(self):
        # False-positive control for the case above: identical record, only the
        # commit differs, and the row lands in `attested`.
        rows = [entry("a", "held-out", "Test.a_x")]
        got = MODULE.surface_validation(rows, self._record(MODULE.SOURCE_COMMIT))
        self.assertEqual(got["attested"], ["F:test-a-0"])
        self.assertEqual(got["unattested"], [])

    def test_a_run_whose_negative_control_was_accepted_is_refused(self):
        rows = [entry("a", "held-out", "Test.a_x")]
        path = self._record(MODULE.SOURCE_COMMIT)
        record = json.loads(path.read_text())
        record["negative_control_rejected"] = False
        path.write_text(json.dumps(record))
        with self.assertRaisesRegex(MODULE.RefillError, r"negative control"):
            MODULE.surface_validation(rows, path)


class LimitationsTests(unittest.TestCase):
    """ADR-0616 -- the manifest may not assert two incompatible grades.

    The committed file carried a populated `surface_validation.attested` list
    AND a limitation reading "these statements carry the quotation grade, not
    v1's real-Lean round-trip attestation". Both cannot be current.
    """

    def test_a_fully_attested_cohort_is_not_described_as_quotation(self):
        rows = [entry("a", "held-out", f"Test.a_{i}", i) for i in range(3)]
        text = " ".join(MODULE.limitations(validation(rows, attested=3)))
        self.assertNotIn("carry the quotation grade", text)
        self.assertIn("real-Lean round-trip attestation", text)

    def test_an_unrun_cohort_is_still_described_as_quotation(self):
        # The other direction, and the reason this is derived rather than
        # deleted: a manifest nobody has attested must still say so.
        rows = [entry("a", "held-out", f"Test.a_{i}", i) for i in range(3)]
        text = " ".join(MODULE.limitations(validation(rows)))
        self.assertIn("carry the quotation grade", text)

    def test_a_partly_attested_cohort_names_both_populations(self):
        rows = [entry("a", "held-out", f"Test.a_{i}", i) for i in range(5)]
        text = " ".join(MODULE.limitations(validation(rows, attested=2,
                                                      rejected=1)))
        self.assertIn("2 of 5", text)
        self.assertIn("2 have had no run", text)
        self.assertIn("1 were REFUSED", text)

    def test_the_dependency_component_gap_survives_full_attestation(self):
        # The difference attestation does NOT repair. v1 freezes partitions
        # against declared dependency weak components; this cohort's
        # source_group is a Mathlib module. Promoting on the attestation axis
        # must not launder that away -- it is a property of the ROW.
        rows = [entry("a", "held-out", f"Test.a_{i}", i) for i in range(3)]
        text = " ".join(MODULE.limitations(validation(rows, attested=3)))
        self.assertIn("declared dependency weak components", text)
        self.assertIn("source_group", text)

    def test_the_committed_manifest_does_not_contradict_its_own_grade(self):
        # False-positive control against the REAL file: the defect this class
        # exists for, asserted where it actually occurred.
        manifest = json.loads(
            (ROOT / "artifacts/autogenesis/nursery-v2-extension.json").read_text())
        text = " ".join(manifest["limitations"])
        attested = manifest["surface_validation"]["attested"]
        self.assertGreater(len(attested), 0)
        self.assertNotIn("carry the quotation grade", text)
        self.assertEqual(manifest["limitations"],
                         MODULE.limitations(manifest["surface_validation"]))


if __name__ == "__main__":
    unittest.main()
