#!/usr/bin/env python3
"""Controls for `scripts/check-development-partition.py`.

One test per guard, each built to die when *its own* guard is removed and no
other. That disjointness is the property CLAUDE.md records as having failed
before: six of seven guards in one suite were removable with everything still
green, because they all rejected through one shared check. A suite that cannot
distinguish its guards measures nothing.

Every test builds its own manifests in a temp directory. Reading live
`artifacts/` would make the suite drift as facts land -- and worse, a fixture
that happens to pass because of today's repository state is a control that
stops controlling on a day nobody is watching.
"""

from __future__ import annotations

import importlib.util
import json
import pathlib
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SUBJECT = ROOT / "scripts/check-development-partition.py"


def load_subject():
    spec = importlib.util.spec_from_file_location("check_development_partition", SUBJECT)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


class Fixture:
    """A synthetic nursery/policy/registry/ledger the subject can be pointed at."""

    def __init__(self, tmp: pathlib.Path):
        self.tmp = tmp
        self.nursery_dir = tmp / "nursery"
        self.nursery_dir.mkdir(exist_ok=True)
        self.facts = tmp / "facts"
        self.facts.mkdir(exist_ok=True)
        self.entries: list[dict] = []
        # Facts that live ONLY in a `nursery-v2-extension.json`-shaped
        # manifest -- see `test_development_fact_in_extension_manifest_is_
        # seen`, which pins the ADR-1570 defect this fixture exists to catch.
        self.extension_entries: list[dict] = []
        self.families: dict[str, str] = {}
        self.operations: list[dict] = []
        self.amendments: list[dict] = []

    def fact(self, fact_id: str, family: str, partition: str, status: str = "open",
             manifest: str = "v1"):
        entry = {"fact_id": fact_id, "family": family, "partition": partition}
        if manifest == "v1":
            self.entries.append(entry)
        elif manifest == "extension":
            self.extension_entries.append(entry)
        else:
            raise ValueError(f"unknown manifest {manifest!r}")
        self.families.setdefault(family, partition)
        (self.facts / f"{fact_id.replace(':', '-')}.json").write_text(
            json.dumps({"id": fact_id, "epistemic_status": status}), encoding="utf-8"
        )
        return self

    def operation(self, op_id: str, fact_ids: list[str], deep: dict | None = None):
        op = {"id": op_id, "applicability": {"fact_ids": fact_ids}}
        if deep:
            op["executor"] = deep
        self.operations.append(op)
        return self

    def amend(self, fact_id: str):
        self.amendments.append({"family": "x", "breach": {"fact_id": fact_id}})
        return self

    def install(self, module):
        (self.nursery_dir / "nursery-v1.json").write_text(
            json.dumps({"entries": self.entries, "amendments": self.amendments}), encoding="utf-8"
        )
        if self.extension_entries:
            (self.nursery_dir / "nursery-v2-extension.json").write_text(
                json.dumps({"entries": self.extension_entries}), encoding="utf-8"
            )
        (self.tmp / "policy.json").write_text(
            json.dumps({"family_partitions": self.families}), encoding="utf-8"
        )
        (self.tmp / "operations.json").write_text(
            json.dumps({"operations": self.operations}), encoding="utf-8"
        )
        module.NURSERY_DIR = self.nursery_dir
        module.SPLIT_POLICY = self.tmp / "policy.json"
        module.OPERATIONS = self.tmp / "operations.json"
        module.FACTS = self.facts
        # Neutral by default so the ratchet does not fire in tests that are not
        # about the ratchet; the two ratchet controls set it explicitly.
        module.MULTI_TARGET_FLOOR = 0
        return module


class DevelopmentPartitionControls(unittest.TestCase):
    def setUp(self):
        self._dir = tempfile.TemporaryDirectory()
        self.tmp = pathlib.Path(self._dir.name)
        self.module = load_subject()

    def tearDown(self):
        self._dir.cleanup()

    def healthy(self) -> Fixture:
        """Train and development populated, one well-formed spanning operation."""
        f = Fixture(self.tmp)
        f.fact("F:t1", "fam-train", "train")
        f.fact("F:t2", "fam-train", "train")
        f.fact("F:d1", "fam-dev", "development")
        f.fact("F:d2", "fam-dev", "development")
        f.operation("op-spanning", ["F:t1", "F:t2", "F:d1"])
        f.operation("op-train-only", ["F:t2"])
        return f

    def test_healthy_fixture_passes(self):
        """Positive control. Without this, a guard that rejects EVERYTHING
        would satisfy every negative test below and look like a working gate."""
        self.healthy().install(self.module)
        self.assertEqual(self.module.check(["--quiet"]), 0)

    # --- guard: an operation on development must also cover train -----------
    def test_development_only_operation_is_a_violation(self):
        f = self.healthy()
        f.operation("op-dev-only", ["F:d2"])
        f.install(self.module)
        self.assertEqual(self.module.check(["--quiet"]), 1)

    # --- guard: the generic string walk, not a field-specific one -----------
    def test_development_fact_hidden_in_executor_is_still_seen(self):
        """The held-out gate learned this: operations carry fact ids at three
        distinct JSON paths, so a field-specific guard is bypassable the day it
        is written. Here the id appears ONLY under `executor`."""
        f = self.healthy()
        f.operation("op-buried", [], deep={"input_fact_id": "F:d2"})
        f.install(self.module)
        self.assertEqual(self.module.check(["--quiet"]), 1)

    # --- guard: recorded amendments exempt an already-spent row -------------
    def test_amended_breach_is_exempt(self):
        f = self.healthy()
        f.operation("op-dev-only", ["F:d2"])
        f.amend("F:d2")
        f.install(self.module)
        self.assertEqual(self.module.check(["--quiet"]), 0)

    # --- guard: every nursery manifest is read, not `nursery-v1.json` alone -
    def test_development_fact_in_extension_manifest_is_seen(self):
        """THE ADR-1570 DEFECT. `authoritative-mathlib-nat-bit-constructor-
        family-v1` closed four `development` facts that live only in
        `nursery-v2-extension.json`, and the gate's old single-file `NURSERY`
        constant never opened that file -- so `referenced` was empty for the
        operation and the dev-only rule never fired. Here `F:d3` sits in a
        `nursery-v2-extension.json`-shaped manifest and nowhere in
        `nursery-v1.json`; an operation touching only it must still be caught."""
        f = self.healthy()
        f.fact("F:d3", "fam-dev-ext", "development", manifest="extension")
        f.operation("op-dev-only-ext", ["F:d3"])
        f.install(self.module)
        self.assertEqual(self.module.check(["--quiet"]), 1)

    def test_unrelated_manifest_shaped_file_is_not_read(self):
        """A file that does not match `MANIFEST_GLOBS` (neither `nursery-v1.
        json` nor `nursery-v*-extension.json`) must not be treated as a
        manifest -- widening to a bare `nursery*.json` glob would make an
        unrelated committed decoy able to take this gate down. `F:decoy` sits
        ONLY in such a file and must never appear in the partition map, so an
        operation naming it is invisible (not a violation, and not a crash)."""
        f = self.healthy()
        f.install(self.module)
        (f.nursery_dir / "nursery-notes-v1.json").write_text(
            json.dumps({"entries": [{"fact_id": "F:decoy", "family": "fam-decoy",
                                     "partition": "development"}]}),
            encoding="utf-8",
        )
        self.assertEqual(self.module.check(["--quiet"]), 0)
        partitions = self.module.fact_partitions()
        self.assertNotIn("F:decoy", partitions)

    # --- guard: the two partition sources must agree ------------------------
    def test_nursery_and_policy_disagreement_is_an_error(self):
        f = self.healthy()
        f.families["fam-dev"] = "train"  # policy now contradicts the entries
        f.install(self.module)
        self.assertEqual(self._main(), 2)

    def _main(self):
        try:
            return self.module.check(["--quiet"])
        except self.module.DevelopmentPartitionError:
            return 2

    # --- guard: fail closed when the subject population is empty ------------
    def test_empty_development_population_is_an_error(self):
        f = Fixture(self.tmp)
        f.fact("F:t1", "fam-train", "train")
        f.operation("op-train-only", ["F:t1"])
        f.install(self.module)
        self.assertEqual(self._main(), 2)

    # --- guard: the generality ratchet --------------------------------------
    def test_ratchet_fires_when_multi_target_coverage_falls(self):
        f = self.healthy()
        f.install(self.module)
        self.module.MULTI_TARGET_FLOOR = 4  # healthy fixture covers 3
        self.assertEqual(self.module.check(["--quiet"]), 1)

    def test_ratchet_passes_at_its_floor(self):
        """Boundary control: the ratchet must not fire AT the floor, or it is
        an off-by-one that would be read as a real regression."""
        f = self.healthy()
        f.install(self.module)
        self.module.MULTI_TARGET_FLOOR = 3
        self.assertEqual(self.module.check(["--quiet"]), 0)

    # --- guard: an empty registry is an error, not a quiet pass -------------
    def test_empty_operations_registry_is_an_error(self):
        f = self.healthy()
        f.operations = []
        f.install(self.module)
        self.assertEqual(self._main(), 2)


class GrandfatherControls(unittest.TestCase):
    """Controls for `GRANDFATHERED_OPERATIONS` (ADR-1563).

    NOT a subclass of `DevelopmentPartitionControls`. Inheriting would re-run
    all nine of its tests under a second class name, and every mutant of a
    guard those tests cover would then kill TWO tests -- which is the mutation
    report saying less about a guard than a single kill does.

    The entry excuses one operation that cannot be retired, because every fact
    it admitted pins `operation_sha256` over its exact bytes. An exemption of
    that shape is one edit away from being the thing CLAUDE.md warns about, so
    each of the two re-derived properties is driven to failure here, and the
    NEW-producer case -- the property that must not be weakened -- is driven
    too.

    Each test installs the grandfather into a synthetic registry rather than
    reading the committed one: what these measure is the mechanism, and
    `LiveGrandfatherTests` below measures that the committed list still names
    something real.
    """

    OP = "op-grandfathered"

    def setUp(self):
        self._dir = tempfile.TemporaryDirectory()
        self.tmp = pathlib.Path(self._dir.name)
        self.module = load_subject()

    def tearDown(self):
        self._dir.cleanup()

    def healthy(self) -> Fixture:
        """Train and development populated, one well-formed spanning operation."""
        f = Fixture(self.tmp)
        f.fact("F:t1", "fam-train", "train")
        f.fact("F:t2", "fam-train", "train")
        f.fact("F:d1", "fam-dev", "development")
        f.operation("op-spanning", ["F:t1", "F:t2", "F:d1"])
        return f

    def grandfathered(self, status: str = "proved", pins: bool = True) -> Fixture:
        """One development-only operation, named in the grandfather dict.

        `status` and `pins` are the two re-derived properties, each togglable
        on its own so the test that fails can only be the one about it.
        """
        f = self.healthy()
        f.fact("F:g1", "fam-gf", "development", status=status)
        if pins:
            path = f.facts / "F-g1.json"
            body = json.loads(path.read_text(encoding="utf-8"))
            body["evidence"] = [{"checker_operation": {"id": self.OP}}]
            path.write_text(json.dumps(body), encoding="utf-8")
        f.operation(self.OP, ["F:g1"])
        f.install(self.module)
        self.module.GRANDFATHERED_OPERATIONS = {
            self.OP: {"registered": "test", "authority": "test", "reason": "test"}
        }
        return f

    def test_a_grandfathered_operation_is_excused(self):
        """The accept case. Without it every rejection below is satisfied by a
        dict that excuses nothing, which would leave the gate red and the
        mechanism inert."""
        self.grandfathered()
        self.assertEqual(self.module.check(["--quiet"]), 0)

    def test_a_grandfather_covering_an_open_development_fact_is_refused(self):
        """A grandfather must never park LIVE development work. Same operation,
        same dict entry, target still `open`."""
        self.grandfathered(status="open")
        self.assertEqual(self.module.check(["--quiet"]), 1)

    def test_a_grandfather_whose_targets_do_not_pin_it_is_refused(self):
        """The justification is that the operation CANNOT be retired because
        its targets pin it. An operation nothing pins can be retired, so it
        must be -- not excused. Same entry, evidence binding removed."""
        self.grandfathered(pins=False)
        self.assertEqual(self.module.check(["--quiet"]), 1)

    def test_a_new_development_only_operation_is_still_a_violation(self):
        """THE PROPERTY THE GRANDFATHER MUST NOT WEAKEN. A second operation,
        settled and pinning itself exactly like the excused one, but absent
        from the dict, still fails."""
        f = self.grandfathered()
        f.fact("F:g2", "fam-gf2", "development", status="proved")
        path = f.facts / "F-g2.json"
        body = json.loads(path.read_text(encoding="utf-8"))
        body["evidence"] = [{"checker_operation": {"id": "op-new"}}]
        path.write_text(json.dumps(body), encoding="utf-8")
        f.operation("op-new", ["F:g2"])
        f.install(self.module)
        self.assertEqual(self.module.check(["--quiet"]), 1)

    def test_a_grandfather_that_excuses_nothing_is_a_violation(self):
        """The stale-exemption discipline. The operation is in the registry and
        covers a TRAIN fact too, so the rule never fires on it -- the entry
        suppresses nothing and must say so rather than sit there."""
        f = self.healthy()
        f.operation(self.OP, ["F:t1"])
        f.install(self.module)
        self.module.GRANDFATHERED_OPERATIONS = {
            self.OP: {"registered": "test", "authority": "test", "reason": "test"}
        }
        self.assertEqual(self.module.check(["--quiet"]), 1)


class LiveGrandfatherTests(unittest.TestCase):
    """The committed grandfather list, measured against the committed registry.

    A closed list in source is only as honest as its subject still being real,
    and a list that names an operation nobody can find is an exemption pointing
    at nothing. This derives its subject from the registry rather than from a
    constant that happens to agree with it.
    """

    def setUp(self):
        self.module = load_subject()

    def test_every_grandfathered_operation_is_in_the_live_registry(self):
        registry = json.loads(
            self.module.OPERATIONS.read_text(encoding="utf-8"))["operations"]
        live = {operation["id"] for operation in registry}
        missing = sorted(set(self.module.GRANDFATHERED_OPERATIONS) - live)
        self.assertEqual(missing, [], "grandfathered operation(s) left the registry")

    # NO `the committed tree passes` test here, deliberately. Such a test reads
    # the live ledger and therefore dies under EVERY mutant of every guard,
    # which turns each single-kill mutation report into a two-kill one and
    # tells a reader less about each guard than the report already did. The
    # live tree is exercised by the gate itself in `justfile` and `check.sh`.


if __name__ == "__main__":
    unittest.main()
