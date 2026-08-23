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
        self.facts = tmp / "facts"
        self.facts.mkdir(exist_ok=True)
        self.entries: list[dict] = []
        self.families: dict[str, str] = {}
        self.operations: list[dict] = []
        self.amendments: list[dict] = []

    def fact(self, fact_id: str, family: str, partition: str, status: str = "open"):
        self.entries.append({"fact_id": fact_id, "family": family, "partition": partition})
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
        (self.tmp / "nursery.json").write_text(
            json.dumps({"entries": self.entries, "amendments": self.amendments}), encoding="utf-8"
        )
        (self.tmp / "policy.json").write_text(
            json.dumps({"family_partitions": self.families}), encoding="utf-8"
        )
        (self.tmp / "operations.json").write_text(
            json.dumps({"operations": self.operations}), encoding="utf-8"
        )
        module.NURSERY = self.tmp / "nursery.json"
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


if __name__ == "__main__":
    unittest.main()
