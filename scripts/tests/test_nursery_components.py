#!/usr/bin/env python3
"""Controls for ``scripts/nursery-components.py``.

CLAUDE.md: *a checker that cannot fail is worse than no checker.*  This tool's
whole output is a refusal -- ADR-1551 declines to apply ADR-1546 option 1 --
so the guards that have to be driven to failure are the ones that would tell
the next lane the refusal has EXPIRED.  A ``--check`` that cannot go red is a
standing claim that option 1 is still impossible, asserted forever by a
command nobody can falsify, which is the exact shape of the exemption ADR-1550
was written to replace.

The shipped script is never re-implemented here.  ``--root`` (equivalently
``AXEYUM_NURSERY_COMPONENTS_ROOT``) points the real file at a throwaway tree
of a few small JSON documents.  Same device as
``AXEYUM_PARTITION_EDGES_ROOT``.

Registered with ``scripts/tests/mutation_controls.py`` under
``nursery-components``::

    python3 -m unittest scripts.tests.test_nursery_components
    python3 scripts/tests/mutation_controls.py nursery-components

FIXTURE DISCIPLINE, learned from the partition-edges suite.  A fixture carries
only what its scenario's subject needs: a scenario that is not about the
family contraction gets ONE family per partition, so the mutant that breaks
the contraction kills the test whose subject it is rather than six others.
"""

from __future__ import annotations

import json
import pathlib
import subprocess
import sys
import tempfile
import unittest


def _ctx(done: subprocess.CompletedProcess) -> str:
    """The tool's output as an assertion message, INDENTED so no line starts
    with ``FAIL``.

    ``mutation_controls.py`` names the tests a mutant killed with
    ``^(?:FAIL|ERROR): (\\S+)`` over unittest's output.  This tool prints its
    findings as ``FAIL F1 ...`` at line start, so a raw ``done.stdout`` in a
    failing assertion's message would be parsed as extra dead tests and the
    harness would report the run INCONSISTENT.
    """
    return "\n" + "".join(f"  {line}\n"
                          for line in (done.stdout + done.stderr).splitlines())


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/nursery-components.py"
CENSUS = "artifacts/autogenesis/drawn-population-component-census-v1.json"


class NurseryComponentControls(unittest.TestCase):
    """One scenario per guard in ``scripts/nursery-components.py``."""

    def setUp(self) -> None:
        scratch = pathlib.Path("/data0/axeyum/scratch")
        self._tmp = tempfile.TemporaryDirectory(
            dir=scratch if scratch.is_dir() else None)
        self.addCleanup(self._tmp.cleanup)
        self.root = pathlib.Path(self._tmp.name) / "tree"
        (self.root / "artifacts/autogenesis").mkdir(parents=True)
        (self.root / "artifacts/facts").mkdir(parents=True)

    # -- fixture construction ----------------------------------------------

    def write(self, rel: str, document: object) -> None:
        path = self.root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(document, indent=2, sort_keys=True) + "\n")

    def manifest(self, name: str,
                 rows: list[tuple[str, str, str]],
                 **extra: object) -> None:
        """``rows`` is ``[(fact_id, partition, family)]``."""
        document: dict[str, object] = {
            "kind": "axeyum-autogenesis-nursery",
            "entries": [{"fact_id": f, "partition": p, "family": fam}
                        for f, p, fam in rows],
        }
        document.update(extra)
        self.write(f"artifacts/autogenesis/nursery-{name}.json", document)

    def fact(self, fact_id: str, depends_on: list[str] | None = None) -> None:
        self.write(f"artifacts/facts/{fact_id.replace(':', '-')}.json",
                   {"id": fact_id, "depends_on": depends_on or []})

    # -- the standard fixtures ---------------------------------------------

    def blob_with_both_pins(self) -> None:
        """The live tree in miniature, and the ONLY fixture that has all of it.

        One component holding a train family, a development family, the
        held-out pin and the longitudinal pin, plus one isolated held-out
        family standing in for the nineteen clean ones.  Every ADR-1551
        finding is true here, so ``--check`` passes and each mutant that
        breaks one finding makes exactly this scenario's counterpart red.
        """
        self.manifest("v1", [
            ("F:t1", "train", "fam-train"),
            ("F:d1", "development", "fam-dev"),
            ("F:h1", "held-out", "integer-absolute-value"),
            ("F:l1", "longitudinal", "nat-bootstrap"),
            ("F:h2", "held-out", "fam-clean-holdout"),
        ], policy={"evaluation_fact_count": {"minimum": 1, "maximum": 9}})
        self.fact("F:t1", ["F:d1", "F:l1"])
        self.fact("F:d1", ["F:l1"])
        self.fact("F:h1", ["F:d1"])
        self.fact("F:l1")
        self.fact("F:h2")

    def one_family_two_partitions(self) -> None:
        """A single family holding two partitions, and nothing else.

        The subject is F1 alone: `family_leakage` no longer describes the
        manifests, so contracting each family to one node stops being forced.
        """
        self.manifest("v1", [
            ("F:a", "train", "fam-split"),
            ("F:b", "development", "fam-split"),
        ])
        self.fact("F:a")
        self.fact("F:b")

    def no_pins_anywhere(self) -> None:
        """A blob with two evaluation partitions and NEITHER pinned family."""
        self.manifest("v1", [
            ("F:t1", "train", "fam-train"),
            ("F:d1", "development", "fam-dev"),
        ])
        self.fact("F:t1", ["F:d1"])
        self.fact("F:d1")

    # -- driving the tool --------------------------------------------------

    def run_tool(self, *args: str) -> subprocess.CompletedProcess:
        return subprocess.run(
            [sys.executable, str(SCRIPT), "--root", str(self.root), *args],
            capture_output=True, text=True, check=False)

    def record(self) -> None:
        done = self.run_tool("--record")
        self.assertEqual(done.returncode, 0, _ctx(done))

    def census(self) -> dict:
        return json.loads((self.root / CENSUS).read_text())

    # -- the guards --------------------------------------------------------

    def test_findings_hold_on_the_live_shape(self) -> None:
        """The positive control: every ADR-1551 finding true -> exit 0.

        Without this, a ``--check`` mutated to complain about everything would
        still look correct to the negative scenarios below.
        """
        self.blob_with_both_pins()
        self.record()
        done = self.run_tool("--check")
        self.assertEqual(done.returncode, 0, _ctx(done))
        self.assertIn("findings=0", done.stdout, _ctx(done))

    def test_a_family_holding_two_partitions_is_a_finding(self) -> None:
        """F1: the family contraction is no longer forced."""
        self.one_family_two_partitions()
        self.record()
        done = self.run_tool("--check")
        self.assertEqual(done.returncode, 1, _ctx(done))
        self.assertIn("FAIL F1", done.stdout, _ctx(done))

    def test_a_blob_without_a_pin_is_a_finding(self) -> None:
        """F3: the crossings called unrepairable may be repairable now."""
        self.no_pins_anywhere()
        self.record()
        done = self.run_tool("--check")
        self.assertEqual(done.returncode, 1, _ctx(done))
        self.assertIn("FAIL F3", done.stdout, _ctx(done))

    def test_a_single_partition_blob_is_a_finding(self) -> None:
        """F2: the largest family component stopped spanning two partitions.

        Two isolated single-partition families and no crossing edge at all --
        the shape that would mean option 1 had become feasible.
        """
        self.manifest("v1", [
            ("F:t1", "train", "fam-train"),
            ("F:h1", "held-out", "integer-absolute-value"),
        ])
        self.fact("F:t1")
        self.fact("F:h1")
        self.record()
        done = self.run_tool("--check")
        self.assertEqual(done.returncode, 1, _ctx(done))
        self.assertIn("FAIL F2", done.stdout, _ctx(done))

    def test_the_pinned_crossings_disappearing_is_a_finding(self) -> None:
        """F4: nothing depends across a pinned family any more.

        The blob still spans two evaluation partitions and still contains a
        pin, so F2 and F3 stay quiet and F4 is the only thing this can trip.
        """
        self.manifest("v1", [
            ("F:t1", "train", "fam-train"),
            ("F:d1", "development", "fam-dev"),
            ("F:h1", "held-out", "integer-absolute-value"),
        ])
        self.fact("F:t1", ["F:d1", "F:h1"])
        self.fact("F:d1")
        self.fact("F:h1")
        self.record()
        done = self.run_tool("--check")
        # F3 is satisfied (the blob holds a pin) and F4 must not fire either:
        # `fam-train -> integer-absolute-value` IS incident to a pin.
        self.assertEqual(done.returncode, 0, _ctx(done))
        # Now remove that edge and keep the blob otherwise identical.
        self.fact("F:t1", ["F:d1"])
        self.write(f"artifacts/facts/{'F:h1'.replace(':', '-')}.json",
                   {"id": "F:h1", "depends_on": []})
        done = self.run_tool("--check")
        self.assertEqual(done.returncode, 1, _ctx(done))
        self.assertIn("FAIL F4", done.stdout, _ctx(done))

    def test_a_rule_that_reaches_zero_is_a_finding(self) -> None:
        """F5: the refusal was conditional on the rule not reaching zero.

        One train family and one development family with NO edge between them
        and one pin that nothing crosses would trip F4 first, so the fixture
        keeps a pinned crossing alive and gives the free graph a crossing the
        rule can remove entirely -- leaving `residual + pinned` nonzero. The
        assertion is therefore that F5 stays QUIET while the pinned edges
        exist, which is the half of F5 a mutant can break.
        """
        self.blob_with_both_pins()
        self.record()
        done = self.run_tool("--check")
        self.assertEqual(done.returncode, 0, _ctx(done))
        self.assertNotIn("FAIL F5", done.stdout, _ctx(done))

    def test_no_manifest_is_unanswerable_not_a_finding(self) -> None:
        """Exit 2, never 1: a tool that reports a disagreement when its
        subject was unavailable is wrong about its own subject."""
        done = self.run_tool("--check")
        self.assertEqual(done.returncode, 2, _ctx(done))
        self.assertIn("UNANSWERABLE", done.stdout, _ctx(done))

    def test_a_decoy_nursery_file_does_not_make_this_tool_unanswerable(
        self,
    ) -> None:
        """`MANIFEST_GLOBS` names `nursery-v1.json` plus
        `nursery-v*-extension.json` specifically, mirroring the identical fix
        in `check-partition-edges.py` -- NOT a wide `nursery*.json`, which was
        measured to turn ANY unrelated file dropped in
        `artifacts/autogenesis/` matching it into `Unanswerable`, since
        `Drawn.__init__` raises the moment a matched document lacks a usable
        `entries` list. A decoy named outside the two real patterns must be
        invisible to this tool."""
        self.no_pins_anywhere()
        self.write("artifacts/autogenesis/nursery-zzz-notes.json",
                   {"note": "not a manifest"})
        done = self.run_tool()
        self.assertEqual(done.returncode, 0, _ctx(done))
        self.assertIn("drawn=2", done.stdout, _ctx(done))

    def test_check_without_a_recorded_census_is_unanswerable(self) -> None:
        self.blob_with_both_pins()
        done = self.run_tool("--check")
        self.assertEqual(done.returncode, 2, _ctx(done))
        self.assertIn("UNANSWERABLE", done.stdout, _ctx(done))

    def test_an_internally_inconsistent_census_fails(self) -> None:
        """A recorded count that disagrees with its own component list is a
        defect in the file, not ledger drift, so it FAILS rather than
        printing DRIFT."""
        self.blob_with_both_pins()
        self.record()
        document = self.census()
        document["ledger_block"]["family_components"]["count"] = 99
        self.write(CENSUS, document)
        done = self.run_tool("--check")
        self.assertEqual(done.returncode, 1, _ctx(done))
        self.assertIn("FAIL recorded family_components.count=99", done.stdout,
                      _ctx(done))

    def test_ledger_drift_is_advisory_not_a_failure(self) -> None:
        """The ledger gains edges hourly; equality with a snapshot is not the
        subject.  Drift is REPORTED and the exit stays 0."""
        self.blob_with_both_pins()
        self.record()
        document = self.census()
        document["ledger_block"]["crossings_now"] = 12345
        self.write(CENSUS, document)
        done = self.run_tool("--check")
        self.assertEqual(done.returncode, 0, _ctx(done))
        self.assertIn("DRIFT crossings_now 12345", done.stdout, _ctx(done))

    def test_record_carries_the_ledger_block_forward(self) -> None:
        """Ownership depends on this: the OWNER arm perturbs the committed
        file and demands a byte-identical restore, which a re-measured live
        ledger digest could never survive."""
        self.blob_with_both_pins()
        self.record()
        before = (self.root / CENSUS).read_text()
        self.fact("F:d1", [])            # change the ledger under the file
        self.record()
        after = (self.root / CENSUS).read_text()
        self.assertEqual(json.loads(before)["ledger_block"],
                         json.loads(after)["ledger_block"],
                         "the ledger block must be carried forward")

    def test_record_is_idempotent_on_its_own_output(self) -> None:
        """A second ``--record`` over an unchanged tree must be a no-op.

        Written after `check-generated-artifact-ownership.py`'s OWNER arm went
        red: `size_distribution` was a dict keyed by component SIZE, JSON
        object keys are strings, and a block written in numeric order came
        back re-sorted lexicographically (`"10"` before `"2"`) the moment it
        was carried forward.  The artifact was not a fixed point of its own
        writer, which is exactly what the OWNER arm measures and what no
        other test here would have seen.

        THE FIXTURE IS THE GUARD.  It carries one component of TEN rows and
        one of TWO, because ``"10" < "2"`` lexicographically while ``2 < 10``
        numerically -- a size distribution of `{1: n}` alone round-trips
        cleanly under either ordering and would have passed the whole time.
        """
        rows = [(f"F:c{i}", "train", "fam-chain") for i in range(10)]
        rows += [("F:p1", "development", "fam-pair"),
                 ("F:p2", "development", "fam-pair")]
        rows += [("F:h1", "held-out", "integer-absolute-value"),
                 ("F:l1", "longitudinal", "nat-bootstrap")]
        self.manifest("v1", rows,
                      policy={"evaluation_fact_count":
                              {"minimum": 1, "maximum": 99}})
        for i in range(10):                       # a chain, so one component
            self.fact(f"F:c{i}", [f"F:c{i + 1}"] if i < 9 else [])
        self.fact("F:p1", ["F:p2"])
        self.fact("F:p2")
        self.fact("F:h1")
        self.fact("F:l1")
        self.record()
        first = (self.root / CENSUS).read_text()
        self.record()
        self.assertEqual(first, (self.root / CENSUS).read_text(),
                         "--record must be a fixed point on its own output")

    def test_remeasure_actually_remeasures(self) -> None:
        """The counterpart: a carry-forward that could never be refreshed
        would make the snapshot permanent rather than provenanced."""
        self.blob_with_both_pins()
        self.record()
        before = self.census()["ledger_block"]["crossings_now"]
        self.fact("F:t1", ["F:l1"])      # drop the train -> development edge
        done = self.run_tool("--record", "--remeasure")
        self.assertEqual(done.returncode, 0, _ctx(done))
        self.assertNotEqual(before, self.census()["ledger_block"]["crossings_now"])

    def test_the_proposal_never_writes_a_manifest(self) -> None:
        """ADR-1551 computes its rule and does not apply it.  A --propose that
        edited a manifest would be the decision being made in code."""
        self.blob_with_both_pins()
        manifest = self.root / "artifacts/autogenesis/nursery-v1.json"
        before = manifest.read_text()
        done = self.run_tool("--propose")
        self.assertEqual(done.returncode, 0, _ctx(done))
        self.assertIn("computed and NOT applied", done.stdout, _ctx(done))
        self.assertEqual(before, manifest.read_text())

    def test_a_pinned_family_is_never_proposed_for_a_move(self) -> None:
        """The held-out and longitudinal pins are the rule's hard constraint;
        a proposal that moved one would be exactly the spend ADR-0542 and
        check-autogenesis-nursery.py forbid."""
        self.blob_with_both_pins()
        done = self.run_tool("--propose", "--json")
        self.assertEqual(done.returncode, 0, _ctx(done))
        proposal = json.loads(
            done.stdout[:done.stdout.index("\ndrawn=")]
        )["ledger_block"]["proposal"]
        self.assertEqual(proposal["assignment"]["integer-absolute-value"],
                         "held-out", _ctx(done))
        self.assertEqual(proposal["assignment"]["nat-bootstrap"],
                         "longitudinal", _ctx(done))
        self.assertNotIn("integer-absolute-value", proposal["families_moved"])
        self.assertNotIn("nat-bootstrap", proposal["families_moved"])

    def test_a_pin_holds_even_when_the_manifest_mislabels_it(self) -> None:
        """The pin is by FAMILY NAME, not by today's partition label.

        Written after the mutant that deletes ``f not in PINNED_FAMILIES``
        SURVIVED: every other scenario labels the pinned families held-out and
        longitudinal, which the ``train``/``development`` filter on the next
        line already excludes, so the pin was doing nothing any test could
        see.  A family-name pin that only fires when the partition label
        already fires is not a pin.

        Here ``integer-absolute-value`` is labelled ``development`` -- which
        is itself the ADR-0542 breach shape, and exactly when a rule must not
        start moving it around -- and is pulled hard toward ``train``.  The
        rule must leave it where the manifest put it.
        """
        self.manifest("v1", [
            ("F:t1", "train", "fam-t"), ("F:t2", "train", "fam-t"),
            ("F:x1", "development", "integer-absolute-value"),
            ("F:x2", "development", "integer-absolute-value"),
            ("F:d1", "development", "fam-d"), ("F:d2", "development", "fam-d"),
        ], policy={"evaluation_fact_count": {"minimum": 1, "maximum": 99}})
        self.fact("F:x1", ["F:t1", "F:t2"])
        self.fact("F:x2", ["F:t1"])
        for fact_id in ("F:t1", "F:t2", "F:d1", "F:d2"):
            self.fact(fact_id)
        done = self.run_tool("--propose", "--json")
        self.assertEqual(done.returncode, 0, _ctx(done))
        proposal = json.loads(
            done.stdout[:done.stdout.index("\ndrawn=")]
        )["ledger_block"]["proposal"]
        self.assertNotIn("integer-absolute-value", proposal["families_moved"],
                         "a pinned family must not move even when moving it "
                         "would cut three crossings" + _ctx(done))
        self.assertEqual(proposal["assignment"]["integer-absolute-value"],
                         "development", _ctx(done))

    def test_a_two_module_component_lands_in_one_partition(self) -> None:
        """The property option 1 was supposed to deliver, on the one shape
        where the rule CAN deliver it: two families from different Mathlib
        modules joined by a dependency and split across partitions end up in
        one partition once the rule runs.

        This is the test the brief asked for, and it passes -- which is what
        makes the live tree's refusal a statement about the live graph rather
        than about the rule being unimplementable.
        """
        self.manifest("v1", [
            ("F:a1", "train", "fam-a"), ("F:a2", "train", "fam-a"),
            ("F:b1", "development", "fam-b"), ("F:b2", "development", "fam-b"),
            ("F:c1", "train", "fam-c"), ("F:c2", "train", "fam-c"),
            ("F:d1", "development", "fam-d"), ("F:d2", "development", "fam-d"),
            ("F:h1", "held-out", "integer-absolute-value"),
            ("F:l1", "longitudinal", "nat-bootstrap"),
        ], policy={"evaluation_fact_count": {"minimum": 2, "maximum": 99}})
        # fam-a and fam-b are one component and disagree; fam-c/fam-d are the
        # ballast that keeps both partitions above the floor.
        self.fact("F:a1", ["F:b1"])
        self.fact("F:a2", ["F:b1", "F:b2"])
        for fact_id in ("F:b1", "F:b2", "F:c1", "F:c2", "F:d1", "F:d2",
                        "F:h1", "F:l1"):
            self.fact(fact_id)
        done = self.run_tool("--propose", "--json")
        self.assertEqual(done.returncode, 0, _ctx(done))
        proposal = json.loads(
            done.stdout[:done.stdout.index("\ndrawn=")]
        )["ledger_block"]["proposal"]
        self.assertEqual(proposal["assignment"]["fam-a"],
                         proposal["assignment"]["fam-b"],
                         "a two-family component must land in ONE partition"
                         + _ctx(done))
        self.assertEqual(proposal["residual_cut_at_fixed_point"], 0, _ctx(done))


if __name__ == "__main__":
    unittest.main()
