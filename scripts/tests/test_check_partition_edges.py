#!/usr/bin/env python3
"""Controls for ``scripts/check-partition-edges.py``.

CLAUDE.md: *a checker that cannot fail is worse than no checker.*  The gate
this one replaces for producer purposes was kept green for four days by an
exemption re-scoped 228 -> 230 -> 258 -> 274 to fit whatever it had failed on
(ADR-1546), so the first thing to establish about the replacement is that
every one of its guards can be driven to failure.

The shipped script is never re-implemented here.  ``--root`` (equivalently
``AXEYUM_PARTITION_EDGES_ROOT``) points the real file at a throwaway tree of
three or four small JSON documents, so each guard is driven from a fixture a
reader can hold in their head.  Same device as ``AXEYUM_MERGE_HYGIENE_ROOT``.

Registered with ``scripts/tests/mutation_controls.py`` under
``partition-edges``::

    python3 -m unittest scripts.tests.test_check_partition_edges
    python3 scripts/tests/mutation_controls.py partition-edges

``--no-blame`` is the default in ``gate`` because the fixture trees are not
repositories and the attribution query has nothing to answer; one test opts
back in precisely to check that the gate REPORTS that rather than dying.
"""

from __future__ import annotations

import json
import pathlib
import subprocess
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-partition-edges.py"

BASELINE = "artifacts/autogenesis/partition-edge-baseline-v1.json"
AMENDMENTS = "artifacts/autogenesis/partition-edge-amendments-v1.json"


class PartitionEdgeControls(unittest.TestCase):
    """One scenario per guard in `scripts/check-partition-edges.py`."""

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

    def manifest(self, name: str, rows: dict[str, str], **extra: object) -> None:
        """`rows` is `{fact_id: partition}`; `extra` adds manifest-level keys."""
        document: dict[str, object] = {
            "kind": "axeyum-autogenesis-nursery",
            "entries": [{"fact_id": fact_id, "partition": partition}
                        for fact_id, partition in rows.items()],
        }
        document.update(extra)
        self.write(f"artifacts/autogenesis/nursery-{name}.json", document)

    def fact(self, fact_id: str, depends_on: list[str] | None = None) -> None:
        safe = fact_id.replace(":", "-")
        self.write(f"artifacts/facts/{safe}.json",
                   {"id": fact_id, "depends_on": depends_on or []})

    def baseline(self, edges: list[tuple[str, str]]) -> None:
        self.write(BASELINE, {
            "kind": "axeyum-partition-edge-baseline",
            "schema_version": 1,
            "recorded_date": "2026-09-02",
            "recorded_at_commit": "deadbeef",
            "ledger_sha256": "0" * 64,
            "edges": [{"from": a, "to": b} for a, b in edges],
        })

    def amendments(self, items: list[dict[str, str]]) -> None:
        self.write(AMENDMENTS, {"kind": "axeyum-partition-edge-amendments",
                                "amendments": items})

    # -- the standard fixture ----------------------------------------------

    def one_crossing_and_one_clean(self) -> None:
        """A[train] -> B[development] crosses; C[train] -> D[train] does not.

        Both edges in one tree on purpose. A gate that reported *some* number
        of violations would satisfy a fixture with only the crossing edge; the
        clean edge is what makes the count and the named edge mean something.
        """
        self.manifest("v1", {"F:a": "train", "F:b": "development",
                             "F:c": "train", "F:d": "train"})
        self.fact("F:a", ["F:b"])
        self.fact("F:b")
        self.fact("F:c", ["F:d"])
        self.fact("F:d")

    def gate(self, *args: str, blame: bool = False) -> subprocess.CompletedProcess:
        argv = [sys.executable, str(SCRIPT), "--root", str(self.root), *args]
        if not blame:
            argv.append("--no-blame")
        return subprocess.run(argv, capture_output=True, text=True, timeout=120)

    # -- guard 1: a crossing edge is a violation ---------------------------

    def test_a_crossing_edge_is_a_violation_and_the_clean_one_is_not(self) -> None:
        """The gate's whole subject. Deleting the partition comparison must
        kill this: it names WHICH edge crossed, not merely how many did."""
        self.one_crossing_and_one_clean()
        done = self.gate()
        self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
        self.assertIn("|violations=1|", done.stdout)
        self.assertIn("F:a [train] depends_on F:b [development]", done.stdout)
        self.assertNotIn("F:c", done.stdout)

    def test_a_tree_with_no_crossing_edge_passes(self) -> None:
        """The positive control. Without it every guard below is satisfied by
        a gate that always fails, which is not a gate either."""
        self.manifest("v1", {"F:c": "train", "F:d": "train"})
        self.fact("F:c", ["F:d"])
        self.fact("F:d")
        done = self.gate()
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertIn("|crossing=0|", done.stdout)
        self.assertIn("|PASS", done.stdout)

    def test_an_edge_into_the_longitudinal_population_crosses(self) -> None:
        """`longitudinal` is a partition here, not a fourth kind of nothing.
        ADR-1546's 305-member component reached it, and an evaluation fact
        depending on the longitudinal regression population fuses the two
        exactly as a train/development edge does."""
        self.manifest("v1", {"F:a": "development", "F:z": "longitudinal"})
        self.fact("F:a", ["F:z"])
        self.fact("F:z")
        done = self.gate()
        self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
        self.assertIn("F:a [development] depends_on F:z [longitudinal]", done.stdout)

    def test_an_edge_to_a_fact_outside_the_draw_is_not_a_violation(self) -> None:
        """The subject is the DRAWN population. A dependency on a fact no
        manifest drew has no partition to cross, and reporting it would make
        the gate's count unreadable."""
        self.manifest("v1", {"F:a": "train"})
        self.fact("F:a", ["F:undrawn"])
        self.fact("F:undrawn")
        done = self.gate()
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertIn("|crossing=0|", done.stdout)

    # -- guard 2: an amendment names ONE EDGE ------------------------------

    def test_a_component_exemption_covering_the_edge_suppresses_nothing(self) -> None:
        """THE GUARD THIS GATE EXISTS FOR.

        The exemption below names both endpoints of the crossing edge in a
        `component_fact_ids` set -- exactly the shape
        `check-autogenesis-nursery.py` honours, and exactly the shape that was
        re-scoped 228 -> 230 -> 258 -> 274 in four days to keep that gate
        green. Here it must suppress nothing and be REPORTED as declined,
        because a fact-id set says nothing about which edge anybody reviewed.
        """
        self.one_crossing_and_one_clean()
        self.manifest(
            "v1",
            {"F:a": "train", "F:b": "development", "F:c": "train", "F:d": "train"},
            component_split_exemptions=[{
                "component_fact_ids": ["F:a", "F:b"],
                "reason": "reviewed as a component",
                "date": "2026-09-02",
            }],
        )
        done = self.gate()
        self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
        self.assertIn("|violations=1|", done.stdout)
        self.assertIn("NOT-AN-AMENDMENT", done.stdout)
        self.assertIn("names a component of 2 fact ids and no edge", done.stdout)

    def test_a_per_edge_amendment_suppresses_exactly_that_edge(self) -> None:
        """The other side of the same guard: an amendment that names the edge,
        a reason and a date IS honoured, and only for that edge."""
        self.manifest("v1", {"F:a": "train", "F:b": "development",
                             "F:e": "development", "F:f": "train"})
        self.fact("F:a", ["F:b"])
        self.fact("F:b")
        self.fact("F:e", ["F:f"])
        self.fact("F:f")
        self.amendments([{"from": "F:a", "to": "F:b",
                          "reason": "reviewed edge", "date": "2026-09-02"}])
        done = self.gate()
        self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
        self.assertIn("|amended=1|", done.stdout)
        self.assertIn("|violations=1|", done.stdout)
        self.assertIn("F:e [development] depends_on F:f [train]", done.stdout)
        self.assertNotIn("FAIL: F:a", done.stdout)

    def test_an_amendment_missing_a_field_is_reported_and_not_honoured(self) -> None:
        """A malformed amendment is a committed defect. Reading it as absent
        would be the quiet half of the same failure -- the edge stays a
        violation, but nobody learns the amendment they wrote does nothing."""
        self.one_crossing_and_one_clean()
        self.amendments([{"from": "F:a", "to": "F:b", "date": "2026-09-02"}])
        done = self.gate()
        self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
        self.assertIn("|amended=0|", done.stdout)
        self.assertIn("AMENDMENT-REJECTED", done.stdout)
        self.assertIn("missing reason", done.stdout)

    # -- guard 3: the baseline ratchet --------------------------------------

    def test_an_edge_in_the_baseline_does_not_fail_the_gate(self) -> None:
        """The ratchet's whole point: the crossings that already existed are
        the re-partition's to repair, and a gate that blocks every push until
        they are is a gate people disable."""
        self.one_crossing_and_one_clean()
        self.baseline([("F:a", "F:b")])
        done = self.gate("--baseline")
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertIn("|baselined=1|violations=0|", done.stdout)

    def test_an_edge_absent_from_the_baseline_fails_the_gate(self) -> None:
        """And the other half: a NEW crossing blocks immediately, even while
        198 recorded ones are still outstanding."""
        self.manifest("v1", {"F:a": "train", "F:b": "development",
                             "F:e": "development", "F:f": "train"})
        self.fact("F:a", ["F:b"])
        self.fact("F:b")
        self.fact("F:e", ["F:f"])
        self.fact("F:f")
        self.baseline([("F:a", "F:b")])
        done = self.gate("--baseline")
        self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
        self.assertIn("|baselined=1|violations=1|", done.stdout)
        self.assertIn("F:e [development] depends_on F:f [train]", done.stdout)

    def test_recording_refuses_to_grow_the_baseline(self) -> None:
        """THE RATCHET IS IN THE WRITING, not the reading.

        If re-recording could enlarge the set, a lane that hit the gate would
        clear it in one command and this would be the growing component
        exemption again under a new name. Nothing may be written.
        """
        self.manifest("v1", {"F:a": "train", "F:b": "development",
                             "F:e": "development", "F:f": "train"})
        self.fact("F:a", ["F:b"])
        self.fact("F:b")
        self.fact("F:e", ["F:f"])
        self.fact("F:f")
        self.baseline([("F:a", "F:b")])
        before = (self.root / BASELINE).read_text()
        done = self.gate("--record-baseline")
        self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
        self.assertIn("REFUSED-TO-GROW-BASELINE", done.stdout)
        self.assertIn("NEW F:e -> F:f", done.stdout)
        self.assertEqual((self.root / BASELINE).read_text(), before,
                         "the refused recording still wrote the file")

    def test_recording_a_shrunken_set_is_accepted_and_reported(self) -> None:
        """The positive control for the refusal: a baseline that got SMALLER
        because an edge was repaired records, and says by how much. Without
        this, `refuses to grow` is satisfiable by a mode that never writes."""
        self.one_crossing_and_one_clean()
        self.baseline([("F:a", "F:b"), ("F:gone", "F:also-gone")])
        done = self.gate("--record-baseline")
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertIn("RECORDED|edges=1|shrank_by=1", done.stdout)
        recorded = json.loads((self.root / BASELINE).read_text())
        self.assertEqual(recorded["edges"],
                         [{"from": "F:a", "from_partition": "train",
                           "to": "F:b", "to_partition": "development"}])

    def test_a_repaired_baseline_edge_is_reported_not_silently_kept(self) -> None:
        """A baseline that outlives its edges is a ratchet that stopped
        ratcheting. The gate says which edge was repaired so the gain gets
        locked in rather than quietly held as headroom for the next one."""
        self.manifest("v1", {"F:c": "train", "F:d": "train"})
        self.fact("F:c", ["F:d"])
        self.fact("F:d")
        self.baseline([("F:a", "F:b")])
        done = self.gate("--baseline")
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertIn("REPAIRED F:a -> F:b", done.stdout)

    # -- guard 4: exit 2 is `cannot answer` ---------------------------------

    def test_no_manifest_is_exit_two_not_exit_one(self) -> None:
        """A gate that reports a disagreement when its subject was unavailable
        is wrong about its own subject, which this repository has shipped
        three times in one day. No manifest means NO DRAWN POPULATION, which
        is not the same finding as a clean one."""
        self.fact("F:a", ["F:b"])
        done = self.gate()
        self.assertEqual(done.returncode, 2, done.stdout + done.stderr)
        self.assertIn("PARTITION-EDGES|UNANSWERABLE", done.stdout)
        self.assertIn("no nursery manifest", done.stdout)

    def test_an_absent_fact_ledger_is_exit_two(self) -> None:
        """The other unanswerable input. An empty `depends_on` graph and an
        ABSENT one are indistinguishable in the violation count and must not
        be indistinguishable in the exit status."""
        self.manifest("v1", {"F:a": "train"})
        (self.root / "artifacts/facts").rmdir()
        done = self.gate()
        self.assertEqual(done.returncode, 2, done.stdout + done.stderr)
        self.assertIn("artifacts/facts is absent", done.stdout)

    def test_baseline_mode_without_a_baseline_file_is_exit_two(self) -> None:
        """`--baseline` with no baseline is not `everything is new`. Ratcheting
        against a file that does not exist would report every recorded edge as
        a fresh violation, which reads as a catastrophe and is a missing
        file."""
        self.one_crossing_and_one_clean()
        done = self.gate("--baseline")
        self.assertEqual(done.returncode, 2, done.stdout + done.stderr)
        self.assertIn("cannot ratchet against a baseline that does not exist",
                      done.stdout)

    def test_two_manifests_disagreeing_on_a_partition_is_exit_two(self) -> None:
        """A fact in two partitions makes every edge touching it meaningless.
        That is a broken input, not a crossing, so it is 2 rather than 1."""
        self.manifest("v1", {"F:a": "train"})
        self.manifest("v2", {"F:a": "development"})
        self.fact("F:a")
        done = self.gate()
        self.assertEqual(done.returncode, 2, done.stdout + done.stderr)
        self.assertIn("is train in", done.stdout)

    # -- attribution --------------------------------------------------------

    def test_attribution_degrades_to_a_named_unknown_outside_a_repository(self) -> None:
        """The fixture tree is not a repository. A gate that died because it
        could not run a version-control query would be failing on a fact about
        where it was invoked; it must say `unknown` and keep the finding."""
        self.one_crossing_and_one_clean()
        done = self.gate(blame=True)
        self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
        self.assertIn("introduced by unknown", done.stdout)


if __name__ == "__main__":
    unittest.main()
