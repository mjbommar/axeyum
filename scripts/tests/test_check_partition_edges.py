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

import hashlib
import json
import pathlib
import shutil
import subprocess
import sys
import tempfile
import unittest

def _ctx(done: subprocess.CompletedProcess) -> str:
    """The gate's output as an assertion message, INDENTED so no line starts
    with ``FAIL:``.

    ``mutation_controls.py`` names the tests a mutant killed with
    ``^(?:FAIL|ERROR): (\\S+)`` over unittest's output and cross-checks that
    against ``FAILED (failures=N)``. This gate prints its findings as
    ``FAIL: <fact> [partition] depends_on ...`` at line start, so a raw
    ``done.stdout`` in a failing assertion's message is parsed as extra dead
    tests: M1 was reported ``INCONSISTENT -- the summary line says 6 died but 7
    were named`` for a mutant that killed exactly 6. The harness refusing to
    report a number it cannot cross-check is the harness working; indenting
    costs nothing and keeps the full context.
    """
    return "\n" + "".join(f"  {line}\n"
                          for line in (done.stdout + done.stderr).splitlines())


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-partition-edges.py"

BASELINE = "artifacts/autogenesis/partition-edge-baseline-v1.json"
AMENDMENTS = "artifacts/autogenesis/partition-edge-amendments-v1.json"

# The roles the split was FROZEN with on 2026-08-18: train evaluated, nothing
# training. The default fixture policy, so every pre-ADR-1564 scenario keeps
# `train -> development` as its crossing.
PREREGISTERED_POLICY: dict[str, object] = {
    "required_evaluation_partitions": ["train", "development", "held-out"],
    "training_partitions": [],
    "blind_partitions": ["held-out"],
}

# The roles that ship today (ADR-1564): train is the TRAINING partition.
AMENDED_POLICY: dict[str, object] = {
    "required_evaluation_partitions": ["development", "held-out"],
    "training_partitions": ["train"],
    "blind_partitions": ["held-out"],
}


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

    def manifest(self, name: str, rows: dict[str, str],
                 policy: dict[str, object] | None = None,
                 **extra: object) -> None:
        """`rows` is `{fact_id: partition}`; `extra` adds manifest-level keys.

        THE DEFAULT POLICY IS THE PREREGISTERED ONE, not the shipped one.
        Every scenario written before ADR-1564 uses a `train -> development`
        edge as its crossing, and those scenarios are about amendments,
        baselines and redaction rather than about which partitions are
        evaluated. Handing them the ORIGINAL
        `required_evaluation_partitions: [train, development, held-out]` keeps
        each one's subject intact; the ADR-1564 scenarios below pass the
        shipped roles explicitly and assert the SAME fixture answers
        differently. That contrast is the point -- it is what makes "the roles
        are read from the policy" a measured property rather than a comment.
        """
        document: dict[str, object] = {
            "kind": "axeyum-autogenesis-nursery",
            "policy": PREREGISTERED_POLICY if policy is None else policy,
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

    def one_crossing_only(self) -> None:
        """A[train] -> B[development], and nothing else.

        Used by every scenario whose subject is NOT the partition comparison.
        A clean edge in those fixtures would make the comparison's mutant kill
        them too, and a mutation report where one mutant kills six tests says
        less about the guard than one where it kills the test that is about
        it.
        """
        self.manifest("v1", {"F:a": "train", "F:b": "development"})
        self.fact("F:a", ["F:b"])
        self.fact("F:b")

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
        self.assertEqual(done.returncode, 1, _ctx(done))
        self.assertIn("|violations=1|", done.stdout)
        self.assertIn("F:a [train] depends_on F:b [development]", done.stdout)
        self.assertNotIn("F:c", done.stdout)

    def test_a_drawn_population_with_no_dependency_edges_passes(self) -> None:
        """The positive control. Without it every guard below is satisfied by
        a gate that always fails, which is not a gate either.

        NO EDGES AT ALL, rather than a same-partition edge: the accept case
        for a same-partition edge is the `assertNotIn` in the test above, and
        putting it here as well would mean the partition comparison's mutant
        kills two tests instead of the one whose subject it is."""
        self.manifest("v1", {"F:c": "train", "F:d": "train"})
        self.fact("F:c")
        self.fact("F:d")
        done = self.gate()
        self.assertEqual(done.returncode, 0, _ctx(done))
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
        self.assertEqual(done.returncode, 1, _ctx(done))
        self.assertIn("F:a [development] depends_on F:z [longitudinal]", done.stdout)

    def test_an_edge_to_a_fact_outside_the_draw_is_not_a_violation(self) -> None:
        """The subject is the DRAWN population. A dependency on a fact no
        manifest drew has no partition to cross, and reporting it would make
        the gate's count unreadable."""
        self.manifest("v1", {"F:a": "train"})
        self.fact("F:a", ["F:undrawn"])
        self.fact("F:undrawn")
        done = self.gate()
        self.assertEqual(done.returncode, 0, _ctx(done))
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
        self.one_crossing_only()
        self.manifest(
            "v1",
            {"F:a": "train", "F:b": "development"},
            component_split_exemptions=[{
                "component_fact_ids": ["F:a", "F:b"],
                "reason": "reviewed as a component",
                "date": "2026-09-02",
            }],
        )
        done = self.gate()
        self.assertEqual(done.returncode, 1, _ctx(done))
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
        self.assertEqual(done.returncode, 1, _ctx(done))
        self.assertIn("|amended=1|", done.stdout)
        self.assertIn("|violations=1|", done.stdout)
        self.assertIn("F:e [development] depends_on F:f [train]", done.stdout)
        self.assertNotIn("FAIL: F:a", done.stdout)

    def test_an_amendment_missing_a_field_is_reported_and_not_honoured(self) -> None:
        """A malformed amendment is a committed defect. Reading it as absent
        would be the quiet half of the same failure -- the edge stays a
        violation, but nobody learns the amendment they wrote does nothing."""
        self.one_crossing_only()
        self.amendments([{"from": "F:a", "to": "F:b", "date": "2026-09-02"}])
        done = self.gate()
        self.assertEqual(done.returncode, 1, _ctx(done))
        self.assertIn("|amended=0|", done.stdout)
        self.assertIn("AMENDMENT-REJECTED", done.stdout)
        self.assertIn("missing reason", done.stdout)

    # -- guard 2b: an amendment CLASS is re-derived, never asserted ---------
    #
    # ADR-1563. The class exists so 45 edges into the two pinned longitudinal
    # bootstrap lemmas can leave the baseline with a rule a reader can check,
    # instead of 45 individual judgements nobody can re-derive. That is only
    # true while the checker recomputes the rule; a class taken on the author's
    # word is the component exemption again at a finer unit, so the three tests
    # below drive the recomputation to failure in the two ways it can fail and
    # once in the way it must not.

    def longitudinal_and_a_decoy(self) -> None:
        """A[development] -> Z[longitudinal], and E[development] -> F[train].

        Two crossing edges of DIFFERENT shape in one tree, because the whole
        subject of this guard is that the class applies to one of them and not
        the other. A fixture with only the longitudinal edge could not tell a
        working class check from one that honours every amendment.
        """
        self.manifest("v1", {"F:a": "development", "F:z": "longitudinal",
                             "F:e": "development", "F:f": "train"})
        self.fact("F:a", ["F:z"])
        self.fact("F:z")
        self.fact("F:e", ["F:f"])
        self.fact("F:f")

    def test_the_bootstrap_class_is_honoured_for_an_edge_into_longitudinal(
        self,
    ) -> None:
        """The accept case. Without it, `the class is refused` below is
        satisfied by a checker that refuses every class, which would leave the
        baseline at 198 and the mechanism decorative."""
        self.longitudinal_and_a_decoy()
        self.amendments([{"from": "F:a", "to": "F:z",
                          "class": "depends-on-longitudinal-bootstrap",
                          "reason": "bootstrap lemma", "date": "2026-09-02"}])
        done = self.gate()
        self.assertEqual(done.returncode, 1, _ctx(done))
        self.assertIn("|amended=1|", done.stdout)
        self.assertNotIn("AMENDMENT-REJECTED", done.stdout)
        self.assertIn("F:e [development] depends_on F:f [train]", done.stdout)

    def test_the_bootstrap_class_is_refused_when_the_target_is_not_longitudinal(
        self,
    ) -> None:
        """THE GUARD. The amendment below is well-formed in every field and
        claims the class for a TRAIN target. Honouring it would mean the class
        is a label an author writes rather than a property the manifests
        carry -- and the label would then suppress exactly the train/development
        crossing the whole gate exists to see."""
        self.longitudinal_and_a_decoy()
        self.amendments([{"from": "F:e", "to": "F:f",
                          "class": "depends-on-longitudinal-bootstrap",
                          "reason": "claims a class it does not have",
                          "date": "2026-09-02"}])
        done = self.gate()
        self.assertEqual(done.returncode, 1, _ctx(done))
        self.assertIn("|amended=0|", done.stdout)
        self.assertIn("AMENDMENT-REJECTED", done.stdout)
        self.assertIn("not `longitudinal`", done.stdout)
        self.assertIn("F:e [development] depends_on F:f [train]", done.stdout)

    def test_an_unknown_class_is_refused_rather_than_ignored(self) -> None:
        """A class name nobody implemented must kill the amendment, not be
        skipped as an unrecognised extra field. Reading it as absent would mean
        a typo silently downgrades a class-checked amendment to an unchecked
        one, which is the failure mode with no symptom."""
        self.one_crossing_only()
        self.amendments([{"from": "F:a", "to": "F:b",
                          "class": "depends-on-something-invented",
                          "reason": "reviewed", "date": "2026-09-02"}])
        done = self.gate()
        self.assertEqual(done.returncode, 1, _ctx(done))
        self.assertIn("|amended=0|", done.stdout)
        self.assertIn("is not one of", done.stdout)

    def test_recording_a_baseline_excludes_the_amended_edge(self) -> None:
        """The amendment must be LOAD-BEARING.

        If `--record-baseline` kept an amended edge, the edge would sit in both
        lists, deleting the amendment would change nothing, and every class
        check above would gate nothing observable. The recorded set here holds
        the unamended edge and not the amended one, which is what makes
        deleting an amendment turn its edge back into a violation.
        """
        self.longitudinal_and_a_decoy()
        self.amendments([{"from": "F:a", "to": "F:z",
                          "class": "depends-on-longitudinal-bootstrap",
                          "reason": "bootstrap lemma", "date": "2026-09-02"}])
        done = self.gate("--record-baseline")
        self.assertEqual(done.returncode, 0, _ctx(done))
        self.assertIn("RECORDED|edges=1", done.stdout)
        recorded = json.loads((self.root / BASELINE).read_text())
        self.assertEqual([(e["from"], e["to"]) for e in recorded["edges"]],
                         [("F:e", "F:f")])

    # -- guard 3: the baseline ratchet --------------------------------------

    def test_an_edge_in_the_baseline_does_not_fail_the_gate(self) -> None:
        """The ratchet's whole point: the crossings that already existed are
        the re-partition's to repair, and a gate that blocks every push until
        they are is a gate people disable.

        A held-out crossing rides alongside the plain one, and the baseline
        is RECORDED rather than hand-written -- `self.baseline()` writes bare
        pairs with no salt, which would never exercise the digested path at
        all. Recording it for real is also what proves `--baseline`'s
        comparison matches a live held-out crossing against its DIGESTED
        record, not merely a plain one, without a second test asserting the
        same `violations=0` outcome M4 already owns."""
        self.manifest("v1", {"F:a": "train", "F:b": "development",
                             "F:h": "held-out"})
        self.fact("F:a", ["F:b", "F:h"])
        self.fact("F:b")
        self.fact("F:h")
        record = self.gate("--record-baseline")
        self.assertEqual(record.returncode, 0, _ctx(record))
        done = self.gate("--baseline")
        self.assertEqual(done.returncode, 0, _ctx(done))
        self.assertIn("|baselined=2|violations=0|", done.stdout)

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
        self.assertEqual(done.returncode, 1, _ctx(done))
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
        self.assertEqual(done.returncode, 1, _ctx(done))
        self.assertIn("REFUSED-TO-GROW-BASELINE", done.stdout)
        self.assertIn("NEW F:e -> F:f", done.stdout)
        self.assertEqual((self.root / BASELINE).read_text(), before,
                         "the refused recording still wrote the file")

    def test_recording_a_shrunken_set_is_accepted_and_reported(self) -> None:
        """The positive control for the refusal: a baseline that got SMALLER
        because an edge was repaired records, and says by how much. Without
        this, `refuses to grow` is satisfiable by a mode that never writes."""
        self.one_crossing_only()
        self.baseline([("F:a", "F:b"), ("F:gone", "F:also-gone")])
        done = self.gate("--record-baseline")
        self.assertEqual(done.returncode, 0, _ctx(done))
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
        self.fact("F:c")
        self.fact("F:d")
        self.baseline([("F:a", "F:b")])
        done = self.gate("--baseline")
        self.assertEqual(done.returncode, 0, _ctx(done))
        self.assertIn("REPAIRED F:a -> F:b", done.stdout)

    # -- guard 5: a held-out endpoint is never written in plain text --------

    def held_out_manifest(self, target: str = "F:h") -> None:
        """A[train] -> `target`[held-out], and nothing else."""
        self.manifest("v1", {"F:a": "train", target: "held-out"})
        self.fact("F:a", [target])
        self.fact(target)

    def test_a_held_out_endpoint_is_recorded_as_a_salted_digest_not_plain_text(
        self,
    ) -> None:
        """ADR-1550's own baseline shipped six held-out fact ids in plain
        text, which is exactly what `check-autogenesis-holdout-isolation.py`
        exists to catch. The recorded file must not contain the id at all --
        not as `from`/`to`, not anywhere in the raw bytes -- only its salted
        digest, alongside `held_out_endpoint: true`."""
        self.held_out_manifest()
        done = self.gate("--record-baseline")
        self.assertEqual(done.returncode, 0, _ctx(done))
        raw = (self.root / BASELINE).read_text()
        self.assertNotIn("F:h", raw)
        recorded = json.loads(raw)
        salt = recorded.get("held_out_salt")
        self.assertTrue(salt, "no held_out_salt was recorded")
        [row] = recorded["edges"]
        self.assertEqual(row["from"], "F:a")
        self.assertIs(row["held_out_endpoint"], True)
        self.assertNotEqual(row["to"], "F:h")
        expected = hashlib.sha256(f"{salt}:F:h".encode()).hexdigest()
        self.assertEqual(row["to"], expected)

    def test_a_different_held_out_id_at_the_same_position_is_a_new_violation(
        self,
    ) -> None:
        """The digest must be a function of the ACTUAL id, not a stand-in for
        `this endpoint is held-out`. Pointing the same source at a DIFFERENT
        held-out fact must still be caught as a new, unbaselined crossing --
        otherwise a digest that ignores its input would pass the test above
        for the wrong reason."""
        self.held_out_manifest(target="F:h")
        record = self.gate("--record-baseline")
        self.assertEqual(record.returncode, 0, _ctx(record))
        self.held_out_manifest(target="F:h2")
        done = self.gate("--baseline")
        self.assertEqual(done.returncode, 1, _ctx(done))
        self.assertIn("|violations=1|", done.stdout)

    def test_recording_an_unchanged_held_out_edge_twice_is_byte_identical(
        self,
    ) -> None:
        """Salt reuse under `carry_over`: re-recording an UNCHANGED edge set
        must reproduce byte-identical output, or `check-generated-artifact-
        ownership.py`'s OWNER arm -- which perturbs a committed copy and
        demands the owner restore it byte-for-byte -- could never pass while
        a held-out edge is baselined."""
        self.held_out_manifest()
        first = self.gate("--record-baseline")
        self.assertEqual(first.returncode, 0, _ctx(first))
        before = (self.root / BASELINE).read_text()
        second = self.gate("--record-baseline")
        self.assertEqual(second.returncode, 0, _ctx(second))
        after = (self.root / BASELINE).read_text()
        self.assertEqual(before, after)

    # -- guard 4: exit 2 is `cannot answer` ---------------------------------

    def test_no_manifest_is_exit_two_not_exit_one(self) -> None:
        """A gate that reports a disagreement when its subject was unavailable
        is wrong about its own subject, which this repository has shipped
        three times in one day. No manifest means NO DRAWN POPULATION, which
        is not the same finding as a clean one."""
        self.fact("F:a", ["F:b"])
        done = self.gate()
        self.assertEqual(done.returncode, 2, _ctx(done))
        self.assertIn("PARTITION-EDGES|UNANSWERABLE", done.stdout)
        # The DISTINCTIVE tail, not the shared prefix. `load_policy` also says
        # "no nursery manifest ...", so asserting that alone let the
        # no-manifest guard be deleted with this test still green -- measured
        # as `M6 SURVIVED` the first time these two guards sat in one path.
        self.assertIn("there is no drawn population to check", done.stdout)

    def test_a_decoy_nursery_file_does_not_make_this_gate_unanswerable(
        self,
    ) -> None:
        """`MANIFEST_GLOBS` is `nursery-v1.json` plus `nursery-v*-extension.json`,
        NOT a wide `nursery*.json` -- the wide form was measured to turn ANY
        unrelated file dropped in `artifacts/autogenesis/` matching it into an
        `Unanswerable`, because `load_partitions` raises the moment a matched
        document lacks a usable `entries` list. A decoy with a name outside
        the two real patterns must be invisible to this gate."""
        self.one_crossing_only()
        self.write("artifacts/autogenesis/nursery-zzz-notes.json",
                   {"note": "not a manifest"})
        done = self.gate()
        self.assertEqual(done.returncode, 1, _ctx(done))
        self.assertIn("|manifests=1|", done.stdout)
        self.assertIn("F:a [train] depends_on F:b [development]", done.stdout)

    def test_an_absent_fact_ledger_is_exit_two(self) -> None:
        """The other unanswerable input. An empty `depends_on` graph and an
        ABSENT one are indistinguishable in the violation count and must not
        be indistinguishable in the exit status."""
        self.manifest("v1", {"F:a": "train"})
        (self.root / "artifacts/facts").rmdir()
        done = self.gate()
        self.assertEqual(done.returncode, 2, _ctx(done))
        self.assertIn("artifacts/facts is absent", done.stdout)

    def test_baseline_mode_without_a_baseline_file_is_exit_two(self) -> None:
        """`--baseline` with no baseline is not `everything is new`. Ratcheting
        against a file that does not exist would report every recorded edge as
        a fresh violation, which reads as a catastrophe and is a missing
        file."""
        self.one_crossing_only()
        done = self.gate("--baseline")
        self.assertEqual(done.returncode, 2, _ctx(done))
        self.assertIn("cannot ratchet against a baseline that does not exist",
                      done.stdout)

    def test_two_manifests_disagreeing_on_a_partition_is_exit_two(self) -> None:
        """A fact in two partitions makes every edge touching it meaningless.
        That is a broken input, not a crossing, so it is 2 rather than 1.

        `v2-extension`, not `v2`: `MANIFEST_GLOBS` narrowed from a wide
        `nursery*.json` to `nursery-v1.json` plus `nursery-v*-extension.json`
        specifically, and a plain `nursery-v2.json` matches neither -- see the
        decoy-file guard below, which is the other half of that change."""
        self.manifest("v1", {"F:a": "train"})
        self.manifest("v2-extension", {"F:a": "development"})
        self.fact("F:a")
        done = self.gate()
        self.assertEqual(done.returncode, 2, _ctx(done))
        self.assertIn("is train in", done.stdout)

    # -- guard 6: the partition ROLES come from the policy (ADR-1564) -------

    def test_a_train_development_edge_is_not_a_crossing_under_the_amended_roles(
        self,
    ) -> None:
        """THE ADR-1564 DECISION, measured on the SAME tree as the fixture
        above that calls it a crossing.

        `one_crossing_only` is `F:a [train] -> F:b [development]`, and under
        the preregistered policy every other scenario uses it is a violation.
        Hand the identical population the amended roles and it is not one --
        both directions, because a development row citing a proved train lemma
        and a train row citing a development one are the same permission.

        This is what makes "the roles are read from the policy" a measurement
        rather than a comment: no fact, no edge and no partition changed
        between this test and the one above; only the authority did."""
        self.manifest("v1", {"F:a": "train", "F:b": "development"},
                      policy=AMENDED_POLICY)
        self.fact("F:a", ["F:b"])
        self.fact("F:b", ["F:a"])
        done = self.gate()
        self.assertEqual(done.returncode, 0, _ctx(done))
        self.assertIn("|crossing=0|", done.stdout)
        self.assertIn("|training=train|", done.stdout)

    def test_a_training_edge_to_the_blind_partition_still_crosses_both_ways(
        self,
    ) -> None:
        """THE SEAL. `train` is a training partition and `held-out` is blind,
        so this pair is the one place the ADR-1564 permission must NOT reach:
        blindness once spent cannot be un-spent, and a train row is worked on
        by producers exactly as a development row is.

        Both directions in one fixture on purpose -- they are one decision,
        and splitting them would make the seal's mutant kill two tests."""
        self.manifest("v1", {"F:a": "train", "F:h": "held-out"},
                      policy=AMENDED_POLICY)
        self.fact("F:a", ["F:h"])
        self.fact("F:h", ["F:a"])
        done = self.gate()
        self.assertEqual(done.returncode, 1, _ctx(done))
        self.assertIn("|crossing=2|", done.stdout)
        self.assertIn("F:a [train] depends_on F:h [held-out]", done.stdout)
        self.assertIn("F:h [held-out] depends_on F:a [train]", done.stdout)

    def test_a_development_to_held_out_edge_still_crosses(self) -> None:
        """Two evaluation partitions, neither of them training. ADR-1564
        changed which partitions are evaluated and changed nothing about what
        happens between two that are."""
        self.manifest("v1", {"F:b": "development", "F:h": "held-out"},
                      policy=AMENDED_POLICY)
        self.fact("F:b", ["F:h"])
        self.fact("F:h")
        done = self.gate()
        self.assertEqual(done.returncode, 1, _ctx(done))
        self.assertIn("F:b [development] depends_on F:h [held-out]",
                      done.stdout)

    def test_a_policy_naming_no_evaluation_partition_is_exit_two(self) -> None:
        """A gate that cannot fail is worse than no gate.

        With `required_evaluation_partitions: []` every pair would be
        permitted and this gate would print `crossing=0 ... PASS` over a
        ledger it never judged. The MESSAGE is asserted, not merely the exit
        code: several inputs here are exit 2, and a guard whose test accepts
        any of them is satisfied by the wrong refusal."""
        self.manifest("v1", {"F:a": "train", "F:b": "development"},
                      policy={"required_evaluation_partitions": [],
                              "training_partitions": ["train"],
                              "blind_partitions": []})
        self.fact("F:a", ["F:b"])
        self.fact("F:b")
        done = self.gate()
        self.assertEqual(done.returncode, 2, _ctx(done))
        self.assertIn("required_evaluation_partitions is empty", done.stdout)

    def test_a_policy_that_seals_no_blind_partition_is_exit_two(self) -> None:
        """`blind_partitions: []` would silently unseal the held-out
        population -- the one thing here that cannot be undone -- by making a
        training partition's edges into it ordinary. Refused, not read as
        `nothing is blind`."""
        self.manifest("v1", {"F:a": "train", "F:h": "held-out"},
                      policy={"required_evaluation_partitions":
                              ["development", "held-out"],
                              "training_partitions": ["train"],
                              "blind_partitions": []})
        self.fact("F:a", ["F:h"])
        self.fact("F:h")
        done = self.gate()
        self.assertEqual(done.returncode, 2, _ctx(done))
        self.assertIn("blind_partitions must be a non-empty subset",
                      done.stdout)

    def test_a_partition_that_is_both_training_and_evaluation_is_exit_two(
        self,
    ) -> None:
        """A partition cannot be the thing producers build on AND the thing
        they are scored against. Naming it both is a defect in the policy, and
        reading it as either one silently picks a side."""
        self.manifest("v1", {"F:a": "train", "F:b": "development"},
                      policy={"required_evaluation_partitions":
                              ["train", "development", "held-out"],
                              "training_partitions": ["train"],
                              "blind_partitions": ["held-out"]})
        self.fact("F:a", ["F:b"])
        self.fact("F:b")
        done = self.gate()
        self.assertEqual(done.returncode, 2, _ctx(done))
        self.assertIn("is both a training and an evaluation partition",
                      done.stdout)

    def test_a_manifest_carrying_no_policy_at_all_is_exit_two(self) -> None:
        """Which partitions are evaluated is UNKNOWN, which is not the same as
        nothing crossing. The pre-ADR-1564 gate had the answer compiled in, so
        this input used to be indistinguishable from a clean tree."""
        self.write("artifacts/autogenesis/nursery-v1.json",
                   {"kind": "axeyum-autogenesis-nursery",
                    "entries": [{"fact_id": "F:a", "partition": "train"},
                                {"fact_id": "F:b", "partition": "development"}]})
        self.fact("F:a", ["F:b"])
        self.fact("F:b")
        done = self.gate()
        self.assertEqual(done.returncode, 2, _ctx(done))
        self.assertIn("no nursery manifest carries a `policy` block",
                      done.stdout)

    def test_two_manifests_disagreeing_about_the_roles_is_exit_two(self) -> None:
        """Two authorities is no authority. A gate that picked one of them
        would report on a split that exists in neither file."""
        self.manifest("v1", {"F:a": "train"})
        self.manifest("v2-extension", {"F:b": "development"},
                      policy=AMENDED_POLICY)
        self.fact("F:a", ["F:b"])
        self.fact("F:b")
        done = self.gate()
        self.assertEqual(done.returncode, 2, _ctx(done))
        self.assertIn("disagree about the partition roles", done.stdout)

    # -- attribution --------------------------------------------------------

    def test_attribution_degrades_to_a_named_unknown_outside_a_repository(self) -> None:
        """The fixture tree is not a repository. A gate that died because it
        could not run a version-control query would be failing on a fact about
        where it was invoked; it must say `unknown` and keep the finding."""
        self.one_crossing_only()
        done = self.gate(blame=True)
        self.assertEqual(done.returncode, 1, _ctx(done))
        self.assertIn("introduced by unknown", done.stdout)


class ScoredEvaluationResidueTests(unittest.TestCase):
    """Controls for the `scored-evaluation-residue` amendment class (ADR-1566).

    THE CLASS EXISTS BECAUSE ONE THING IS TRUE AND THREE NEARBY THINGS ARE NOT.
    A blind row that was SCORED against a preregistered protocol legitimately
    ends up citing the training set -- that is what scoring against a training
    set means, and ADR-1565 measured that every one of the six live crossings
    entered at the commit that closed the evaluation, three days after the seal
    and 55 minutes after the protocol. What is NOT true, and what these tests
    drive one at a time, is that any of the following is the same thing:

      * an edge INTO a blind row (blindness spent, not spent-and-recorded);
      * an edge from a blind row the record does not score (a sibling of a
        spent family is still a row nobody evaluated);
      * an edge whose introducing commit PREDATES the preregistration (not
        created by the evaluation; that is ADR-1450's reclassification case);
      * an amendment keyed to anything but the evaluation record.

    THE FIXTURE IS A REAL GIT REPOSITORY, because clause (b) is a question
    about the commit graph and there is no honest way to fake the answer. Three
    commits: the population, then the record carrying `protocol_commit`, then
    the edge. `predating_fixture` inverts the last two, which is the only
    difference between the accept case and the third refusal.

    EVERY EDGE HERE IS `held-out <-> development`, never `held-out <-> train`.
    Both are crossings, but the second is one ONLY through
    `PartitionRoles.is_crossing`'s blind clause -- so M17/M18, whose subject is
    that clause, would kill all six of these tests and stop being single-kill
    mutants for the test whose subject they are. A `held-out`/`development`
    pair crosses through the two-evaluation-partitions arm instead, which no
    mutant in this suite touches.

    Registered with `scripts/tests/mutation_controls.py` under
    ``partition-edges`` (M24-M27).
    """

    SALT = "0123456789abcdef" * 4
    RECORD_ID = "test-evaluation-1"
    FAMILY = "fixture-family"

    def setUp(self) -> None:
        scratch = pathlib.Path("/data0/axeyum/scratch")
        self._tmp = tempfile.TemporaryDirectory(
            dir=scratch if scratch.is_dir() else None)
        self.addCleanup(self._tmp.cleanup)
        self.root = pathlib.Path(self._tmp.name) / "tree"
        (self.root / "artifacts/autogenesis").mkdir(parents=True)
        (self.root / "artifacts/facts").mkdir(parents=True)
        self.git("init", "-q", "-b", "main")
        self.git("config", "user.email", "fixture@example.invalid")
        self.git("config", "user.name", "fixture")

    # -- fixture construction ----------------------------------------------

    def git(self, *args: str) -> subprocess.CompletedProcess:
        done = subprocess.run(["git", *args], cwd=self.root,
                              capture_output=True, text=True, timeout=60)
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        return done

    def commit(self, message: str) -> str:
        self.git("add", "-A")
        self.git("commit", "-q", "-m", message)
        return self.git("rev-parse", "HEAD").stdout.strip()

    def write(self, rel: str, document: object) -> None:
        path = self.root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(document, indent=2, sort_keys=True) + "\n")

    def fact(self, fact_id: str, depends_on: list[str] | None = None) -> None:
        self.write(f"artifacts/facts/{fact_id.replace(':', '-')}.json",
                   {"id": fact_id, "depends_on": depends_on or []})

    def digest(self, fact_id: str) -> str:
        return hashlib.sha256(f"{self.SALT}:{fact_id}".encode()).hexdigest()

    def population(self, rows: list[tuple[str, str, str | None]]) -> None:
        """`rows` is `(fact_id, partition, family)`, plus a salted baseline."""
        self.write("artifacts/autogenesis/nursery-v1.json", {
            "kind": "axeyum-autogenesis-nursery",
            "policy": AMENDED_POLICY,
            "entries": [{"fact_id": fact_id, "partition": partition,
                         **({} if family is None else {"family": family})}
                        for fact_id, partition, family in rows],
        })
        self.write(BASELINE, {"kind": "axeyum-partition-edge-baseline",
                              "schema_version": 1, "held_out_salt": self.SALT,
                              "edges": []})

    def record(self, scored: list[str], protocol_commit: str | None = None,
               state: str = "scored") -> None:
        self.write("artifacts/autogenesis/holdout-evaluation-v1.json", {
            "kind": "axeyum-holdout-evaluation-record",
            "record_id": self.RECORD_ID,
            "family": self.FAMILY,
            "state": state,
            "protocol_commit": protocol_commit or "",
            "outcomes": [{"fact_id": fact_id} for fact_id in scored],
        })

    def amendments(self, items: list[dict]) -> None:
        self.write(AMENDMENTS, {"kind": "axeyum-partition-edge-amendments",
                                "amendments": items})

    def residue(self, frm: str, to: str, **overrides: object) -> dict:
        item = {"class": "scored-evaluation-residue",
                "evaluation_record": self.RECORD_ID,
                "from": frm, "to": to,
                "reason": "the residue of a scored evaluation",
                "date": "2026-09-02"}
        item.update(overrides)
        return item

    def gate(self, *args: str) -> subprocess.CompletedProcess:
        return subprocess.run(
            [sys.executable, str(SCRIPT), "--root", str(self.root), *args,
             "--no-blame"], capture_output=True, text=True, timeout=120)

    # -- the two fixture shapes --------------------------------------------

    def scored_fixture(self, extra_blind: bool = False) -> None:
        """The honest one: population, then protocol, THEN the edge.

        `extra_blind` adds a second blind row of the same family that the
        record does NOT score -- the sibling that clause (a) is about.
        """
        rows = [("F:blind", "held-out", self.FAMILY),
                ("F:dev", "development", "other-family")]
        if extra_blind:
            rows.append(("F:sibling", "held-out", self.FAMILY))
        self.population(rows)
        self.fact("F:blind")
        self.fact("F:dev")
        if extra_blind:
            self.fact("F:sibling")
        self.record(["F:blind"])
        self.commit("the drawn population, no edges")
        protocol = self.commit_protocol()
        # THE EDGE, strictly after the preregistration.
        self.fact("F:blind", ["F:dev"])
        if extra_blind:
            self.fact("F:sibling", ["F:dev"])
        self.commit("close the evaluation")
        self.assertTrue(protocol)

    def commit_protocol(self) -> str:
        """Stamp the record with the HEAD it was preregistered against."""
        head = self.git("rev-parse", "HEAD").stdout.strip()
        self.record(["F:blind"], protocol_commit=head)
        self.commit("preregister the scoring protocol")
        return head

    def predating_fixture(self) -> None:
        """The edge FIRST, the preregistration after it.

        The only difference from `scored_fixture`, and the whole of ADR-1565's
        argument: an edge older than the protocol was not created by the
        evaluation.
        """
        self.population([("F:blind", "held-out", self.FAMILY),
                         ("F:dev", "development", "other-family")])
        self.fact("F:blind", ["F:dev"])
        self.fact("F:dev")
        self.record(["F:blind"])
        self.commit("the population WITH the edge already in it")
        self.commit_protocol()

    # -- the positive control ----------------------------------------------

    def test_a_scored_evaluations_residue_edge_is_honoured(self) -> None:
        """THE ACCEPT CASE. Without it every refusal below is satisfied by a
        class that never honours anything, which is not a class."""
        self.scored_fixture()
        self.amendments([self.residue("F:blind", "F:dev")])
        done = self.gate()
        self.assertEqual(done.returncode, 0, _ctx(done))
        self.assertIn("|amended=1|", done.stdout)
        self.assertIn("|violations=0|", done.stdout)

    def test_the_same_edge_is_a_violation_with_no_amendment(self) -> None:
        """THE NEGATIVE HALF of the accept case. Without it the test above is
        satisfied by a fixture in which nothing ever crossed."""
        self.scored_fixture()
        self.amendments([])
        done = self.gate()
        self.assertEqual(done.returncode, 1, _ctx(done))
        self.assertIn("F:blind [held-out] depends_on F:dev [development]",
                      done.stdout)

    # -- clause (d): keyed to the record, never to a fact ------------------

    def test_an_amendment_naming_no_evaluation_record_is_refused(self) -> None:
        """M24. The key is what makes this a class rather than a judgement: a
        record is a committed artifact with a preregistration commit in it, and
        `evaluation_record` is the only field this class reads for identity."""
        self.scored_fixture()
        self.amendments([self.residue(self.digest("F:blind"), "F:dev",
                                      evaluation_record=None)])
        done = self.gate()
        self.assertEqual(done.returncode, 1, _ctx(done))
        self.assertIn("must name `evaluation_record`", done.stdout)
        self.assertIn("|violations=1|", done.stdout)

    # -- clause (a): the blind endpoint is a SCORED row --------------------

    def test_an_unscored_sibling_of_the_scored_family_is_still_a_leak(self) -> None:
        """M25. `families_spent` is real, but spent is not scored: a sibling
        the record does not list is a row nobody evaluated, and an edge from it
        is the ordinary breach wearing the scored family's name."""
        self.scored_fixture(extra_blind=True)
        self.amendments([self.residue("F:blind", "F:dev"),
                         self.residue("F:sibling", "F:dev")])
        done = self.gate()
        self.assertEqual(done.returncode, 1, _ctx(done))
        self.assertIn("is not a scored row of family", done.stdout)
        self.assertIn("F:sibling [held-out] depends_on F:dev [development]",
                      done.stdout)
        self.assertNotIn("F:blind [held-out] depends_on", done.stdout)

    # -- clause (c): the direction is half the rule ------------------------

    def test_an_edge_into_a_scored_blind_row_can_never_carry_the_class(self) -> None:
        """M26. THE MUTANT WORTH READING TWICE.

        Every other clause of this amendment HOLDS: the blind endpoint is the
        scored row of the scored family, the record is scored, and the edge
        postdates the preregistration. Only the direction is wrong -- a drawn
        row's proof cites the blind row rather than the other way round -- and
        that is blindness being spent, which no evaluation record retroactively
        licenses. If clause (c) were written against the edge's SOURCE family
        instead of its blind ENDPOINT, clause (a) would refuse this too and
        M26 would kill nothing.
        """
        self.population([("F:blind", "held-out", self.FAMILY),
                         ("F:dev", "development", "other-family")])
        self.fact("F:blind")
        self.fact("F:dev")
        self.record(["F:blind"])
        self.commit("the drawn population, no edges")
        self.commit_protocol()
        self.fact("F:dev", ["F:blind"])
        self.commit("a drawn row's proof cites the blind row")
        self.amendments([self.residue("F:dev", self.digest("F:blind"))])
        done = self.gate()
        self.assertEqual(done.returncode, 1, _ctx(done))
        self.assertIn("does not run FROM a blind row", done.stdout)
        self.assertIn("F:dev [development] depends_on F:blind [held-out]",
                      done.stdout)

    # -- clause (b): the preregistration predates the edge -----------------

    def test_an_edge_older_than_the_preregistration_is_refused(self) -> None:
        """M27. ADR-1565's argument, mechanised and inverted.

        Same population, same record, same family, same direction; the only
        difference from the accept case is that the edge was in the tree
        BEFORE the protocol commit. Then the row was not blind when it was
        scored, the residue story is false, and the instrument is ADR-1450's
        reclassification rather than this class.
        """
        self.predating_fixture()
        self.amendments([self.residue(self.digest("F:blind"), "F:dev")])
        done = self.gate()
        self.assertEqual(done.returncode, 1, _ctx(done))
        self.assertIn("strict git ancestor", done.stdout)
        self.assertIn("|violations=1|", done.stdout)

    def test_an_unscored_record_licenses_nothing(self) -> None:
        """A preregistration is not a result. Same fixture, `state` flipped."""
        self.scored_fixture()
        head = self.git("rev-parse", "HEAD~1").stdout.strip()
        self.record(["F:blind"], protocol_commit=head, state="preregistered")
        self.commit("downgrade the record to a preregistration")
        self.amendments([self.residue(self.digest("F:blind"), "F:dev")])
        done = self.gate()
        self.assertEqual(done.returncode, 1, _ctx(done))
        self.assertIn("state is 'preregistered', not `scored`", done.stdout)

    # -- the redaction the class depends on --------------------------------

    def test_the_preregistration_clause_is_reported_when_it_cannot_be_asked(
        self,
    ) -> None:
        """A tree with no version control cannot answer clause (b), and the
        gate must SAY so rather than pass in silence.

        Three real trees here have no history: `mutation_controls.py` copies
        the checkout with `.git` in its `ignore_patterns`, a lane snapshot from
        `git archive | tar -x` has none, and a fixture tree is built from
        scratch. Refusing every amendment in those would make this gate red on
        a fact about WHERE it ran; honouring silently would tell a reader a
        clause held that was never asked. So the amendment is honoured and the
        skipped clause is printed and counted.
        """
        self.scored_fixture()
        shutil.rmtree(self.root / ".git")
        self.amendments([self.residue("F:blind", "F:dev")])
        done = self.gate()
        self.assertEqual(done.returncode, 0, _ctx(done))
        self.assertIn("CLASS-UNVERIFIED", done.stdout)
        self.assertIn("preregistration clause", done.stdout)
        self.assertIn("|class_unverified=1|", done.stdout)

    def test_the_amendment_names_no_blind_row_and_still_matches(self) -> None:
        """The property that made the six edges amendable at all (ADR-1563
        recorded them as structurally un-amendable for exactly this reason).

        The artifact carries a salted digest; the gate resolves it through the
        live manifests and honours the edge. A `grep` of the amendment file for
        the blind row's id finds nothing, and that is asserted here rather than
        described, because it is the whole justification for the format.
        """
        self.scored_fixture()
        self.amendments([self.residue(self.digest("F:blind"), "F:dev")])
        written = (self.root / AMENDMENTS).read_text()
        self.assertNotIn("F:blind", written)
        self.assertIn(self.digest("F:blind"), written)
        done = self.gate()
        self.assertEqual(done.returncode, 0, _ctx(done))
        self.assertIn("|amended=1|", done.stdout)


if __name__ == "__main__":
    unittest.main()
