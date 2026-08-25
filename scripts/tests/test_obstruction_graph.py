"""Controls for the obstruction graph: its generator, its validator, its blindness.

Three properties, and each one has been a real failure somewhere in this
repository rather than a hypothetical:

1.  **The graph is derived, and a regeneration is byte-stable.** A generated
    artifact that drifts from its generator is a hand-authored artifact wearing
    a generator's name, which is exactly what doc 243 forbids for this graph.
2.  **Every validator rule can fail.** One corrupt document per guard, each
    asserting the SPECIFIC message rather than merely a nonzero exit -- a test
    that only checks "it failed" survives the deletion of the guard it was
    written for whenever any other rule also fires, and this file has
    `jsonschema` available, so several of them do.
3.  **A held-out id is refused by BOTH programs.** Generation and validation are
    separate refusals on purpose: a capsule registered against one held-out row
    cost 19 of 76 held-out propositions on 2026-08-21, and one guard between the
    evidence and the artifact is one guard.

Every case runs against a scratch copy of the real inputs, never against the
worktree. Mutation testing edits a tracked source file in place, and a lane that
mutated a constant in the shared checkout made a sibling lane's suite report
eight failures that were not theirs (`CLAUDE.md`, multi-agent hygiene).
"""

from __future__ import annotations

import contextlib
import copy
import importlib.util
import io
import json
import pathlib
import shutil
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
GRAPH = ROOT / "artifacts/autogenesis/obstruction-graph-v1.json"

#: Everything the generator reads, and nothing else. Copied rather than
#: referenced so a test can corrupt one file without touching the worktree.
COPIED = (
    "artifacts/facts",
    "artifacts/episodes",
    "artifacts/ontology/obstruction-graph.schema.json",
    "artifacts/autogenesis/nursery-v1.json",
    "artifacts/autogenesis/knowledge-overlay-v1.json",
    "artifacts/autogenesis/tactic-catalog-v1.json",
    "artifacts/autogenesis/must-decline-mutations-v1.json",
)


def load_script(name: str):
    """Import a hyphenated script by path. A fresh module object every call.

    Fresh matters: a test that repoints module-level paths at a scratch tree
    must not leave the next test pointed there.
    """
    path = ROOT / "scripts" / name
    spec = importlib.util.spec_from_file_location(name.replace("-", "_").removesuffix(".py"), path)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def scratch_root(tmp: pathlib.Path) -> pathlib.Path:
    root = tmp / "repo"
    for relative in COPIED:
        source = ROOT / relative
        target = root / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        if source.is_dir():
            shutil.copytree(source, target)
        else:
            shutil.copy2(source, target)
    autogenesis = root / "artifacts/autogenesis"
    for record in sorted((ROOT / "artifacts/autogenesis").glob("*-decline-v*.json")):
        shutil.copy2(record, autogenesis / record.name)
    return root


def point_generator(module, root: pathlib.Path) -> None:
    module.ROOT = root
    module.EPISODES = root / "artifacts/episodes"
    module.AUTOGENESIS = root / "artifacts/autogenesis"
    module.NURSERY = module.AUTOGENESIS / "nursery-v1.json"
    module.OVERLAY = module.AUTOGENESIS / "knowledge-overlay-v1.json"
    module.CATALOG = module.AUTOGENESIS / "tactic-catalog-v1.json"
    module.MUST_DECLINE = module.AUTOGENESIS / "must-decline-mutations-v1.json"
    module.FACTS = root / "artifacts/facts"
    module.OUTPUT = module.AUTOGENESIS / "obstruction-graph-v1.json"


def point_validator(module, root: pathlib.Path) -> None:
    module.ROOT = root
    module.SCHEMA = root / "artifacts/ontology/obstruction-graph.schema.json"
    module.OVERLAY = root / "artifacts/autogenesis/knowledge-overlay-v1.json"
    module.CATALOG = root / "artifacts/autogenesis/tactic-catalog-v1.json"
    module.NURSERY = root / "artifacts/autogenesis/nursery-v1.json"
    module.FACTS = root / "artifacts/facts"
    module.DEFAULT_GRAPH = root / "artifacts/autogenesis/obstruction-graph-v1.json"


def committed_graph() -> dict:
    return json.loads(GRAPH.read_text(encoding="utf-8"))


def held_out_id() -> str:
    manifest = json.loads((ROOT / "artifacts/autogenesis/nursery-v1.json").read_text())
    return sorted(
        entry["fact_id"] for entry in manifest["entries"] if entry.get("partition") == "held-out"
    )[0]


class Regeneration(unittest.TestCase):
    def test_the_committed_graph_is_a_regeneration(self) -> None:
        """`--check` against the worktree. A stale artifact is a hand-authored one."""
        generator = load_script("gen-obstruction-graph.py")
        self.assertEqual(generator.main(["--check"]), 0)

    def test_regeneration_is_byte_stable(self) -> None:
        """Two derivations of the same inputs produce the same bytes.

        Sorted keys and digest-derived ids are the mechanism; this is the
        measurement. A generator whose output depended on filesystem order would
        pass `--check` on the machine that wrote it and fail everywhere else.
        """
        with tempfile.TemporaryDirectory() as tmp:
            root = scratch_root(pathlib.Path(tmp))
            first = load_script("gen-obstruction-graph.py")
            point_generator(first, root)
            document, breaches = first.derive()
            self.assertEqual(breaches, [])
            second = load_script("gen-obstruction-graph.py")
            point_generator(second, root)
            again, _ = second.derive()
            self.assertEqual(first.render(document), second.render(again))

    def test_the_dashboard_is_a_regeneration(self) -> None:
        dashboard = load_script("gen-obstruction-dashboard.py")
        self.assertEqual(dashboard.main(["--check"]), 0)

    def test_the_committed_graph_validates(self) -> None:
        validator = load_script("validate-obstruction-graph.py")
        self.assertEqual(validator.validate_document(committed_graph()), [])

    def test_an_obstruction_id_is_a_digest_of_its_cluster_key(self) -> None:
        """Nothing in this graph is named by judgement."""
        validator = load_script("validate-obstruction-graph.py")
        for entity in committed_graph()["entities"]:
            self.assertEqual(entity["id"], validator.cluster_id(entity["cluster_key"]))

    def test_the_generator_refuses_an_empty_derivation(self) -> None:
        """A census that found nothing must not exit 0 for a tree that is not there."""
        with tempfile.TemporaryDirectory() as tmp:
            root = scratch_root(pathlib.Path(tmp))
            for directory in (root / "artifacts/episodes").iterdir():
                if directory.is_dir():
                    shutil.rmtree(directory)
            generator = load_script("gen-obstruction-graph.py")
            point_generator(generator, root)
            self.assertEqual(generator.main([]), 1)

    def test_the_generator_refuses_an_unclassifiable_decline_record(self) -> None:
        """A new decline shape must be classified, never silently dropped.

        This is the checker-that-cannot-fail defect one arrow upstream: the
        census would keep exiting 0 while measuring less and less of the world.
        """
        with tempfile.TemporaryDirectory() as tmp:
            root = scratch_root(pathlib.Path(tmp))
            (root / "artifacts/autogenesis/novel-shape-decline-v1.json").write_text(
                json.dumps({"schema_version": 1, "kind": "something-new", "state": "unknown-shape"})
            )
            generator = load_script("gen-obstruction-graph.py")
            point_generator(generator, root)
            self.assertEqual(generator.main([]), 1)


class HeldOutIsolation(unittest.TestCase):
    def run_generator_on_a_blind_selection(self) -> tuple[int, str]:
        """Point an episode at a held-out fact and report `(status, stderr)`.

        The stderr is what the two tests below discriminate on. Asserting only
        "it exited 1" would let either of the generator's two independent
        held-out guards be deleted while the other kept the status nonzero --
        the defence is deliberately layered, so the controls have to be too.
        """
        blind = held_out_id()
        with tempfile.TemporaryDirectory() as tmp:
            root = scratch_root(pathlib.Path(tmp))
            episodes = sorted((root / "artifacts/episodes/2026-08-24").glob("episode-*.json"))
            target = episodes[0]
            document = json.loads(target.read_text())
            document["selection"]["fact_id"] = blind
            target.write_text(json.dumps(document))
            generator = load_script("gen-obstruction-graph.py")
            point_generator(generator, root)
            stderr = io.StringIO()
            with contextlib.redirect_stderr(stderr):
                status = generator.main([])
            return status, stderr.getvalue()

    def test_generation_refuses_an_episode_selecting_a_held_out_fact(self) -> None:
        status, stderr = self.run_generator_on_a_blind_selection()
        self.assertEqual(status, 1)
        self.assertIn("selection names a held-out fact", stderr)

    def test_generation_walks_the_rendered_bytes_for_a_held_out_id(self) -> None:
        """The second guard, over the RENDERED document rather than a field.

        The case is one no field-specific guard can see: a decline record whose
        free-text diagnostic names a held-out fact. That diagnostic is copied
        verbatim into `first_blocker.detail`, so the id reaches the artifact
        through a path that never looks like a fact id to anything reading
        fields. `check-autogenesis-holdout-isolation.py` string-walks whole
        artifacts for exactly this reason.
        """
        blind = held_out_id()
        with tempfile.TemporaryDirectory() as tmp:
            root = scratch_root(pathlib.Path(tmp))
            (root / "artifacts/autogenesis/leaky-driver-decline-v1.json").write_text(
                json.dumps(
                    {
                        "schema_version": 1,
                        "kind": "leaky",
                        "state": "driver-declined",
                        "driver": {"diagnostic": f"borrow error while proving {blind}"},
                    }
                )
            )
            generator = load_script("gen-obstruction-graph.py")
            point_generator(generator, root)
            stderr = io.StringIO()
            with contextlib.redirect_stderr(stderr):
                status = generator.main([])
        self.assertEqual(status, 1)
        self.assertIn("rendered document names held-out fact", stderr.getvalue())

    def test_validation_refuses_a_population_naming_a_held_out_fact(self) -> None:
        blind = held_out_id()
        validator = load_script("validate-obstruction-graph.py")
        document = committed_graph()
        entity = next(e for e in document["entities"] if e["population"]["fact_ids"])
        entity["population"]["fact_ids"] = sorted(entity["population"]["fact_ids"] + [blind])
        entity["facts_blocked"] = len(entity["population"]["fact_ids"])
        errors = validator.validate_document(document)
        self.assertTrue(
            any("population names a held-out fact" in error for error in errors),
            f"a held-out population was accepted: {errors}",
        )

    def test_validation_walks_every_string_for_a_held_out_id(self) -> None:
        """A held-out id in a `reason` is as much a breach as one in a population."""
        blind = held_out_id()
        validator = load_script("validate-obstruction-graph.py")
        document = committed_graph()
        document["links"][0]["reason"] = f"mentions {blind} in prose"
        errors = validator.validate_document(document)
        self.assertTrue(
            any("appear as strings in this document" in error for error in errors),
            f"a held-out id in a link reason was accepted: {errors}",
        )

    def test_validation_refuses_a_held_out_partition_count(self) -> None:
        """`partitions` is a separate object and can lie without naming an id."""
        validator = load_script("validate-obstruction-graph.py")
        document = committed_graph()
        entity = next(e for e in document["entities"] if e["population"]["fact_ids"])
        entity["population"]["partitions"] = dict(entity["population"]["partitions"])
        entity["population"]["partitions"]["held-out"] = 1
        errors = validator.validate_document(document)
        self.assertTrue(
            any("partitions count a held-out row" in error for error in errors),
            f"a held-out partition count was accepted: {errors}",
        )

    def test_the_held_out_guard_fails_closed_on_an_empty_population(self) -> None:
        """A guard whose subject has vanished must not report "no violations"."""
        with tempfile.TemporaryDirectory() as tmp:
            root = scratch_root(pathlib.Path(tmp))
            nursery = root / "artifacts/autogenesis/nursery-v1.json"
            manifest = json.loads(nursery.read_text())
            manifest["entries"] = [
                entry for entry in manifest["entries"] if entry.get("partition") != "held-out"
            ]
            nursery.write_text(json.dumps(manifest))
            validator = load_script("validate-obstruction-graph.py")
            point_validator(validator, root)
            with self.assertRaises(validator.ValidationError):
                validator.held_out_ids()

    def test_no_held_out_id_appears_anywhere_in_the_committed_graph(self) -> None:
        """The generic walk, with a positive control: an empty grep proves nothing."""
        manifest = json.loads((ROOT / "artifacts/autogenesis/nursery-v1.json").read_text())
        blind = {e["fact_id"] for e in manifest["entries"] if e.get("partition") == "held-out"}
        self.assertTrue(blind, "the held-out population is empty; this check has no subject")
        text = GRAPH.read_text(encoding="utf-8")
        self.assertEqual(sorted(ident for ident in blind if ident in text), [])
        control = next(iter(sorted(blind)))
        self.assertIn(control, text + control, "the positive control did not fire")


class ValidatorRules(unittest.TestCase):
    """One corrupt document per guard. Each asserts its own message.

    Asserting the message rather than the exit status is what makes these
    mutation controls: `jsonschema` is installed in this environment and catches
    several of the same shapes, so a test that only demanded a nonzero result
    would survive the deletion of the rule it was written for.
    """

    def setUp(self) -> None:
        self.validator = load_script("validate-obstruction-graph.py")
        self.document = committed_graph()

    def errors(self) -> list[str]:
        return self.validator.validate_document(self.document)

    def assert_error(self, needle: str) -> None:
        errors = self.errors()
        self.assertTrue(
            any(needle in error for error in errors),
            f"no error mentioning {needle!r}; got {errors}",
        )

    def first_with_facts(self) -> dict:
        return next(e for e in self.document["entities"] if e["population"]["fact_ids"])

    def test_an_edited_obstruction_id_is_rejected(self) -> None:
        self.document["entities"][0]["id"] = "O:renamed-by-hand"
        self.assert_error("does not re-derive from cluster_key")

    def test_an_entity_assurance_above_the_ceiling_is_rejected(self) -> None:
        self.document["entities"][0]["assurance"] = "independently-checked"
        self.assert_error("is above the ceiling")

    def test_a_link_assurance_above_the_ceiling_is_rejected(self) -> None:
        self.document["links"][0]["assurance"] = "human-reviewed"
        self.assert_error("assurance 'human-reviewed' is above the ceiling")

    def test_a_provenance_method_other_than_observation_is_rejected(self) -> None:
        self.document["links"][0]["provenance"]["method"] = "kernel-derived"
        self.assert_error("mechanically observed and nothing else")

    def test_a_stale_evidence_digest_is_rejected(self) -> None:
        self.document["entities"][0]["evidence"][0]["sha256"] = "0" * 64
        self.assert_error("hashes to")

    def test_evidence_that_is_not_on_disk_is_rejected(self) -> None:
        self.document["entities"][0]["evidence"][0]["path"] = "artifacts/episodes/nope.json"
        self.assert_error("is not on disk")

    def test_an_obstruction_with_no_evidence_is_rejected(self) -> None:
        self.document["entities"][0]["evidence"] = []
        self.assert_error("an obstruction nobody observed is prose")

    def test_a_facts_blocked_count_that_disagrees_is_rejected(self) -> None:
        entity = self.first_with_facts()
        entity["facts_blocked"] = entity["facts_blocked"] + 1
        self.assert_error("but the population holds")

    def test_a_capability_flag_that_disagrees_with_the_overlay_is_rejected(self) -> None:
        entity = next(
            e for e in self.document["entities"] if not e["candidate_capability"]["exists"]
        )
        entity["candidate_capability"]["exists"] = True
        self.assert_error("but the overlay does not have")

    def test_an_absent_capability_must_say_it_is_proposed(self) -> None:
        entity = self.document["entities"][0]
        entity["candidate_capability"] = {
            "id": "K:invented-capability",
            "exists": False,
            "reason": "a wish that does not say it is one",
        }
        self.assert_error("a wish must say so in its own id")

    def test_a_first_blocker_outside_the_known_set_is_rejected(self) -> None:
        entity = self.document["entities"][0]
        entity["known_blockers"] = [
            {
                "kind": "budget",
                "detail": "unrelated",
                "source": "episode-decline-class",
                "observed_in": "artifacts/episodes",
            }
        ]
        self.assert_error("first_blocker is absent from known_blockers")

    def test_an_unknown_decline_class_is_rejected(self) -> None:
        self.document["entities"][0]["decline_classes"] = ["invented-class"]
        self.assert_error("is not in the v2 episode enum")

    def test_a_tactic_that_does_not_resolve_is_rejected(self) -> None:
        self.document["entities"][0]["tactic_ids"] = ["T:not-a-tactic"]
        self.assert_error("does not resolve in the tactic catalog")

    def test_a_population_fact_outside_the_ledger_is_rejected(self) -> None:
        entity = self.first_with_facts()
        entity["population"]["fact_ids"] = ["F:not-in-the-ledger"]
        entity["facts_blocked"] = 1
        self.assert_error("does not resolve in the ledger")

    def test_a_link_pointing_at_no_obstruction_is_rejected(self) -> None:
        self.document["links"][0]["target"]["id"] = "O:nowhere-00000000"
        self.assert_error("is not an obstruction here")

    def test_a_link_whose_source_kind_is_out_of_domain_is_rejected(self) -> None:
        self.document["links"][0]["source"]["kind"] = "obstruction"
        self.assert_error("is not a source kind of")

    def test_a_duplicate_obstruction_id_is_rejected(self) -> None:
        clone = copy.deepcopy(self.document["entities"][0])
        self.document["entities"].append(clone)
        self.assert_error("duplicate obstruction id")

    def test_an_after_funnel_without_a_resolution_commit_is_rejected(self) -> None:
        entity = self.document["entities"][0]
        entity["resolution"]["after"] = dict(entity["resolution"]["before"])
        self.assert_error("never measured twice")

    def test_a_graph_with_no_entity_is_rejected(self) -> None:
        self.document["entities"] = []
        self.document["links"] = []
        self.assert_error("a validator with no subject is not a pass")


class Census(unittest.TestCase):
    def test_the_funnel_accounts_for_every_episode(self) -> None:
        """`goal` counts every episode read; obstructions plus proofs must equal it."""
        funnel = committed_graph()["funnel"]
        self.assertEqual(funnel["goal"], funnel["episodes_read"])
        self.assertEqual(funnel["obstruction"], funnel["episodes_contributing"])
        self.assertLessEqual(funnel["adapter"], funnel["goal"])
        self.assertLessEqual(funnel["checker"], funnel["reconstruction"])

    def test_every_cluster_names_a_candidate_capability(self) -> None:
        for entity in committed_graph()["entities"]:
            self.assertTrue(entity["candidate_capability"]["id"].startswith("K:"))
            self.assertGreaterEqual(len(entity["candidate_capability"]["reason"]), 16)

    def test_at_least_one_capability_is_named_for_more_than_one_cluster(self) -> None:
        """Doc 228's finding, one layer up: a capability per cluster is a dispatch table.

        If this ever fails, the graph has stopped clustering and every
        obstruction has become its own special case -- which is the shape the
        operation registry had when 24 of 26 entries named exactly one fact.
        """
        counts: dict[str, int] = {}
        for entity in committed_graph()["entities"]:
            key = entity["candidate_capability"]["id"]
            counts[key] = counts.get(key, 0) + 1
        self.assertTrue(
            any(value > 1 for value in counts.values()),
            f"every capability is named for exactly one cluster: {counts}",
        )


if __name__ == "__main__":
    unittest.main()
