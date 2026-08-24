#!/usr/bin/env python3
"""Mutation controls for the agent-episode gate.

One corrupt document per named rule, built in a temporary directory from a
committed fixture, plus the discriminating cases that stop the gate from being
a rubber stamp in the other direction: an episode that is merely *unusual* must
still pass, and a non-ancestor commit without `--require-ancestor` must WARN
rather than fail.

Every rule below is deletable, and deleting it kills exactly the test named
beside it (`scripts/tests/mutation_controls.py`, suite ``agent-episode``)::

    schema                              -> a_schema_violation_is_a_failure
    git-commit-ancestor                 -> a_non_ancestor_commit_fails_when_required
    frontier-digest                     -> a_frontier_digest_mismatch_is_a_failure
    frontier-reverify                   -> a_stale_frontier_is_rejected
    web-snapshot-digest                 -> a_web_snapshot_digest_mismatch_is_a_failure
    ledger-writes-must-be-zero          -> a_nonzero_ledger_write_is_a_failure
    held-out-reference                  -> a_held_out_id_anywhere_is_a_failure
    proved-requires-zero-checker-status -> proved_with_a_failing_checker_is_a_failure
    proved-requires-checker-command     -> proved_with_no_checker_command_is_a_failure
    proposal-digest                     -> a_proposal_digest_mismatch_is_a_failure
    empty-transcript                    -> an_empty_transcript_is_a_failure
    unknown-fact-id                     -> an_unknown_fact_id_is_a_failure
    no-episodes-is-not-a-pass           -> checking_nothing_is_not_a_pass
    empty-fact-ledger fail-closed       -> an_empty_fact_ledger_is_an_error
    missing-nursery fail-closed         -> a_missing_nursery_is_an_error

The rule NAME is asserted, never just the exit status, and that is load-bearing
for two of them: `ledger_writes: 1` also violates the schema's ``maximum: 0``,
so a test that only asserted "this fails" would survive the deletion of the rule
it is supposed to pin. `test_the_held_out_set_agrees_with_the_isolation_gate`
cross-checks the imported population against an independent re-derivation and
against the manifest's own count, because the whole held-out rule rests on that
one import being the same set the isolation gate uses.
"""

from __future__ import annotations

import importlib.util
import json
import pathlib
import subprocess
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-agent-episode.py"
FRONTIER = ROOT / "scripts/fact-frontier.py"
NURSERY = ROOT / "artifacts/autogenesis/nursery-v1.json"
FIXTURES = ROOT / "artifacts/episodes/fixtures"
DECLINED = FIXTURES / "episode-declined-v1.json"
PROVED = FIXTURES / "episode-proved-v1.json"

BAD_SHA = "0" * 64


def _module(path: pathlib.Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


gate = _module(SCRIPT, "agent_episode_gate")
frontier_tool = _module(FRONTIER, "agent_episode_fact_frontier")


def run(*arguments: str) -> tuple[int, str]:
    done = subprocess.run(
        [sys.executable, str(SCRIPT), *arguments],
        capture_output=True, text=True, cwd=str(ROOT), timeout=300,
    )
    return (done.returncode, done.stdout + done.stderr)


class AgentEpisodeTests(unittest.TestCase):
    _frontier_json: dict | None = None

    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.dir = pathlib.Path(self._tmp.name)
        self.addCleanup(self._tmp.cleanup)

    # ------------------------------------------------------------- helpers

    def corrupt(self, source: pathlib.Path, mutate, name: str = "episode.json") -> str:
        document = json.loads(source.read_text())
        mutate(document)
        target = self.dir / name
        target.write_text(json.dumps(document, indent=2) + "\n")
        return str(target)

    def assertRule(self, output: str, rule: str) -> None:
        self.assertIn(f"|rules=", output, output)
        named = {r for line in output.splitlines() if "|rules=" in line
                 for r in line.rsplit("|rules=", 1)[1].split(",") if r}
        self.assertIn(rule, named, output)

    def frontier(self) -> dict:
        if AgentEpisodeTests._frontier_json is None:
            done = subprocess.run(
                [sys.executable, str(FRONTIER), "--json"],
                capture_output=True, text=True, cwd=str(ROOT), timeout=300,
            )
            self.assertEqual(done.returncode, 0, done.stderr)
            AgentEpisodeTests._frontier_json = json.loads(done.stdout)
        return json.loads(json.dumps(AgentEpisodeTests._frontier_json))

    def held_out_id(self) -> str:
        manifest = json.loads(NURSERY.read_text())
        held = sorted(e["fact_id"] for e in manifest["entries"]
                      if e["partition"] == "held-out")
        self.assertTrue(held)
        return held[0]

    # ------------------------------------------------------- the good cases

    def test_the_committed_fixtures_pass(self) -> None:
        code, out = run(str(DECLINED), str(PROVED))
        self.assertIn("EPISODES|checked=2|ok=2|failed=0", out)
        self.assertEqual(code, 0, out)

    def test_a_directory_argument_is_walked(self) -> None:
        code, out = run(str(FIXTURES))
        self.assertIn("EPISODES|checked=2|ok=2|failed=0", out)
        self.assertEqual(code, 0, out)

    def test_the_held_out_set_agrees_with_the_isolation_gate(self) -> None:
        isolation = _module(
            ROOT / "scripts/check-autogenesis-holdout-isolation.py",
            "agent_episode_isolation_crosscheck",
        )
        imported = isolation.held_out_facts()
        manifest = json.loads(NURSERY.read_text())
        replicated = {e["fact_id"] for e in manifest["entries"]
                      if e["partition"] == "held-out"}
        self.assertEqual(imported, replicated)
        self.assertEqual(len(imported), sum(
            1 for e in manifest["entries"] if e["partition"] == "held-out"))
        self.assertGreater(len(imported), 0)

    # ------------------------------------------------------------ the rules

    def test_a_schema_violation_is_a_failure(self) -> None:
        path = self.corrupt(DECLINED, lambda d: d.__setitem__("kind", "not-an-episode"))
        code, out = run(path)
        self.assertEqual(code, 1, out)
        self.assertRule(out, "schema")

    def test_a_non_ancestor_commit_fails_when_required(self) -> None:
        path = self.corrupt(DECLINED, lambda d: d.__setitem__("git_commit", "0" * 40))
        code, out = run(path, "--require-ancestor")
        self.assertEqual(code, 1, out)
        self.assertRule(out, "git-commit-ancestor")

    def test_a_non_ancestor_commit_is_only_a_warning_by_default(self) -> None:
        path = self.corrupt(DECLINED, lambda d: d.__setitem__("git_commit", "0" * 40))
        code, out = run(path)
        self.assertEqual(code, 0, out)
        self.assertIn("rule=git-commit-ancestor", out)

    def test_a_frontier_digest_mismatch_is_a_failure(self) -> None:
        saved = self.dir / "frontier.json"
        saved.write_text(json.dumps(self.frontier(), indent=2))

        def mutate(document):
            document["selection"]["frontier_path"] = str(saved)
            document["selection"]["frontier_sha256"] = BAD_SHA

        code, out = run(self.corrupt(DECLINED, mutate))
        self.assertEqual(code, 1, out)
        self.assertRule(out, "frontier-digest")

    def test_a_matching_frontier_digest_passes(self) -> None:
        artifact = self.frontier()
        saved = self.dir / "frontier.json"
        saved.write_text(json.dumps(artifact, indent=2))

        def mutate(document):
            document["selection"]["frontier_path"] = str(saved)
            document["selection"]["frontier_sha256"] = artifact["frontier_sha256"]

        code, out = run(self.corrupt(DECLINED, mutate))
        self.assertEqual(code, 0, out)
        self.assertNotIn("frontier", out.rsplit("|rules=", 1)[-1])

    def test_a_stale_frontier_is_rejected(self) -> None:
        # Internally consistent -- its own digest is recomputed the way
        # fact-frontier.py computes it, and the episode claims that digest -- but
        # it no longer describes the ledger. Only `--verify` can see that.
        artifact = self.frontier()
        artifact["ledger"]["fact_count"] += 1
        unsigned = {k: v for k, v in artifact.items() if k != "frontier_sha256"}
        artifact["frontier_sha256"] = frontier_tool.digest(unsigned)
        saved = self.dir / "stale-frontier.json"
        saved.write_text(json.dumps(artifact, indent=2))

        def mutate(document):
            document["selection"]["frontier_path"] = str(saved)
            document["selection"]["frontier_sha256"] = artifact["frontier_sha256"]

        code, out = run(self.corrupt(DECLINED, mutate))
        self.assertEqual(code, 1, out)
        self.assertRule(out, "frontier-reverify")

    def test_a_web_snapshot_digest_mismatch_is_a_failure(self) -> None:
        page = self.dir / "page.html"
        page.write_text("<html>a snapshot whose bytes are not what it claims</html>")

        def mutate(document):
            document["web_snapshots"] = [{
                "url": "https://arxiv.org/abs/0000.00000",
                "fetched_at": "2026-08-24T00:00:00Z",
                "sha256": BAD_SHA,
                "bytes": page.stat().st_size,
                "path": str(page),
            }]

        code, out = run(self.corrupt(DECLINED, mutate))
        self.assertEqual(code, 1, out)
        self.assertRule(out, "web-snapshot-digest")

    def test_a_nonzero_ledger_write_is_a_failure(self) -> None:
        path = self.corrupt(DECLINED, lambda d: d["outcome"].__setitem__("ledger_writes", 1))
        code, out = run(path)
        self.assertEqual(code, 1, out)
        self.assertRule(out, "ledger-writes-must-be-zero")

    def test_a_held_out_id_anywhere_is_a_failure(self) -> None:
        held = self.held_out_id()
        path = self.corrupt(
            DECLINED, lambda d: d["observed"].__setitem__("facts_unlocked", [held]))
        code, out = run(path)
        self.assertEqual(code, 1, out)
        self.assertRule(out, "held-out-reference")

    def test_proved_with_a_failing_checker_is_a_failure(self) -> None:
        path = self.corrupt(PROVED, lambda d: d["outcome"].__setitem__("checker_exit_status", 1))
        code, out = run(path)
        self.assertEqual(code, 1, out)
        self.assertRule(out, "proved-requires-zero-checker-status")

    def test_proved_with_no_checker_command_is_a_failure(self) -> None:
        path = self.corrupt(PROVED, lambda d: d["outcome"].__setitem__("checker_command", "   "))
        code, out = run(path)
        self.assertEqual(code, 1, out)
        self.assertRule(out, "proved-requires-checker-command")

    def test_a_proposal_digest_mismatch_is_a_failure(self) -> None:
        proposal = self.dir / "strategy.json"
        proposal.write_text(json.dumps({"assurance": "proposed"}))

        def mutate(document):
            document["proposals"] = [{
                "path": str(proposal),
                "sha256": BAD_SHA,
                "kind": "strategy",
                "assurance": "proposed",
            }]

        code, out = run(self.corrupt(DECLINED, mutate))
        self.assertEqual(code, 1, out)
        self.assertRule(out, "proposal-digest")

    def test_an_empty_transcript_is_a_failure(self) -> None:
        path = self.corrupt(DECLINED, lambda d: d["transcript"].__setitem__("tool_calls", []))
        code, out = run(path)
        self.assertEqual(code, 1, out)
        self.assertRule(out, "empty-transcript")

    def test_an_unknown_fact_id_is_a_failure(self) -> None:
        path = self.corrupt(
            DECLINED,
            lambda d: d["selection"].__setitem__("fact_id", "F:no-such-fact-00000000"),
        )
        code, out = run(path)
        self.assertEqual(code, 1, out)
        self.assertRule(out, "unknown-fact-id")

    # ------------------------------------------------------- fail-closed

    def test_checking_nothing_is_not_a_pass(self) -> None:
        code, out = run()
        self.assertIn("EPISODES|checked=0|ok=0|failed=0", out)
        self.assertEqual(code, 1, out)

    def test_an_empty_fact_ledger_is_an_error(self) -> None:
        empty = self.dir / "facts"
        empty.mkdir()
        code, out = run(str(DECLINED), "--facts", str(empty))
        self.assertEqual(code, 2, out)
        self.assertIn("EPISODE_ERROR|fact-ledger", out)

    def test_a_missing_nursery_is_an_error(self) -> None:
        code, out = run(str(DECLINED), "--nursery", str(self.dir / "absent.json"))
        self.assertEqual(code, 2, out)
        self.assertIn("EPISODE_ERROR|held-out-population", out)

    def test_an_unreadable_document_is_a_failure(self) -> None:
        broken = self.dir / "broken.json"
        broken.write_text("{not json")
        code, out = run(str(broken))
        self.assertEqual(code, 1, out)
        self.assertRule(out, "unreadable-document")


if __name__ == "__main__":
    unittest.main()
