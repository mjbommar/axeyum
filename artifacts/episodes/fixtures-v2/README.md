# Schema v2 episode fixtures

Two hand-written schema v2 documents, one `proved` and one `declined`, used by
`scripts/tests/test_check_agent_episode.py` to exercise the version dispatch and
rule 11 (`proved-requires-checked-call`).

They live in their own directory rather than beside the v1 fixtures for a
mechanical reason: `test_a_directory_argument_is_walked` asserts
`EPISODES|checked=2|ok=2|failed=0` against `artifacts/episodes/fixtures`, and
adding files there would change what that control measures without changing
what it says.

Their `selection.frontier_path` and `transcript.messages_path` deliberately
point at files that are **not** committed, exactly as the v1 fixtures do: the
frontier-digest rule then WARNs rather than failing, which is what lets every
other rule be exercised against a document that is otherwise complete. A fixture
whose every input existed would be a live episode, and there are six of those
under `artifacts/episodes/2026-08-24-a4/`.
