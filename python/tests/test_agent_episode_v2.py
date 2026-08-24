"""Schema v2 and the writer, held against each other.

Two documents describe the same taxonomy -- the JSON Schema a stdlib gate reads
and the Python tuple the writer refuses against -- and they are written by hand
in two files. That is exactly the arrangement that drifts, so it is pinned here
in both directions: the schema may not enumerate a class the writer would
reject, and the writer may not admit one the schema would.
"""

from __future__ import annotations

import json
from pathlib import Path

import pytest

pytest.importorskip("pydantic_ai", reason="the [agent] extra is not installed")

from axeyum.agent import episode as episode_api
from axeyum.agent import models as models_api
from axeyum.knowledge._paths import resolve_root

SCHEMA_V1 = Path("artifacts/ontology/agent-episode.schema.json")
SCHEMA_V2 = Path("artifacts/ontology/agent-episode-v2.schema.json")


@pytest.fixture(scope="module")
def root() -> Path:
    return resolve_root(None)


@pytest.fixture(scope="module")
def schema(root: Path) -> dict:
    return json.loads((root / SCHEMA_V2).read_text())


def test_v1_is_still_committed_beside_v2(root: Path) -> None:
    """A2's ten episodes declare version 1 and must stay checkable."""
    assert (root / SCHEMA_V1).is_file()
    assert json.loads((root / SCHEMA_V1).read_text())["properties"]["schema_version"]["const"] == 1


def test_the_v2_schema_declares_version_two(schema: dict) -> None:
    assert schema["properties"]["schema_version"]["const"] == 2


def test_the_decline_enum_is_exactly_the_taxonomy_the_writer_enforces(schema: dict) -> None:
    enumerated = [c for c in schema["$defs"]["declineClass"]["enum"] if c is not None]
    assert tuple(enumerated) == models_api.DECLINE_CLASSES


def test_the_nine_ag41_classes_are_present_and_are_the_seed(schema: dict) -> None:
    """AG4.1 lists NINE classes as prose. Nine appear, kebab-cased, and the
    five that follow are loop-local and separately named."""
    assert len(models_api.AG41_DECLINE_CLASSES) == 9
    enumerated = [c for c in schema["$defs"]["declineClass"]["enum"] if c is not None]
    assert enumerated[:9] == list(models_api.AG41_DECLINE_CLASSES)
    assert set(models_api.LOOP_DECLINE_CLASSES).isdisjoint(models_api.AG41_DECLINE_CLASSES)


def test_no_general_route_is_not_folded_into_an_ag41_class() -> None:
    """It is a RESULT, and mapping it onto `missing-plan-rule` would record a
    mathematical obstruction nobody observed."""
    assert "no-general-route" in models_api.LOOP_DECLINE_CLASSES
    assert "no-general-route" not in models_api.AG41_DECLINE_CLASSES


def test_the_selection_block_requires_the_ledger_digest(schema: dict) -> None:
    assert "ledger_sha256" in schema["$defs"]["selection"]["required"]
    assert schema["$defs"]["selection"]["additionalProperties"] is False


def test_the_partition_enum_still_admits_only_train_and_development(schema: dict) -> None:
    assert schema["$defs"]["selection"]["properties"]["partition"]["enum"] == [
        "train",
        "development",
    ]


def test_ledger_writes_is_still_pinned_to_zero(schema: dict) -> None:
    writes = schema["$defs"]["outcome"]["properties"]["ledger_writes"]
    assert (writes["minimum"], writes["maximum"]) == (0, 0)


def test_v2_keeps_the_v1_singular_checker_fields_so_every_v1_rule_still_bites(
    schema: dict,
) -> None:
    for field in ("checker_command", "checker_exit_status", "checker_output_sha256"):
        assert field in schema["$defs"]["outcome"]["required"]
    assert "checker_runs" in schema["$defs"]["outcome"]["required"]


def test_a_checker_run_must_name_a_command(schema: dict) -> None:
    run = schema["$defs"]["checkerRun"]
    assert run["properties"]["command"]["minLength"] == 1
    assert set(run["required"]) == {"command", "exit_status", "output_sha256", "assurance"}


def test_proved_needs_both_halves_and_neither_implies_the_other() -> None:
    checked = [{"assurance": "checked"}]
    passing = [{"exit_status": 0}]
    assert episode_api.proved_is_supported(checked, passing)[0] is True
    assert episode_api.proved_is_supported([{"assurance": "read"}], passing)[0] is False
    assert episode_api.proved_is_supported(checked, [{"exit_status": 1}])[0] is False
    assert episode_api.proved_is_supported([], [])[0] is False


def test_the_writer_refuses_a_decline_class_outside_the_taxonomy(root: Path) -> None:
    from axeyum.knowledge import frontier as frontier_api

    with pytest.raises(episode_api.EpisodeWriteError, match="not in the v2 taxonomy"):
        episode_api.build_episode_v2(
            root=root,
            commit="0" * 40,
            fact_id="F:ml430-nat-modeq-refl-d870c8f5",
            frontier=frontier_api.load(root),
            frontier_path=root / "artifacts",
            partition="development",
            model_id="test:offline",
            settings={"temperature": 0.0, "top_p": 1.0, "max_tokens": 8192, "seed": None},
            prompt_hashes={},
            budgets=episode_api.Budgets(600, 10, 16, 400000, 32000, 1.0),
            messages_path="x",
            messages_sha256="0" * 64,
            tool_calls=[{"assurance": "read"}],
            proposal_rows=[],
            verdict="declined",
            decline_class="the-model-was-tired",
        )


def test_the_v1_writer_still_refuses_proved_and_the_v2_one_does_not_by_default() -> None:
    assert "proved" not in episode_api.V1_VERDICTS
    assert "proved" in episode_api.A2_VERDICTS
    assert "error" not in episode_api.A2_VERDICTS
