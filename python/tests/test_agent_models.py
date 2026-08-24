"""Tier-P proposals: what an LLM is structurally prevented from claiming.

Every rejection below is a rejection at CONSTRUCTION, in the same library the
tool schemas come from, so it reaches the model as validator feedback rather
than as a note in a prompt nobody can audit afterwards.
"""

from __future__ import annotations

import pytest

pytest.importorskip("pydantic_ai", reason="the [agent] extra is not installed")

from pydantic import TypeAdapter, ValidationError

from axeyum.agent import tools
from axeyum.agent.models import (
    NoGeneralRoute,
    Plan,
    StrategyProposal,
    known_producers,
    known_tactics,
)
from axeyum.knowledge import nursery as nursery_api
from axeyum.knowledge._paths import resolve_root


@pytest.fixture(scope="module")
def root():
    return resolve_root(None)


@pytest.fixture(scope="module")
def facts(root) -> list[str]:
    eligible = list(tools.eligible_fact_ids(root))
    assert len(eligible) >= 4, "need a target plus three siblings"
    return eligible


def good(facts: list[str], **overrides):
    payload = {
        "fact_id": facts[0],
        "tactic_ids": [min(known_tactics())],
        "producer_id": min(known_producers()),
        "why": "the terminal goal is an Eq whose sides unfold to the same normal form",
        "expected_decline_class": "TerminalNotDefEqNoRewrite",
        "sibling_fact_ids": facts[1:4],
    }
    payload.update(overrides)
    return payload


def test_a_well_formed_strategy_proposal_validates(facts) -> None:
    proposal = StrategyProposal(**good(facts))
    assert proposal.assurance == "proposed"
    assert proposal.route == "general"


def test_assurance_cannot_be_anything_but_proposed(facts) -> None:
    """The single most important constraint here: nothing an LLM emits can read
    as checked evidence, and it is a type error rather than a convention."""
    for value in ("checked", "independently-checked", "formal-derived", "human-reviewed"):
        with pytest.raises(ValidationError):
            StrategyProposal(**good(facts, assurance=value))


def test_unknown_tactic_ids_are_rejected(facts) -> None:
    with pytest.raises(ValidationError, match="not in the catalog"):
        StrategyProposal(**good(facts, tactic_ids=["T:invent-a-tactic"]))


def test_a_mix_of_known_and_unknown_tactics_is_rejected(facts) -> None:
    known = min(known_tactics())
    with pytest.raises(ValidationError, match="not in the catalog"):
        StrategyProposal(**good(facts, tactic_ids=[known, "T:invent-a-tactic"]))


def test_an_empty_tactic_list_is_rejected(facts) -> None:
    with pytest.raises(ValidationError):
        StrategyProposal(**good(facts, tactic_ids=[]))


def test_unknown_producer_ids_are_rejected(facts) -> None:
    with pytest.raises(ValidationError, match="neither a registered operation"):
        StrategyProposal(**good(facts, producer_id="run_my_own_prover"))


def test_a_catalog_symbol_is_an_acceptable_producer(facts) -> None:
    assert StrategyProposal(**good(facts, producer_id="close_terminal")).producer_id


def test_two_siblings_are_not_enough(facts) -> None:
    """Doc 228 as a schema constraint: an operation reaching one theorem is a
    dispatch entry. Three is the smallest falsifiable claim of generality."""
    with pytest.raises(ValidationError):
        StrategyProposal(**good(facts, sibling_fact_ids=facts[1:3]))


def test_zero_siblings_are_not_enough(facts) -> None:
    with pytest.raises(ValidationError):
        StrategyProposal(**good(facts, sibling_fact_ids=[]))


def test_the_target_may_not_be_its_own_sibling(facts) -> None:
    with pytest.raises(ValidationError, match="OTHER than fact_id"):
        StrategyProposal(**good(facts, sibling_fact_ids=[facts[0], facts[1], facts[2]]))


def test_repeated_siblings_do_not_count(facts) -> None:
    """Otherwise `[x, x, x]` satisfies min_length=3 and generality is a label."""
    with pytest.raises(ValidationError, match="distinct"):
        StrategyProposal(**good(facts, sibling_fact_ids=[facts[1], facts[1], facts[1]]))


def test_a_held_out_target_is_rejected(facts, root) -> None:
    """Measured 2026-08-24: the validator's own message does not echo the id,
    but pydantic's rendering of a `ValidationError` appends `input_value=...`,
    so `str(error)` DOES carry it. That is a real path into a retry prompt and
    therefore into a transcript -- which is exactly why the write-time guard in
    `episode.assert_no_held_out` is not redundant with this validator. Assert
    what we control; the guard covers what we do not."""
    blind = min(nursery_api.load(root).held_out_ids())
    with pytest.raises(ValidationError) as caught:
        StrategyProposal(**good(facts, fact_id=blind))
    messages = [error["msg"] for error in caught.value.errors()]
    assert any("blind held-out population" in m for m in messages)
    assert all(blind not in m for m in messages)


def test_a_held_out_sibling_is_rejected(facts, root) -> None:
    blind = min(nursery_api.load(root).held_out_ids())
    with pytest.raises(ValidationError):
        StrategyProposal(**good(facts, sibling_fact_ids=[facts[1], facts[2], blind]))


def test_a_bare_fact_id_is_rejected(facts) -> None:
    with pytest.raises(ValidationError):
        StrategyProposal(**good(facts, fact_id="ml430-int-add-modeq-left-ee732b5b"))


def test_a_thin_justification_is_rejected(facts) -> None:
    with pytest.raises(ValidationError):
        StrategyProposal(**good(facts, why="because"))


def test_no_general_route_needs_no_siblings_but_needs_an_obstruction(facts) -> None:
    payload = good(facts)
    payload.pop("sibling_fact_ids")
    with pytest.raises(ValidationError):
        NoGeneralRoute(**payload)
    proposal = NoGeneralRoute(
        **payload, obstruction="the goal's modulus is a literal, so no sibling shares the shape"
    )
    assert proposal.route == "none"
    assert proposal.assurance == "proposed"


def test_the_union_discriminates_on_route(facts) -> None:
    adapter = TypeAdapter(Plan)
    payload = good(facts)
    assert isinstance(adapter.validate_python({**payload, "route": "general"}), StrategyProposal)
    payload.pop("sibling_fact_ids")
    parsed = adapter.validate_python(
        {**payload, "route": "none", "obstruction": "no sibling shares this literal modulus"}
    )
    assert isinstance(parsed, NoGeneralRoute)


def test_extra_fields_are_refused(facts) -> None:
    with pytest.raises(ValidationError):
        StrategyProposal(**good(facts), confidence=0.99)


def test_the_vocabulary_is_not_empty() -> None:
    """A vocabulary that lost its subject would reject every plan, and the
    failure would read as "the model proposed nonsense"."""
    assert len(known_tactics()) >= 8
    assert len(known_producers()) >= 20
