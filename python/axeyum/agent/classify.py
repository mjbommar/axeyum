"""Turn a decline into a typed obstruction cluster. Deterministic, and no model runs.

Slice A5 of `docs/python-2026-08/03-agentic-layer.md`. The `Classify` node in
:mod:`axeyum.agent.graph` sits on the decline path and calls :func:`classify`.

**Why this is deterministic when the plan drew it as a model node.** Plan 03
italicizes *Classify* alongside *Gather* and *Plan*, and italic means "the model
runs here". It is deterministic anyway, for three measured reasons:

1.  **Its inputs are already typed.** A `NoGeneralRoute` is a discriminated
    variant, not prose; a v2 `decline_class` is an enum the schema pins; a
    `ProducerDeclined.reason_kind` is the producer's own Rust `DeclineReason`
    variant carried across the language boundary unflattened. There is nothing
    left to read out of free text, which is what a classifier would be for.
2.  **A model call here would make the graph unreplayable in the one place the
    replay matters.** `replay --from-transcript` requires every deterministic
    node to re-derive bit-identically and treats divergence as a finding. A
    classification that varied per run would put the obstruction graph's own
    cluster keys outside that guarantee.
3.  **The same mapping has to run outside this package.** `just check` is
    stdlib-only and nothing under `scripts/` may import the `[agent]` extra, so
    `scripts/gen-obstruction-graph.py` re-derives the identical clusters from
    committed episode bytes. That is only possible because the mapping is a
    function of those bytes. `python/tests/test_agent_classify.py` asserts the
    two agree on every committed episode, so the duplication cannot drift
    silently.

**This module adds no field to the episode schema.** A classification is a
function of `outcome.decline_class` and the committed `proposals[]`, both of
which schema v2 already has. That is the constraint that made the design work
rather than a happy accident: a taxonomy needing a new column would be a
taxonomy the sixteen committed episodes could not be scored against.

Import-light on purpose: nothing here imports pydantic, pydantic-ai, or the
native extension, so the mapping can be exercised without either.
"""

from __future__ import annotations

import hashlib
from collections.abc import Sequence
from dataclasses import dataclass
from typing import Any

#: Blocker kinds this classifier can produce, matching
#: `artifacts/ontology/obstruction-graph.schema.json`'s `blockerKind` for the
#: values an EPISODE can reach. The record-only kinds (`axiom-footprint-nonempty`,
#: `elaboration-blocked`, `tooling-gate-refused`, `tactic-precondition-unmatched`,
#: `replay-readiness-mismatch`) are not here because no episode produces one:
#: they come from producer decline records that predate the loop.
NO_GENERAL_ROUTE = "no-general-route"
GATE_REFUSED = "gate-refused"
EXPORT_MISSING = "export-missing"
BUDGET = "budget"
UNCLASSIFIED = "unclassified"

#: Where each v2 `decline_class` lands when no earlier observation overrides it.
#:
#: `no-general-route` and `gate-refused` map to the same blocker on purpose and
#: it is the single most important line in this file. A2 recorded
#: `no-general-route` for a model that declined to claim three siblings; A4
#: records `gate-refused` for the identical situation, because A4 added a gate
#: that refuses a `NoGeneralRoute` plan. The obstruction did not change -- the
#: harness did -- and a classifier keyed on the decline class alone would split
#: one cluster in two and attribute the split to the mathematics.
DECLINE_CLASS_BLOCKERS: dict[str | None, str] = {
    None: UNCLASSIFIED,
    "unsupported-semantics": UNCLASSIFIED,
    "missing-lemma": UNCLASSIFIED,
    "missing-plan-rule": UNCLASSIFIED,
    "missing-certificate": UNCLASSIFIED,
    "representation-explosion": UNCLASSIFIED,
    "resource-exhaustion": BUDGET,
    "retrieval-miss": EXPORT_MISSING,
    "formalization-mismatch": UNCLASSIFIED,
    "operational-failure": UNCLASSIFIED,
    "no-general-route": NO_GENERAL_ROUTE,
    "gate-refused": NO_GENERAL_ROUTE,
    "supervisor-denied": UNCLASSIFIED,
    "budget-exhausted-before-plan": BUDGET,
    "budget-exhausted-during-plan": BUDGET,
}

#: What a `retrieval-miss` actually is, measured: plan 03's A4 finding 2 counted
#: exactly 3 of 98 eligible facts with a frozen, proof-free statement export a
#: producer can import. The producer did not fail; there was nothing to give it.
EXPORT_DETAIL = "frozen-statement-export"

GATE_DETAIL = "the deterministic gate refuses a NoGeneralRoute plan"


@dataclass(frozen=True)
class Blocker:
    """One observed blocker: what stopped the run, and which typed field said so."""

    kind: str
    detail: str
    source: str


@dataclass(frozen=True)
class Classification:
    """The decline, as an obstruction cluster.

    `first_blocker` is what the run hit FIRST in time, which is not always the
    class the episode recorded; `known_blockers` is the complete set. Autogenesis
    F3 asks for both, separately, and a record that kept only one of them would
    lose the distinction between "what stopped this run" and "what we now know
    about this cluster".
    """

    decline_class: str | None
    first_blocker: Blocker
    known_blockers: tuple[Blocker, ...]
    cluster_key: str
    obstruction_id: str

    @property
    def blocker_kind(self) -> str:
        return self.first_blocker.kind


def cluster_id(cluster_key: str) -> str:
    """`O:<kind>-<8 hex of sha256(cluster_key)>`.

    Byte-identical to `scripts/gen-obstruction-graph.py`'s. The digest is what
    makes an obstruction id unassignable by judgement, and the validator
    recomputes it rather than trusting it.
    """
    kind = cluster_key.split("|", 1)[0]
    return f"O:{kind}-{hashlib.sha256(cluster_key.encode('utf-8')).hexdigest()[:8]}"


def _field(row: Any, name: str) -> Any:
    """Read `name` off a pydantic model or a plain dict, without importing either.

    A live run holds `NoGeneralRoute` objects; a replay and the offline tests
    hold the same rows deserialized from `proposals/proposal-N.json.snapshot`.
    They are the same data and this module refuses to care which it got.
    """
    if isinstance(row, dict):
        return row.get(name)
    return getattr(row, name, None)


def classify(
    *,
    decline_class: str | None,
    proposals: Sequence[Any] = (),
    verdict: str = "declined",
) -> Classification | None:
    """The obstruction one declined episode belongs to, or `None` when it proved.

    Returns `None` for `verdict == "proved"`: a proof is not an obstruction, and
    a classifier that produced a cluster for one would put successes in the
    backlog.
    """
    if verdict == "proved":
        return None

    no_route = [row for row in proposals if _field(row, "route") == "none"]
    if no_route:
        tactics = sorted({t for row in no_route for t in (_field(row, "tactic_ids") or [])})
        detail = "+".join(tactics) or "no-tactic-named"
        first = Blocker(NO_GENERAL_ROUTE, detail, "episode-proposal-route")
        known = [first]
        if decline_class == "gate-refused":
            known.append(Blocker(GATE_REFUSED, GATE_DETAIL, "episode-decline-class"))
        return _build(decline_class, first, known, detail)

    kind = DECLINE_CLASS_BLOCKERS.get(decline_class, UNCLASSIFIED)
    if kind == EXPORT_MISSING:
        first = Blocker(EXPORT_MISSING, EXPORT_DETAIL, "episode-decline-class")
        return _build(decline_class, first, [first], EXPORT_DETAIL)
    if kind == BUDGET:
        detail = str(decline_class).removeprefix("budget-exhausted-")
        first = Blocker(BUDGET, detail, "episode-decline-class")
        return _build(decline_class, first, [first], detail)

    detail = str(decline_class)
    first = Blocker(UNCLASSIFIED, detail, "episode-decline-class")
    return _build(decline_class, first, [first], detail)


def _build(
    decline_class: str | None,
    first: Blocker,
    known: list[Blocker],
    detail: str,
) -> Classification:
    key = f"{first.kind}|{detail}"
    return Classification(
        decline_class=decline_class,
        first_blocker=first,
        known_blockers=tuple(known),
        cluster_key=key,
        obstruction_id=cluster_id(key),
    )


def classify_episode(document: dict, proposals: Sequence[Any]) -> Classification | None:
    """The same classification, read off a committed episode document.

    This is the entry point the tests use to compare against
    `scripts/gen-obstruction-graph.py`: same bytes in, same cluster out, or the
    two implementations have drifted.
    """
    outcome = document["outcome"]
    return classify(
        decline_class=outcome.get("decline_class"),
        proposals=proposals,
        verdict=outcome["verdict"],
    )


__all__ = [
    "BUDGET",
    "DECLINE_CLASS_BLOCKERS",
    "EXPORT_MISSING",
    "GATE_REFUSED",
    "NO_GENERAL_ROUTE",
    "UNCLASSIFIED",
    "Blocker",
    "Classification",
    "classify",
    "classify_episode",
    "cluster_id",
]
