"""Typed inputs and outputs for the agentic layer, and the vocabulary they resolve against.

Two kinds of model live here and they are held to different standards.

**Tool I/O models** (tier R) describe what the loop was allowed to see. They are
plain views over :mod:`axeyum.knowledge`; the only rule they add is that a
held-out fact id never reaches one, which is enforced in :mod:`axeyum.agent.tools`
and re-asserted here whenever a fact id crosses a model boundary.

**Proposal models** (tier P) describe what the model claimed. Three constraints
are structural rather than advisory, because a prompt that asks for them cannot
be audited afterwards:

1. ``assurance`` is ``Literal["proposed"]``. An LLM-authored artifact cannot be
   constructed carrying any other value, so nothing it emits can read as
   checked. The episode schema pins the same constant a second time.
2. ``tactic_ids`` must resolve in ``artifacts/autogenesis/tactic-catalog-v1.json``
   and ``producer_id`` in ``artifacts/autogenesis/operations.json`` (or in a
   catalog entry's ``implemented_by.symbol``). A plan therefore names a move
   that exists, not prose about one.
3. A :class:`StrategyProposal` must name **at least three** sibling facts the
   same route would reach. That is doc 228's finding -- 24 of 26 registered
   operations named exactly one fact, so the registry was a dispatch table that
   could not fail to "produce" -- turned into a schema constraint. A model with
   no general route says so explicitly with :class:`NoGeneralRoute`; it does not
   get to be silent about it.

The discriminator is ``route``, so the two variants are distinguishable in the
serialized proposal without inspecting which fields are present.
"""

from __future__ import annotations

import fnmatch
import re
from functools import lru_cache
from pathlib import Path
from typing import Annotated, Any, Literal

from pydantic import BaseModel, ConfigDict, Field, field_validator, model_validator

from ..knowledge import nursery, operations
from ..knowledge._paths import read_json, resolve_root

#: The tactic catalog, relative to the repository root (plan 04).
TACTIC_CATALOG = Path("artifacts") / "autogenesis" / "tactic-catalog-v1.json"

#: A fact id, as the fact ledger and the episode schema both spell it.
FACT_ID_PATTERN = re.compile(r"^F:[a-z0-9]+(?:-[a-z0-9]+)*$")

#: The partitions a proposal may reference. ``held-out`` is not among them and
#: neither is ``longitudinal``: the episode schema admits only these two, so a
#: row outside them cannot be recorded even if it could be selected.
ELIGIBLE_PARTITIONS = ("train", "development")

_root: Path | None = None


class VocabularyError(RuntimeError):
    """The vocabulary a proposal must resolve against could not be read.

    Fail-closed: an unreadable catalog must not be reported as "no known
    tactics", which would make every ``tactic_ids`` value invalid, nor as "all
    tactics known", which would make every value valid. Neither is an answer.
    """


def set_vocabulary_root(root: Path | str | None) -> None:
    """Point the validators at a checkout. ``None`` restores auto-discovery."""
    global _root
    _root = None if root is None else resolve_root(root)
    known_tactics.cache_clear()
    known_producers.cache_clear()
    _held_out.cache_clear()


def vocabulary_root() -> Path:
    return _root if _root is not None else resolve_root(None)


@lru_cache(maxsize=4)
def known_tactics(root_key: str = "") -> frozenset[str]:
    """Every ``T:`` id in the tactic catalog.

    Raises:
        VocabularyError: when the catalog is missing or holds no tactics. An
            empty vocabulary would silently reject every plan, which reads as
            "the model proposed nonsense" when the truth is "the gate lost its
            subject".
    """
    root = Path(root_key) if root_key else vocabulary_root()
    try:
        document = read_json(root / TACTIC_CATALOG)
    except (OSError, ValueError) as error:
        raise VocabularyError(f"tactic catalog is unreadable: {error}") from error
    ids = frozenset(
        row["id"] for row in document.get("tactics", []) if isinstance(row, dict) and "id" in row
    )
    if not ids:
        raise VocabularyError(f"{root / TACTIC_CATALOG} declares no tactics")
    return ids


@lru_cache(maxsize=4)
def known_producers(root_key: str = "") -> frozenset[str]:
    """Registered operation ids, plus the producer symbols the catalog names.

    Both are admitted because a plan may name either the registered *operation*
    that would carry it (``operations.json``) or the producer *symbol* that
    implements the move (``implemented_by.symbol``). Neither set is a superset
    of the other, and refusing one of them would push the model into prose.
    """
    root = Path(root_key) if root_key else vocabulary_root()
    registry = operations.load(root)
    catalog = read_json(root / TACTIC_CATALOG)
    symbols = {
        row.get("implemented_by", {}).get("symbol")
        for row in catalog.get("tactics", [])
        if isinstance(row, dict)
    }
    names = {op.id for op in registry} | {s for s in symbols if isinstance(s, str) and s}
    if not names:
        raise VocabularyError(f"{root} declares neither operations nor producer symbols")
    return frozenset(names)


@lru_cache(maxsize=4)
def _held_out(root_key: str = "") -> frozenset[str]:
    root = Path(root_key) if root_key else vocabulary_root()
    return nursery.load(root).held_out_ids()


def assert_referenceable(fact_id: str) -> str:
    """The fact id, when naming it is allowed. Raises otherwise, WITHOUT echoing it.

    The refusal deliberately does not repeat the offending id. A held-out id in
    an exception message is a held-out id in the transcript, in the episode's
    ``eligibility_reason``, and in whatever log caught it -- which is exactly
    the breach the guard exists to prevent.

    This is NOT sufficient on its own, and the reason is worth stating.
    Measured 2026-08-24: when this raises inside a pydantic field validator,
    pydantic's rendering of the resulting ``ValidationError`` appends
    ``input_value=<the id>``, and pydantic-ai feeds that rendering back to the
    model as a retry prompt. So the id can reach a transcript through a channel
    this function does not control. The backstop is
    :func:`axeyum.agent.episode.assert_no_held_out`, which walks the bytes
    before they reach disk and refuses the write. Two guards, different layers,
    and neither is redundant.
    """
    if not FACT_ID_PATTERN.match(fact_id):
        raise ValueError("not a fact id (expected F:<slug>)")
    if fact_id in _held_out():
        raise ValueError(
            "that fact is in the blind held-out population and cannot be referenced; "
            "select from frontier_select, which filters by partition before returning"
        )
    return fact_id


# ------------------------------------------------------------------ tier R I/O


class _Frozen(BaseModel):
    model_config = ConfigDict(frozen=True, extra="forbid")


class FrontierRow(_Frozen):
    """One eligible fact as the loop is allowed to see it."""

    fact_id: str = Field(description="The fact ledger id.")
    partition: Literal["train", "development"] = Field(
        description="Nursery partition. Held-out and longitudinal rows are dropped before this."
    )
    band: str | None = Field(description="Frontier band: research, backlog, blocked, established.")
    fragment: str | None = Field(description="The logical fragment the statement is written in.")
    route_class: str | None = Field(
        description="decidable, proof-route-only, or none -- how it could be attacked."
    )
    epistemic_status: str | None = Field(description="What we established: open here.")
    external_status: str | None = Field(description="What the literature knows.")
    registered_operation_ids: tuple[str, ...] = Field(
        description="Operations in operations.json that already name this fact."
    )
    would_unlock: tuple[str, ...] = Field(
        description="Open facts that depend on this one; closing it frees them."
    )


class FrontierPage(_Frozen):
    """The eligible slice of the frontier, with the filtering stated."""

    eligible_total: int = Field(description="How many facts cleared the filter in total.")
    returned: int = Field(description="How many rows are in this page.")
    dropped_held_out: int = Field(description="Dependency-ready rows dropped as held-out.")
    dropped_longitudinal: int = Field(description="Dependency-ready rows dropped as longitudinal.")
    dropped_unpartitioned: int = Field(
        description="Dependency-ready rows dropped because the nursery does not preregister them."
    )
    frontier_sha256: str = Field(
        description="Digest of the frontier artifact these rows come from."
    )
    rows: tuple[FrontierRow, ...] = Field(description="The eligible rows.")


class EvidenceView(_Frozen):
    kind: str | None
    check_status: str | None
    checker_command: str | None


class FactView(_Frozen):
    """One fact, as the ledger holds it."""

    fact_id: str
    title: str | None
    statement: str | None
    formal_language: str | None
    formal_statement: str | None
    fragment: str | None
    epistemic_status: str | None
    external_status: str | None
    proof_route: str | None
    depends_on: tuple[str, ...]
    axiom_footprint: tuple[str, ...] | None
    evidence: tuple[EvidenceView, ...]
    partition: str | None
    notes: str | None


class NeighbourRow(_Frozen):
    fact_id: str
    epistemic_status: str | None
    settled: bool


class Neighbourhood(_Frozen):
    """What a fact rests on and what rests on it."""

    fact_id: str
    depends_on: tuple[NeighbourRow, ...]
    would_unlock: tuple[NeighbourRow, ...]
    unmet_dependencies: tuple[str, ...]


class TheoremRow(_Frozen):
    name: str
    binders: int
    type: str


class TheoremPage(_Frozen):
    """Premise retrieval over a kernel prelude."""

    prelude: str
    name_glob: str
    matched: int
    total_theorems: int
    rows: tuple[TheoremRow, ...]


class LemmaNeighbourhoodRow(_Frozen):
    declaration_id: str
    canonical_type: str
    axiom_footprint_size: int
    visible_in: tuple[str, ...]
    dependencies: tuple[str, ...]
    dependents: tuple[str, ...]
    dependency_depth: int
    fact_ids: tuple[str, ...]


class LemmaNeighbourhoodPage(_Frozen):
    """Search-only kernel dependency rows; applicability remains unchecked."""

    name_glob: str
    fact_id: str
    matched: int
    total_lemmas: int
    dropped_held_out_fact_links: int
    rows: tuple[LemmaNeighbourhoodRow, ...]


class LemmaCandidateRow(_Frozen):
    """One exact kernel lemma linked to a declared fact dependency."""

    declaration_id: str
    canonical_type: str
    source_dependency_fact_id: str
    axiom_footprint_size: int
    visible_in: tuple[str, ...]
    dependency_depth: int


class LemmaCandidatesPage(_Frozen):
    """Deterministic proof-context join; every row remains candidate-only."""

    fact_id: str
    declared_dependency_count: int
    linked_dependency_count: int
    matched: int
    unresolved_dependency_fact_ids: tuple[str, ...]
    rows: tuple[LemmaCandidateRow, ...]


class OperationRow(_Frozen):
    operation_id: str
    scope: str
    n_targets: int = Field(
        description="How many facts applicability.fact_ids names. 1 means a dispatch entry."
    )
    fact_ids: tuple[str, ...]
    producer: str | None
    checker: str | None
    driver: str | None


class OperationRegistryView(_Frozen):
    """The registry, with the generality counter visible."""

    total: int
    multi_target: int = Field(description="Operations naming more than one fact.")
    single_target: int = Field(description="Operations naming exactly one fact.")
    rows: tuple[OperationRow, ...]


class OverlayLinkRow(_Frozen):
    link_id: str
    relation: str
    source: str
    target: str
    assurance: str
    status: str | None
    reason: str | None


class OverlayPage(_Frozen):
    relation: str | None
    endpoint_id: str | None
    matched: int
    total_links: int
    rows: tuple[OverlayLinkRow, ...]


# ------------------------------------------------------------- tier P output


class _Proposal(BaseModel):
    """Shared spine. ``assurance`` is pinned here so no variant can widen it."""

    model_config = ConfigDict(extra="forbid")

    fact_id: str = Field(description="The fact this plan targets. Must be the selected fact.")
    tactic_ids: list[str] = Field(
        min_length=1,
        description="Tactic ids from artifacts/autogenesis/tactic-catalog-v1.json, in order.",
    )
    producer_id: str = Field(
        description="A registered operation id, or a producer symbol the tactic catalog names."
    )
    why: str = Field(
        min_length=16,
        description="Why these tactics on this goal: the structural precondition you matched.",
    )
    expected_decline_class: str = Field(
        min_length=3,
        description="The decline you expect if the producer refuses (e.g. NotEqualityGoal).",
    )
    assurance: Literal["proposed"] = Field(
        default="proposed",
        description="Always 'proposed'. Nothing an LLM emits is checked evidence.",
    )

    @field_validator("fact_id")
    @classmethod
    def _fact_is_referenceable(cls, value: str) -> str:
        return assert_referenceable(value)

    @field_validator("tactic_ids")
    @classmethod
    def _tactics_resolve(cls, value: list[str]) -> list[str]:
        known = known_tactics()
        unknown = [t for t in value if t not in known]
        if unknown:
            raise ValueError(
                f"tactic ids not in the catalog: {sorted(unknown)}; "
                f"the catalog declares {len(known)} tactics"
            )
        return value

    @field_validator("producer_id")
    @classmethod
    def _producer_resolves(cls, value: str) -> str:
        known = known_producers()
        if value not in known:
            raise ValueError(
                f"producer_id {value!r} is neither a registered operation id nor a "
                f"producer symbol named by the tactic catalog"
            )
        return value


class StrategyProposal(_Proposal):
    """A plan the model believes generalizes, with the siblings that prove it does.

    ``sibling_fact_ids`` is the whole point: an operation that names exactly one
    fact is a dispatch entry, and 24 of 26 registered operations were exactly
    that when it was last measured. Three is the smallest number that makes
    "this route generalizes" a falsifiable claim rather than a label.
    """

    route: Literal["general"] = "general"
    sibling_fact_ids: list[str] = Field(
        min_length=3,
        description=(
            "At least three OTHER eligible facts the same tactics and producer would reach. "
            "If you cannot name three, emit NoGeneralRoute instead -- do not invent them."
        ),
    )

    @field_validator("sibling_fact_ids")
    @classmethod
    def _siblings_referenceable(cls, value: list[str]) -> list[str]:
        return [assert_referenceable(v) for v in value]

    @model_validator(mode="after")
    def _target_is_not_its_own_sibling(self) -> StrategyProposal:
        if self.fact_id in self.sibling_fact_ids:
            raise ValueError("sibling_fact_ids must name facts OTHER than fact_id")
        if len(set(self.sibling_fact_ids)) != len(self.sibling_fact_ids):
            raise ValueError("sibling_fact_ids must be distinct; a repeated id is not a sibling")
        return self


class NoGeneralRoute(_Proposal):
    """The honest alternative: this route reaches one fact and the model says so.

    Emitting this is a *result*, not a failure. It is the datapoint slice A5
    turns into an obstruction graph, and forcing a three-sibling claim where
    none exists would poison exactly that measurement.
    """

    route: Literal["none"] = "none"
    obstruction: str = Field(
        min_length=16,
        description="What is specific to this goal that stops the route reaching its siblings.",
    )


#: What the Plan node asks the model for. Discriminated on ``route`` so the
#: serialized proposal says which variant it is without shape-sniffing.
Plan = Annotated[StrategyProposal | NoGeneralRoute, Field(discriminator="route")]


# ------------------------------------------------------- tier C: what a producer said


#: Decline classes an episode may record, seeded from the AG4.1 taxonomy in
#: ``docs/autogenesis/02-phased-roadmap.md``, which lists exactly NINE cross-route
#: classes as prose. Those nine are kebab-cased here and nothing was invented in
#: that group. The five after them are LOOP-LOCAL: they say why this harness
#: stopped, not what obstructed the mathematics. Keeping them apart is not
#: tidiness -- ``no-general-route`` is a *result*, and folding it into
#: ``missing-plan-rule`` would record a mathematical obstruction nobody observed
#: and poison the obstruction graph slice A5 derives from exactly this field.
AG41_DECLINE_CLASSES = (
    "unsupported-semantics",
    "missing-lemma",
    "missing-plan-rule",
    "missing-certificate",
    "representation-explosion",
    "resource-exhaustion",
    "retrieval-miss",
    "formalization-mismatch",
    "operational-failure",
)

LOOP_DECLINE_CLASSES = (
    "no-general-route",
    "gate-refused",
    "supervisor-denied",
    "budget-exhausted-before-plan",
    "budget-exhausted-during-plan",
)

#: Every value ``outcome.decline_class`` may take in a v2 episode, in the order
#: the schema lists them. The schema is the authority; this tuple is checked
#: against it by a test so the two cannot drift.
DECLINE_CLASSES = AG41_DECLINE_CLASSES + LOOP_DECLINE_CLASSES


class ProducerAccepted(_Frozen):
    """A producer returned a candidate AND a kernel admitted it.

    Every field here is *measured*, never inferred from the fact that admission
    succeeded. ``axiom_footprint`` in particular comes from
    :meth:`axeyum.kernel.Kernel.axiom_footprint` on the admitted name -- the
    Python binding raises ``KeyError`` for an absent name rather than answering
    with the empty vector, which is what makes an empty list here mean
    "axiom-free" instead of "nobody looked".

    ``assurance`` is ``checked`` and cannot be anything else. That is the whole
    difference between tier C and tier P: a tier-P object is what a model said,
    a tier-C object is what a kernel decided.
    """

    status: Literal["accepted"] = "accepted"
    fact_id: str = Field(description="The fact whose adapted goal was closed.")
    tool: str = Field(description="Which tier-C tool ran: bounded_induction or modeq_family.")
    target_definition: str = Field(description="The proof-free Lean definition that was imported.")
    export_path: str = Field(description="The frozen NDJSON export the goal came from.")
    export_sha256: str = Field(description="Digest of those bytes, re-hashed before importing.")
    goal_sha256: str = Field(description="sha256 of render_lean(goal), as the drivers stamp it.")
    proof_sha256: str = Field(description="sha256 of render_lean(proof), comparable to a manifest.")
    binders_used: int
    inductions_used: int | None = Field(
        description="Inductions the search spent, or null for a producer that performs none. "
        "Null is not zero: the two producers measure different quantities."
    )
    admitted_declarations: int
    axiom_footprint: tuple[str, ...] = Field(
        description="Measured on the admitted declaration. Empty means axiom-free."
    )
    theorem_dependencies: tuple[str, ...]
    duration_ms: int
    assurance: Literal["checked"] = "checked"


class ProducerDeclined(_Frozen):
    """The producer refused, and the refusal is a typed value rather than an error.

    ``reason_kind`` is the producer's own Rust enum variant, carried across the
    language boundary unflattened. ``decline_class`` is where that lands in the
    taxonomy an episode can aggregate; both are kept because the mapping is a
    judgement and the raw variant is the evidence for it.
    """

    status: Literal["declined"] = "declined"
    fact_id: str
    tool: str
    reason_kind: str = Field(description="The producer's typed DeclineReason variant.")
    detail: str = Field(description="Its payload, verbatim.")
    decline_class: str = Field(description="Where that lands in the episode taxonomy.")
    duration_ms: int
    assurance: Literal["checked"] = "checked"


class ProducerError(_Frozen):
    """The tool could not run at all. Never a silent decline.

    "The export is not on this host" and "the producer refused this goal" are
    different findings about the world and this repository has been bitten by
    tools that reported them identically.
    """

    status: Literal["error"] = "error"
    fact_id: str
    tool: str
    error_kind: str
    detail: str
    decline_class: str
    duration_ms: int
    assurance: Literal["checked"] = "checked"


#: What a tier-C tool returns. Discriminated on ``status`` so the serialized
#: result says which variant it is without shape-sniffing, exactly as ``route``
#: does for a proposal.
ProducerOutcome = Annotated[
    ProducerAccepted | ProducerDeclined | ProducerError, Field(discriminator="status")
]


class CheckVerified(_Frozen):
    """A SECOND kernel re-derived the same proof and measured the same footprint."""

    status: Literal["verified"] = "verified"
    fact_id: str
    goal_sha256: str
    proof_sha256: str
    axiom_footprint: tuple[str, ...]
    theorem_dependencies: tuple[str, ...]
    admitted_declarations: int


class CheckFailed(_Frozen):
    """The independent re-check did not agree. This is the finding, not an error."""

    status: Literal["failed"] = "failed"
    fact_id: str
    reason: str
    expected: str | None = None
    actual: str | None = None


CheckOutcome = Annotated[CheckVerified | CheckFailed, Field(discriminator="status")]


def glob_match(name: str, pattern: str) -> bool:
    """Case-sensitive glob, with the empty pattern meaning "everything"."""
    return True if not pattern else fnmatch.fnmatchcase(name, pattern)


def proposal_kind(proposal: Any) -> str:
    """The ``proposals[].kind`` value for the episode artifact."""
    if isinstance(proposal, (StrategyProposal, NoGeneralRoute)):
        return "strategy"
    raise TypeError(f"not a proposal: {type(proposal).__name__}")


__all__ = [
    "AG41_DECLINE_CLASSES",
    "DECLINE_CLASSES",
    "ELIGIBLE_PARTITIONS",
    "FACT_ID_PATTERN",
    "LOOP_DECLINE_CLASSES",
    "TACTIC_CATALOG",
    "CheckFailed",
    "CheckOutcome",
    "CheckVerified",
    "EvidenceView",
    "FactView",
    "FrontierPage",
    "FrontierRow",
    "LemmaCandidateRow",
    "LemmaCandidatesPage",
    "LemmaNeighbourhoodPage",
    "LemmaNeighbourhoodRow",
    "NeighbourRow",
    "Neighbourhood",
    "NoGeneralRoute",
    "OperationRegistryView",
    "OperationRow",
    "OverlayLinkRow",
    "OverlayPage",
    "Plan",
    "ProducerAccepted",
    "ProducerDeclined",
    "ProducerError",
    "ProducerOutcome",
    "StrategyProposal",
    "TheoremPage",
    "TheoremRow",
    "VocabularyError",
    "assert_referenceable",
    "glob_match",
    "known_producers",
    "known_tactics",
    "proposal_kind",
    "set_vocabulary_root",
    "vocabulary_root",
]
