"""The additive Autogenesis knowledge overlay.

The overlay does not modify facts or operations -- it adds typed edges between
them. Two properties matter to a reader:

* **every link carries an ``assurance``**, and the vocabulary is ordered from
  ``formal-derived`` down to ``proposed``. A link is only as good as its
  assurance, so this module never exposes a link without it.
* **every endpoint resolves inside this checkout.** Until 2026-08-24 the overlay
  could name a pinned sibling repository and an endpoint into it carried a
  ``source_revision``; ADR-0553 removed external sources entirely. The parser
  still reads ``source_revision`` -- :attr:`Endpoint.is_external` and
  :meth:`Overlay.external_links` are how a reintroduced external endpoint would
  be *seen* rather than silently accepted -- and the committed artifact carries
  none, which ``test_the_overlay_declares_no_external_source`` pins.

Constants are mirrored from ``scripts/validate-autogenesis-knowledge.py``, whose
relational contract (unique ids, typed endpoints, local resolution, relation
domain/range) is what this artifact actually promises.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from functools import lru_cache
from pathlib import Path
from typing import Any

from ._paths import read_json, resolve_root

OVERLAY_PATH = Path("artifacts") / "autogenesis" / "knowledge-overlay-v1.json"
VALIDATOR = "validate-autogenesis-knowledge.py"

#: The seven top-level keys the schema requires, exactly.
TOP_KEYS = frozenset(
    {"schema_version", "kind", "sources", "namespaces", "relation_types", "entities", "links"}
)
#: Mirrored from the validator, which shrank with ADR-0553: ``concept``,
#: ``encounter``, ``technique``, ``curriculum-node`` and ``external-declaration``
#: were kinds only a sibling repository could supply, and there is no longer a
#: source that could carry one.
ENTITY_KINDS = frozenset(
    {
        "fact",
        "kernel-declaration",
        "operation",
        "producer",
        "checker",
        "capability",
        "obstruction",
        "episode",
        "evidence-artifact",
        "representation",
    }
)
#: Ordered strongest-first. An assurance is a claim about how the edge was
#: established, not about how confident anyone feels.
ASSURANCE_ORDER = (
    "formal-derived",
    "independently-checked",
    "registry-derived",
    "mechanically-observed",
    "human-reviewed",
    "heuristic",
    "proposed",
)
ASSURANCE = frozenset(ASSURANCE_ORDER)
METHODS = frozenset(
    {
        "kernel-derived",
        "checker-derived",
        "registry-derived",
        "mechanically-observed",
        "human-reviewed",
        "heuristic",
        "proposed",
    }
)


@dataclass(frozen=True, slots=True)
class Source:
    """One repository the overlay reads from."""

    id: str
    kind: str | None
    revision_policy: str | None
    revision: str | None
    path_hint: str | None
    license_note: str | None
    raw: dict[str, Any] = field(repr=False, default_factory=dict)

    @property
    def is_pinned(self) -> bool:
        """A source pinned to a foreign commit.

        False for every source since ADR-0553, and kept for the same reason as
        :meth:`Overlay.external_links`: it is what makes a reintroduced external
        source *visible* to a test rather than something the parser shrugs at.
        """
        return self.revision_policy == "pinned"


@dataclass(frozen=True, slots=True)
class Namespace:
    id: str
    resolution: str | None
    path: str | None
    id_pattern: str | None
    raw: dict[str, Any] = field(repr=False, default_factory=dict)


@dataclass(frozen=True, slots=True)
class RelationType:
    """A relation's declared domain and range."""

    id: str
    source_kinds: tuple[str, ...]
    target_kinds: tuple[str, ...]
    semantics: str | None


@dataclass(frozen=True, slots=True)
class Entity:
    """An overlay-owned node (a capability, obstruction, episode, ...)."""

    id: str
    kind: str
    title: str | None
    description: str | None
    status: str | None
    attributes: dict[str, Any] = field(default_factory=dict)
    raw: dict[str, Any] = field(repr=False, default_factory=dict)


@dataclass(frozen=True, slots=True)
class Endpoint:
    """One end of a link. ``source_revision`` is present exactly when external."""

    namespace: str
    kind: str
    id: str
    source_revision: str | None = None

    @property
    def is_external(self) -> bool:
        return self.source_revision is not None

    @classmethod
    def from_raw(cls, raw: dict[str, Any]) -> Endpoint:
        return cls(
            namespace=raw.get("namespace", ""),
            kind=raw.get("kind", ""),
            id=raw.get("id", ""),
            source_revision=raw.get("source_revision"),
        )


@dataclass(frozen=True, slots=True)
class Link:
    """One typed edge, with the assurance that says what it is worth."""

    id: str
    relation: str
    source: Endpoint
    target: Endpoint
    assurance: str
    status: str | None
    reason: str | None
    provenance: dict[str, Any] = field(default_factory=dict, repr=False)
    raw: dict[str, Any] = field(repr=False, default_factory=dict)

    @property
    def method(self) -> str | None:
        return self.provenance.get("method")

    @property
    def assurance_rank(self) -> int:
        """Position in :data:`ASSURANCE_ORDER`; lower is stronger.

        An unknown assurance ranks last rather than first: an unrecognised value
        must never read as the strongest one.
        """
        try:
            return ASSURANCE_ORDER.index(self.assurance)
        except ValueError:
            return len(ASSURANCE_ORDER)

    def touches(self, endpoint_id: str) -> bool:
        return endpoint_id in (self.source.id, self.target.id)

    @classmethod
    def from_raw(cls, raw: dict[str, Any]) -> Link:
        return cls(
            id=raw["id"],
            relation=raw.get("relation", ""),
            source=Endpoint.from_raw(raw.get("source") or {}),
            target=Endpoint.from_raw(raw.get("target") or {}),
            assurance=raw.get("assurance", ""),
            status=raw.get("status"),
            reason=raw.get("reason"),
            provenance=dict(raw.get("provenance") or {}),
            raw=raw,
        )


@dataclass(frozen=True, slots=True)
class Overlay:
    """The overlay document, typed."""

    root: Path
    path: Path
    schema_version: Any
    kind: str
    sources: tuple[Source, ...]
    namespaces: tuple[Namespace, ...]
    relation_types: tuple[RelationType, ...]
    entities: tuple[Entity, ...]
    links: tuple[Link, ...]

    def __len__(self) -> int:
        return len(self.links)

    # -- lookups (KeyError when absent, never a silent empty) ------------------

    def entity(self, entity_id: str) -> Entity:
        for row in self.entities:
            if row.id == entity_id:
                return row
        raise KeyError(f"no overlay entity {entity_id!r} in {self.path}")

    def link(self, link_id: str) -> Link:
        for row in self.links:
            if row.id == link_id:
                return row
        raise KeyError(f"no overlay link {link_id!r} in {self.path}")

    def source(self, source_id: str) -> Source:
        for row in self.sources:
            if row.id == source_id:
                return row
        raise KeyError(f"no overlay source {source_id!r} in {self.path}")

    def relation_type(self, relation: str) -> RelationType:
        for row in self.relation_types:
            if row.id == relation:
                return row
        raise KeyError(f"no relation type {relation!r} in {self.path}")

    # -- queries ---------------------------------------------------------------

    def query(
        self,
        relation: str | None = None,
        endpoint_id: str | None = None,
        *,
        assurance: str | None = None,
    ) -> tuple[Link, ...]:
        """Links matching every supplied filter.

        An empty result means the overlay was read and no link matched; the
        document is always fully loaded before this is called.
        """
        rows = self.links
        if relation is not None:
            rows = tuple(row for row in rows if row.relation == relation)
        if endpoint_id is not None:
            rows = tuple(row for row in rows if row.touches(endpoint_id))
        if assurance is not None:
            rows = tuple(row for row in rows if row.assurance == assurance)
        return rows

    def relation_counts(self) -> dict[str, int]:
        counts: dict[str, int] = {}
        for row in self.links:
            counts[row.relation] = counts.get(row.relation, 0) + 1
        return dict(sorted(counts.items()))

    def assurance_counts(self) -> dict[str, int]:
        counts: dict[str, int] = {}
        for row in self.links:
            counts[row.assurance] = counts.get(row.assurance, 0) + 1
        return dict(sorted(counts.items()))

    def external_links(self) -> tuple[Link, ...]:
        """Links with at least one endpoint outside this checkout.

        Empty by construction since ADR-0553 -- the overlay declares no external
        source -- and kept as the *detector* for one coming back, not as a
        supported query.
        """
        return tuple(row for row in self.links if row.source.is_external or row.target.is_external)


@lru_cache(maxsize=4)
def _load_cached(root_key: str) -> Overlay:
    root = Path(root_key)
    path = root / OVERLAY_PATH
    document = read_json(path)
    return Overlay(
        root=root,
        path=path,
        schema_version=document.get("schema_version"),
        kind=document.get("kind", ""),
        sources=tuple(
            Source(
                id=row.get("id", ""),
                kind=row.get("kind"),
                revision_policy=row.get("revision_policy"),
                revision=row.get("revision"),
                path_hint=row.get("path_hint"),
                license_note=row.get("license_note"),
                raw=row,
            )
            for row in document.get("sources", [])
        ),
        namespaces=tuple(
            Namespace(
                id=row.get("id", ""),
                resolution=row.get("resolution"),
                path=row.get("path"),
                id_pattern=row.get("id_pattern"),
                raw=row,
            )
            for row in document.get("namespaces", [])
        ),
        relation_types=tuple(
            RelationType(
                id=row.get("id", ""),
                source_kinds=tuple(row.get("source_kinds") or ()),
                target_kinds=tuple(row.get("target_kinds") or ()),
                semantics=row.get("semantics"),
            )
            for row in document.get("relation_types", [])
        ),
        entities=tuple(
            Entity(
                id=row.get("id", ""),
                kind=row.get("kind", ""),
                title=row.get("title"),
                description=row.get("description"),
                status=row.get("status"),
                attributes=dict(row.get("attributes") or {}),
                raw=row,
            )
            for row in document.get("entities", [])
        ),
        links=tuple(Link.from_raw(row) for row in document.get("links", [])),
    )


def load(root: Path | str | None = None, *, refresh: bool = False) -> Overlay:
    """Read the knowledge overlay. Cached per root."""
    resolved = resolve_root(root)
    if refresh:
        _load_cached.cache_clear()
    return _load_cached(str(resolved))


def query(
    relation: str | None = None,
    endpoint_id: str | None = None,
    *,
    assurance: str | None = None,
    root: Path | str | None = None,
) -> tuple[Link, ...]:
    return load(root).query(relation, endpoint_id, assurance=assurance)


def entities(root: Path | str | None = None) -> tuple[Entity, ...]:
    return load(root).entities


def links(root: Path | str | None = None) -> tuple[Link, ...]:
    return load(root).links


def relation_types(root: Path | str | None = None) -> tuple[RelationType, ...]:
    return load(root).relation_types


__all__ = [
    "ASSURANCE",
    "ASSURANCE_ORDER",
    "ENTITY_KINDS",
    "METHODS",
    "OVERLAY_PATH",
    "TOP_KEYS",
    "VALIDATOR",
    "Endpoint",
    "Entity",
    "Link",
    "Namespace",
    "Overlay",
    "RelationType",
    "Source",
    "entities",
    "links",
    "load",
    "query",
    "relation_types",
]
