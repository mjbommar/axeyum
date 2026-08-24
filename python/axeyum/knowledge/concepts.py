"""``artifacts/ontology/foundational-concepts.json`` -- the curriculum layer.

This file is **generated** by ``scripts/gen-foundational-concepts.py`` from
``docs/curriculum/curriculum.toml``, ``docs/foundational-resources/MATH-FIELDS.md``
and the curriculum layer directories. It is never hand-written, so this module
is a reader and nothing else.

It is the ``curriculum-node`` layer of the overlay's entity kinds, and the
natural join target for a fact's ``concept_refs``. An ``example_packs`` row with
``status == "validated"`` promises its ``path`` exists on disk -- the validator
checks that, and :meth:`Concept.missing_validated_packs` reproduces it so a
caller can see the same thing without shelling out.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from functools import lru_cache
from pathlib import Path
from typing import Any

from ._paths import read_json, resolve_root

CONCEPTS_PATH = Path("artifacts") / "ontology" / "foundational-concepts.json"
GENERATOR = "gen-foundational-concepts.py"
VALIDATOR = "validate-foundational-concepts.py"


@dataclass(frozen=True, slots=True)
class ExamplePack:
    id: str | None
    status: str | None
    path: str | None
    notes: str | None

    @property
    def is_validated(self) -> bool:
        return self.status == "validated"

    @classmethod
    def from_raw(cls, raw: Any) -> ExamplePack:
        if not isinstance(raw, dict):
            return cls(None, None, None, None)
        return cls(
            id=raw.get("id"),
            status=raw.get("status"),
            path=raw.get("path"),
            notes=raw.get("notes"),
        )


@dataclass(frozen=True, slots=True)
class Concept:
    """One foundational concept row."""

    id: str
    kind: str | None
    title: str | None
    domain: str | None
    field_ids: tuple[str, ...]
    curriculum_node: str | None
    curriculum_layer: int | str | None
    curriculum_area: str | None
    curriculum_status: str | None
    curriculum_family: str | None
    resource_status: str | None
    summary: str | None
    prerequisites: tuple[str, ...]
    unlocks: tuple[str, ...]
    decidability: Any
    axeyum_fragments: tuple[str, ...]
    example_packs: tuple[ExamplePack, ...]
    proof_routes: tuple[str, ...]
    source_refs: tuple[Any, ...]
    open_gaps: tuple[Any, ...]
    graduation: Any
    raw: dict[str, Any] = field(repr=False, default_factory=dict)

    def missing_validated_packs(self, root: Path) -> tuple[str, ...]:
        """Paths a ``validated`` example pack promises but does not have."""
        return tuple(
            pack.path
            for pack in self.example_packs
            if pack.is_validated and pack.path and not (root / pack.path).exists()
        )

    @classmethod
    def from_raw(cls, raw: dict[str, Any]) -> Concept:
        def seq(key: str) -> tuple[Any, ...]:
            value = raw.get(key) or []
            return tuple(value) if isinstance(value, list) else ()

        return cls(
            id=raw["id"],
            kind=raw.get("kind"),
            title=raw.get("title"),
            domain=raw.get("domain"),
            field_ids=seq("field_ids"),
            curriculum_node=raw.get("curriculum_node"),
            curriculum_layer=raw.get("curriculum_layer"),
            curriculum_area=raw.get("curriculum_area"),
            curriculum_status=raw.get("curriculum_status"),
            curriculum_family=raw.get("curriculum_family"),
            resource_status=raw.get("resource_status"),
            summary=raw.get("summary"),
            prerequisites=seq("prerequisites"),
            unlocks=seq("unlocks"),
            decidability=raw.get("decidability"),
            axeyum_fragments=seq("axeyum_fragments"),
            example_packs=tuple(ExamplePack.from_raw(row) for row in seq("example_packs")),
            proof_routes=seq("proof_routes"),
            source_refs=seq("source_refs"),
            open_gaps=seq("open_gaps"),
            graduation=raw.get("graduation"),
            raw=raw,
        )


@dataclass(frozen=True, slots=True)
class FoundationalConcepts:
    """The generated concept table."""

    root: Path
    path: Path
    schema_version: Any
    generated_from: tuple[str, ...]
    rows: tuple[Concept, ...]

    def __len__(self) -> int:
        return len(self.rows)

    def __iter__(self):
        return iter(self.rows)

    def get(self, concept_id: str) -> Concept:
        """One concept; :class:`KeyError` when absent."""
        for row in self.rows:
            if row.id == concept_id:
                return row
        raise KeyError(f"no foundational concept {concept_id!r} in {self.path}")

    def by_layer(self) -> dict[str, tuple[Concept, ...]]:
        """Grouped by curriculum layer.

        The key is stringified because the generated column mixes ``int`` layers
        with ``null``; a heterogeneous sort key raises, and a reader wants a
        stable label anyway.
        """
        grouped: dict[str, list[Concept]] = {}
        for row in self.rows:
            layer = "<none>" if row.curriculum_layer is None else str(row.curriculum_layer)
            grouped.setdefault(layer, []).append(row)
        return {k: tuple(v) for k, v in sorted(grouped.items())}

    def by_domain(self) -> dict[str, tuple[Concept, ...]]:
        grouped: dict[str, list[Concept]] = {}
        for row in self.rows:
            grouped.setdefault(row.domain or "<none>", []).append(row)
        return {k: tuple(v) for k, v in sorted(grouped.items())}

    def with_fragment(self, fragment: str) -> tuple[Concept, ...]:
        """Concepts naming an Axeyum fragment. Empty means none did."""
        return tuple(row for row in self.rows if fragment in row.axeyum_fragments)

    def missing_validated_packs(self) -> dict[str, tuple[str, ...]]:
        """Concept id to the validated example-pack paths that are absent."""
        out: dict[str, tuple[str, ...]] = {}
        for row in self.rows:
            missing = row.missing_validated_packs(self.root)
            if missing:
                out[row.id] = missing
        return out


@lru_cache(maxsize=4)
def _load_cached(root_key: str) -> FoundationalConcepts:
    root = Path(root_key)
    path = root / CONCEPTS_PATH
    document = read_json(path)
    sources = document.get("generated_from") or []
    return FoundationalConcepts(
        root=root,
        path=path,
        schema_version=document.get("schema_version"),
        generated_from=tuple(sources) if isinstance(sources, list) else (),
        rows=tuple(Concept.from_raw(row) for row in document.get("rows", [])),
    )


def load(root: Path | str | None = None, *, refresh: bool = False) -> FoundationalConcepts:
    """Read the generated foundational-concept table. Cached per root."""
    resolved = resolve_root(root)
    if refresh:
        _load_cached.cache_clear()
    return _load_cached(str(resolved))


def get(concept_id: str, root: Path | str | None = None) -> Concept:
    return load(root).get(concept_id)


def rows(root: Path | str | None = None) -> tuple[Concept, ...]:
    return load(root).rows


__all__ = [
    "CONCEPTS_PATH",
    "GENERATOR",
    "VALIDATOR",
    "Concept",
    "ExamplePack",
    "FoundationalConcepts",
    "get",
    "load",
    "rows",
]
