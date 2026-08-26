"""Deterministic retrieval over the kernel-derived lemma search index.

This module exposes candidates, never applicability or proof authority.  The
index is generated from declarations already accepted by the kernel; a producer
that retrieves a row must still construct a term and submit it to the checker.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from functools import lru_cache
from pathlib import Path
from typing import Any

from ._paths import read_json, resolve_root

INDEX_PATH = Path("artifacts") / "autogenesis" / "kernel-lemma-search-index-v1.json"


@dataclass(frozen=True, slots=True)
class Lemma:
    """One accepted theorem and its mechanically observed neighborhood."""

    id: str
    canonical_type: str
    axiom_footprint_size: int
    visible_in: tuple[str, ...]
    direct_type_declarations: tuple[str, ...]
    direct_declarations: tuple[str, ...]
    dependencies: tuple[str, ...]
    dependents: tuple[str, ...]
    dependency_depth: int
    fact_ids: tuple[str, ...]
    search_authority: str
    raw: dict[str, Any] = field(repr=False, default_factory=dict)

    @classmethod
    def from_raw(cls, raw: dict[str, Any]) -> Lemma:
        return cls(
            id=raw["kernel_declaration_id"],
            canonical_type=raw["canonical_type"],
            axiom_footprint_size=raw["axiom_footprint_size"],
            visible_in=tuple(raw["visible_in"]),
            direct_type_declarations=tuple(raw["direct_type_dependencies"]),
            direct_declarations=tuple(raw["direct_declaration_dependencies"]),
            dependencies=tuple(raw["direct_theorem_dependencies"]),
            dependents=tuple(raw["direct_theorem_dependents"]),
            dependency_depth=raw["dependency_depth"],
            fact_ids=tuple(raw["exact_fact_ids"]),
            search_authority=raw["search_authority"],
            raw=raw,
        )


@dataclass(frozen=True, slots=True)
class LemmaIndex:
    """The generated candidate index with exact-identity queries."""

    root: Path
    path: Path
    lemmas: tuple[Lemma, ...]
    census: dict[str, int]
    unresolved: tuple[dict[str, str], ...]
    _by_id: dict[str, Lemma] = field(repr=False, default_factory=dict)
    _by_fact: dict[str, tuple[Lemma, ...]] = field(repr=False, default_factory=dict)

    def __len__(self) -> int:
        return len(self.lemmas)

    def __iter__(self):
        return iter(self.lemmas)

    def get(self, declaration_id: str) -> Lemma:
        """Return one exact declaration; raise :class:`KeyError` when absent."""
        try:
            return self._by_id[declaration_id]
        except KeyError:
            raise KeyError(f"no kernel lemma {declaration_id!r} in {self.path}") from None

    def for_fact(self, fact_id: str) -> tuple[Lemma, ...]:
        """Return exact evidence links for ``fact_id`` in stable declaration order."""
        return self._by_fact.get(fact_id, ())

    def prerequisites(self, declaration_id: str) -> tuple[Lemma, ...]:
        lemma = self.get(declaration_id)
        return tuple(self._by_id[item] for item in lemma.dependencies)

    def consumers(self, declaration_id: str) -> tuple[Lemma, ...]:
        lemma = self.get(declaration_id)
        return tuple(self._by_id[item] for item in lemma.dependents)

    def with_type_fragment(self, fragment: str) -> tuple[Lemma, ...]:
        """Return stable candidate rows whose canonical type contains ``fragment``."""
        if not fragment:
            raise ValueError("canonical type fragment must not be empty")
        return tuple(lemma for lemma in self.lemmas if fragment in lemma.canonical_type)


@lru_cache(maxsize=4)
def _load_cached(root_key: str) -> LemmaIndex:
    root = Path(root_key)
    path = root / INDEX_PATH
    document = read_json(path)
    rows = tuple(Lemma.from_raw(raw) for raw in document["lemmas"])
    by_id = {lemma.id: lemma for lemma in rows}
    if len(by_id) != len(rows):
        raise ValueError(f"duplicate kernel declaration in {path}")
    by_fact_lists: dict[str, list[Lemma]] = {}
    for lemma in rows:
        for fact_id in lemma.fact_ids:
            by_fact_lists.setdefault(fact_id, []).append(lemma)
    by_fact = {
        fact_id: tuple(sorted(lemmas, key=lambda item: item.id))
        for fact_id, lemmas in sorted(by_fact_lists.items())
    }
    return LemmaIndex(
        root=root,
        path=path,
        lemmas=rows,
        census=dict(document["census"]),
        unresolved=tuple(document["unresolved_prefixed_kernel_evidence"]),
        _by_id=by_id,
        _by_fact=by_fact,
    )


def load(root: Path | str | None = None, *, refresh: bool = False) -> LemmaIndex:
    resolved = resolve_root(root)
    if refresh:
        _load_cached.cache_clear()
    return _load_cached(str(resolved))


def get(declaration_id: str, root: Path | str | None = None) -> Lemma:
    return load(root).get(declaration_id)


def for_fact(fact_id: str, root: Path | str | None = None) -> tuple[Lemma, ...]:
    return load(root).for_fact(fact_id)


__all__ = ["INDEX_PATH", "Lemma", "LemmaIndex", "for_fact", "get", "load"]
