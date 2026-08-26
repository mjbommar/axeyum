"""Read-only access to exact, footprint-aware imported theorem candidates."""

from __future__ import annotations

from dataclasses import dataclass, field
from functools import lru_cache
from pathlib import Path
from typing import Any

from ._paths import read_json, resolve_root

INDEX_PATH = Path("artifacts/autogenesis/imported-candidate-search-index-v1.json")


@dataclass(frozen=True, slots=True)
class ImportedCandidate:
    """One independently audited imported theorem candidate."""

    name: str
    canonical_type: str
    alpha_type_expression_sha256: str
    declaration_content_sha256: str
    axiom_footprint: tuple[str, ...]
    direct_theorem_dependencies: tuple[str, ...]
    retrieval_disposition: str
    strategy_eligible: bool
    execution_eligible: bool
    raw: dict[str, Any] = field(repr=False, default_factory=dict)

    @classmethod
    def from_raw(cls, raw: dict[str, Any]) -> ImportedCandidate:
        return cls(
            name=raw["name"],
            canonical_type=raw["canonical_type"],
            alpha_type_expression_sha256=raw["alpha_type_expression_sha256"],
            declaration_content_sha256=raw["declaration_content_sha256"],
            axiom_footprint=tuple(raw["axiom_footprint"]),
            direct_theorem_dependencies=tuple(raw["direct_theorem_dependencies"]),
            retrieval_disposition=raw["retrieval_disposition"],
            strategy_eligible=raw["strategy_eligible"],
            execution_eligible=raw["execution_eligible"],
            raw=raw,
        )


@dataclass(frozen=True, slots=True)
class ImportedCandidateIndex:
    root: Path
    path: Path
    candidates: tuple[ImportedCandidate, ...]
    census: dict[str, int]

    def __len__(self) -> int:
        return len(self.candidates)

    def __iter__(self):
        return iter(self.candidates)

    def with_type_fragment(self, fragment: str) -> tuple[ImportedCandidate, ...]:
        if not fragment:
            raise ValueError("canonical type fragment must not be empty")
        return tuple(row for row in self.candidates if fragment in row.canonical_type)


@lru_cache(maxsize=4)
def _load_cached(root_key: str) -> ImportedCandidateIndex:
    root = Path(root_key)
    path = root / INDEX_PATH
    document = read_json(path)
    rows = tuple(ImportedCandidate.from_raw(raw) for raw in document["candidates"])
    identities = {(row.name, row.declaration_content_sha256) for row in rows}
    if len(identities) != len(rows):
        raise ValueError(f"duplicate imported candidate identity in {path}")
    return ImportedCandidateIndex(
        root=root,
        path=path,
        candidates=rows,
        census=dict(document["census"]),
    )


def load(root: Path | str | None = None, *, refresh: bool = False) -> ImportedCandidateIndex:
    resolved = resolve_root(root)
    if refresh:
        _load_cached.cache_clear()
    return _load_cached(str(resolved))


__all__ = ["INDEX_PATH", "ImportedCandidate", "ImportedCandidateIndex", "load"]
