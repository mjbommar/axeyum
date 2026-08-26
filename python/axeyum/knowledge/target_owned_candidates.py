"""Read-only access to reusable target-owned theorem capsules."""

from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path

from ._paths import read_json, resolve_root

CAPSULE_PATH = Path("artifacts/autogenesis/bitwise-clean-family-capsule-v1.json")
PROJECTION_PATH = Path("artifacts/autogenesis/bitwise-clean-family-projection-v1.json")


@dataclass(frozen=True, slots=True)
class TargetOwnedCandidate:
    """One checked theorem root from an Axeyum-produced reusable capsule."""

    name: str
    canonical_type: str
    declaration_identity: str
    axiom_footprint: tuple[str, ...]
    direct_theorem_dependencies: tuple[str, ...]
    semantic_analogue_fact_ids: tuple[str, ...]
    capsule_path: str
    capsule_sha256: str
    exact_imported_identity: bool
    reuse_eligible: bool
    authoritative_operation_eligible: bool


@dataclass(frozen=True, slots=True)
class TargetOwnedCandidateIndex:
    root: Path
    candidates: tuple[TargetOwnedCandidate, ...]

    def __len__(self) -> int:
        return len(self.candidates)

    def __iter__(self):
        return iter(self.candidates)

    def with_type_fragment(self, fragment: str) -> tuple[TargetOwnedCandidate, ...]:
        if not fragment:
            raise ValueError("canonical type fragment must not be empty")
        return tuple(row for row in self.candidates if fragment in row.canonical_type)


@lru_cache(maxsize=4)
def _load_cached(root_key: str) -> TargetOwnedCandidateIndex:
    root = Path(root_key)
    capsule = read_json(root / CAPSULE_PATH)
    projection = read_json(root / PROJECTION_PATH)
    projected = {row["clean_theorem"]: row for row in projection["rows"]}
    stream = capsule["external_stream"]
    candidates = []
    for capsule_root in capsule["roots"]:
        name = capsule_root["name"]
        row = projected.get(name)
        if row is None:
            raise ValueError(f"target-owned capsule root is absent from projection: {name}")
        candidates.append(
            TargetOwnedCandidate(
                name=name,
                canonical_type=row["clean_canonical_type"],
                declaration_identity=capsule_root["declaration_identity"],
                axiom_footprint=tuple(capsule_root["axiom_footprint"]),
                direct_theorem_dependencies=tuple(capsule_root["direct_theorem_dependencies"]),
                semantic_analogue_fact_ids=(row["fact_id"],),
                capsule_path=stream["path"],
                capsule_sha256=stream["sha256"],
                exact_imported_identity=row["exact_imported_identity"],
                reuse_eligible=not capsule_root["axiom_footprint"],
                authoritative_operation_eligible=row["authoritative_operation_eligible"],
            )
        )
    candidates.sort(key=lambda row: (row.name, row.declaration_identity))
    identities = {(row.name, row.declaration_identity) for row in candidates}
    if len(identities) != len(candidates):
        raise ValueError("duplicate target-owned candidate identity")
    return TargetOwnedCandidateIndex(root=root, candidates=tuple(candidates))


def load(root: Path | str | None = None, *, refresh: bool = False) -> TargetOwnedCandidateIndex:
    resolved = resolve_root(root)
    if refresh:
        _load_cached.cache_clear()
    return _load_cached(str(resolved))


__all__ = [
    "CAPSULE_PATH",
    "PROJECTION_PATH",
    "TargetOwnedCandidate",
    "TargetOwnedCandidateIndex",
    "load",
]
