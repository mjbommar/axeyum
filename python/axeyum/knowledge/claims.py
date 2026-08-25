"""The claim ledger: ``artifacts/claims/<family>/<id>/claim.json``.

A claim is not a fact, and the difference is in ``formal``. A fact's ``formal``
is the proposition itself; a claim's is a **generator recipe** -- a CNF family,
its parameters and the source file that emits it. So a claim records what a
search computed, and it becomes evidence for a proposition only through a
``claim-ref`` evidence row on a fact.

The layout is nested, not flat: reading ``artifacts/claims/*.json`` finds
nothing at all, which is exactly the "empty answer to a question you did not
ask" trap. :func:`load` globs ``**/claim.json`` and records the directory it
walked, so an empty ledger is always distinguishable from an unread one.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from functools import lru_cache
from pathlib import Path
from typing import Any

from ._paths import read_json, require_dir, resolve_root

CLAIMS_DIR = Path("artifacts") / "claims"
VALIDATOR = "validate-claims.py"

#: Required keys, mirrored from ``artifacts/ontology/claim.schema.json``.
REQUIRED = frozenset(
    {
        "schema_version",
        "id",
        "title",
        "statement",
        "epistemic_status",
        "formal",
        "concept_refs",
        "axeyum_refs",
        "provenance",
        "evidence",
    }
)


@dataclass(frozen=True, slots=True)
class ConceptRef:
    """A claim's pointer at a named concept.

    Carried no ``resolved`` flag since 2026-08-24. It used to assert that the
    ``ref`` had been found in a sibling repository at a pinned revision, which
    nothing in this checkout could re-derive; ADR-0553 removed that repository
    from the project's surface and the flag with it. A boolean nobody can check
    is worse than no boolean.
    """

    graph: str | None
    ref: str | None
    relation: str | None
    note: str | None

    @classmethod
    def from_raw(cls, raw: Any) -> ConceptRef:
        if not isinstance(raw, dict):
            return cls(None, None, None, None)
        return cls(
            graph=raw.get("graph"),
            ref=raw.get("ref"),
            relation=raw.get("relation"),
            note=raw.get("note") or raw.get("notes"),
        )


@dataclass(frozen=True, slots=True)
class Claim:
    """One computed claim."""

    id: str
    family: str
    path: Path
    title: str | None
    statement: str | None
    epistemic_status: str | None
    novelty: str | None
    formal: dict[str, Any] = field(default_factory=dict, repr=False)
    concept_refs: tuple[ConceptRef, ...] = ()
    axeyum_refs: dict[str, Any] = field(default_factory=dict, repr=False)
    provenance: dict[str, Any] = field(default_factory=dict, repr=False)
    evidence: tuple[dict[str, Any], ...] = ()
    frontier: Any = None
    notes: Any = None
    raw: dict[str, Any] = field(repr=False, default_factory=dict)

    @property
    def generator(self) -> str | None:
        """The source file that emits this family. ``formal`` is a recipe."""
        return self.formal.get("generator")

    @property
    def cnf_family(self) -> str | None:
        return self.formal.get("family")

    @property
    def parameters(self) -> dict[str, Any]:
        params = self.formal.get("parameters")
        return dict(params) if isinstance(params, dict) else {}

    @property
    def fragments(self) -> tuple[str, ...]:
        fragments = self.axeyum_refs.get("fragments")
        return tuple(fragments) if isinstance(fragments, list) else ()

    @property
    def missing_required(self) -> frozenset[str]:
        return frozenset(REQUIRED - set(self.raw))

    @classmethod
    def from_raw(cls, path: Path, family: str, raw: dict[str, Any]) -> Claim:
        refs = raw.get("concept_refs") or []
        evidence = raw.get("evidence") or []
        return cls(
            id=raw.get("id", f"<{path.parent.name}>"),
            family=family,
            path=path,
            title=raw.get("title"),
            statement=raw.get("statement"),
            epistemic_status=raw.get("epistemic_status"),
            novelty=raw.get("novelty"),
            formal=dict(raw.get("formal") or {}),
            concept_refs=tuple(ConceptRef.from_raw(row) for row in refs),
            axeyum_refs=dict(raw.get("axeyum_refs") or {}),
            provenance=dict(raw.get("provenance") or {}),
            evidence=tuple(row for row in evidence if isinstance(row, dict)),
            frontier=raw.get("frontier"),
            notes=raw.get("notes"),
            raw=raw,
        )


@dataclass(frozen=True, slots=True)
class ClaimLedger:
    """Every ``claim.json`` under ``artifacts/claims/``."""

    root: Path
    directory: Path
    claims: tuple[Claim, ...]

    def __len__(self) -> int:
        return len(self.claims)

    def __iter__(self):
        return iter(self.claims)

    def get(self, claim_id: str) -> Claim:
        """One claim; :class:`KeyError` when absent."""
        for claim in self.claims:
            if claim.id == claim_id:
                return claim
        raise KeyError(f"no claim {claim_id!r} under {self.directory}")

    def families(self) -> dict[str, tuple[Claim, ...]]:
        grouped: dict[str, list[Claim]] = {}
        for claim in self.claims:
            grouped.setdefault(claim.family, []).append(claim)
        return {k: tuple(v) for k, v in sorted(grouped.items())}

    def by_status(self) -> dict[str, tuple[Claim, ...]]:
        grouped: dict[str, list[Claim]] = {}
        for claim in self.claims:
            grouped.setdefault(claim.epistemic_status or "?", []).append(claim)
        return {k: tuple(v) for k, v in sorted(grouped.items())}

    def concept_refs(self) -> tuple[ConceptRef, ...]:
        """Every topic citation, across all claims. Nothing resolves them."""
        return tuple(ref for claim in self.claims for ref in claim.concept_refs)

    def referenced_by(self, path_suffix: str) -> tuple[Claim, ...]:
        """Claims whose file path ends with ``path_suffix``.

        A fact's ``claim-ref`` evidence names a repository-relative artifact
        path; this is how that resolves back to a claim.
        """
        return tuple(claim for claim in self.claims if str(claim.path).endswith(path_suffix))


@lru_cache(maxsize=4)
def _load_cached(root_key: str) -> ClaimLedger:
    root = Path(root_key)
    directory = require_dir(root / CLAIMS_DIR)
    claims: list[Claim] = []
    for path in sorted(directory.glob("*/*/claim.json")):
        raw = read_json(path)
        family = path.parent.parent.name
        claims.append(Claim.from_raw(path, family, raw))
    return ClaimLedger(root=root, directory=directory, claims=tuple(claims))


def load(root: Path | str | None = None, *, refresh: bool = False) -> ClaimLedger:
    """Read every claim. Cached per root; a missing directory raises."""
    resolved = resolve_root(root)
    if refresh:
        _load_cached.cache_clear()
    return _load_cached(str(resolved))


def get(claim_id: str, root: Path | str | None = None) -> Claim:
    return load(root).get(claim_id)


def families(root: Path | str | None = None) -> dict[str, tuple[Claim, ...]]:
    return load(root).families()


__all__ = [
    "CLAIMS_DIR",
    "REQUIRED",
    "VALIDATOR",
    "Claim",
    "ClaimLedger",
    "ConceptRef",
    "families",
    "get",
    "load",
]
