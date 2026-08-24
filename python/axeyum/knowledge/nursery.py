"""The frozen blind-evaluation population, and the held-out rule it enforces.

``artifacts/autogenesis/nursery-v1.json`` preregisters propositions into
``train`` / ``development`` / ``held-out`` (plus two ``longitudinal`` rows). The
split key is ``<family>:<statement-shape>`` **because a proof route for one
member is evidence about its siblings**: on 2026-08-21 one capsule registered
against a single held-out fact spent 19 of 76 held-out propositions, 25% of the
partition, and nothing caught it for a day.

Two consequences are hard-coded here:

* **Every accessor answers by ``partition``, never by a count.**
  "Dependency-ready" and "train + development" are both 138 and are *different
  sets* -- the ready set is 44 train, 44 development and 50 held-out. A count is
  not an answer to a partition question.
* **The filter lives in the tool.** :func:`is_safe_to_reference` is what an
  agent calls before naming a fact anywhere, so the guarantee does not depend on
  a prompt remembering it.

The repair for a breach is an amendment, never a deletion (ADR-0542); the
amendment ledger is exposed read-only.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from functools import lru_cache
from pathlib import Path
from typing import Any

from ._paths import read_json, resolve_root

NURSERY_PATH = Path("artifacts") / "autogenesis" / "nursery-v1.json"
GATE = "check-autogenesis-holdout-isolation.py"

#: The partition that must stay blind.
HELD_OUT = "held-out"
#: The partitions the policy requires to exist.
EVALUATION_PARTITIONS = ("train", "development", "held-out")
#: A held-out fact settled by ANY route is spent; the registry is only one way in.
SETTLED = frozenset({"proved", "computed"})
#: The two files that DEFINE the population and so necessarily name its members.
POPULATION_FILES = frozenset({"nursery-v1.json", "mathlib-nat-int-fact-catalog-v1.json"})


class NurseryError(RuntimeError):
    """Fail-closed: an unreadable manifest, or a held-out population that has
    somehow become empty, is an error rather than a quiet pass."""


@dataclass(frozen=True, slots=True)
class NurseryEntry:
    """One preregistered proposition."""

    fact_id: str
    partition: str
    family: str | None
    proof_shape: str | None
    provenance_class: str | None
    source_group: str | None
    route_hypotheses: tuple[str, ...]
    mutation_of: str | None
    answer_access: str | None
    raw: dict[str, Any] = field(repr=False, default_factory=dict)

    @property
    def is_held_out(self) -> bool:
        return self.partition == HELD_OUT

    @property
    def split_key(self) -> str:
        """``<family>:<statement-shape>`` -- the unit that is actually spent."""
        return f"{self.family}:{self.proof_shape}"

    @classmethod
    def from_raw(cls, raw: dict[str, Any]) -> NurseryEntry:
        hypotheses = raw.get("route_hypotheses") or []
        return cls(
            fact_id=raw["fact_id"],
            partition=raw.get("partition", ""),
            family=raw.get("family"),
            proof_shape=raw.get("proof_shape"),
            provenance_class=raw.get("provenance_class"),
            source_group=raw.get("source_group"),
            route_hypotheses=tuple(hypotheses) if isinstance(hypotheses, list) else (),
            mutation_of=raw.get("mutation_of"),
            answer_access=raw.get("answer_access"),
            raw=raw,
        )


@dataclass(frozen=True, slots=True)
class Amendment:
    """One irreversible repair to the split. Read-only here, always."""

    date: str | None
    family: str | None
    from_partition: str | None
    to_partition: str | None
    irreversible: bool | None
    reason: str | None
    authority: str | None
    breach: dict[str, Any] = field(default_factory=dict, repr=False)
    raw: dict[str, Any] = field(repr=False, default_factory=dict)

    @classmethod
    def from_raw(cls, raw: dict[str, Any]) -> Amendment:
        return cls(
            date=raw.get("date"),
            family=raw.get("family"),
            from_partition=raw.get("from_partition") or raw.get("from"),
            to_partition=raw.get("to_partition") or raw.get("to"),
            irreversible=raw.get("irreversible"),
            reason=raw.get("reason"),
            authority=raw.get("authority"),
            breach=dict(raw.get("breach") or {}),
            raw=raw,
        )


@dataclass(frozen=True, slots=True)
class Nursery:
    """The manifest, typed and partition-aware."""

    root: Path
    path: Path
    schema_version: Any
    kind: str
    state: str
    entries: tuple[NurseryEntry, ...]
    amendments: tuple[Amendment, ...]
    policy: dict[str, Any] = field(default_factory=dict, repr=False)
    split_policy_sha256: str | None = None
    source_catalog_sha256: str | None = None

    def __len__(self) -> int:
        return len(self.entries)

    def __iter__(self):
        return iter(self.entries)

    # -- partition answers -----------------------------------------------------

    def entry(self, fact_id: str) -> NurseryEntry:
        """One row; :class:`KeyError` when the fact is not in the population.

        Not-in-the-population and held-out are different answers and must not be
        collapsed: the first means this manifest says nothing about the fact.
        """
        for row in self.entries:
            if row.fact_id == fact_id:
                return row
        raise KeyError(f"{fact_id!r} is not in the nursery population ({self.path})")

    def partition_of(self, fact_id: str) -> str:
        """The fact's partition; :class:`KeyError` when it is not preregistered."""
        return self.entry(fact_id).partition

    def family_of(self, fact_id: str) -> str | None:
        """The fact's family -- the unit a breach actually spends."""
        return self.entry(fact_id).family

    def contains(self, fact_id: str) -> bool:
        """Whether the manifest says anything at all about this fact."""
        return any(row.fact_id == fact_id for row in self.entries)

    def by_partition(self) -> dict[str, tuple[NurseryEntry, ...]]:
        grouped: dict[str, list[NurseryEntry]] = {}
        for row in self.entries:
            grouped.setdefault(row.partition, []).append(row)
        return {k: tuple(v) for k, v in sorted(grouped.items())}

    def partition(self, name: str) -> tuple[NurseryEntry, ...]:
        """Every row in one partition; :class:`KeyError` when the partition does
        not exist, so a typo cannot read as an empty partition."""
        grouped = self.by_partition()
        if name not in grouped:
            raise KeyError(f"no partition {name!r}; the manifest has {sorted(grouped)}")
        return grouped[name]

    def held_out_ids(self) -> frozenset[str]:
        """Exactly what ``check-autogenesis-holdout-isolation.py`` protects.

        Raises:
            NurseryError: when the population is empty -- fail-closed, because a
                guard whose subject has vanished reports the same "no violations"
                as a guard that works.
        """
        held = frozenset(row.fact_id for row in self.entries if row.partition == HELD_OUT)
        if not held:
            raise NurseryError(
                "the held-out population is empty; any isolation check would pass vacuously"
            )
        return held

    def is_safe_to_reference(self, fact_id: str) -> bool:
        """False exactly for a held-out fact.

        A fact outside the population is safe: the manifest makes no claim about
        it. Use :meth:`contains` when the distinction matters.
        """
        for row in self.entries:
            if row.fact_id == fact_id:
                return not row.is_held_out
        return True

    def families(self) -> dict[str, tuple[NurseryEntry, ...]]:
        """Rows grouped by family. The partition unit is the whole family:
        ``whole-family-with-source-review-groups-indivisible``."""
        grouped: dict[str, list[NurseryEntry]] = {}
        for row in self.entries:
            grouped.setdefault(row.family or "<none>", []).append(row)
        return {k: tuple(v) for k, v in sorted(grouped.items())}

    def family(self, name: str) -> tuple[NurseryEntry, ...]:
        """Every row in one family; :class:`KeyError` when the family is unknown."""
        grouped = self.families()
        if name not in grouped:
            raise KeyError(f"no family {name!r}; the manifest has {len(grouped)} families")
        return grouped[name]

    def held_out_families(self) -> frozenset[str]:
        """The families a breach would spend whole."""
        return frozenset(
            row.family for row in self.entries if row.is_held_out and row.family is not None
        )

    def split_keys(self) -> dict[str, tuple[NurseryEntry, ...]]:
        """Rows grouped by ``<family>:<statement-shape>``, the real split key."""
        grouped: dict[str, list[NurseryEntry]] = {}
        for row in self.entries:
            grouped.setdefault(row.split_key, []).append(row)
        return {k: tuple(v) for k, v in sorted(grouped.items())}

    def filter_safe(self, fact_ids) -> tuple[str, ...]:
        """Drop held-out ids from a sequence. The filter is in the tool, not the
        prompt."""
        return tuple(fid for fid in fact_ids if self.is_safe_to_reference(fid))


@lru_cache(maxsize=4)
def _load_cached(root_key: str) -> Nursery:
    root = Path(root_key)
    path = root / NURSERY_PATH
    if not path.is_file():
        raise NurseryError(f"nursery manifest is missing: {path}")
    document = read_json(path)
    rows = document.get("entries")
    if not isinstance(rows, list):
        raise NurseryError(f"nursery manifest has no entries: {path}")
    return Nursery(
        root=root,
        path=path,
        schema_version=document.get("schema_version"),
        kind=document.get("kind", ""),
        state=document.get("state", ""),
        entries=tuple(NurseryEntry.from_raw(row) for row in rows if isinstance(row, dict)),
        amendments=tuple(Amendment.from_raw(row) for row in document.get("amendments", [])),
        policy=dict(document.get("policy") or {}),
        split_policy_sha256=document.get("split_policy_sha256"),
        source_catalog_sha256=document.get("source_catalog_sha256"),
    )


def load(root: Path | str | None = None, *, refresh: bool = False) -> Nursery:
    """Read the nursery manifest. Cached per root; fail-closed on a bad manifest."""
    resolved = resolve_root(root)
    if refresh:
        _load_cached.cache_clear()
    return _load_cached(str(resolved))


def partition_of(fact_id: str, root: Path | str | None = None) -> str:
    return load(root).partition_of(fact_id)


def family_of(fact_id: str, root: Path | str | None = None) -> str | None:
    return load(root).family_of(fact_id)


def held_out_ids(root: Path | str | None = None) -> frozenset[str]:
    return load(root).held_out_ids()


def is_safe_to_reference(fact_id: str, root: Path | str | None = None) -> bool:
    return load(root).is_safe_to_reference(fact_id)


def families(root: Path | str | None = None) -> dict[str, tuple[NurseryEntry, ...]]:
    return load(root).families()


def amendments(root: Path | str | None = None) -> tuple[Amendment, ...]:
    return load(root).amendments


__all__ = [
    "EVALUATION_PARTITIONS",
    "GATE",
    "HELD_OUT",
    "NURSERY_PATH",
    "POPULATION_FILES",
    "SETTLED",
    "Amendment",
    "Nursery",
    "NurseryEntry",
    "NurseryError",
    "amendments",
    "families",
    "family_of",
    "held_out_ids",
    "is_safe_to_reference",
    "load",
    "partition_of",
]
