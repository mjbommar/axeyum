"""A shape-classified index of ``artifacts/autogenesis/``.

958 JSON documents carry **707 distinct ``kind`` values**: the vocabulary is
per-episode, not a closed set, so nothing here enumerates kinds. The index
classifies by *shape* instead -- the terminal token of the filename, after a
trailing ``-vN`` is stripped -- and uses ``kind`` as the authoritative
confirmation. The two agree closely and where they do not,
:attr:`Artifact.shape_confirmed` is ``False`` and both readings are kept; a
router that silently preferred one would hide exactly the drift worth seeing.

The dominant idiom is a plan paired with a result, each pair having its own
dedicated ``scripts/check-autogenesis-<name>-{plan,result}.py``.
:meth:`ArtifactIndex.pairs` reconstructs those pairs by stem, and
:meth:`ArtifactIndex.unpaired_plans` names the plans with no result -- a plan
without a result is an episode that did not finish, which is a different thing
from an episode that failed.
"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass, field
from functools import lru_cache
from pathlib import Path
from typing import Any

from ._paths import require_dir, resolve_root

ARTIFACTS_DIR = Path("artifacts") / "autogenesis"

#: The shapes a filename suffix routes to. Everything else is ``other`` -- a
#: value, not a failure.
SHAPES = ("plan", "result", "decline", "admission", "adapter", "policy", "capsule")
OTHER = "other"

_VERSION_RE = re.compile(r"-v\d+$")


def _strip_version(text: str) -> tuple[str, str | None]:
    match = _VERSION_RE.search(text)
    if match:
        return text[: match.start()], match.group(0)[1:]
    return text, None


def classify(text: str) -> str:
    """Map a filename stem or a ``kind`` string to one of :data:`SHAPES`."""
    base, _ = _strip_version(text)
    terminal = base.rsplit("-", 1)[-1]
    return terminal if terminal in SHAPES else OTHER


@dataclass(frozen=True, slots=True)
class Artifact:
    """One JSON document under ``artifacts/autogenesis/``."""

    path: Path
    name: str
    stem: str
    version: str | None
    shape: str
    kind: str | None
    kind_shape: str
    readable: bool
    document: dict[str, Any] = field(repr=False, default_factory=dict)

    @property
    def shape_confirmed(self) -> bool:
        """The filename router and the ``kind`` field agree."""
        return self.shape == self.kind_shape

    @property
    def pair_key(self) -> tuple[str, str | None]:
        """``(base stem without the shape token, version)`` -- the plan/result key."""
        base, version = _strip_version(self.stem)
        if self.shape in SHAPES and base.endswith(f"-{self.shape}"):
            base = base[: -(len(self.shape) + 1)]
        return base, version


@dataclass(frozen=True, slots=True)
class Pair:
    """A plan and the result that answers it."""

    key: tuple[str, str | None]
    plan: Artifact
    result: Artifact


@dataclass(frozen=True, slots=True)
class ArtifactIndex:
    """Every artifact JSON, indexed by shape."""

    root: Path
    directory: Path
    artifacts: tuple[Artifact, ...]

    def __len__(self) -> int:
        return len(self.artifacts)

    def __iter__(self):
        return iter(self.artifacts)

    def get(self, name: str) -> Artifact:
        """One artifact by file name; :class:`KeyError` when absent."""
        for row in self.artifacts:
            if row.name == name or row.stem == name:
                return row
        raise KeyError(f"no artifact {name!r} under {self.directory}")

    def by_shape(self) -> dict[str, tuple[Artifact, ...]]:
        grouped: dict[str, list[Artifact]] = {}
        for row in self.artifacts:
            grouped.setdefault(row.shape, []).append(row)
        return {k: tuple(v) for k, v in sorted(grouped.items())}

    def shape(self, name: str) -> tuple[Artifact, ...]:
        """Every artifact of one shape; :class:`KeyError` for an unknown shape,
        so a typo cannot read as "none of those exist"."""
        if name not in (*SHAPES, OTHER):
            raise KeyError(f"unknown shape {name!r}; known shapes are {(*SHAPES, OTHER)}")
        return tuple(row for row in self.artifacts if row.shape == name)

    def kinds(self) -> frozenset[str]:
        """Every distinct ``kind`` seen. Deliberately not enumerated as a
        constant: the vocabulary is per-episode."""
        return frozenset(row.kind for row in self.artifacts if row.kind)

    def unconfirmed(self) -> tuple[Artifact, ...]:
        """Artifacts whose filename shape and ``kind`` shape disagree."""
        return tuple(row for row in self.artifacts if not row.shape_confirmed)

    def unreadable(self) -> tuple[Artifact, ...]:
        """Files that are not valid JSON. Recorded rather than skipped."""
        return tuple(row for row in self.artifacts if not row.readable)

    def pairs(self) -> tuple[Pair, ...]:
        """Plan/result pairs, matched on stem and version."""
        plans = {row.pair_key: row for row in self.artifacts if row.shape == "plan"}
        results = {row.pair_key: row for row in self.artifacts if row.shape == "result"}
        return tuple(
            Pair(key=key, plan=plans[key], result=results[key])
            for key in sorted(set(plans) & set(results), key=lambda k: (k[0], k[1] or ""))
        )

    def unpaired_plans(self) -> tuple[Artifact, ...]:
        """Plans with no matching result -- an episode that did not finish."""
        results = {row.pair_key for row in self.artifacts if row.shape == "result"}
        return tuple(
            row for row in self.artifacts if row.shape == "plan" and row.pair_key not in results
        )

    def unpaired_results(self) -> tuple[Artifact, ...]:
        """Results with no matching plan."""
        plans = {row.pair_key for row in self.artifacts if row.shape == "plan"}
        return tuple(
            row for row in self.artifacts if row.shape == "result" and row.pair_key not in plans
        )


@lru_cache(maxsize=4)
def _load_cached(root_key: str) -> ArtifactIndex:
    root = Path(root_key)
    directory = require_dir(root / ARTIFACTS_DIR)
    rows: list[Artifact] = []
    for path in sorted(directory.glob("*.json")):
        stem = path.stem
        _, version = _strip_version(stem)
        try:
            document = json.loads(path.read_text(encoding="utf-8"))
            readable = True
        except json.JSONDecodeError:
            document = {}
            readable = False
        kind = document.get("kind") if isinstance(document, dict) else None
        rows.append(
            Artifact(
                path=path,
                name=path.name,
                stem=stem,
                version=version,
                shape=classify(stem),
                kind=kind if isinstance(kind, str) else None,
                kind_shape=classify(kind) if isinstance(kind, str) else OTHER,
                readable=readable,
                document=document if isinstance(document, dict) else {},
            )
        )
    return ArtifactIndex(root=root, directory=directory, artifacts=tuple(rows))


def load(root: Path | str | None = None, *, refresh: bool = False) -> ArtifactIndex:
    """Index ``artifacts/autogenesis/*.json``. Cached per root."""
    resolved = resolve_root(root)
    if refresh:
        _load_cached.cache_clear()
    return _load_cached(str(resolved))


def pairs(root: Path | str | None = None) -> tuple[Pair, ...]:
    return load(root).pairs()


def by_shape(root: Path | str | None = None) -> dict[str, tuple[Artifact, ...]]:
    return load(root).by_shape()


__all__ = [
    "ARTIFACTS_DIR",
    "OTHER",
    "SHAPES",
    "Artifact",
    "ArtifactIndex",
    "Pair",
    "by_shape",
    "classify",
    "load",
    "pairs",
]
