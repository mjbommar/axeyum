"""``docs/plan/generated/*.md`` and the scripts that write them.

These are the dashboards the flywheel reads: the theorem production ledger, the
production provenance ledger, the proof-gap matrix, the Lean axiom ledger. None
of them is hand-written, and every one has a generator that supports ``--check``
so a stale dashboard reddens rather than drifts.

:attr:`GeneratedDoc.generator` is recovered from the file's own header, and it
is ``None`` when the header names none. That is a value, not an error, and it is
distinguishable from "not looked at" because :attr:`GeneratedDoc.header` records
exactly what was scanned.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from functools import lru_cache
from pathlib import Path

from ._paths import require_dir, resolve_root

GENERATED_DIR = Path("docs") / "plan" / "generated"

#: How many header lines are scanned for a generator reference. The attribution
#: sometimes wraps onto a second or third line ("regenerate with\n python3 ...").
HEADER_LINES = 30

_SCRIPT_RE = re.compile(r"scripts/[A-Za-z0-9_.\-]+\.py")
_ATTRIBUTION = ("generated", "regenerate", "generator")


@dataclass(frozen=True, slots=True)
class GeneratedDoc:
    """One generated Markdown dashboard."""

    path: Path
    name: str
    stem: str
    generator: str | None
    json_twin: Path | None
    header: str = field(repr=False, default="")

    @property
    def has_json_twin(self) -> bool:
        return self.json_twin is not None

    @property
    def title(self) -> str | None:
        """The document's first ``# `` heading, when it has one."""
        for line in self.header.splitlines():
            if line.startswith("# "):
                return line[2:].strip()
        return None


@dataclass(frozen=True, slots=True)
class GeneratedIndex:
    """Every dashboard under ``docs/plan/generated/``."""

    root: Path
    directory: Path
    docs: tuple[GeneratedDoc, ...]

    def __len__(self) -> int:
        return len(self.docs)

    def __iter__(self):
        return iter(self.docs)

    def get(self, name: str) -> GeneratedDoc:
        """One dashboard by name or stem; :class:`KeyError` when absent."""
        for doc in self.docs:
            if doc.name == name or doc.stem == name:
                return doc
        raise KeyError(f"no generated document {name!r} under {self.directory}")

    def with_generator(self) -> tuple[GeneratedDoc, ...]:
        return tuple(doc for doc in self.docs if doc.generator is not None)

    def without_generator(self) -> tuple[GeneratedDoc, ...]:
        """Dashboards whose header names no generator script. A value: the file
        was read and the header did not say."""
        return tuple(doc for doc in self.docs if doc.generator is None)

    def generators(self) -> frozenset[str]:
        return frozenset(doc.generator for doc in self.docs if doc.generator)

    def by_generator(self) -> dict[str, tuple[GeneratedDoc, ...]]:
        grouped: dict[str, list[GeneratedDoc]] = {}
        for doc in self.docs:
            grouped.setdefault(doc.generator or "<none>", []).append(doc)
        return {k: tuple(v) for k, v in sorted(grouped.items())}


def _find_generator(header: str) -> str | None:
    """Prefer a script named on an attribution line; fall back to any in the header."""
    for line in header.splitlines():
        if any(word in line.lower() for word in _ATTRIBUTION):
            match = _SCRIPT_RE.search(line)
            if match:
                return match.group(0)
    match = _SCRIPT_RE.search(header)
    return match.group(0) if match else None


@lru_cache(maxsize=4)
def _load_cached(root_key: str) -> GeneratedIndex:
    root = Path(root_key)
    directory = require_dir(root / GENERATED_DIR)
    docs: list[GeneratedDoc] = []
    for path in sorted(directory.glob("*.md")):
        header = "\n".join(path.read_text(encoding="utf-8").splitlines()[:HEADER_LINES])
        twin = path.with_suffix(".json")
        docs.append(
            GeneratedDoc(
                path=path,
                name=path.name,
                stem=path.stem,
                generator=_find_generator(header),
                json_twin=twin if twin.is_file() else None,
                header=header,
            )
        )
    return GeneratedIndex(root=root, directory=directory, docs=tuple(docs))


def load(root: Path | str | None = None, *, refresh: bool = False) -> GeneratedIndex:
    """Index the generated dashboards. Cached per root."""
    resolved = resolve_root(root)
    if refresh:
        _load_cached.cache_clear()
    return _load_cached(str(resolved))


def docs(root: Path | str | None = None) -> tuple[GeneratedDoc, ...]:
    return load(root).docs


def get(name: str, root: Path | str | None = None) -> GeneratedDoc:
    return load(root).get(name)


__all__ = [
    "GENERATED_DIR",
    "HEADER_LINES",
    "GeneratedDoc",
    "GeneratedIndex",
    "docs",
    "get",
    "load",
]
