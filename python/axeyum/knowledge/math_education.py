"""The pinned sibling knowledge graph at ``../math-education``.

The overlay pins this checkout to one commit. The canonical validator's rule is
mirrored exactly here and it has three states, none of which is an exception:

* **unavailable** -- the sibling is not checked out. External resolution is
  skipped; the checkout is optional and CI does not vendor it.
* **off-pin** -- present at a different commit. A *warning*: live resolution is
  skipped, but the files can still be read.
* **available** -- present at exactly the pinned commit, so endpoint resolution
  is live.

``PyYAML`` is not a dependency of this package (and ``scripts/`` is
standard-library-only by policy), so the front matter is parsed by the small
hand-written reader below. It covers the subset the graph actually uses --
plain/quoted scalars, flow sequences, folded and literal block scalars, and
nested block mappings and sequences -- and refuses to guess at anything else.

``encounters/`` **is not a directory**: an encounter is an inline front-matter
row inside its concept file, so :class:`Encounter` is only ever reached through
:attr:`MEConcept.encounters`.

Ownership: the sibling belongs to the project owner and Axeyum copies or adapts
selected metadata and never mutates it. Everything here is read-only.
"""

from __future__ import annotations

import re
import subprocess
from dataclasses import dataclass, field
from functools import lru_cache
from pathlib import Path
from typing import Any

from . import overlay as _overlay
from ._paths import require_dir, resolve_root

#: The three states. ``unavailable`` and ``off-pin`` are values, never errors.
AVAILABLE = "available"
OFF_PIN = "off-pin"
UNAVAILABLE = "unavailable"
STATUSES = (AVAILABLE, OFF_PIN, UNAVAILABLE)

DEFAULT_SOURCE_ID = "math-education"
DEFAULT_PATH_HINT = Path("..") / "math-education"

#: Bloom levels an encounter can sit at, in order.
ENCOUNTER_LEVELS = ("remember", "understand", "apply", "analyze", "evaluate", "create")


# --------------------------------------------------------------------------
# A minimal YAML front-matter reader
# --------------------------------------------------------------------------

_KEY_RE = re.compile(r"^([A-Za-z_][A-Za-z0-9_.\-]*):(?:\s+(.*))?$")
_BLOCK_RE = re.compile(r"^([|>])([+-]?)$")
_INT_RE = re.compile(r"^[+-]?\d+$")
_FLOAT_RE = re.compile(r"^[+-]?(?:\d+\.\d*|\.\d+)(?:[eE][+-]?\d+)?$")


class FrontMatterError(ValueError):
    """The front matter used a YAML construct this reader does not cover.

    Raised rather than guessed at: a silently wrong parse of a knowledge graph
    is worse than a refusal that names the line.
    """


def _indent_of(line: str) -> int:
    return len(line) - len(line.lstrip(" "))


def _is_blank(line: str) -> bool:
    stripped = line.strip()
    return not stripped or stripped.startswith("#")


def _unescape_double(text: str) -> str:
    out: list[str] = []
    i = 0
    while i < len(text):
        ch = text[i]
        if ch == "\\" and i + 1 < len(text):
            nxt = text[i + 1]
            mapping = {"n": "\n", "t": "\t", "r": "\r", '"': '"', "\\": "\\", "/": "/", "0": "\0"}
            if nxt in mapping:
                out.append(mapping[nxt])
                i += 2
                continue
            if nxt == "u" and i + 6 <= len(text):
                out.append(chr(int(text[i + 2 : i + 6], 16)))
                i += 6
                continue
        out.append(ch)
        i += 1
    return "".join(out)


def _strip_plain_comment(text: str) -> str:
    """Remove a trailing ``# comment`` from a plain scalar."""
    index = text.find(" #")
    return text[:index].rstrip() if index >= 0 else text


def _is_closed_quote(text: str) -> bool:
    """Whether a scalar that opens with a quote also closes it."""
    quote = text[0]
    if len(text) < 2 or not text.endswith(quote):
        return False
    if quote == "'":
        return (len(text) - len(text.rstrip("'"))) % 2 == 1
    trailing = len(text) - len(text.rstrip("\\"))
    return trailing % 2 == 0


def _plain_or_quoted(text: str) -> Any:
    """Interpret a folded multi-line scalar. Folded text is never a number."""
    stripped = text.strip()
    if stripped and stripped[0] in "\"'" and _is_closed_quote(stripped):
        return _scalar(stripped)
    return _strip_plain_comment(stripped)


def _scalar(text: str) -> Any:
    text = text.strip()
    if not text:
        return None
    if text[0] == "'" and text.endswith("'") and len(text) >= 2:
        return text[1:-1].replace("''", "'")
    if text[0] == '"' and text.endswith('"') and len(text) >= 2:
        return _unescape_double(text[1:-1])
    text = _strip_plain_comment(text)
    if text in {"null", "~", "Null", "NULL"}:
        return None
    if text in {"true", "True", "TRUE"}:
        return True
    if text in {"false", "False", "FALSE"}:
        return False
    if _INT_RE.match(text):
        return int(text)
    if _FLOAT_RE.match(text):
        return float(text)
    return text


def _split_flow(body: str) -> list[str]:
    """Split a flow sequence body on commas that are not inside quotes or brackets."""
    items: list[str] = []
    depth = 0
    quote: str | None = None
    current: list[str] = []
    for ch in body:
        if quote is not None:
            current.append(ch)
            if ch == quote:
                quote = None
            continue
        if ch in "\"'" and not "".join(current).strip():
            # Only an item-initial quote opens a quoted scalar: an apostrophe
            # inside a plain item ("Bezout's identity") must not swallow the
            # separating comma.
            quote = ch
            current.append(ch)
            continue
        if ch in "[{":
            depth += 1
        elif ch in "]}":
            depth -= 1
        if ch == "," and depth == 0:
            items.append("".join(current))
            current = []
            continue
        current.append(ch)
    tail = "".join(current).strip()
    if tail:
        items.append(tail)
    return [item.strip() for item in items if item.strip()]


def _flow(text: str) -> Any:
    text = text.strip()
    if text.startswith("[") and text.endswith("]"):
        return [
            _flow(item) if item[0] in "[{" else _scalar(item) for item in _split_flow(text[1:-1])
        ]
    if text.startswith("{") and text.endswith("}"):
        out: dict[str, Any] = {}
        for item in _split_flow(text[1:-1]):
            key, _, value = item.partition(":")
            out[key.strip()] = _scalar(value)
        return out
    return _scalar(text)


class _Reader:
    """Indentation-driven reader over the front-matter lines."""

    def __init__(self, lines: list[str], origin: str) -> None:
        self.lines = lines
        self.index = 0
        self.origin = origin

    def _skip_blank(self) -> None:
        while self.index < len(self.lines) and _is_blank(self.lines[self.index]):
            self.index += 1

    def _peek(self) -> tuple[int, str] | None:
        self._skip_blank()
        if self.index >= len(self.lines):
            return None
        line = self.lines[self.index]
        return _indent_of(line), line

    def parse_document(self) -> dict[str, Any]:
        peeked = self._peek()
        if peeked is None:
            return {}
        value = self.parse_mapping(peeked[0])
        remainder = self._peek()
        if remainder is not None:
            raise FrontMatterError(f"{self.origin}: unconsumed line {remainder[1]!r}")
        return value

    def parse_mapping(self, indent: int) -> dict[str, Any]:
        out: dict[str, Any] = {}
        while True:
            peeked = self._peek()
            if peeked is None:
                return out
            line_indent, line = peeked
            if line_indent < indent:
                return out
            if line_indent > indent:
                raise FrontMatterError(f"{self.origin}: unexpected indent at {line!r}")
            content = line.strip()
            match = _KEY_RE.match(content)
            if match is None:
                raise FrontMatterError(f"{self.origin}: not a mapping entry: {line!r}")
            key, rest = match.group(1), (match.group(2) or "").strip()
            self.index += 1
            out[key] = self.parse_value(indent, rest)

    def parse_value(self, indent: int, rest: str) -> Any:
        block = _BLOCK_RE.match(rest)
        if block:
            return self.parse_block_scalar(indent, block.group(1), block.group(2))
        if rest.startswith(("[", "{")):
            return _flow(self.consume_flow(rest))
        if rest:
            return self.parse_scalar_value(indent, rest)
        # No inline value: a nested block, or nothing at all.
        peeked = self._peek()
        if peeked is None:
            return None
        child_indent, child_line = peeked
        if child_indent > indent:
            if child_line.strip().startswith("- ") or child_line.strip() == "-":
                return self.parse_sequence(child_indent)
            return self.parse_mapping(child_indent)
        if child_indent == indent and (
            child_line.strip().startswith("- ") or child_line.strip() == "-"
        ):
            # A sequence may sit at the key's own indent.
            return self.parse_sequence(indent)
        return None

    def parse_scalar_value(self, indent: int, rest: str) -> Any:
        """Read a scalar, continuing onto more-indented lines when it wraps.

        Both plain and quoted scalars may span lines. A wrapped plain scalar
        folds its line breaks to spaces; a blank line inside one becomes a
        newline, matching YAML folding.
        """
        parts = [rest]
        if rest[0] in "\"'" and not _is_closed_quote(rest):
            while self.index < len(self.lines):
                line = self.lines[self.index]
                self.index += 1
                parts.append(line.strip())
                if _is_closed_quote(" ".join(parts)):
                    break
            return _scalar(" ".join(parts))
        while self.index < len(self.lines):
            line = self.lines[self.index]
            if not line.strip():
                nxt = self.index + 1
                while nxt < len(self.lines) and not self.lines[nxt].strip():
                    nxt += 1
                if nxt >= len(self.lines) or _indent_of(self.lines[nxt]) <= indent:
                    break
                if _KEY_RE.match(self.lines[nxt].strip()) or self.lines[nxt].strip().startswith(
                    "- "
                ):
                    break
                parts.append("\n")
                self.index = nxt
                continue
            if _indent_of(line) <= indent:
                break
            stripped = line.strip()
            if _KEY_RE.match(stripped) or stripped.startswith("- "):
                break
            parts.append(stripped)
            self.index += 1
        if len(parts) == 1:
            return _scalar(rest)
        folded = parts[0]
        for part in parts[1:]:
            if part == "\n":
                folded += "\n"
            elif folded.endswith("\n"):
                folded += part
            else:
                folded += " " + part
        return _scalar(folded) if len(parts) == 1 else _plain_or_quoted(folded)

    def consume_flow(self, rest: str) -> str:
        """Read a flow collection, continuing across lines until it balances."""
        text = rest
        while text.count("[") != text.count("]") or text.count("{") != text.count("}"):
            if self.index >= len(self.lines):
                raise FrontMatterError(f"{self.origin}: unterminated flow collection")
            text += " " + self.lines[self.index].strip()
            self.index += 1
        return text

    def parse_sequence(self, indent: int) -> list[Any]:
        out: list[Any] = []
        while True:
            peeked = self._peek()
            if peeked is None:
                return out
            line_indent, line = peeked
            if line_indent != indent:
                return out
            stripped = line.strip()
            if not (stripped.startswith("- ") or stripped == "-"):
                return out
            dash_column = line.index("-", indent)
            body = line[dash_column + 1 :]
            body_stripped = body.strip()
            if not body_stripped:
                self.index += 1
                nested = self._peek()
                if nested is None or nested[0] <= indent:
                    out.append(None)
                    continue
                nested_line = nested[1].strip()
                if nested_line.startswith("- ") or nested_line == "-":
                    out.append(self.parse_sequence(nested[0]))
                else:
                    out.append(self.parse_mapping(nested[0]))
                continue
            child_indent = dash_column + 1 + (len(body) - len(body.lstrip(" ")))
            if _KEY_RE.match(body_stripped):
                # An inline mapping entry: blank out the dash and re-read.
                self.lines[self.index] = " " * child_indent + body_stripped
                out.append(self.parse_mapping(child_indent))
                continue
            self.index += 1
            out.append(self.parse_value(child_indent, body_stripped))

    def parse_block_scalar(self, indent: int, style: str, chomp: str) -> str:
        raw: list[str] = []
        block_indent: int | None = None
        while self.index < len(self.lines):
            line = self.lines[self.index]
            if not line.strip():
                raw.append("")
                self.index += 1
                continue
            line_indent = _indent_of(line)
            if line_indent <= indent:
                break
            if block_indent is None:
                block_indent = line_indent
            raw.append(line[block_indent:])
            self.index += 1
        while raw and not raw[-1].strip():
            raw.pop()
        if style == "|":
            body = "\n".join(raw)
        else:
            folded: list[str] = []
            for line in raw:
                if not line.strip():
                    folded.append("\n")
                elif folded and folded[-1] != "\n" and not line.startswith(" "):
                    folded.append(" " + line)
                else:
                    folded.append(line)
            body = "".join(folded)
            body = body.replace("\n ", "\n")
        if chomp == "-":
            return body
        return body + "\n"


def parse_front_matter(text: str, origin: str = "<string>") -> dict[str, Any]:
    """Parse the YAML front matter of a Markdown document.

    Raises:
        FrontMatterError: when the document has no front matter, or uses a
            construct this reader does not cover.
    """
    if not text.startswith("---"):
        raise FrontMatterError(f"{origin}: no front matter (file does not start with ---)")
    lines = text.splitlines()
    end = None
    for i in range(1, len(lines)):
        if lines[i].rstrip() == "---":
            end = i
            break
    if end is None:
        raise FrontMatterError(f"{origin}: front matter is not terminated by ---")
    return _Reader(lines[1:end], origin).parse_document()


def split_front_matter(text: str, origin: str = "<string>") -> tuple[dict[str, Any], str]:
    """Return ``(front matter, body)``."""
    front = parse_front_matter(text, origin)
    lines = text.splitlines()
    end = next(i for i in range(1, len(lines)) if lines[i].rstrip() == "---")
    return front, "\n".join(lines[end + 1 :]).lstrip("\n")


# --------------------------------------------------------------------------
# Typed rows
# --------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class Objective:
    statement: str | None
    knowledge_dimension: str | None


@dataclass(frozen=True, slots=True)
class Requirement:
    """A prerequisite encounter, e.g. ``C:comparison@understand``."""

    encounter: str | None
    strength: str | None
    reason: str | None

    @property
    def concept_id(self) -> str | None:
        return self.encounter.split("@", 1)[0] if self.encounter else None

    @property
    def level(self) -> str | None:
        if self.encounter and "@" in self.encounter:
            return self.encounter.split("@", 1)[1]
        return None


@dataclass(frozen=True, slots=True)
class Encounter:
    """One inline encounter row. There is no ``encounters/`` directory."""

    level: str | None
    summary: str | None
    objectives: tuple[Objective, ...]
    requires: tuple[Requirement, ...]
    uses_technique: tuple[str, ...]
    raw: dict[str, Any] = field(repr=False, default_factory=dict)

    @classmethod
    def from_raw(cls, raw: Any) -> Encounter:
        if not isinstance(raw, dict):
            return cls(None, None, (), (), (), {})
        objectives = raw.get("objectives") or []
        requires = raw.get("requires") or []
        techniques = raw.get("uses_technique") or []
        return cls(
            level=raw.get("level"),
            summary=raw.get("summary"),
            objectives=tuple(
                Objective(
                    statement=row.get("statement") if isinstance(row, dict) else None,
                    knowledge_dimension=row.get("knowledge_dimension")
                    if isinstance(row, dict)
                    else None,
                )
                for row in objectives
            ),
            requires=tuple(
                Requirement(
                    encounter=row.get("encounter") if isinstance(row, dict) else row,
                    strength=row.get("strength") if isinstance(row, dict) else None,
                    reason=row.get("reason") if isinstance(row, dict) else None,
                )
                for row in requires
            ),
            uses_technique=tuple(techniques) if isinstance(techniques, list) else (),
            raw=raw,
        )


@dataclass(frozen=True, slots=True)
class MEConcept:
    """A ``C:<slug>`` node."""

    id: str
    path: Path
    title: str | None
    pref_label: str | None
    alt_labels: tuple[str, ...]
    short_definition: str | None
    definition: str | None
    epistemic_status: str | None
    status: str | None
    confidence: str | None
    strand: str | None
    created: Any
    updated: Any
    related: tuple[str, ...]
    bridges_to: tuple[dict[str, Any], ...]
    encounters: tuple[Encounter, ...]
    front_matter: dict[str, Any] = field(repr=False, default_factory=dict)

    @property
    def slug(self) -> str:
        return self.id.split(":", 1)[1] if ":" in self.id else self.id

    def encounter(self, level: str) -> Encounter:
        """One encounter by Bloom level; :class:`KeyError` when the concept has
        none at that level."""
        for row in self.encounters:
            if row.level == level:
                return row
        raise KeyError(
            f"{self.id} has no {level!r} encounter (has {[e.level for e in self.encounters]})"
        )


@dataclass(frozen=True, slots=True)
class METechnique:
    """A ``TQ:<slug>`` node."""

    id: str
    path: Path
    title: str | None
    pref_label: str | None
    short_definition: str | None
    definition: str | None
    epistemic_status: str | None
    status: str | None
    confidence: str | None
    refrain: str | None
    related: tuple[str, ...]
    created: Any
    updated: Any
    front_matter: dict[str, Any] = field(repr=False, default_factory=dict)

    @property
    def slug(self) -> str:
        return self.id.split(":", 1)[1] if ":" in self.id else self.id


# --------------------------------------------------------------------------
# The graph
# --------------------------------------------------------------------------


def git_head(path: Path) -> str | None:
    """``git -C <path> rev-parse HEAD``, or ``None`` when that cannot be answered.

    Mirrors the validator: an absent checkout, an absent git, or a non-repository
    are all "cannot resolve", never an exception.
    """
    try:
        # Fixed argv, no shell.
        completed = subprocess.run(
            ["git", "-C", str(path), "rev-parse", "HEAD"],
            capture_output=True,
            text=True,
            timeout=30,
            check=False,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    if completed.returncode != 0:
        return None
    return completed.stdout.strip() or None


@dataclass(frozen=True, slots=True)
class MathEducationGraph:
    """The sibling graph, in whatever state it is actually in."""

    path: Path
    pinned_revision: str | None
    revision: str | None

    @property
    def status(self) -> str:
        """``available`` | ``off-pin`` | ``unavailable``. Never raises."""
        if not (self.path / "graph").is_dir():
            return UNAVAILABLE
        if self.revision is None or self.pinned_revision is None:
            return UNAVAILABLE
        return AVAILABLE if self.revision == self.pinned_revision else OFF_PIN

    def pin_ok(self) -> bool:
        """True only when the checkout is present at exactly the pinned commit."""
        return self.status == AVAILABLE

    @property
    def is_present(self) -> bool:
        return (self.path / "graph").is_dir()

    # -- readers ---------------------------------------------------------------

    def concepts(self) -> tuple[MEConcept, ...]:
        """Every ``graph/concepts/*.md`` node.

        Raises:
            FileNotFoundError: when the directory is absent. Being off-pin is not
                a reason to refuse -- the files are still readable and the
                validator's own response to off-pin is a warning.
        """
        directory = require_dir(self.path / "graph" / "concepts")
        return tuple(_read_concept(path) for path in sorted(directory.glob("*.md")))

    def techniques(self) -> tuple[METechnique, ...]:
        """Every ``graph/techniques/*.md`` node."""
        directory = require_dir(self.path / "graph" / "techniques")
        return tuple(_read_technique(path) for path in sorted(directory.glob("*.md")))

    def get(self, node_id: str) -> MEConcept | METechnique:
        """Resolve ``C:<slug>[@level]`` or ``TQ:<slug>`` to its node.

        Raises:
            KeyError: when the id is unknown or malformed.
            FileNotFoundError: when the graph directory is absent.
        """
        base = node_id.split("@", 1)[0]
        if base.startswith("C:"):
            path = self.path / "graph" / "concepts" / f"{base[2:]}.md"
            if not path.is_file():
                raise KeyError(f"no concept {node_id!r} at {path}")
            return _read_concept(path)
        if base.startswith("TQ:"):
            path = self.path / "graph" / "techniques" / f"{base[3:]}.md"
            if not path.is_file():
                raise KeyError(f"no technique {node_id!r} at {path}")
            return _read_technique(path)
        raise KeyError(f"{node_id!r} is neither a C: concept nor a TQ: technique id")

    def resolves(self, node_id: str) -> bool:
        """Whether an overlay endpoint resolves to a file, without raising."""
        try:
            self.get(node_id)
        except (KeyError, FileNotFoundError):
            return False
        return True


def _read_concept(path: Path) -> MEConcept:
    front = parse_front_matter(path.read_text(encoding="utf-8"), str(path))
    encounters = front.get("encounters") or []
    related = front.get("related") or []
    bridges = front.get("bridges_to") or []
    alt = front.get("alt_labels") or []
    return MEConcept(
        id=front.get("id", f"C:{path.stem}"),
        path=path,
        title=front.get("title"),
        pref_label=front.get("pref_label"),
        alt_labels=tuple(alt) if isinstance(alt, list) else (),
        short_definition=front.get("short_definition"),
        definition=front.get("definition"),
        epistemic_status=front.get("epistemic_status"),
        status=front.get("status"),
        confidence=front.get("confidence"),
        strand=front.get("strand"),
        created=front.get("created"),
        updated=front.get("updated"),
        related=tuple(related) if isinstance(related, list) else (),
        bridges_to=tuple(row for row in bridges if isinstance(row, dict)),
        encounters=tuple(Encounter.from_raw(row) for row in encounters),
        front_matter=front,
    )


def _read_technique(path: Path) -> METechnique:
    front = parse_front_matter(path.read_text(encoding="utf-8"), str(path))
    related = front.get("related") or []
    return METechnique(
        id=front.get("id", f"TQ:{path.stem}"),
        path=path,
        title=front.get("title"),
        pref_label=front.get("pref_label"),
        short_definition=front.get("short_definition"),
        definition=front.get("definition"),
        epistemic_status=front.get("epistemic_status"),
        status=front.get("status"),
        confidence=front.get("confidence"),
        refrain=front.get("refrain"),
        related=tuple(related) if isinstance(related, list) else (),
        created=front.get("created"),
        updated=front.get("updated"),
        front_matter=front,
    )


@lru_cache(maxsize=4)
def _graph_cached(root_key: str) -> MathEducationGraph:
    root = Path(root_key)
    pinned: str | None = None
    path_hint: str | None = None
    try:
        document = _overlay.load(root)
        source = document.source(DEFAULT_SOURCE_ID)
        pinned = source.revision
        path_hint = source.path_hint
    except (FileNotFoundError, KeyError):
        pinned = None
    sibling = (root / path_hint).resolve() if path_hint else (root / DEFAULT_PATH_HINT).resolve()
    return MathEducationGraph(path=sibling, pinned_revision=pinned, revision=git_head(sibling))


def graph(root: Path | str | None = None, *, refresh: bool = False) -> MathEducationGraph:
    """The sibling graph as this checkout sees it. Never raises for absent/off-pin."""
    resolved = resolve_root(root)
    if refresh:
        _graph_cached.cache_clear()
    return _graph_cached(str(resolved))


def status(root: Path | str | None = None) -> str:
    """``available`` | ``off-pin`` | ``unavailable``."""
    return graph(root).status


def pin_ok(root: Path | str | None = None) -> bool:
    """``git rev-parse HEAD`` in the sibling equals the overlay's pin."""
    return graph(root).pin_ok()


def concepts(root: Path | str | None = None) -> tuple[MEConcept, ...]:
    return graph(root).concepts()


def techniques(root: Path | str | None = None) -> tuple[METechnique, ...]:
    return graph(root).techniques()


def get(node_id: str, root: Path | str | None = None) -> MEConcept | METechnique:
    return graph(root).get(node_id)


__all__ = [
    "AVAILABLE",
    "ENCOUNTER_LEVELS",
    "OFF_PIN",
    "STATUSES",
    "UNAVAILABLE",
    "Encounter",
    "FrontMatterError",
    "MEConcept",
    "METechnique",
    "MathEducationGraph",
    "Objective",
    "Requirement",
    "concepts",
    "get",
    "git_head",
    "graph",
    "parse_front_matter",
    "pin_ok",
    "split_front_matter",
    "status",
    "techniques",
]
