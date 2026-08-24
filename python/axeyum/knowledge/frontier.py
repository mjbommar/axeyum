"""The content-addressed fact frontier, as produced by ``scripts/fact-frontier.py``.

The frontier is what pins a dispatch decision: :attr:`Frontier.frontier_sha256`
is the digest of the whole artifact, and ``--verify`` re-derives it from the
ledger. This module runs the script and types its output; it never re-implements
the banding or selection policy, because a second implementation of a scheduler
that disagrees with the first is worse than no second implementation.

**``refused-no-admissible-candidate`` is a value, not a failure.** An empty
:attr:`Selection.admissible_fact_ids` with that outcome is the designed
behaviour of an autonomous dispatcher that will not act without a registered
operation and a supported route. Nothing here raises on it.
"""

from __future__ import annotations

import json
import tempfile
from dataclasses import dataclass, field
from functools import lru_cache
from pathlib import Path
from typing import Any

from ._paths import DEFAULT_TIMEOUT_S, ScriptRun, resolve_root, run_script

SCRIPT = "fact-frontier.py"

#: The dispatcher declined to select. A VALUE: no candidate cleared the policy.
REFUSED_NO_ADMISSIBLE_CANDIDATE = "refused-no-admissible-candidate"


class FrontierError(RuntimeError):
    """The frontier script failed, or its output was not the expected artifact."""


@dataclass(frozen=True, slots=True)
class FrontierEntry:
    """One open fact as the scheduler sees it."""

    fact_id: str
    band: str | None
    dependency_ready: bool | None
    epistemic_status: str | None
    external_status: str | None
    fact_sha256: str | None
    fragment: str | None
    gate_mentions: tuple[str, ...]
    missing_dependencies: tuple[str, ...]
    registered_operation_ids: tuple[str, ...]
    route_class: str | None
    stale_reviewed_gate_mentions: tuple[str, ...]
    unreviewed_gate_mentions: tuple[str, ...]
    would_unlock: tuple[str, ...]
    raw: dict[str, Any] = field(repr=False)

    @property
    def has_registered_operation(self) -> bool:
        return bool(self.registered_operation_ids)

    @classmethod
    def from_raw(cls, raw: dict[str, Any]) -> FrontierEntry:
        def seq(key: str) -> tuple[str, ...]:
            value = raw.get(key) or []
            return tuple(value) if isinstance(value, list) else ()

        return cls(
            fact_id=raw["fact_id"],
            band=raw.get("band"),
            dependency_ready=raw.get("dependency_ready"),
            epistemic_status=raw.get("epistemic_status"),
            external_status=raw.get("external_status"),
            fact_sha256=raw.get("fact_sha256"),
            fragment=raw.get("fragment"),
            gate_mentions=seq("gate_mentions"),
            missing_dependencies=seq("missing_dependencies"),
            registered_operation_ids=seq("registered_operation_ids"),
            route_class=raw.get("route_class"),
            stale_reviewed_gate_mentions=seq("stale_reviewed_gate_mentions"),
            unreviewed_gate_mentions=seq("unreviewed_gate_mentions"),
            would_unlock=seq("would_unlock"),
            raw=raw,
        )


@dataclass(frozen=True, slots=True)
class Rationale:
    """Why one ready fact was not admissible."""

    fact_id: str
    rejected_by: tuple[str, ...]


@dataclass(frozen=True, slots=True)
class Selection:
    """The dispatch decision. ``outcome`` is the whole answer; read it first."""

    outcome: str
    admissible_fact_ids: tuple[str, ...]
    ready_fact_ids: tuple[str, ...]
    selected_fact_id: str | None
    rationale: tuple[Rationale, ...]

    @property
    def refused(self) -> bool:
        """True when the dispatcher declined -- a value, never an error."""
        return self.outcome == REFUSED_NO_ADMISSIBLE_CANDIDATE

    def rejected_by(self, fact_id: str) -> tuple[str, ...]:
        """Reasons one ready fact was rejected.

        Raises:
            KeyError: when the fact carries no rationale row. Silence here would
                read as "nothing rejected it", which is the opposite claim.
        """
        for row in self.rationale:
            if row.fact_id == fact_id:
                return row.rejected_by
        raise KeyError(f"no selection rationale for {fact_id!r}")

    @classmethod
    def from_raw(cls, raw: dict[str, Any]) -> Selection:
        rationale = raw.get("rationale") or []
        return cls(
            outcome=raw["outcome"],
            admissible_fact_ids=tuple(raw.get("admissible_fact_ids") or ()),
            ready_fact_ids=tuple(raw.get("ready_fact_ids") or ()),
            selected_fact_id=raw.get("selected_fact_id"),
            rationale=tuple(
                Rationale(fact_id=row["fact_id"], rejected_by=tuple(row.get("rejected_by") or ()))
                for row in rationale
            ),
        )


@dataclass(frozen=True, slots=True)
class Capabilities:
    """What the stack can decide, and the fact that demonstrates each fragment."""

    decidable_fragments: tuple[str, ...]
    demonstrated_by: dict[str, str]

    def demonstration(self, fragment: str) -> str:
        """The fact id demonstrating ``fragment``.

        Raises:
            KeyError: when the fragment is declared decidable but no settled fact
                demonstrates it. Measured 2026-08-24: 9 of 19 fragments carry a
                demonstration, so this is a routine answer and not a defect --
                but it must be an answer a caller can see, never a silent
                ``None`` that reads as "demonstrated by nothing in particular".
        """
        return self.demonstrated_by[fragment]

    def undemonstrated(self) -> tuple[str, ...]:
        """Fragments declared decidable with no demonstrating fact."""
        return tuple(f for f in self.decidable_fragments if f not in self.demonstrated_by)


@dataclass(frozen=True, slots=True)
class VerifyResult:
    """The outcome of ``fact-frontier.py --verify``.

    ``ok`` is derived from the script's exit status, not from whether it printed
    something -- a checker whose verdict does not depend on what the run found
    cannot fail.
    """

    ok: bool
    returncode: int
    sha256: str | None
    stdout: str
    stderr: str


@dataclass(frozen=True, slots=True)
class Frontier:
    """The whole ``--json`` artifact, typed."""

    root: Path
    document: dict[str, Any] = field(repr=False)
    entries: tuple[FrontierEntry, ...] = ()
    selection: Selection | None = None
    capabilities: Capabilities | None = None
    frontier_sha256: str = ""
    ledger: dict[str, Any] = field(default_factory=dict)
    policy: dict[str, Any] = field(default_factory=dict, repr=False)
    authority: str = ""
    kind: str = ""
    schema_version: int = 0

    def __len__(self) -> int:
        return len(self.entries)

    def entry(self, fact_id: str) -> FrontierEntry:
        """One entry; :class:`KeyError` when the fact is not on the frontier."""
        for row in self.entries:
            if row.fact_id == fact_id:
                return row
        raise KeyError(f"{fact_id!r} is not on the frontier ({len(self.entries)} entries)")

    def by_band(self) -> dict[str, tuple[FrontierEntry, ...]]:
        grouped: dict[str, list[FrontierEntry]] = {}
        for row in self.entries:
            grouped.setdefault(row.band or "?", []).append(row)
        return {k: tuple(v) for k, v in sorted(grouped.items())}

    def dependency_ready(self) -> tuple[FrontierEntry, ...]:
        """Entries whose dependencies are all settled.

        Not the same set as any partition of the nursery, and not interchangeable
        with a count -- see :mod:`axeyum.knowledge.nursery`.
        """
        return tuple(row for row in self.entries if row.dependency_ready)

    def verify(
        self,
        path: Path | str | None = None,
        *,
        timeout_s: float = DEFAULT_TIMEOUT_S,
    ) -> VerifyResult:
        """Re-verify a saved frontier against the live ledger.

        With no ``path``, this frontier's own document is written to a temporary
        file and verified, which answers "is what I am holding still true of the
        ledger?".
        """
        if path is not None:
            return _verify_path(self.root, Path(path), timeout_s=timeout_s)
        with tempfile.TemporaryDirectory(prefix="axeyum-frontier-") as tmp:
            saved = Path(tmp) / "frontier.json"
            saved.write_text(
                json.dumps(self.document, indent=2, sort_keys=True) + "\n", encoding="utf-8"
            )
            return _verify_path(self.root, saved, timeout_s=timeout_s)

    @classmethod
    def from_document(cls, root: Path, document: dict[str, Any]) -> Frontier:
        if document.get("kind") != "axeyum-fact-frontier":
            raise FrontierError(f"not a fact frontier artifact: kind={document.get('kind')!r}")
        capabilities_raw = document.get("capabilities") or {}
        return cls(
            root=root,
            document=document,
            entries=tuple(FrontierEntry.from_raw(row) for row in document.get("entries", [])),
            selection=Selection.from_raw(document["selection"]),
            capabilities=Capabilities(
                decidable_fragments=tuple(capabilities_raw.get("decidable_fragments") or ()),
                demonstrated_by=dict(capabilities_raw.get("demonstrated_by") or {}),
            ),
            frontier_sha256=document.get("frontier_sha256", ""),
            ledger=dict(document.get("ledger") or {}),
            policy=dict(document.get("policy") or {}),
            authority=document.get("authority", ""),
            kind=document.get("kind", ""),
            schema_version=document.get("schema_version", 0),
        )


def _verify_path(root: Path, path: Path, *, timeout_s: float) -> VerifyResult:
    run: ScriptRun = run_script(root, SCRIPT, ["--verify", str(path)], timeout_s=timeout_s)
    sha: str | None = None
    for line in run.stdout.splitlines():
        if line.startswith("FACT_FRONTIER_OK|"):
            sha = line.split("|", 1)[1].strip()
    return VerifyResult(
        ok=run.returncode == 0,
        returncode=run.returncode,
        sha256=sha,
        stdout=run.stdout,
        stderr=run.stderr,
    )


@lru_cache(maxsize=4)
def _load_cached(root_key: str, timeout_s: float) -> Frontier:
    root = Path(root_key)
    run = run_script(root, SCRIPT, ["--json"], timeout_s=timeout_s)
    if run.returncode != 0:
        raise FrontierError(
            f"{SCRIPT} --json exited {run.returncode}: {run.stderr.strip() or run.stdout.strip()}"
        )
    try:
        document = json.loads(run.stdout)
    except json.JSONDecodeError as exc:  # pragma: no cover - a broken script, not a value
        raise FrontierError(f"{SCRIPT} --json did not emit JSON: {exc}") from exc
    return Frontier.from_document(root, document)


def load(
    root: Path | str | None = None,
    *,
    refresh: bool = False,
    timeout_s: float = DEFAULT_TIMEOUT_S,
) -> Frontier:
    """Run ``fact-frontier.py --json`` and type the result. Cached per root."""
    resolved = resolve_root(root)
    if refresh:
        _load_cached.cache_clear()
    return _load_cached(str(resolved), timeout_s)


def entries(root: Path | str | None = None) -> tuple[FrontierEntry, ...]:
    return load(root).entries


def selection(root: Path | str | None = None) -> Selection:
    frontier = load(root)
    assert frontier.selection is not None
    return frontier.selection


def capabilities(root: Path | str | None = None) -> Capabilities:
    frontier = load(root)
    assert frontier.capabilities is not None
    return frontier.capabilities


def frontier_sha256(root: Path | str | None = None) -> str:
    return load(root).frontier_sha256


def verify(
    path: Path | str | None = None,
    root: Path | str | None = None,
    *,
    timeout_s: float = DEFAULT_TIMEOUT_S,
) -> VerifyResult:
    """Verify a saved frontier (or the live one) against the ledger."""
    return load(root).verify(path, timeout_s=timeout_s)


__all__ = [
    "REFUSED_NO_ADMISSIBLE_CANDIDATE",
    "SCRIPT",
    "Capabilities",
    "Frontier",
    "FrontierEntry",
    "FrontierError",
    "Rationale",
    "Selection",
    "VerifyResult",
    "capabilities",
    "entries",
    "frontier_sha256",
    "load",
    "selection",
    "verify",
]
