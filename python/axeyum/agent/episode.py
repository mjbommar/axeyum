"""Writing the episode artifact: the only thing this loop is allowed to produce.

`artifacts/ontology/agent-episode.schema.json` defines the document and
`scripts/check-agent-episode.py` -- standard library only, run from gates that
never import this package -- decides whether one is admissible. This module's
job is to build a document that survives that checker *because it is true*, not
because it was shaped to pass.

Three rules are enforced here rather than left to the checker, on the principle
that a producer which cannot emit a bad artifact is worth more than a checker
which rejects one:

* **`tool_calls` is projected from the serialized message list.** The digests
  come from the same objects `messages_sha256` covers, so the transcript and its
  projection cannot silently disagree. Only duration and exit status come from
  the harness's own log, because the message list does not carry them -- and a
  tool name absent from `TOOL_TIERS` raises instead of defaulting to `read`.
* **Nothing is written until it has been walked for held-out ids.** The checker
  walks the episode document; this walks the transcript and every proposal
  *before* they reach disk, because a blind id in a file the checker does not
  read is still a spent population.
* **`verdict` is restricted to what this slice can honestly claim.** A2
  dispatches nothing, so `proved` and `error` are not constructible here: the
  admissible verdicts are `declined` and `budget-exhausted`. `proved` requires a
  `checked` tool call, and the C tier does not exist yet.

The frontier snapshot is deliberately NOT walked for held-out ids. It is a
census of the whole open ledger -- the same category as `nursery-v1.json`
itself, which the isolation gate exempts as a population file -- and
`fact-frontier.py --verify` re-derives it entry for entry, so a filtered copy
would fail the very rule that makes it evidence.
"""

from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from collections.abc import Iterable
from dataclasses import dataclass
from datetime import UTC, datetime
from pathlib import Path
from typing import Any, Literal

from pydantic import BaseModel
from pydantic_ai import ModelMessagesTypeAdapter

from ..knowledge import facts as facts_api
from ..knowledge import frontier as frontier_api
from ..knowledge import nursery as nursery_api
from ..knowledge._paths import resolve_root
from .models import (
    DECLINE_CLASSES,
    ELIGIBLE_PARTITIONS,
    NoGeneralRoute,
    StrategyProposal,
    proposal_kind,
)
from .tools import TOOL_TIERS, ToolCallRecord, is_output_tool, toolset_sha256

SCHEMA_VERSION = 1
SCHEMA_VERSION_V2 = 2
KIND = "axeyum-agent-episode"

#: The verdicts this writer may produce, widened by slice A4 to include
#: `proved`.
#:
#: The widening is CONDITIONAL and the condition is checked here, at write time,
#: not left to the gate: `proved` requires at least one `checked` tool call and
#: at least one checker run that exited 0 (rule 11). A writer that could emit
#: `proved` on a run that dispatched nothing would be the "checker that cannot
#: fail" defect moved one step upstream -- into the thing the checker reads.
#:
#: `error` is still absent. A run that failed is raised, not recorded, so a
#: crash cannot be mistaken for a finding.
A2_VERDICTS = ("declined", "budget-exhausted", "proved")

#: What a schema v1 document may say. Unchanged, deliberately: a v1 episode has
#: no `checker_runs`, so rule 11 has nothing to stand on there and `proved`
#: would be a claim the document cannot support.
V1_VERDICTS = ("declined", "budget-exhausted")

#: Sidecars are named `*.json.snapshot`, NOT `*.json`, and the reason is
#: mechanical: `check-agent-episode.py` walks a directory argument with
#: `rglob("*.json")` and checks EVERY match as an episode. A frontier or a
#: transcript committed as `frontier.json` beside its episode would be read as a
#: malformed episode and redden the gate. Only episode documents carry a bare
#: `.json` extension under `artifacts/episodes/`.
SNAPSHOT_SUFFIX = ".json.snapshot"


class EpisodeWriteError(RuntimeError):
    """The episode cannot be written truthfully. Never downgraded to a warning."""


class HeldOutLeak(EpisodeWriteError):
    """A blind fact id reached bytes that were about to be committed."""


def repo_relative(path: Path, root: Path) -> str:
    """A root-relative path where possible, an absolute one where not.

    `check-agent-episode.py` resolves a relative path against the checkout and
    an absolute one as given, so both are checkable. What is NOT acceptable is
    raising: a scratch directory outside the tree is exactly where a test or a
    replay writes, and an episode writer that only works in one directory is a
    writer nothing can exercise.
    """
    try:
        return str(path.relative_to(root))
    except ValueError:
        return str(path.resolve())


def canonical(document: Any) -> str:
    """Canonical JSON: sorted keys, two-space indent, ASCII, one trailing newline."""
    return json.dumps(document, sort_keys=True, indent=2, ensure_ascii=True) + "\n"


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def now_utc() -> str:
    return datetime.now(UTC).strftime("%Y-%m-%dT%H:%M:%SZ")


def assert_no_held_out(payload: bytes | str, where: str, root: Path) -> None:
    """Refuse to write bytes containing a held-out fact id.

    The message names the FILE and the COUNT, never the id: repeating it would
    put the blind id into a log, a traceback and probably a bug report, which is
    the breach the guard exists to prevent.
    """
    text = payload.decode("utf-8", "replace") if isinstance(payload, bytes) else payload
    held = nursery_api.load(root).held_out_ids()
    hits = sum(1 for fact_id in held if fact_id in text)
    if hits:
        raise HeldOutLeak(
            f"{where}: {hits} held-out fact id(s) appear in bytes about to be written; "
            f"refusing. The population is a shared resource with no owner"
        )


def agent_code_sha256() -> str:
    """Digest of this package's own source, so a replay knows which agent ran.

    Built from ``(relative name, file digest)`` pairs rather than concatenated
    bytes: renaming a module changes the digest, which is the point.
    """
    here = Path(__file__).resolve().parent
    rows = {path.name: sha256_bytes(path.read_bytes()) for path in sorted(here.glob("*.py"))}
    if not rows:
        raise EpisodeWriteError(f"no agent source found under {here}; the digest would be vacuous")
    return sha256_text(json.dumps(rows, sort_keys=True))


def library_versions() -> dict[str, str]:
    """Exact versions of everything whose behaviour a replay depends on."""
    from importlib.metadata import PackageNotFoundError, version

    out = {"python": ".".join(str(p) for p in sys.version_info[:3])}
    for name in ("axeyum", "pydantic-ai-slim", "pydantic-graph", "pydantic", "anthropic", "httpx2"):
        try:
            out[name] = version(name)
        except PackageNotFoundError:
            continue
    return out


def git_commit(root: Path, override: str | None = None) -> str:
    """The commit the episode was produced against.

    A lane snapshot from ``git archive`` has no ``.git``, so an override is a
    first-class input rather than a fallback. What is NOT allowed is inventing
    one: without either, this raises, because a wrong ``git_commit`` makes the
    ancestor rule pass on the wrong history.
    """
    if override:
        if len(override) != 40 or any(c not in "0123456789abcdef" for c in override):
            raise EpisodeWriteError(f"git commit override is not a 40-hex sha: {override!r}")
        return override
    try:
        done = subprocess.run(
            ["git", "-C", str(root), "rev-parse", "HEAD"],
            capture_output=True,
            text=True,
            timeout=30,
            check=False,
        )
    except (OSError, subprocess.SubprocessError) as error:
        raise EpisodeWriteError(f"cannot resolve HEAD in {root}: {error}") from error
    sha = done.stdout.strip()
    if done.returncode != 0 or len(sha) != 40:
        raise EpisodeWriteError(
            f"cannot resolve HEAD in {root} (exit {done.returncode}); pass an explicit commit"
        )
    return sha


# ------------------------------------------------------------- the projection


def _part_kind(part: Any) -> str:
    return str(getattr(part, "part_kind", ""))


def _args_json(part: Any) -> str:
    """The tool arguments, as canonical JSON, whatever shape the model sent."""
    args = getattr(part, "args", None)
    if isinstance(args, str):
        try:
            return canonical(json.loads(args))
        except json.JSONDecodeError:
            return args
    return canonical(args if args is not None else {})


def _return_text(part: Any) -> str:
    content = getattr(part, "content", None)
    if isinstance(content, BaseModel):
        return canonical(content.model_dump(mode="json"))
    if isinstance(content, str):
        return content
    try:
        return canonical(content)
    except TypeError:
        return repr(content)


def project_tool_calls(
    messages: Iterable[Any],
    records: Iterable[ToolCallRecord],
) -> list[dict[str, Any]]:
    """`transcript.tool_calls`, derived from the message list the digest covers.

    Raises:
        EpisodeWriteError: on a tool name that is neither in ``TOOL_TIERS`` nor
            recognized by :func:`axeyum.agent.tools.is_output_tool`. Defaulting
            an unknown tool to ``read`` is how a tool with side effects gets
            recorded as harmless.
    """
    messages = list(messages)
    by_id: dict[str, ToolCallRecord] = {}
    positional: list[ToolCallRecord] = []
    for record in records:
        positional.append(record)
        if record.tool_call_id:
            by_id[record.tool_call_id] = record

    returns: dict[str, tuple[str, bool]] = {}
    for message in messages:
        for part in getattr(message, "parts", ()):
            kind = _part_kind(part)
            call_id = getattr(part, "tool_call_id", None)
            if not call_id:
                continue
            if kind == "tool-return":
                returns[call_id] = (_return_text(part), False)
            elif kind == "retry-prompt":
                returns[call_id] = (str(getattr(part, "content", "")), True)

    out: list[dict[str, Any]] = []
    seen = 0
    for message in messages:
        for part in getattr(message, "parts", ()):
            if _part_kind(part) != "tool-call":
                continue
            name = str(getattr(part, "tool_name", ""))
            if is_output_tool(name):
                continue
            if name not in TOOL_TIERS:
                raise EpisodeWriteError(
                    f"tool {name!r} has no declared assurance tier; refusing to record it. "
                    f"Add it to TOOL_TIERS with the tier it actually is"
                )
            call_id = getattr(part, "tool_call_id", None)
            record = by_id.get(call_id) if call_id else None
            if record is None and seen < len(positional):
                record = positional[seen]
            result_text, retried = returns.get(call_id, ("", True)) if call_id else ("", True)
            out.append(
                {
                    "ordinal": len(out),
                    "tool": name,
                    "args_sha256": sha256_text(_args_json(part)),
                    "result_sha256": sha256_text(result_text),
                    "assurance": TOOL_TIERS[name],
                    "duration_ms": record.duration_ms if record else 0,
                    "exit_status": (record.exit_status if record else (1 if retried else 0)),
                }
            )
            seen += 1
    return out


# ------------------------------------------------------------------ the writer


@dataclass(frozen=True)
class Budgets:
    """The limits the run was given. Recorded whether or not they were reached."""

    wall_seconds: int
    request_limit: int
    tool_calls_limit: int
    input_tokens_limit: int
    output_tokens_limit: int
    cost_limit_usd: float

    def as_document(self) -> dict[str, Any]:
        return {
            "wall_seconds": int(self.wall_seconds),
            "request_limit": int(self.request_limit),
            "tool_calls_limit": int(self.tool_calls_limit),
            "input_tokens_limit": int(self.input_tokens_limit),
            "output_tokens_limit": int(self.output_tokens_limit),
            "cost_limit_usd": float(self.cost_limit_usd),
        }


def episode_id_for(fact_id: str, prefix: str = "a2") -> str:
    """`E:<prefix>-<fact slug>` -- stable, so a re-run overwrites its own episode."""
    slug = fact_id.split(":", 1)[1] if ":" in fact_id else fact_id
    return f"E:{prefix}-{slug}"


def save_frontier(frontier: frontier_api.Frontier, directory: Path) -> tuple[Path, str]:
    """Commit the frontier the selection was made from, beside the episodes.

    Returns the path and the digest the artifact carries for itself. That digest
    is what `check-agent-episode.py` compares against `selection.frontier_sha256`,
    and `fact-frontier.py --verify` re-derives it from the live ledger -- so a
    stale snapshot is a failure, not a warning.
    """
    directory.mkdir(parents=True, exist_ok=True)
    path = directory / f"frontier{SNAPSHOT_SUFFIX}"
    path.write_text(canonical(frontier.document), encoding="utf-8")
    return path, frontier.frontier_sha256


def eligibility_reason(
    entry: frontier_api.FrontierEntry,
    partition: str,
    ledger_sha256: str,
) -> str:
    """Why this fact was admissible, in a form a referee can check line by line.

    The ledger digest is carried here because schema v1's `selection` block is
    `additionalProperties: false` and has no `ledger_sha256` field. It is not
    decoration: `fact-frontier.py --verify` recomputes the frontier from the live
    ledger, so an episode read a year from now needs to know which ledger it was
    selected from. Schema v2 (slice A4) gives it a field of its own.
    """
    return (
        f"{partition} partition, epistemic_status {entry.epistemic_status}, dependency-ready "
        f"with no unmet depends_on; fragment {entry.fragment} is {entry.route_class}; "
        f"{len(entry.registered_operation_ids)} registered operation(s); "
        f"selected from ledger sha256 {ledger_sha256}"
    )


def write_proposals(
    proposals: Iterable[StrategyProposal | NoGeneralRoute],
    directory: Path,
    root: Path,
) -> list[dict[str, Any]]:
    """Write each proposal to its own file and return the `proposals[]` rows."""
    rows: list[dict[str, Any]] = []
    proposals = list(proposals)
    if proposals:
        directory.mkdir(parents=True, exist_ok=True)
    for index, proposal in enumerate(proposals):
        if proposal.assurance != "proposed":  # pragma: no cover - Literal makes this unreachable
            raise EpisodeWriteError("a proposal carrying anything but assurance='proposed'")
        text = canonical(proposal.model_dump(mode="json"))
        assert_no_held_out(text, f"proposal {index}", root)
        path = directory / f"proposal-{index}{SNAPSHOT_SUFFIX}"
        path.write_text(text, encoding="utf-8")
        rows.append(
            {
                "path": repo_relative(path, root),
                "sha256": sha256_text(text),
                "kind": proposal_kind(proposal),
                "assurance": "proposed",
            }
        )
    return rows


def write_transcript(messages: list[Any], directory: Path, root: Path) -> tuple[str, str]:
    """Serialize the message list and return `(relative path, digest)`."""
    directory.mkdir(parents=True, exist_ok=True)
    payload = ModelMessagesTypeAdapter.dump_json(messages, indent=2)
    assert_no_held_out(payload, "transcript", root)
    path = directory / f"messages{SNAPSHOT_SUFFIX}"
    path.write_bytes(payload)
    return repo_relative(path, root), sha256_bytes(payload)


def build_episode(
    *,
    root: Path,
    commit: str,
    fact_id: str,
    frontier: frontier_api.Frontier,
    frontier_path: Path,
    partition: str,
    model_id: str,
    settings: dict[str, Any],
    prompt_hashes: dict[str, str],
    budgets: Budgets,
    messages_path: str,
    messages_sha256: str,
    tool_calls: list[dict[str, Any]],
    proposal_rows: list[dict[str, Any]],
    verdict: str,
    decline_class: str | None,
    created_at: str | None = None,
) -> dict[str, Any]:
    """Assemble the document. Every refusal here is a refusal to lie in a file."""
    if verdict not in V1_VERDICTS:
        raise EpisodeWriteError(
            f"verdict {verdict!r} is not writable into a schema v1 document (which "
            f"dispatches nothing and has no checker_runs to support rule 11); "
            f"admissible: {list(V1_VERDICTS)}. Use build_episode_v2"
        )
    if partition not in ELIGIBLE_PARTITIONS:
        raise EpisodeWriteError(
            f"partition {partition!r} is not recordable; the schema admits "
            f"{list(ELIGIBLE_PARTITIONS)} and nothing else"
        )
    if not tool_calls:
        raise EpisodeWriteError(
            "transcript.tool_calls is empty; a run that called nothing is not a clean decline"
        )
    entry = frontier.entry(fact_id)
    fact_sha256 = entry.fact_sha256
    if not fact_sha256:
        raise EpisodeWriteError(f"the frontier carries no fact_sha256 for {fact_id}")
    ledger_sha256 = str(frontier.ledger.get("ledger_sha256", ""))
    if not ledger_sha256:
        raise EpisodeWriteError("the frontier carries no ledger digest; selection is unpinnable")
    return {
        "schema_version": SCHEMA_VERSION,
        "kind": KIND,
        "episode_id": episode_id_for(fact_id),
        "git_commit": commit,
        "created_at": created_at or now_utc(),
        "selection": {
            "frontier_sha256": frontier.frontier_sha256,
            "frontier_path": repo_relative(frontier_path, root),
            "fact_id": fact_id,
            "fact_sha256": fact_sha256,
            "partition": partition,
            "eligibility_reason": eligibility_reason(entry, partition, ledger_sha256),
        },
        "policy": {
            "model_id": model_id,
            "settings": settings,
            "prompt_hashes": prompt_hashes,
            "toolset_sha256": toolset_sha256(),
            "agent_code_sha256": agent_code_sha256(),
            "library_versions": library_versions(),
        },
        "budgets": budgets.as_document(),
        "transcript": {
            "messages_sha256": messages_sha256,
            "messages_path": messages_path,
            "tool_calls": tool_calls,
        },
        "web_snapshots": [],
        "proposals": proposal_rows,
        "outcome": {
            "verdict": verdict,
            "decline_class": decline_class,
            # Empty on purpose: A2 shells out to no checker, and naming one that
            # did not run would be the "checker that cannot fail" defect written
            # into the evidence itself. The schema puts no minLength here for
            # exactly this case; `proved` is what requires a command.
            "checker_command": "",
            "checker_exit_status": 0,
            "checker_output_sha256": None,
            "axiom_footprint": [],
            "ledger_writes": 0,
            "search_invocations": 0,
            "target_theorem_submissions": 0,
        },
        "observed": {
            "facts_unlocked": [],
            "operations_widened": [],
            "overlay_links_proposed": [],
        },
    }


def proved_is_supported(
    tool_calls: list[dict[str, Any]],
    checker_runs: list[dict[str, Any]],
) -> tuple[bool, str]:
    """Whether this run may be recorded as `proved`, and why not when it may not.

    Rule 11, stated once and enforced twice: here, so a document claiming
    `proved` without support cannot be BUILT, and again in
    `scripts/check-agent-episode.py`, so one that was built elsewhere cannot be
    ADMITTED. The two are deliberately not the same code -- the gate is stdlib
    only and never imports this package -- and a test cross-checks that they
    agree.

    Both halves are required and neither implies the other. A `checked` tool
    call without a passing checker is a producer nobody re-validated; a passing
    checker without a `checked` call is a checker that ran against nothing this
    episode did.
    """
    checked = [c for c in tool_calls if c.get("assurance") == "checked"]
    passed = [r for r in checker_runs if r.get("exit_status") == 0]
    if not checked:
        return (
            False,
            "no tool call carries assurance='checked'; the C tier is the only route to proved",
        )
    if not passed:
        return (False, "no checker run exited 0; a proof nobody re-validated is not proved")
    return (True, "")


def build_episode_v2(
    *,
    root: Path,
    commit: str,
    fact_id: str,
    frontier: frontier_api.Frontier,
    frontier_path: Path,
    partition: str,
    model_id: str,
    settings: dict[str, Any],
    prompt_hashes: dict[str, str],
    budgets: Budgets,
    messages_path: str,
    messages_sha256: str,
    tool_calls: list[dict[str, Any]],
    proposal_rows: list[dict[str, Any]],
    verdict: str,
    decline_class: str | None,
    checker_runs: list[dict[str, Any]] | None = None,
    axiom_footprint: list[str] | None = None,
    observed: dict[str, Any] | None = None,
    created_at: str | None = None,
) -> dict[str, Any]:
    """Assemble a schema v2 document. Every refusal here is a refusal to lie in a file.

    The v1 singular checker fields are filled from the FIRST recorded run, which
    is by construction the independent kernel re-check, so every v1 rule still
    bites on a v2 document instead of being skipped by the version dispatch.
    """
    checker_runs = list(checker_runs or [])
    if verdict not in A2_VERDICTS:
        raise EpisodeWriteError(
            f"verdict {verdict!r} is not writable; admissible: {list(A2_VERDICTS)}"
        )
    if verdict == "proved":
        supported, why = proved_is_supported(tool_calls, checker_runs)
        if not supported:
            raise EpisodeWriteError(f"refusing to record verdict 'proved': {why}")
    if decline_class is not None and decline_class not in DECLINE_CLASSES:
        raise EpisodeWriteError(
            f"decline_class {decline_class!r} is not in the v2 taxonomy; the enum is "
            f"seeded from AG4.1 and a free string is a taxonomy nobody can aggregate"
        )
    if partition not in ELIGIBLE_PARTITIONS:
        raise EpisodeWriteError(
            f"partition {partition!r} is not recordable; the schema admits "
            f"{list(ELIGIBLE_PARTITIONS)} and nothing else"
        )
    if not tool_calls:
        raise EpisodeWriteError(
            "transcript.tool_calls is empty; a run that called nothing is not a clean decline"
        )
    entry = frontier.entry(fact_id)
    fact_sha256 = entry.fact_sha256
    if not fact_sha256:
        raise EpisodeWriteError(f"the frontier carries no fact_sha256 for {fact_id}")
    ledger_sha256 = str(frontier.ledger.get("ledger_sha256", ""))
    if not ledger_sha256:
        raise EpisodeWriteError("the frontier carries no ledger digest; selection is unpinnable")
    primary = checker_runs[0] if checker_runs else None
    return {
        "schema_version": SCHEMA_VERSION_V2,
        "kind": KIND,
        "episode_id": episode_id_for(fact_id, "a4"),
        "git_commit": commit,
        "created_at": created_at or now_utc(),
        "selection": {
            "frontier_sha256": frontier.frontier_sha256,
            "frontier_path": repo_relative(frontier_path, root),
            "ledger_sha256": ledger_sha256,
            "fact_id": fact_id,
            "fact_sha256": fact_sha256,
            "partition": partition,
            "eligibility_reason": eligibility_reason(entry, partition, ledger_sha256),
        },
        "policy": {
            "model_id": model_id,
            "settings": settings,
            "prompt_hashes": prompt_hashes,
            "toolset_sha256": toolset_sha256(),
            "agent_code_sha256": agent_code_sha256(),
            "library_versions": library_versions(),
        },
        "budgets": budgets.as_document(),
        "transcript": {
            "messages_sha256": messages_sha256,
            "messages_path": messages_path,
            "tool_calls": tool_calls,
        },
        "web_snapshots": [],
        "proposals": proposal_rows,
        "outcome": {
            "verdict": verdict,
            "decline_class": decline_class,
            "checker_command": str(primary["command"]) if primary else "",
            "checker_exit_status": int(primary["exit_status"]) if primary else 0,
            "checker_output_sha256": (primary or {}).get("output_sha256"),
            "checker_runs": checker_runs,
            "axiom_footprint": list(axiom_footprint or []),
            "ledger_writes": 0,
            "search_invocations": sum(1 for c in tool_calls if c.get("assurance") == "checked"),
            "target_theorem_submissions": 0,
        },
        "observed": observed
        or {
            "facts_unlocked": [],
            "operations_widened": [],
            "overlay_links_proposed": [],
        },
    }


def write_episode(document: dict[str, Any], directory: Path, root: Path) -> Path:
    """Write the episode document, refusing anything that would carry a blind id."""
    directory.mkdir(parents=True, exist_ok=True)
    text = canonical(document)
    assert_no_held_out(text, "episode document", root)
    slug = document["episode_id"].split(":", 1)[1]
    path = directory / f"episode-{slug}.json"
    path.write_text(text, encoding="utf-8")
    return path


def fact_partition(root: Path, fact_id: str) -> Literal["train", "development"]:
    """The partition, refusing anything the episode schema cannot express."""
    pen = nursery_api.load(root)
    if not pen.contains(fact_id):
        raise EpisodeWriteError(
            "the nursery does not preregister that fact, so no partition can be recorded"
        )
    partition = pen.partition_of(fact_id)
    if partition not in ELIGIBLE_PARTITIONS:
        raise EpisodeWriteError(
            "that fact's partition is not one the episode schema admits; refusing"
        )
    return partition  # type: ignore[return-value]


def fact_exists(root: Path | str | None, fact_id: str) -> bool:
    return fact_id in facts_api.load(resolve_root(root)).ids


__all__ = [
    "A2_VERDICTS",
    "KIND",
    "SCHEMA_VERSION",
    "SCHEMA_VERSION_V2",
    "SNAPSHOT_SUFFIX",
    "V1_VERDICTS",
    "Budgets",
    "EpisodeWriteError",
    "HeldOutLeak",
    "agent_code_sha256",
    "assert_no_held_out",
    "build_episode",
    "build_episode_v2",
    "canonical",
    "eligibility_reason",
    "episode_id_for",
    "fact_exists",
    "fact_partition",
    "git_commit",
    "library_versions",
    "now_utc",
    "project_tool_calls",
    "proved_is_supported",
    "repo_relative",
    "save_frontier",
    "sha256_bytes",
    "sha256_text",
    "write_episode",
    "write_proposals",
    "write_transcript",
]
