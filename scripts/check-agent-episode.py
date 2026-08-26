#!/usr/bin/env python3
"""An agent episode is a record, and a record that cannot fail is not evidence.

`docs/python-2026-08/03-agentic-layer.md` builds an autonomous loop over the
Python API. Nothing in that loop has admission authority -- the whole design is
that an LLM replaces the enumerator and *nothing else changes* -- so the episode
artifact is the only thing standing between "a model ran" and "a model proved
something". This is the gate that makes the difference measurable.

It is written against the failure this repository keeps finding in itself:
**40 of 162 checker runs across 36 settled facts exit 0 on completion alone**
(CLAUDE.md, audited 2026-08-15). So every rule below is named, every rule's exit
status depends on what it found, and the file that checks nothing is the loudest
failure of all:

    EPISODES|checked=0|ok=0|failed=0        -> exit 1

Two schema versions are checked, dispatched on the document's own
`schema_version`. v1 is the A2 episode; v2 (slice A4) adds
`selection.ledger_sha256`, `outcome.checker_runs[]` and a `decline_class` enum,
and brings one new rule with it:

    proved-requires-checked-call        v2 `proved` without a `checked` tool
                                        call, or without a checker run that
                                        exited 0

Both halves are required and neither implies the other. A `checked` tool call
with no passing checker is a producer nobody re-validated; a passing checker
with no `checked` call is a checker that ran against nothing this episode did.
The v2 schema keeps v1's singular `checker_command` / `checker_exit_status`
fields and requires them, so every rule below still bites on a v2 document
rather than being skipped by the version dispatch -- a new schema version that
quietly turned rules off would be the worst possible way to add one.

Named rules, each with a mutation control in
`scripts/tests/mutation_controls.py` under the `agent-episode` suite:

    schema                              the document is not an episode
    git-commit-ancestor                 --require-ancestor and the commit is not one
    frontier-digest                     selection.frontier_sha256 != the file's
    frontier-reverify                   --verify-frontier and fact-frontier.py --verify rejects the file
    web-snapshot-digest                 a snapshot's bytes are not what it claims
    ledger-writes-must-be-zero          an episode wrote to the ledger
    held-out-reference                  a blind fact id appears ANYWHERE
    proved-requires-zero-checker-status "proved" on a checker that did not pass
    proved-requires-checker-command     "proved" with nothing named as the checker
    proposal-digest                     a proposal's bytes are not what it claims
    empty-transcript                    a run that called nothing is not a decline
    unknown-fact-id                     selection.fact_id is not in the ledger

Three of those deserve a note.

**held-out-reference is a generic recursive string walk**, and the held-out set
is computed by importing `held_out_facts` from
`scripts/check-autogenesis-holdout-isolation.py` rather than by re-deriving it.
That script's own docstring records why the walk is generic: operations already
carried fact ids at three distinct JSON paths, so a field-specific guard was
bypassable the day it was written. An episode has more free-text surface than an
operation (an `eligibility_reason`, a `decline_class`, a tool name), so the same
argument applies with more force. Importing rather than copying means the two
gates cannot drift about what "held out" means; a control cross-checks the count.

**frontier-digest is skipped with a WARN when the frontier file is absent.**
A committed episode should carry its frontier; a fixture does not, and refusing
to check anything else because one input is missing would make the gate
unusable on exactly the artifacts written to exercise it. The WARN is printed,
never swallowed -- an absent input that reports nothing is the shape this
repository has been bitten by four times.

**--require-ancestor is opt-in, and that is a deliberate weakening.** The rule
in plan 03 is that `git_commit` must be an ancestor of `HEAD`. That is true of a
committed episode in this checkout and NOT necessarily true anywhere else: CI
clones shallow (`fetch-depth: 1` leaves one commit, so every ancestor query
answers "no"), a lane snapshot from `git archive` has no `.git` at all, and a
release tarball has no history. A rule that fails in those environments would be
switched off, which is worse than a rule that is asked for. So the default is a
WARN naming the same rule, and any gate that runs in a full checkout passes
`--require-ancestor` to get the hard failure. Fail-closed within the opt-in: if
ancestry cannot be DETERMINED, that is a failure, not a pass.

Usage::

    scripts/check-agent-episode.py artifacts/episodes            # a directory
    scripts/check-agent-episode.py artifacts/episodes --production-only
    scripts/check-agent-episode.py path/to/episode.json ...      # explicit files
    scripts/check-agent-episode.py artifacts/episodes --require-ancestor
    scripts/check-agent-episode.py ep.json --nursery N.json --facts artifacts/facts

A directory argument is walked for `*.json`; anything else is read as a file.
`--production-only` excludes every path below a directory whose name starts
with `fixtures`. This is the aggregate evidence mode: illustrative documents
remain useful checker inputs, but cannot make the production population
nonempty. Exit status is 0 only when at least one episode was checked and every
one passed.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import pathlib
import re
import subprocess
import sys
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
SCHEMA = ROOT / "artifacts/ontology/agent-episode.schema.json"
SCHEMA_V2 = ROOT / "artifacts/ontology/agent-episode-v2.schema.json"

# Which schema file each `schema_version` is checked against. A document
# declaring a version that is not a key here is a FAILURE, not a document
# checked against the nearest schema: validating a v3 episode against the v2
# schema would report on constraints nobody wrote for it, and an unknown
# version silently checked is a version silently trusted.
SCHEMAS = {1: SCHEMA, 2: SCHEMA_V2}
NURSERY = ROOT / "artifacts/autogenesis/nursery-v1.json"
FACTS = ROOT / "artifacts/facts"
FRONTIER = ROOT / "scripts/fact-frontier.py"
ISOLATION = ROOT / "scripts/check-autogenesis-holdout-isolation.py"

# A subprocess that never returns is a gate that never fails. Both shell-outs
# here are bounded; a timeout is reported as the rule failing, not as a skip.
SUBPROCESS_TIMEOUT = 120


class EpisodeError(RuntimeError):
    """The gate cannot run. Distinct from an episode that fails a rule."""


def _load_module(path: pathlib.Path, name: str) -> Any:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise EpisodeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


# ---------------------------------------------------------------- JSON Schema
#
# `jsonschema` is not available: `scripts/` is standard-library only. So this is
# a validator for the SUBSET the episode schema uses, and it refuses vocabulary
# it does not implement rather than ignoring it -- an unimplemented keyword that
# is silently skipped is a constraint that looks enforced and is not.

_SUPPORTED = {
    "$ref", "$schema", "$id", "title", "description", "$defs",
    "type", "required", "properties", "additionalProperties", "items",
    "enum", "const", "minimum", "maximum", "minLength", "minItems", "pattern",
}

_TYPES: dict[str, Any] = {
    "object": dict,
    "array": list,
    "string": str,
    "boolean": bool,
    "null": type(None),
}


def _is_type(value: Any, name: str) -> bool:
    if name == "integer":
        return isinstance(value, int) and not isinstance(value, bool)
    if name == "number":
        return isinstance(value, (int, float)) and not isinstance(value, bool)
    if name == "boolean":
        return isinstance(value, bool)
    expected = _TYPES.get(name)
    if expected is None:
        raise EpisodeError(f"schema uses an unimplemented type: {name}")
    return isinstance(value, expected)


def validate(value: Any, schema: dict, root: dict, where: str = "") -> list[str]:
    """Return every violation, deepest first. Never raises on the DOCUMENT."""
    unknown = set(schema) - _SUPPORTED
    if unknown:
        raise EpisodeError(
            f"the episode schema uses keywords this validator does not implement: "
            f"{sorted(unknown)} (at {where or '<root>'})"
        )
    if "$ref" in schema:
        ref = schema["$ref"]
        if not ref.startswith("#/$defs/"):
            raise EpisodeError(f"only local #/$defs/ refs are implemented, got {ref}")
        target = root.get("$defs", {}).get(ref.split("/")[-1])
        if target is None:
            raise EpisodeError(f"unresolvable ref {ref}")
        return validate(value, target, root, where)

    errors: list[str] = []
    if "const" in schema and value != schema["const"]:
        errors.append(f"{where or '<root>'}: expected {schema['const']!r}, got {value!r}")
    if "enum" in schema and value not in schema["enum"]:
        errors.append(f"{where or '<root>'}: {value!r} is not one of {schema['enum']}")
    if "type" in schema:
        names = schema["type"]
        names = [names] if isinstance(names, str) else names
        if not any(_is_type(value, name) for name in names):
            errors.append(f"{where or '<root>'}: expected type {schema['type']}, got {type(value).__name__}")
            return errors
    if isinstance(value, str):
        if "pattern" in schema and re.search(schema["pattern"], value) is None:
            errors.append(f"{where}: {value!r} does not match {schema['pattern']}")
        if "minLength" in schema and len(value) < schema["minLength"]:
            errors.append(f"{where}: shorter than minLength {schema['minLength']}")
    if isinstance(value, (int, float)) and not isinstance(value, bool):
        if "minimum" in schema and value < schema["minimum"]:
            errors.append(f"{where}: {value} is below minimum {schema['minimum']}")
        if "maximum" in schema and value > schema["maximum"]:
            errors.append(f"{where}: {value} is above maximum {schema['maximum']}")
    if isinstance(value, dict):
        for key in schema.get("required", []):
            if key not in value:
                errors.append(f"{where}.{key}: required property is missing")
        properties = schema.get("properties", {})
        extra = schema.get("additionalProperties", True)
        for key, item in value.items():
            if key in properties:
                errors += validate(item, properties[key], root, f"{where}.{key}")
            elif extra is False:
                errors.append(f"{where}.{key}: additional property is not allowed")
            elif isinstance(extra, dict):
                errors += validate(item, extra, root, f"{where}.{key}")
    if isinstance(value, list):
        if "minItems" in schema and len(value) < schema["minItems"]:
            errors.append(f"{where}: fewer than minItems {schema['minItems']}")
        if "items" in schema:
            for index, item in enumerate(value):
                errors += validate(item, schema["items"], root, f"{where}[{index}]")
    return errors


# ------------------------------------------------------------------- helpers

def strings(value: Any, path: str = "") -> list[tuple[str, str]]:
    """Every string in the document with the JSON path it sits at.

    Deliberately identical in shape to the walk in
    `check-autogenesis-holdout-isolation.py`: a held-out id is a violation
    wherever it appears, including in a field nobody has invented yet.
    """
    if isinstance(value, dict):
        return [x for k, v in value.items() for x in strings(v, f"{path}.{k}")]
    if isinstance(value, list):
        return [x for v in value for x in strings(v, f"{path}[]")]
    if isinstance(value, str):
        return [(value, path)]
    return []


def resolve(path: str) -> pathlib.Path:
    candidate = pathlib.Path(path)
    return candidate if candidate.is_absolute() else ROOT / candidate


def file_sha256(path: pathlib.Path) -> str | None:
    try:
        return hashlib.sha256(path.read_bytes()).hexdigest()
    except OSError:
        return None


def is_ancestor(commit: str) -> bool | None:
    """True / False / None when git cannot answer (no repo, no such object)."""
    try:
        done = subprocess.run(
            ["git", "-C", str(ROOT), "merge-base", "--is-ancestor", commit, "HEAD"],
            capture_output=True, text=True, timeout=SUBPROCESS_TIMEOUT,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    if done.returncode == 0:
        return True
    if done.returncode == 1:
        return False
    return None


def reverify_frontier(path: pathlib.Path) -> tuple[bool, str]:
    try:
        done = subprocess.run(
            [sys.executable, str(FRONTIER), "--verify", str(path)],
            capture_output=True, text=True, timeout=SUBPROCESS_TIMEOUT, cwd=str(ROOT),
        )
    except subprocess.TimeoutExpired:
        return (False, f"fact-frontier.py --verify did not finish in {SUBPROCESS_TIMEOUT}s")
    except OSError as error:
        return (False, f"fact-frontier.py --verify could not be run: {error}")
    if done.returncode != 0:
        detail = (done.stderr or done.stdout or "").strip().splitlines()
        return (False, detail[-1] if detail else f"exit status {done.returncode}")
    return (True, (done.stdout or "").strip())


# --------------------------------------------------------------------- rules

def check_episode(
    path: pathlib.Path,
    document: Any,
    schema: dict,
    held: set[str],
    fact_ids: set[str],
    require_ancestor: bool,
    verify_frontier: bool = False,
) -> tuple[list[tuple[str, str]], list[tuple[str, str]]]:
    """Return (failures, warnings) as (rule, detail) pairs."""
    failures: list[tuple[str, str]] = []
    warnings: list[tuple[str, str]] = []

    def fail(rule: str, detail: str) -> None:
        failures.append((rule, detail))

    def warn(rule: str, detail: str) -> None:
        warnings.append((rule, detail))

    # (1) schema
    for message in validate(document, schema, schema):
        fail("schema", message)

    if not isinstance(document, dict):
        return (failures, warnings)

    selection = document.get("selection") or {}
    transcript = document.get("transcript") or {}
    outcome = document.get("outcome") or {}
    selection = selection if isinstance(selection, dict) else {}
    transcript = transcript if isinstance(transcript, dict) else {}
    outcome = outcome if isinstance(outcome, dict) else {}

    # (2) git-commit-ancestor
    commit = document.get("git_commit")
    if isinstance(commit, str):
        ancestor = is_ancestor(commit)
        if ancestor is not True:
            reason = "is not an ancestor of HEAD" if ancestor is False else "cannot be resolved against this checkout"
            if require_ancestor:
                fail("git-commit-ancestor", f"{commit} {reason}")
            else:
                warn("git-commit-ancestor", f"{commit} {reason}; --require-ancestor was not given")

    # (3) frontier-digest and (3b) frontier-reverify
    frontier_path = selection.get("frontier_path")
    claimed = selection.get("frontier_sha256")
    if isinstance(frontier_path, str):
        target = resolve(frontier_path)
        if not target.is_file():
            warn("frontier-digest", f"{frontier_path} is not on disk; the digest was not re-derived")
        else:
            try:
                saved = json.loads(target.read_text())
                actual = saved.get("frontier_sha256") if isinstance(saved, dict) else None
            except (OSError, json.JSONDecodeError) as error:
                actual, saved = None, None
                fail("frontier-digest", f"{frontier_path} is unreadable: {error}")
            if actual is not None and actual != claimed:
                fail("frontier-digest", f"episode claims {claimed}, {frontier_path} carries {actual}")
            if verify_frontier:
                ok, detail = reverify_frontier(target)
                if not ok:
                    fail("frontier-reverify", f"{frontier_path}: {detail}")
            else:
                # Re-deriving the saved frontier against the LIVE ledger rots the
                # moment any lane adds a fact (measured 2026-08-24: 16 of 20
                # committed episodes went red within hours of landing while
                # every digest still matched). The self-digest above is the
                # committed claim; freshness is an explicit question.
                warn("frontier-reverify", f"{frontier_path} not re-derived; --verify-frontier was not given")

    # (4) web-snapshot-digest
    for index, snapshot in enumerate(document.get("web_snapshots") or []):
        if not isinstance(snapshot, dict):
            continue
        where = f"web_snapshots[{index}]"
        digest = file_sha256(resolve(str(snapshot.get("path"))))
        if digest != snapshot.get("sha256"):
            fail("web-snapshot-digest", f"{where} {snapshot.get('path')}: claims {snapshot.get('sha256')}, on disk {digest}")

    # (5) ledger-writes-must-be-zero
    writes = outcome.get("ledger_writes")
    if writes != 0:
        fail("ledger-writes-must-be-zero", f"outcome.ledger_writes is {writes!r}; an episode has no admission authority")

    # (6) held-out-reference -- generic walk, every string, every path
    for value, where in strings(document):
        if value in held:
            fail("held-out-reference", f"{where or '<root>'}: {value}")

    # (7) proved-requires-zero-checker-status / proved-requires-checker-command
    if outcome.get("verdict") == "proved":
        status = outcome.get("checker_exit_status")
        if status != 0:
            fail("proved-requires-zero-checker-status", f"verdict is proved with checker_exit_status {status!r}")
        command = outcome.get("checker_command")
        if not (isinstance(command, str) and command.strip()):
            fail("proved-requires-checker-command", "verdict is proved with no checker_command")

    # (11) proved-requires-checked-call -- schema v2 only, because v1 has no
    # `checker_runs` for the rule to stand on. The C tier is the ONLY producer
    # of a `checked` assurance, so this is what makes "proved" mean "a tool that
    # dispatches ran, and something re-validated what it produced".
    if document.get("schema_version") == 2 and outcome.get("verdict") == "proved":
        checked_calls = [
            call
            for call in (transcript.get("tool_calls") or [])
            if isinstance(call, dict) and call.get("assurance") == "checked"
        ]
        if not checked_calls:
            fail(
                "proved-requires-checked-call",
                "verdict is proved but no tool call carries assurance='checked'; the C "
                "tier is the only route to proved and nothing in this episode used it",
            )
        passing_runs = [
            run
            for run in (outcome.get("checker_runs") or [])
            if isinstance(run, dict) and run.get("exit_status") == 0
        ]
        if not passing_runs:
            fail(
                "proved-requires-checked-call",
                "verdict is proved but no checker run exited 0; a proof nobody "
                "re-validated is not proved",
            )

    # (8) proposal-digest
    for index, proposal in enumerate(document.get("proposals") or []):
        if not isinstance(proposal, dict):
            continue
        where = f"proposals[{index}]"
        digest = file_sha256(resolve(str(proposal.get("path"))))
        if digest != proposal.get("sha256"):
            fail("proposal-digest", f"{where} {proposal.get('path')}: claims {proposal.get('sha256')}, on disk {digest}")

    # (9) empty-transcript
    calls = transcript.get("tool_calls")
    if not calls:
        fail("empty-transcript", "transcript.tool_calls is empty; a run that called nothing is not a clean decline")

    # (10) unknown-fact-id
    fact_id = selection.get("fact_id")
    if fact_id not in fact_ids:
        fail("unknown-fact-id", f"selection.fact_id {fact_id!r} is not in the fact ledger")

    return (failures, warnings)


# ---------------------------------------------------------------------- main

def is_fixture_path(path: pathlib.Path) -> bool:
    """Return whether a path is inside a fixture population."""
    return any(part.startswith("fixtures") for part in path.parts)


def episode_paths(
    arguments: list[str], *, production_only: bool = False
) -> tuple[list[pathlib.Path], int]:
    out: list[pathlib.Path] = []
    excluded = 0
    for argument in arguments:
        path = pathlib.Path(argument)
        if path.is_dir():
            candidates = sorted(p for p in path.rglob("*.json"))
        else:
            candidates = [path]
        for candidate in candidates:
            if production_only and is_fixture_path(candidate):
                excluded += 1
            else:
                out.append(candidate)
    return (out, excluded)


def ledger_fact_ids(facts: pathlib.Path) -> set[str]:
    return {"F:" + p.stem[2:] for p in sorted(facts.glob("F-*.json"))}


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description="check agent episode artifacts")
    ap.add_argument("episodes", nargs="*", help="episode JSON files or directories")
    ap.add_argument("--verify-frontier", action="store_true",
                    help="re-derive each saved frontier against the LIVE ledger (opt-in: it rots as the ledger grows)")
    ap.add_argument("--require-ancestor", action="store_true",
                    help="fail when git_commit is not an ancestor of HEAD (see the module docstring)")
    ap.add_argument(
        "--production-only",
        action="store_true",
        help="exclude paths below fixtures* directories from the evidence population",
    )
    ap.add_argument("--nursery", type=pathlib.Path, default=NURSERY)
    ap.add_argument("--facts", type=pathlib.Path, default=FACTS)
    args = ap.parse_args(argv)

    schemas: dict[int, dict] = {}
    for version, path in SCHEMAS.items():
        try:
            schemas[version] = json.loads(path.read_text())
        except (OSError, json.JSONDecodeError) as error:
            print(f"EPISODE_ERROR|schema|v{version}|{error}", file=sys.stderr)
            return 2

    isolation = _load_module(ISOLATION, "episode_holdout_isolation")
    isolation.NURSERY = args.nursery
    try:
        held = isolation.held_out_facts()
    except isolation.IsolationError as error:
        print(f"EPISODE_ERROR|held-out-population|{error}", file=sys.stderr)
        return 2

    fact_ids = ledger_fact_ids(args.facts)
    if not fact_ids:
        print(f"EPISODE_ERROR|fact-ledger|{args.facts} holds no facts; "
              f"rule unknown-fact-id would reject everything", file=sys.stderr)
        return 2

    paths, excluded = episode_paths(
        args.episodes, production_only=args.production_only
    )
    if args.production_only:
        print(
            "EPISODE_DISCOVERY|production_only=true|"
            f"candidates={len(paths)}|excluded_fixtures={excluded}"
        )

    checked = failed = 0
    for path in paths:
        checked += 1
        try:
            document = json.loads(path.read_text())
        except (OSError, json.JSONDecodeError) as error:
            failed += 1
            print(f"EPISODE|path={path}|status=FAIL|rules=unreadable-document")
            print(f"  unreadable-document|{path}|{error}", file=sys.stderr)
            continue
        declared = document.get("schema_version") if isinstance(document, dict) else None
        schema = schemas.get(declared) if isinstance(declared, int) else None
        if schema is None:
            failed += 1
            print(
                f"EPISODE|path={path}|episode_id=None|verdict=None|status=FAIL"
                f"|rules=unknown-schema-version"
            )
            print(
                f"  unknown-schema-version|{path}|schema_version={declared!r}; this gate "
                f"checks {sorted(SCHEMAS)} and refuses to check a document against a "
                f"schema nobody wrote for it",
                file=sys.stderr,
            )
            continue
        try:
            failures, warnings = check_episode(
                path, document, schema, held, fact_ids, args.require_ancestor,
                args.verify_frontier,
            )
        except EpisodeError as error:
            print(f"EPISODE_ERROR|validator|{error}", file=sys.stderr)
            return 2
        for rule, detail in warnings:
            print(f"EPISODE_WARN|path={path}|rule={rule}|{detail}")
        episode_id = document.get("episode_id") if isinstance(document, dict) else None
        verdict = (document.get("outcome") or {}).get("verdict") if isinstance(document, dict) else None
        if failures:
            failed += 1
            rules = ",".join(sorted({rule for rule, _ in failures}))
            print(f"EPISODE|path={path}|episode_id={episode_id}|verdict={verdict}|status=FAIL|rules={rules}")
            for rule, detail in failures:
                print(f"  {rule}|{detail}", file=sys.stderr)
        else:
            print(f"EPISODE|path={path}|episode_id={episode_id}|verdict={verdict}|status=OK|rules=")

    print(f"EPISODES|checked={checked}|ok={checked - failed}|failed={failed}")
    if checked == 0:
        print("check-agent-episode: no episodes were checked; a check that checked "
              "nothing is not a pass", file=sys.stderr)
        return 1
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
