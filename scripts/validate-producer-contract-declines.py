#!/usr/bin/env python3
"""Validate contract-driven decline artifacts under `artifacts/autogenesis/`.

Doc `docs/autogenesis/290-int-add-modeq-left-contract-dispatch-decline.md`
recorded the first real run of a producer contract (ADR-0602): a clean import,
a real producer attempt, and an honest, typed decline
(`artifacts/autogenesis/mathlib-int-add-modeq-left-decline-v1.json`). Doc
`docs/autogenesis/291-decline-feedback-loop.md` is the convention this
validator enforces: that decline is not just a receipt, it is now SELECTOR
INPUT -- `scripts/fact-frontier.py` reads it and stops presenting the same
`(fact, contract)` pair as admissible.

That makes this validator load-bearing in a new way. The failure mode to
design against, verbatim from the task that added this file: **a decline
artifact becomes a cheap way to make the selector shut up about a fact
forever.** So every guard here is written to be able to FAIL, exactly as
CLAUDE.md's standing finding about checkers demands (40 of 162 checker runs
in this repository once exited 0 on completion alone):

  * `fact_id` must resolve to a REAL fact in `artifacts/facts/` -- an
    invented id would let a decline suppress nothing real while looking like
    it suppresses something;
  * `contract` must resolve to a REAL, loadable producer contract file --
    same reasoning;
  * `producer.decline_reason` must be a bare TYPED identifier
    (`^[A-Z][A-Za-z0-9]*$`, the shape of a Rust `DeclineReason` enum variant),
    never free text -- a free-text reason is exactly the "we tried, no dice"
    loophole nothing could ever check;
  * `producer.result` must be exactly `"declined"`, and `producer.tool` /
    `producer.decline_message` must be non-empty -- an artifact with no
    checkable producer identity or human-readable detail is unfalsifiable by
    construction;
  * `contract_sha256` must be a well-formed sha256 hex digest -- the
    re-dispatch key `fact-frontier.py` uses to decide whether a decline is
    still live against the contract's CURRENT content.

ADR-1510 RULE 2: A DECLINE IS A LIFECYCLE OBJECT. Every guard above is about
the decline being well-formed at the moment it is written; none of them
notices what happens to its FACT afterwards. Measured 2026-09-01, that gap was
already 96% of the ledger: `declined_by_contract` summed to 27 live
suppressions while `declined_count` -- declines suppressing a fact that is
still ready and open -- was **1**. Twenty-six named facts that had since been
proved, by hand, through a route that never touched a producer. To every
checker and to the selector, such a decline is indistinguishable from one
suppressing live work, which is exactly the "cheap way to make the selector
shut up about a fact forever" failure mode named above, materialised in its
benign direction and therefore invisible. Three further guards, each expected
to die under exactly one mutation:

  * a decline whose fact is SETTLED (`epistemic_status` outside
    `{open, conjectured, empirical}`) must carry a `resolution` block naming
    the route, the artifact that closed it, and on what basis the decline's
    own diagnosis is still believed (`diagnosis_status`, which is a
    three-valued vocabulary and not a boolean, precisely so "nobody
    re-checked" cannot be written as "still accurate");
  * a decline whose fact is still OPEN must NOT carry one -- the inverse
    direction, so a lane cannot pre-emptively "resolve" a live suppression
    and silence the guard above while the work is still outstanding;
  * `resolution.closed_by` must resolve to a real path in this repository.
    An invented artifact is the same unfalsifiable object as an invented
    `fact_id`: it makes the record look answerable while answering nothing.

The 5 declines the `int-modeq-kernel` lane wrote voluntarily carry the same
content as an `amendment` block; that field is preserved unedited as the
historical record and `resolution` is the machine-checkable form.

A contract-driven decline is identified STRUCTURALLY, not by filename or
directory: any JSON object under `artifacts/autogenesis/` carrying top-level
`contract` and `fact_id` keys together with `producer.result == "declined"`.
That is exactly the shape of the one seed instance
(`mathlib-int-add-modeq-left-decline-v1.json`) and exactly what distinguishes
it from the eleven pre-ADR-0602 decline files, none of which have a top-level
`contract` key -- so this validator (and `fact-frontier.py`) never touches
those older files, and nothing about them needs to change.

Usage::

    python3 scripts/validate-producer-contract-declines.py
"""

from __future__ import annotations

import json
import pathlib
import re
import sys
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
FACTS = ROOT / "artifacts" / "facts"
AUTOGENESIS = ROOT / "artifacts" / "autogenesis"
CONTRACTS_DIR = ROOT / "artifacts" / "autogenesis" / "producer-contracts"

FACT_ID_RE = re.compile(r"^F:[a-z0-9]+(-[a-z0-9]+)*$")
# The shape of a Rust enum variant name: PascalCase, no spaces, no
# punctuation. This is what makes a reason TYPED rather than free text.
TYPED_REASON_RE = re.compile(r"^[A-Z][A-Za-z0-9]*$")
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")

DECLINE_TOP_LEVEL_REQUIRED = {
    "schema_version",
    "kind",
    "contract",
    "contract_sha256",
    "fact_id",
    "producer",
}
PRODUCER_REQUIRED = {"tool", "result", "decline_reason", "decline_message"}

# Mirrors `fact-frontier.py`'s `band()` and `validate-producer-contracts.py`'s
# OPEN_STATUSES: a fact still needing proof in OUR ledger. Anything else is
# SETTLED, and a decline against a settled fact must be resolved (ADR-1510).
OPEN_STATUSES = {"open", "conjectured", "empirical"}
RESOLUTION_REQUIRED = {"date", "route", "closed_by", "diagnosis_status"}
RESOLUTION_OPTIONAL = {"theorem", "note"}
RESOLUTION_ROUTES = {"kernel-lane", "cas-bridge", "import"}
# Whether the decline's OWN typed reason is still a correct description of what
# the producer cannot do -- and, deliberately, HOW that is known. A boolean
# cannot say "nobody checked", and 19 of the 26 backfilled resolutions are in
# exactly that state: the design review re-executed two representatives and the
# closing lane attested five, leaving the rest argued rather than re-run. An
# `unknown` wearing a `true` is the checker-that-cannot-fail defect in the data
# instead of the code, so the vocabulary carries the basis:
#   reproduced      -- the dispatch was re-run and the same decline came back
#   attested        -- the lane that closed the fact recorded that the decline
#                      still describes the producer correctly
#   not-re-executed -- neither; the decline is preserved unedited and no claim
#                      is made about re-running it
DIAGNOSIS_STATUSES = {"reproduced", "attested", "not-re-executed"}
DATE_RE = re.compile(r"^[0-9]{4}-[0-9]{2}-[0-9]{2}$")


class DeclineError(RuntimeError):
    """A contract-driven decline artifact is malformed or unfalsifiable."""


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def digest(value: Any) -> str:
    import hashlib

    return hashlib.sha256(canonical_json(value).encode()).hexdigest()


def load_facts(facts_dir: pathlib.Path = FACTS) -> dict[str, dict]:
    facts: dict[str, dict] = {}
    if not facts_dir.is_dir():
        raise DeclineError(f"no fact ledger at {facts_dir}")
    for path in sorted(facts_dir.glob("*.json")):
        fact = json.loads(path.read_text())
        fact_id = fact.get("id")
        if isinstance(fact_id, str):
            facts[fact_id] = fact
    return facts


def is_contract_decline_shaped(candidate: Any) -> bool:
    """Structural identification of the NEW decline convention (doc 291).

    Deliberately loose here -- this only decides whether a file is a
    contract-driven decline AT ALL, so that the eleven pre-ADR-0602 decline
    files (none of which have a top-level `contract` key) are silently
    skipped rather than rejected. `validate_decline` below does the strict
    checking once a file has already been identified this way.
    """
    return (
        isinstance(candidate, dict)
        and "contract" in candidate
        and "fact_id" in candidate
        and isinstance(candidate.get("producer"), dict)
        and candidate["producer"].get("result") == "declined"
    )


def load_contract(contract_path_str: Any, label: str) -> dict[str, Any]:
    if not isinstance(contract_path_str, str) or not contract_path_str:
        raise DeclineError(f"{label}: contract must be a non-empty string path")
    contract_path = ROOT / contract_path_str
    try:
        resolved = contract_path.resolve()
        contracts_dir_resolved = CONTRACTS_DIR.resolve()
    except OSError as error:
        raise DeclineError(f"{label}: contract path {contract_path_str!r} unreadable: {error}") from error
    if contracts_dir_resolved not in resolved.parents:
        raise DeclineError(
            f"{label}: contract {contract_path_str!r} does not resolve under {CONTRACTS_DIR} -- "
            "a decline must name a real, committed producer contract, not an arbitrary path."
        )
    if not resolved.is_file():
        raise DeclineError(
            f"{label}: contract {contract_path_str!r} does not resolve to a real file -- "
            "an invented contract reference proves nothing."
        )
    try:
        loaded = json.loads(resolved.read_text())
    except json.JSONDecodeError as error:
        raise DeclineError(f"{label}: contract {contract_path_str!r} is not valid JSON: {error}") from error
    if not isinstance(loaded, dict) or not isinstance(loaded.get("id"), str):
        raise DeclineError(f"{label}: contract {contract_path_str!r} has no string `id`")
    return loaded


def validate_resolution(resolution: Any, label: str) -> None:
    """Structural validation of an ADR-1510 `resolution` block.

    `closed_by` is checked against the filesystem for the same reason
    `fact_id` and `contract` are: a record naming an artifact that does not
    exist explains nothing while looking like an explanation.
    """
    if not isinstance(resolution, dict):
        raise DeclineError(f"{label}: resolution must be an object")
    missing = RESOLUTION_REQUIRED - set(resolution)
    if missing:
        raise DeclineError(f"{label}: resolution missing required key(s) {sorted(missing)}")
    extra = set(resolution) - RESOLUTION_REQUIRED - RESOLUTION_OPTIONAL
    if extra:
        raise DeclineError(f"{label}: resolution has unexpected key(s) {sorted(extra)}")

    if not isinstance(resolution["date"], str) or not DATE_RE.match(resolution["date"]):
        raise DeclineError(f"{label}: resolution.date must be an ISO date (YYYY-MM-DD)")

    if resolution["route"] not in RESOLUTION_ROUTES:
        raise DeclineError(
            f"{label}: resolution.route must be one of {sorted(RESOLUTION_ROUTES)} "
            f"(the ADR-0601 SS4 producer routes), got {resolution['route']!r}"
        )

    if resolution["diagnosis_status"] not in DIAGNOSIS_STATUSES:
        raise DeclineError(
            f"{label}: resolution.diagnosis_status must be one of "
            f"{sorted(DIAGNOSIS_STATUSES)}, got {resolution['diagnosis_status']!r} -- "
            "the basis on which the decline's own typed reason is still believed "
            "to describe the producer. A bare boolean here would let "
            "\"nobody re-checked\" be written as \"still accurate\"."
        )

    closed_by = resolution["closed_by"]
    if not isinstance(closed_by, str) or not closed_by:
        raise DeclineError(f"{label}: resolution.closed_by must be a non-empty path string")
    if not (ROOT / closed_by).exists():
        raise DeclineError(
            f"{label}: resolution.closed_by {closed_by!r} does not resolve to a real "
            "path in this repository -- an invented artifact explains nothing, which "
            "is the same defect as an invented fact_id one field over."
        )

    for key in ("theorem", "note"):
        if key in resolution and (
            not isinstance(resolution[key], str) or not resolution[key]
        ):
            raise DeclineError(f"{label}: resolution.{key} must be a non-empty string")


def validate_decline(
    decline: Any, facts: dict[str, dict], path: pathlib.Path | None = None
) -> None:
    """Strict validation of an artifact already identified as a
    contract-driven decline by `is_contract_decline_shaped`.

    Raises `DeclineError` on the first violation found; callers wanting every
    violation should call this once per file and let the caller aggregate.
    """
    label = str(path) if path is not None else decline.get("fact_id", "<decline>")
    if not isinstance(decline, dict):
        raise DeclineError(f"{label}: expected an object")

    missing = DECLINE_TOP_LEVEL_REQUIRED - set(decline)
    if missing:
        raise DeclineError(f"{label}: missing required key(s) {sorted(missing)}")

    if decline.get("schema_version") != 1:
        raise DeclineError(f"{label}: schema_version must be 1")

    fact_id = decline["fact_id"]
    if not isinstance(fact_id, str) or not FACT_ID_RE.match(fact_id):
        raise DeclineError(f"{label}: fact_id {fact_id!r} is malformed")
    if fact_id not in facts:
        raise DeclineError(
            f"{label}: fact_id {fact_id!r} does not resolve to any fact in {FACTS} -- "
            "a decline naming nothing real suppresses nothing real."
        )

    load_contract(decline.get("contract"), label)

    contract_sha256 = decline["contract_sha256"]
    if not isinstance(contract_sha256, str) or not SHA256_RE.match(contract_sha256):
        raise DeclineError(
            f"{label}: contract_sha256 must be a 64-character lowercase hex sha256 digest, "
            f"got {contract_sha256!r}"
        )

    producer = decline["producer"]
    if not isinstance(producer, dict):
        raise DeclineError(f"{label}: producer must be an object")
    missing_producer = PRODUCER_REQUIRED - set(producer)
    if missing_producer:
        raise DeclineError(f"{label}: producer missing required key(s) {sorted(missing_producer)}")

    if producer["result"] != "declined":
        raise DeclineError(
            f"{label}: producer.result must be exactly \"declined\", got {producer['result']!r} -- "
            "this validator only ever applies to genuine decline records."
        )

    tool = producer["tool"]
    if not isinstance(tool, str) or not tool:
        raise DeclineError(f"{label}: producer.tool must be a non-empty string (producer identity)")

    reason = producer["decline_reason"]
    if not isinstance(reason, str) or not TYPED_REASON_RE.match(reason):
        raise DeclineError(
            f"{label}: producer.decline_reason {reason!r} is not a typed identifier "
            f"(must match {TYPED_REASON_RE.pattern!r}) -- free-text reasons cannot be "
            "checked, which is exactly the 'make the selector shut up' loophole this "
            "validator exists to close. Put prose detail in decline_message instead."
        )

    message = producer["decline_message"]
    if not isinstance(message, str) or not message:
        raise DeclineError(f"{label}: producer.decline_message must be a non-empty string")

    # ------------------------------------------------------------------
    # ADR-1510 rule 2: a decline dies with its fact.
    # ------------------------------------------------------------------
    settled = facts[fact_id].get("epistemic_status") not in OPEN_STATUSES
    resolution = decline.get("resolution")

    if settled and resolution is None:
        raise DeclineError(
            f"{label}: fact {fact_id!r} is settled "
            f"(epistemic_status {facts[fact_id].get('epistemic_status')!r}) but this "
            "decline carries no `resolution` block -- ADR-1510 rule 2. A decline "
            "against a settled fact is indistinguishable, to every checker and to "
            "fact-frontier.py, from one suppressing live work. Record how the fact "
            "was actually closed: `route`, `closed_by` (the artifact), "
            "`diagnosis_still_accurate`, and a dated `note`."
        )

    if not settled and resolution is not None:
        raise DeclineError(
            f"{label}: fact {fact_id!r} is still open but this decline already "
            "carries a `resolution` block -- a resolution records that the fact was "
            "closed, so writing one ahead of time silences the settled-fact guard "
            "while the work is still outstanding."
        )

    if resolution is not None:
        validate_resolution(resolution, label)


def load_declines(
    directory: pathlib.Path = AUTOGENESIS,
) -> list[tuple[pathlib.Path, dict[str, Any]]]:
    """Every `*.json` directly under `artifacts/autogenesis/` that is
    structurally a contract-driven decline. Non-decline files (contracts,
    operations, nursery, older decline shapes, ...) are silently skipped --
    this only enumerates the new convention.
    """
    if not directory.is_dir():
        return []
    found: list[tuple[pathlib.Path, dict[str, Any]]] = []
    for path in sorted(directory.glob("*.json")):
        try:
            loaded = json.loads(path.read_text())
        except json.JSONDecodeError as error:
            raise DeclineError(f"{path}: not valid JSON: {error}") from error
        if is_contract_decline_shaped(loaded):
            found.append((path, loaded))
    return found


def validate_declines_dir(
    directory: pathlib.Path = AUTOGENESIS, facts: dict[str, dict] | None = None
) -> list[dict[str, Any]]:
    if facts is None:
        facts = load_facts()
    declines: list[dict[str, Any]] = []
    for path, decline in load_declines(directory):
        validate_decline(decline, facts, path)
        declines.append(decline)
    return declines


def main() -> int:
    try:
        facts = load_facts()
        declines = validate_declines_dir(facts=facts)
        ledger_digest = digest(
            [
                {"fact_id": d["fact_id"], "contract": d["contract"], "sha256": digest(d)}
                for d in sorted(declines, key=lambda d: (d["fact_id"], d["contract"]))
            ]
        )
        resolved = sum(1 for d in declines if d.get("resolution") is not None)
        print(
            f"PRODUCER_CONTRACT_DECLINES_OK|declines={len(declines)}"
            f"|resolved={resolved}|registry={ledger_digest}"
        )
        return 0
    except (OSError, json.JSONDecodeError, DeclineError) as error:
        print(f"PRODUCER_CONTRACT_DECLINES_ERROR|{error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
