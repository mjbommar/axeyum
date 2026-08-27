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
        print(f"PRODUCER_CONTRACT_DECLINES_OK|declines={len(declines)}|registry={ledger_digest}")
        return 0
    except (OSError, json.JSONDecodeError, DeclineError) as error:
        print(f"PRODUCER_CONTRACT_DECLINES_ERROR|{error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
