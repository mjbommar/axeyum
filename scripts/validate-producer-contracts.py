#!/usr/bin/env python3
"""Validate `artifacts/autogenesis/producer-contracts/*.json` (ADR-0602).

The autogenesis operation registry (`validate-autogenesis-operations.py`) is a
retrospective RECEIPT system: every `ADMISSION_CONTRACTS` arm requires
`epistemic_status: "proved"`, so it cannot express "we could attempt this open
fact" without asserting a proof that does not exist. Doc
`docs/autogenesis/288-admission-precedes-registration.md` measured that this is
why `fact-frontier.py --json` reported `admissible: 0` over 132 dependency-ready
facts: nothing prospective can enter a system built to certify completed work.

A producer contract is the separate, prospective artifact ADR-0602 decides:
a CAPABILITY CLAIM ("facts matching this shape are dischargeable via route R
with recipe X"), never a completion claim. `artifacts/ontology/
producer-contract.schema.json` makes the false-assertion failure mode
UNREPRESENTABLE rather than merely forbidden -- there is no `proved` field,
no `epistemic_status` field, anywhere in the schema, and `additionalProperties:
false` at every level means smuggling one in is a schema violation.

This validator is a CHECKER, and CLAUDE.md's standing finding is that 40 of 162
checker runs in this repository exited 0 on completion alone. So every guard
here is written to be able to FAIL, and each is expected to die under exactly
one mutation (`scripts/tests/mutation_controls.py producer-contracts`):

  * every non-example fact id must resolve to a REAL fact in
    `artifacts/facts/` -- an invented id would let a contract claim
    falsifiability against nothing;
  * every non-example must FAIL the shape predicate, checked by EXECUTING the
    predicate against the fact's current ledger entry, never by trusting the
    contract's own `reason` prose;
  * a shape predicate that matches EVERY open fact in the ledger is rejected --
    the vacuous-matcher defect, reborn one arrow upstream of the operation
    registry it was meant to unblock;
  * a shape narrowed only by `formal_language`/`fragments` (with no
    `title_prefix`, `statement_contains`, or `id_prefix`) is rejected: those
    two fields alone are a fragment-wide claim, and this project already found
    that "the fragment is Nat" is not a shape, it is almost the whole ledger.

Usage::

    python3 scripts/validate-producer-contracts.py
"""

from __future__ import annotations

import hashlib
import json
import pathlib
import re
import sys
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
FACTS = ROOT / "artifacts" / "facts"
CONTRACTS_DIR = ROOT / "artifacts" / "autogenesis" / "producer-contracts"
SCHEMA = ROOT / "artifacts" / "ontology" / "producer-contract.schema.json"

CONTRACT_ID_RE = re.compile(r"^producer-contract-[a-z0-9]+(-[a-z0-9]+)*-v[0-9]+$")
FACT_ID_RE = re.compile(r"^F:[a-z0-9]+(-[a-z0-9]+)*$")

ROUTES = {"kernel-lane", "cas-bridge", "import"}

# A fact still needing proof in OUR ledger. Mirrors `fact-frontier.py`'s own
# `band()` unmet-dependency check (`status not in {"open","conjectured",
# "empirical"}` => already done) so "matches every open fact" means the same
# thing here as it does to the tool that will actually dispatch against it.
OPEN_STATUSES = {"open", "conjectured", "empirical"}

TOP_LEVEL_REQUIRED = {"schema_version", "id", "title", "route", "recipe", "shape", "non_examples"}
TOP_LEVEL_OPTIONAL = {"notes"}
RECIPE_REQUIRED = {"description"}
RECIPE_OPTIONAL = {"reference"}
SHAPE_REQUIRED = {"formal_language", "fragments"}
SHAPE_OPTIONAL = {"title_prefix", "statement_contains", "id_prefix"}
# At least one of these must be present, or the shape is narrowed only by
# language/fragment -- a claim over most of a fragment, not a shape.
SHAPE_NARROWING_KEYS = SHAPE_OPTIONAL
NON_EXAMPLE_REQUIRED = {"fact_id", "reason"}


class ContractError(RuntimeError):
    """A producer contract is malformed, unfalsifiable, or vacuous."""


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode()).hexdigest()


def exact_keys(value: Any, required: set[str], optional: set[str], label: str) -> None:
    if not isinstance(value, dict):
        raise ContractError(f"{label}: expected an object")
    keys = set(value)
    missing = required - keys
    if missing:
        raise ContractError(f"{label}: missing required key(s) {sorted(missing)}")
    extra = keys - required - optional
    if extra:
        raise ContractError(f"{label}: unexpected key(s) {sorted(extra)}")


def load_facts(facts_dir: pathlib.Path = FACTS) -> dict[str, dict]:
    facts: dict[str, dict] = {}
    if not facts_dir.is_dir():
        raise ContractError(f"no fact ledger at {facts_dir}")
    for path in sorted(facts_dir.glob("*.json")):
        fact = json.loads(path.read_text())
        fact_id = fact.get("id")
        if not isinstance(fact_id, str):
            raise ContractError(f"{path}: fact has no string id")
        if fact_id in facts:
            raise ContractError(f"duplicate fact id {fact_id!r}")
        facts[fact_id] = fact
    return facts


def shape_matches(shape: dict[str, Any], fact: dict[str, Any]) -> bool:
    """The executable predicate. Every present field is ANDed."""
    formal = fact.get("formal", {})
    if formal.get("language") not in shape["formal_language"]:
        return False
    if formal.get("fragment") not in shape["fragments"]:
        return False
    title_prefix = shape.get("title_prefix")
    if title_prefix is not None and not fact.get("title", "").startswith(title_prefix):
        return False
    statement_contains = shape.get("statement_contains")
    if statement_contains is not None and statement_contains not in formal.get("statement", ""):
        return False
    id_prefix = shape.get("id_prefix")
    if id_prefix is not None and not fact.get("id", "").startswith(id_prefix):
        return False
    return True


def validate_shape(shape: Any, label: str) -> None:
    exact_keys(shape, SHAPE_REQUIRED, SHAPE_OPTIONAL, label)
    for key in ("formal_language", "fragments"):
        value = shape[key]
        if not isinstance(value, list) or not value or not all(
            isinstance(v, str) and v for v in value
        ):
            raise ContractError(f"{label}.{key}: must be a non-empty list of non-empty strings")
    for key in SHAPE_OPTIONAL:
        if key in shape and (not isinstance(shape[key], str) or not shape[key]):
            raise ContractError(f"{label}.{key}: must be a non-empty string")
    if not any(key in shape for key in SHAPE_NARROWING_KEYS):
        raise ContractError(
            f"{label}: `formal_language`/`fragments` alone is too coarse a shape -- "
            f"at least one of {sorted(SHAPE_NARROWING_KEYS)} is required. A contract "
            "narrowed only by language and fragment is a near-fragment-wide claim, "
            "which is the vacuous-matcher defect one field short of tripping the "
            "explicit 'matches every open fact' guard."
        )


def validate_contract(
    contract: Any, facts: dict[str, dict], path: pathlib.Path | None = None
) -> None:
    label = str(path) if path is not None else contract.get("id", "<contract>")
    if not isinstance(contract, dict):
        raise ContractError(f"{label}: expected an object")
    exact_keys(contract, TOP_LEVEL_REQUIRED, TOP_LEVEL_OPTIONAL, label)

    if contract.get("schema_version") != 1:
        raise ContractError(f"{label}: schema_version must be 1")

    contract_id = contract["id"]
    if not isinstance(contract_id, str) or not CONTRACT_ID_RE.match(contract_id):
        raise ContractError(f"{label}: id {contract_id!r} does not match {CONTRACT_ID_RE.pattern}")

    if not isinstance(contract["title"], str) or not contract["title"]:
        raise ContractError(f"{contract_id}: title must be a non-empty string")

    if contract["route"] not in ROUTES:
        raise ContractError(f"{contract_id}: route must be one of {sorted(ROUTES)}")

    exact_keys(contract["recipe"], RECIPE_REQUIRED, RECIPE_OPTIONAL, f"{contract_id}.recipe")
    if not isinstance(contract["recipe"]["description"], str) or not contract["recipe"]["description"]:
        raise ContractError(f"{contract_id}.recipe.description: must be a non-empty string")
    if "reference" in contract["recipe"] and (
        not isinstance(contract["recipe"]["reference"], str) or not contract["recipe"]["reference"]
    ):
        raise ContractError(f"{contract_id}.recipe.reference: must be a non-empty string")

    shape = contract["shape"]
    validate_shape(shape, f"{contract_id}.shape")

    non_examples = contract["non_examples"]
    if not isinstance(non_examples, list) or not non_examples:
        raise ContractError(
            f"{contract_id}: non_examples must be a non-empty list -- ADR-0602's "
            "falsifiability requirement. A contract with nothing it provably does "
            "not match cannot be falsified."
        )
    seen_non_example_ids: set[str] = set()
    for entry in non_examples:
        exact_keys(entry, NON_EXAMPLE_REQUIRED, set(), f"{contract_id}.non_examples[]")
        fact_id = entry["fact_id"]
        if not isinstance(fact_id, str) or not FACT_ID_RE.match(fact_id):
            raise ContractError(f"{contract_id}: non_example fact_id {fact_id!r} is malformed")
        if fact_id in seen_non_example_ids:
            raise ContractError(f"{contract_id}: duplicate non_example fact_id {fact_id!r}")
        seen_non_example_ids.add(fact_id)
        if not isinstance(entry["reason"], str) or not entry["reason"]:
            raise ContractError(f"{contract_id}: non_example {fact_id} reason must be non-empty")
        fact = facts.get(fact_id)
        if fact is None:
            raise ContractError(
                f"{contract_id}: non_example {fact_id!r} does not resolve to any fact in "
                f"{FACTS} -- a non-example naming nothing real proves nothing."
            )
        # THE falsifiability check: EXECUTE the predicate, never trust `reason`.
        if shape_matches(shape, fact):
            raise ContractError(
                f"{contract_id}: non_example {fact_id!r} MATCHES its own shape predicate -- "
                "it is not a non-example at all, so this contract's falsifiability claim "
                "is false."
            )

    # THE vacuous-matcher guard: a shape claiming every open fact in the whole
    # ledger is not a capability claim over a shape, it is a blank check.
    open_ids = {fid for fid, fact in facts.items() if fact.get("epistemic_status") in OPEN_STATUSES}
    matched_open_ids = {fid for fid in open_ids if shape_matches(shape, facts[fid])}
    if open_ids and matched_open_ids == open_ids:
        raise ContractError(
            f"{contract_id}: shape predicate matches every open fact in the ledger "
            f"({len(open_ids)}) -- this is the vacuous-checker defect: a predicate "
            "that can never fail to admit an open fact makes no capability claim at all."
        )


def load_contracts(
    directory: pathlib.Path = CONTRACTS_DIR,
) -> list[tuple[pathlib.Path, dict[str, Any]]]:
    if not directory.is_dir():
        return []
    loaded: list[tuple[pathlib.Path, dict[str, Any]]] = []
    for path in sorted(directory.glob("*.json")):
        loaded.append((path, json.loads(path.read_text())))
    return loaded


def validate_contracts_dir(
    directory: pathlib.Path = CONTRACTS_DIR, facts: dict[str, dict] | None = None
) -> list[dict[str, Any]]:
    if facts is None:
        facts = load_facts()
    loaded = load_contracts(directory)
    contracts: list[dict[str, Any]] = []
    seen_ids: dict[str, pathlib.Path] = {}
    for path, contract in loaded:
        validate_contract(contract, facts, path)
        contract_id = contract["id"]
        if contract_id in seen_ids:
            raise ContractError(
                f"duplicate producer contract id {contract_id!r}: {seen_ids[contract_id]} and {path}"
            )
        seen_ids[contract_id] = path
        contracts.append(contract)
    return contracts


def main() -> int:
    try:
        facts = load_facts()
        contracts = validate_contracts_dir(facts=facts)
        ledger_digest = digest(
            [{"id": c["id"], "sha256": digest(c)} for c in sorted(contracts, key=lambda c: c["id"])]
        )
        print(f"PRODUCER_CONTRACTS_OK|contracts={len(contracts)}|registry={ledger_digest}")
        return 0
    except (OSError, json.JSONDecodeError, ContractError) as error:
        print(f"PRODUCER_CONTRACTS_ERROR|{error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
