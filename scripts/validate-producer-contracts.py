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

ADR-1510 ADDS A LIFECYCLE. A capability claim over an EMPTY population cannot
be falsified by any dispatch, which puts it in the same class as an operation
registry entry with no proof behind it -- the object ADR-0602 exists to
prevent one arrow upstream. Measured 2026-09-01, both seed contracts had been
written against families that another route (hand-authored kernel
declarations) finished within days: `int-modeq-family-v1` matches ZERO open
facts today, and `nat-coprime-family-v1` matches two, one of which is blind
held-out evaluation population that must never be closed. So a contract now
carries a `sizing` block recording the population it was measured against, and
three further guards, each expected to die under exactly one mutation:

  * no fact id in `sizing.matched_open_ready_fact_ids` may be a HELD-OUT
    nursery row. A contract sized against blind evaluation population is
    claiming capability over facts it is forbidden to discharge, and the
    partition is read from EVERY `nursery*.json` manifest, never from one --
    `nursery-v2-extension.json` exists and two other readers in this
    repository hardcode `nursery-v1.json` and are blind to it;
  * a contract whose LIVE population is empty must carry a `retirement`
    block. Live means: open, dependency-ready, not held-out, and not an
    outcome-blind mutation fixture -- a contract kept alive by a fact nobody
    may ever prove is exactly the unfalsifiable claim this guard is for;
  * a contract that DOES carry `retirement` must not still match live work.
    The inverse direction, so retirement cannot be used to silence the guard
    above while real targets remain.

`sizing.ledger_sha256` is PROVENANCE, not a live check: it is
`ledger_digest(facts)`, the sha256 over the canonical JSON of the sorted
`[[fact_id, epistemic_status], ...]` list, and it pins which ledger snapshot
the recorded count was taken over so the count can be re-derived. It is
deliberately NOT compared against the current ledger -- that would turn every
unrelated fact edit into a red gate. The LIVE check is the re-execution of the
shape predicate in `live_population`.

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
AUTOGENESIS = ROOT / "artifacts" / "autogenesis"
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

TOP_LEVEL_REQUIRED = {
    "schema_version",
    "id",
    "title",
    "route",
    "recipe",
    "shape",
    "non_examples",
    "sizing",
}
TOP_LEVEL_OPTIONAL = {"notes", "retirement"}
RECIPE_REQUIRED = {"description"}
RECIPE_OPTIONAL = {"reference"}
SIZING_REQUIRED = {"date", "ledger_sha256", "matched_open_ready_count"}
SIZING_OPTIONAL = {
    "matched_open_ready_fact_ids",
    "frontier_query",
    "note",
    "held_out_overlap_salt",
    "held_out_overlap_reviewed",
}
RETIREMENT_REQUIRED = {"date", "reason"}
RETIREMENT_OPTIONAL = {"superseded_by", "note"}
HELD_OUT_REVIEW_REQUIRED = {"digest", "date", "reason"}
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
DATE_RE = re.compile(r"^[0-9]{4}-[0-9]{2}-[0-9]{2}$")
# Every nursery manifest, not one. `nursery-v2-extension.json` preregisters a
# further 500 rows (190 held-out) and two other readers in this repository --
# `fact-frontier.py`'s `held_out_fact_ids` and this validator's own sibling
# test -- name `nursery-v1.json` literally and are blind to all of them.
NURSERY_GLOB = "nursery*.json"
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


def ledger_digest(facts: dict[str, dict]) -> str:
    """The provenance digest a `sizing` block pins its count to.

    sha256 over the canonical JSON of the sorted
    `[[fact_id, epistemic_status], ...]` list. Re-derivable from any checkout
    in one line, which is the point: a recorded count nobody can re-take is
    not a measurement.
    """
    return digest(
        sorted([fid, fact.get("epistemic_status")] for fid, fact in facts.items())
    )


def held_out_fact_ids(directory: pathlib.Path = AUTOGENESIS) -> frozenset[str]:
    """Fact ids in a blind HELD-OUT nursery partition, read from EVERY
    `nursery*.json` manifest in `directory`.

    The split key is `<family>:<statement-shape>`, so a proof route for one
    member is evidence about its siblings and closing ONE spends the whole
    family (ADR-0542). Reading a single manifest is how this goes wrong:
    measured 2026-09-01, `fact-frontier.py` selected
    `F:ml430-nat-coprime-factorizationlcmleft-factorizationlcmright-e7db70ce`
    as `admissible_via_contract` with `outcome: selected` while that fact is
    `partition: held-out` in `nursery-v2-extension.json` -- a manifest that
    did not exist when the single-file reader was written.

    Degrades to whatever it could read: a manifest that is missing or
    unparseable contributes nothing rather than crashing the gate. That is
    fail-OPEN for this one input, which is why it is not the only guard --
    but a held-out row that IS readable can never be silently admitted.
    """
    ids: set[str] = set()
    if not directory.is_dir():
        return frozenset()
    for path in sorted(directory.glob(NURSERY_GLOB)):
        try:
            raw = json.loads(path.read_text())
        except (OSError, ValueError):
            continue
        for entry in raw.get("entries", []) if isinstance(raw, dict) else []:
            if isinstance(entry, dict) and entry.get("partition") == "held-out":
                fact_id = entry.get("fact_id")
                if isinstance(fact_id, str):
                    ids.add(fact_id)
    return frozenset(ids)


def digest_held_out_fact_id(fact_id: str, salt: str) -> str:
    """Salted digest of a held-out fact id (ADR-1550's redaction pattern).

    A contract's `sizing.held_out_overlap_reviewed` entries key by this
    digest, never by the plain id, so a `grep` for a held-out id -- or a
    producer reading a committed contract file -- finds nothing here. The
    salt is committed alongside the digests in `sizing.held_out_overlap_salt`;
    committing it does not make the digest reversible, and a reviewer who
    already holds the plain id can still confirm it produced the recorded
    digest. Same construction as `check-partition-edges.py`'s
    `digest_fact_id`, kept local rather than imported: the two tools redact
    unrelated artifacts and must not come to depend on one module for it.
    """
    return hashlib.sha256(f"{salt}:{fact_id}".encode()).hexdigest()


def held_out_shape_matches(
    shape: dict[str, Any], facts: dict[str, dict], held_out: frozenset[str]
) -> list[str]:
    """Held-out fact ids this shape predicate CURRENTLY matches.

    Derived at call time from the live ledger and the live nursery manifests
    -- never from a literal id list -- so a contract that starts overlapping
    a NEW held-out row is caught the next time this runs, and a contract
    whose overlap resolves (the row proves, the shape narrows) drops out with
    no file to edit. `fid in facts` guards a manifest entry that names a fact
    with no ledger file yet; such a row cannot be shape-matched at all.
    """
    return sorted(
        fid for fid in held_out if fid in facts and shape_matches(shape, facts[fid])
    )


def is_mutation_fixture(fact_id: str) -> bool:
    """An outcome-blind mutation negative control, never a target.

    Mirrors `fact-frontier.py`'s own `mutation_kind`: `F:ml430-mutation-*`
    rows are deliberate perturbations of pinned propositions and several are
    FALSE. A contract whose only remaining matches are mutation fixtures has
    no live population, however many rows the raw predicate returns.
    """
    return "-mutation-" in fact_id


def live_population(
    shape: dict[str, Any],
    facts: dict[str, dict],
    held_out: frozenset[str] | None = None,
) -> list[str]:
    """Fact ids this shape could actually be dispatched at, today.

    Open AND dependency-ready AND not held-out AND not a mutation fixture.
    Each exclusion is a fact the contract may not be dispatched at for a
    reason that is permanent, so counting them would keep an exhausted
    contract alive on work nobody may ever do.
    """
    if held_out is None:
        held_out = held_out_fact_ids()
    live: list[str] = []
    for fact_id, fact in facts.items():
        if fact.get("epistemic_status") not in OPEN_STATUSES:
            continue
        if fact_id in held_out or is_mutation_fixture(fact_id):
            continue
        if not shape_matches(shape, fact):
            continue
        depends = fact.get("depends_on") or []
        if any(
            dep not in facts or facts[dep].get("epistemic_status") in OPEN_STATUSES
            for dep in depends
        ):
            continue
        live.append(fact_id)
    return sorted(live)


def validate_sizing(sizing: Any, label: str) -> None:
    """Structural validation of the ADR-1510 `sizing` block.

    The population semantics are checked in `validate_contract`; this only
    establishes that the record is well formed enough to be read.
    """
    exact_keys(sizing, SIZING_REQUIRED, SIZING_OPTIONAL, label)
    if not isinstance(sizing["date"], str) or not DATE_RE.match(sizing["date"]):
        raise ContractError(f"{label}.date: must be an ISO date (YYYY-MM-DD)")
    if not isinstance(sizing["ledger_sha256"], str) or not SHA256_RE.match(
        sizing["ledger_sha256"]
    ):
        raise ContractError(
            f"{label}.ledger_sha256: must be a 64-character lowercase sha256 digest -- "
            "the ledger snapshot the recorded count was taken over, so the count "
            "can be re-derived rather than believed."
        )
    count = sizing["matched_open_ready_count"]
    if not isinstance(count, int) or isinstance(count, bool) or count < 0:
        raise ContractError(f"{label}.matched_open_ready_count: must be a non-negative integer")
    ids = sizing.get("matched_open_ready_fact_ids")
    if ids is not None:
        if not isinstance(ids, list) or not all(
            isinstance(i, str) and FACT_ID_RE.match(i) for i in ids
        ):
            raise ContractError(
                f"{label}.matched_open_ready_fact_ids: must be a list of well-formed fact ids"
            )
        if len(ids) != count:
            raise ContractError(
                f"{label}: matched_open_ready_count is {count} but "
                f"matched_open_ready_fact_ids lists {len(ids)} -- the count and the "
                "population it names must agree, or neither is a measurement."
            )
    for key in ("frontier_query", "note"):
        if key in sizing and (not isinstance(sizing[key], str) or not sizing[key]):
            raise ContractError(f"{label}.{key}: must be a non-empty string")
    salt = sizing.get("held_out_overlap_salt")
    if salt is not None and (not isinstance(salt, str) or not salt):
        raise ContractError(f"{label}.held_out_overlap_salt: must be a non-empty string")
    reviewed = sizing.get("held_out_overlap_reviewed")
    if reviewed is not None:
        if not isinstance(reviewed, list):
            raise ContractError(
                f"{label}.held_out_overlap_reviewed: must be a list of "
                "{digest, date, reason} objects"
            )
        seen_digests: set[str] = set()
        for entry in reviewed:
            entry_label = f"{label}.held_out_overlap_reviewed[]"
            exact_keys(entry, HELD_OUT_REVIEW_REQUIRED, set(), entry_label)
            entry_digest = entry["digest"]
            if not isinstance(entry_digest, str) or not SHA256_RE.match(entry_digest):
                raise ContractError(
                    f"{entry_label}.digest: must be a 64-character lowercase sha256 "
                    "digest -- a salted digest of the held-out fact id (ADR-1550), "
                    "never the plain id."
                )
            if entry_digest in seen_digests:
                raise ContractError(f"{entry_label}: duplicate digest {entry_digest}")
            seen_digests.add(entry_digest)
            if not isinstance(entry["date"], str) or not DATE_RE.match(entry["date"]):
                raise ContractError(f"{entry_label}.date: must be an ISO date (YYYY-MM-DD)")
            if not isinstance(entry["reason"], str) or not entry["reason"]:
                raise ContractError(f"{entry_label}.reason: must be a non-empty string")


def validate_retirement(retirement: Any, label: str) -> None:
    exact_keys(retirement, RETIREMENT_REQUIRED, RETIREMENT_OPTIONAL, label)
    if not isinstance(retirement["date"], str) or not DATE_RE.match(retirement["date"]):
        raise ContractError(f"{label}.date: must be an ISO date (YYYY-MM-DD)")
    for key in ("reason", "superseded_by", "note"):
        if key in retirement and (
            not isinstance(retirement[key], str) or not retirement[key]
        ):
            raise ContractError(f"{label}.{key}: must be a non-empty string")


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
    contract: Any,
    facts: dict[str, dict],
    path: pathlib.Path | None = None,
    held_out: frozenset[str] | None = None,
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

    validate_sizing(contract["sizing"], f"{contract_id}.sizing")
    retirement = contract.get("retirement")
    if retirement is not None:
        validate_retirement(retirement, f"{contract_id}.retirement")

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

    # ------------------------------------------------------------------
    # ADR-1510 rule 1: a contract is sized by the frontier and retires when
    # that population empties. Three guards, each able to fail on its own.
    # ------------------------------------------------------------------
    if held_out is None:
        held_out = held_out_fact_ids()

    # (a) A contract may not be SIZED against blind evaluation population.
    sized_held_out = sorted(
        set(contract["sizing"].get("matched_open_ready_fact_ids") or []) & set(held_out)
    )
    if sized_held_out:
        raise ContractError(
            f"{contract_id}: sizing.matched_open_ready_fact_ids names HELD-OUT "
            f"fact(s) {sized_held_out} -- blind evaluation population (ADR-0542), "
            "which this contract is forbidden to discharge. A capability claim "
            "counted against facts nobody may close cannot be falsified by any "
            "dispatch. Partition read from every artifacts/autogenesis/nursery*.json."
        )

    live = live_population(shape, facts, held_out)

    # (b) An exhausted contract must be retired.
    if not live and retirement is None:
        raise ContractError(
            f"{contract_id}: shape predicate matches ZERO live facts (open, "
            "dependency-ready, not held-out, not a mutation fixture) but the "
            "contract is not retired -- ADR-1510 rule 1. A capability claim over "
            "an empty population cannot be falsified by any dispatch, which is the "
            "same unfalsifiable object ADR-0602 exists to prevent one arrow "
            "upstream. Add a `retirement` block, or supersede this contract with a "
            "-vN whose shape covers live work."
        )

    # (c) ...and the inverse: retirement may not silence a live contract.
    if live and retirement is not None:
        raise ContractError(
            f"{contract_id}: marked retired but its shape still matches "
            f"{len(live)} live fact(s) {live[:5]} -- retirement records that a "
            "population emptied, so using it while real targets remain removes the "
            "claim without removing the work."
        )

    # (d) A contract's shape predicate is checked against every held-out row,
    # not only the ones it names in `matched_open_ready_fact_ids` -- (a)
    # above catches a contract that CLAIMS a held-out fact, this catches one
    # whose predicate happens to ALSO match one it never claimed. Every such
    # overlap must carry a dated, reasoned entry in
    # `sizing.held_out_overlap_reviewed`, keyed by a salted digest
    # (`digest_held_out_fact_id`, ADR-1550's redaction pattern) so the review
    # record itself never names the held-out id. Derived from the live ledger
    # and the live nursery manifests every run -- never from a literal id
    # list in this file or in a test -- so a NEW overlap is caught the first
    # time this validator runs after it appears, and a resolved overlap drops
    # the requirement with no file to edit.
    held_out_matches = held_out_shape_matches(shape, facts, held_out)
    if held_out_matches:
        salt = contract["sizing"].get("held_out_overlap_salt")
        if not isinstance(salt, str) or not salt:
            raise ContractError(
                f"{contract_id}: shape predicate matches {len(held_out_matches)} "
                "HELD-OUT fact(s) but sizing.held_out_overlap_salt is missing -- "
                "an overlap with blind evaluation population must be reviewed and "
                "recorded as a salted digest in sizing.held_out_overlap_reviewed "
                "(ADR-1550), never as a plain id."
            )
        reviewed_digests = {
            entry["digest"]
            for entry in contract["sizing"].get("held_out_overlap_reviewed") or []
        }
        unreviewed = sorted(
            digest_held_out_fact_id(fact_id, salt) for fact_id in held_out_matches
        )
        missing = [d for d in unreviewed if d not in reviewed_digests]
        if missing:
            raise ContractError(
                f"{contract_id}: shape predicate matches {len(missing)} HELD-OUT "
                f"fact(s) with no reviewed entry in sizing.held_out_overlap_reviewed "
                f"(salted digest(s) {missing}) -- a contract cannot silently start "
                "matching blind evaluation population. Add a dated review entry "
                "keyed by digest_held_out_fact_id(fact_id, sizing.held_out_overlap_salt), "
                "naming the reason (e.g. the row is held-out and this contract is "
                "retired/does not dispatch it) -- never by fact id."
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
    held_out = held_out_fact_ids()
    for path, contract in loaded:
        validate_contract(contract, facts, path, held_out)
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
        registry_digest = digest(
            [{"id": c["id"], "sha256": digest(c)} for c in sorted(contracts, key=lambda c: c["id"])]
        )
        retired = sum(1 for c in contracts if c.get("retirement") is not None)
        print(
            f"PRODUCER_CONTRACTS_OK|contracts={len(contracts)}|retired={retired}"
            f"|registry={registry_digest}"
        )
        return 0
    except (OSError, json.JSONDecodeError, ContractError) as error:
        print(f"PRODUCER_CONTRACTS_ERROR|{error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
