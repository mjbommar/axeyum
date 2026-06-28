#!/usr/bin/env python3
"""Validate the first Rules-as-Code Verification Lab pack."""

from __future__ import annotations

import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
SCHEMA = ROOT / "artifacts" / "ontology" / "rules-core.schema.json"
PACK = ROOT / "docs" / "rules-as-code" / "examples" / "benefit-eligibility-v0"
METADATA = PACK / "metadata.json"
EXPECTED = PACK / "expected.json"


class ValidationError(Exception):
    pass


def fail(message: str) -> None:
    raise ValidationError(message)


def load_json(path: Path) -> Any:
    try:
        with path.open("r", encoding="utf-8") as handle:
            return json.load(handle)
    except json.JSONDecodeError as error:
        fail(f"{path.relative_to(ROOT)} is invalid JSON: {error}")


def require_keys(context: str, value: dict[str, Any], keys: set[str]) -> None:
    missing = sorted(keys - set(value))
    if missing:
        fail(f"{context} missing keys: {', '.join(missing)}")


def require_date(context: str, value: Any) -> str:
    if not isinstance(value, str) or not re.fullmatch(r"\d{4}-\d{2}-\d{2}", value):
        fail(f"{context} must be YYYY-MM-DD")
    return value


@dataclass(frozen=True)
class Facts:
    age: int
    income: int
    resident: bool
    veteran: bool
    sanctioned: bool
    application_date: str


def facts_from_json(context: str, value: Any) -> Facts:
    if not isinstance(value, dict):
        fail(f"{context} must be an object")
    require_keys(
        context,
        value,
        {"age", "income", "resident", "veteran", "sanctioned", "application_date"},
    )
    for key in ("age", "income"):
        if not isinstance(value[key], int):
            fail(f"{context}.{key} must be an integer")
    for key in ("resident", "veteran", "sanctioned"):
        if not isinstance(value[key], bool):
            fail(f"{context}.{key} must be a boolean")
    return Facts(
        age=value["age"],
        income=value["income"],
        resident=value["resident"],
        veteran=value["veteran"],
        sanctioned=value["sanctioned"],
        application_date=require_date(f"{context}.application_date", value["application_date"]),
    )


def standard_threshold(date: str, params: dict[str, Any]) -> int:
    return (
        params["standard_threshold_before"]
        if date < params["change_date"]
        else params["standard_threshold_after"]
    )


def eligible(facts: Facts, params: dict[str, Any]) -> bool:
    standard = standard_threshold(facts.application_date, params)
    veteran_threshold = standard + params["veteran_bonus"]
    return (
        facts.resident
        and facts.age >= 18
        and not facts.sanctioned
        and (
            facts.income <= standard
            or (facts.veteran and facts.income <= veteran_threshold)
        )
    )


def validate_metadata(metadata: dict[str, Any]) -> None:
    require_keys(
        "metadata",
        metadata,
        {
            "schema_version",
            "id",
            "title",
            "domain",
            "jurisdiction",
            "source_citations",
            "effective_interval",
            "actors",
            "inputs",
            "outputs",
            "checks",
            "axeyum_fragments",
            "proof_expectation",
        },
    )
    if metadata["schema_version"] != 1:
        fail("metadata.schema_version must be 1")
    if not re.fullmatch(r"[a-z0-9_]+", metadata["id"]):
        fail("metadata.id must be lowercase snake case")
    seen_labels: set[str] = set()
    for index, citation in enumerate(metadata["source_citations"]):
        require_keys(f"source_citations[{index}]", citation, {"label", "uri"})
        seen_labels.add(citation["label"])
        path = PACK / citation["uri"].split("#", 1)[0]
        if not path.exists():
            fail(f"citation {citation['label']} references missing file {citation['uri']}")
    if len(seen_labels) != len(metadata["source_citations"]):
        fail("source citation labels must be unique")
    checks = set(metadata["checks"])
    expected = {
        "consistency",
        "coverage",
        "threshold_cliff",
        "monotonicity",
        "temporal_transition",
        "implementation_equivalence",
    }
    if checks != expected:
        fail(f"metadata.checks mismatch: {sorted(checks)}")


def validate_expected(metadata: dict[str, Any], expected: dict[str, Any]) -> None:
    require_keys(
        "expected",
        expected,
        {"schema_version", "pack_id", "parameters", "sample_domain", "witnesses", "checks"},
    )
    if expected["schema_version"] != 1:
        fail("expected.schema_version must be 1")
    if expected["pack_id"] != metadata["id"]:
        fail("expected.pack_id must match metadata.id")

    params = expected["parameters"]
    require_keys(
        "parameters",
        params,
        {
            "change_date",
            "standard_threshold_before",
            "standard_threshold_after",
            "veteran_bonus",
        },
    )
    require_date("parameters.change_date", params["change_date"])
    for key in ("standard_threshold_before", "standard_threshold_after", "veteran_bonus"):
        if not isinstance(params[key], int) or params[key] < 0:
            fail(f"parameters.{key} must be a non-negative integer")

    citations = {citation["label"] for citation in metadata["source_citations"]}
    witness_ids: set[str] = set()
    for index, witness in enumerate(expected["witnesses"]):
        require_keys(
            f"witnesses[{index}]",
            witness,
            {"id", "facts", "expected_eligible", "source_citations", "explanation"},
        )
        witness_id = witness["id"]
        if witness_id in witness_ids:
            fail(f"duplicate witness id {witness_id}")
        witness_ids.add(witness_id)
        if not isinstance(witness["expected_eligible"], bool):
            fail(f"{witness_id}.expected_eligible must be boolean")
        facts = facts_from_json(f"{witness_id}.facts", witness["facts"])
        actual = eligible(facts, params)
        if actual != witness["expected_eligible"]:
            fail(f"{witness_id} replay mismatch: expected {witness['expected_eligible']}, got {actual}")
        missing = sorted(set(witness["source_citations"]) - citations)
        if missing:
            fail(f"{witness_id} cites unknown labels: {', '.join(missing)}")

    checks = {check["id"]: check for check in expected["checks"]}
    if set(checks) != set(metadata["checks"]):
        fail("expected.checks must match metadata.checks")
    for check_id, check in checks.items():
        require_keys(f"checks.{check_id}", check, {"id", "expected_result", "validation", "proof_status"})
        if check["expected_result"] not in {"sat", "unsat", "unknown"}:
            fail(f"{check_id}.expected_result is invalid")
        if check["proof_status"] == "proof-gap" and "proof_gap" not in check:
            fail(f"{check_id} marks proof-gap without proof_gap text")
        for witness_id in check.get("witnesses", []):
            if witness_id not in witness_ids:
                fail(f"{check_id} references unknown witness {witness_id}")

    validate_finite_sample(expected["sample_domain"], params)


def validate_finite_sample(sample_domain: dict[str, Any], params: dict[str, Any]) -> None:
    require_keys("sample_domain", sample_domain, {"ages", "incomes", "dates", "booleans"})
    ages = sample_domain["ages"]
    incomes = sorted(sample_domain["incomes"])
    dates = sample_domain["dates"]
    booleans = sample_domain["booleans"]
    if booleans != [False, True]:
        fail("sample_domain.booleans must be [false, true]")
    for date in dates:
        require_date("sample_domain.dates[]", date)

    checked = 0
    for age in ages:
        for income in incomes:
            for date in dates:
                for resident in booleans:
                    for veteran in booleans:
                        for sanctioned in booleans:
                            facts = Facts(age, income, resident, veteran, sanctioned, date)
                            is_eligible = eligible(facts, params)
                            is_ineligible = not is_eligible
                            if is_eligible and is_ineligible:
                                fail(f"consistency failed for {facts}")
                            if not (is_eligible or is_ineligible):
                                fail(f"coverage failed for {facts}")
                            checked += 1

    for age in ages:
        for date in dates:
            for resident in booleans:
                for veteran in booleans:
                    for sanctioned in booleans:
                        prior_ineligible = False
                        for income in incomes:
                            facts = Facts(age, income, resident, veteran, sanctioned, date)
                            is_eligible = eligible(facts, params)
                            if prior_ineligible and is_eligible:
                                fail(f"monotonicity failed for {facts}")
                            if not is_eligible:
                                prior_ineligible = True

    if checked == 0:
        fail("finite sample was empty")


def main() -> int:
    load_json(SCHEMA)
    metadata = load_json(METADATA)
    expected = load_json(EXPECTED)
    if not isinstance(metadata, dict) or not isinstance(expected, dict):
        fail("metadata and expected artifacts must be JSON objects")
    validate_metadata(metadata)
    validate_expected(metadata, expected)
    print(
        "validated rules-as-code pack "
        f"{metadata['id']} with {len(expected['witnesses'])} replayed witnesses"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except ValidationError as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(1)
