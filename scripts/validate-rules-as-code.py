#!/usr/bin/env python3
"""Validate Rules-as-Code Verification Lab example packs."""

from __future__ import annotations

import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
SCHEMA = ROOT / "artifacts" / "ontology" / "rules-core.schema.json"
EXAMPLES_ROOT = ROOT / "docs" / "rules-as-code" / "examples"


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


def require_string(context: str, value: Any) -> str:
    if not isinstance(value, str) or not value:
        fail(f"{context} must be a non-empty string")
    return value


def require_int(context: str, value: Any) -> int:
    if not isinstance(value, int):
        fail(f"{context} must be an integer")
    return value


def require_bool(context: str, value: Any) -> bool:
    if not isinstance(value, bool):
        fail(f"{context} must be a boolean")
    return value


def check_repo_path(context: str, value: Any) -> str:
    path_text = require_string(context, value)
    path = ROOT / path_text
    if not path.exists():
        fail(f"{context} references missing path {path_text}")
    return path_text


@dataclass(frozen=True)
class BenefitFacts:
    age: int
    income: int
    resident: bool
    veteran: bool
    sanctioned: bool
    application_date: str


@dataclass(frozen=True)
class AuthorizationFacts:
    user_tenant: int
    resource_tenant: int
    role: str
    action: str
    explicit_deny: bool
    policy_version: int


def benefit_facts_from_json(context: str, value: Any) -> BenefitFacts:
    if not isinstance(value, dict):
        fail(f"{context} must be an object")
    require_keys(
        context,
        value,
        {"age", "income", "resident", "veteran", "sanctioned", "application_date"},
    )
    return BenefitFacts(
        age=require_int(f"{context}.age", value["age"]),
        income=require_int(f"{context}.income", value["income"]),
        resident=require_bool(f"{context}.resident", value["resident"]),
        veteran=require_bool(f"{context}.veteran", value["veteran"]),
        sanctioned=require_bool(f"{context}.sanctioned", value["sanctioned"]),
        application_date=require_date(
            f"{context}.application_date", value["application_date"]
        ),
    )


def authorization_facts_from_json(context: str, value: Any) -> AuthorizationFacts:
    if not isinstance(value, dict):
        fail(f"{context} must be an object")
    require_keys(
        context,
        value,
        {
            "user_tenant",
            "resource_tenant",
            "role",
            "action",
            "explicit_deny",
            "policy_version",
        },
    )
    return AuthorizationFacts(
        user_tenant=require_int(f"{context}.user_tenant", value["user_tenant"]),
        resource_tenant=require_int(
            f"{context}.resource_tenant", value["resource_tenant"]
        ),
        role=require_string(f"{context}.role", value["role"]),
        action=require_string(f"{context}.action", value["action"]),
        explicit_deny=require_bool(f"{context}.explicit_deny", value["explicit_deny"]),
        policy_version=require_int(f"{context}.policy_version", value["policy_version"]),
    )


def standard_threshold(date: str, params: dict[str, Any]) -> int:
    return (
        params["standard_threshold_before"]
        if date < params["change_date"]
        else params["standard_threshold_after"]
    )


def benefit_eligible(facts: BenefitFacts, params: dict[str, Any]) -> bool:
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


def authorization_allows(facts: AuthorizationFacts) -> bool:
    if facts.explicit_deny:
        return False
    if facts.user_tenant != facts.resource_tenant:
        return False
    if facts.role == "admin":
        return facts.action in {"read", "export"}
    if facts.role == "analyst":
        if facts.action == "read":
            return True
        if facts.action == "export":
            return facts.policy_version >= 2
    return False


def validate_metadata(pack_dir: Path, metadata: dict[str, Any]) -> None:
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
        path = pack_dir / citation["uri"].split("#", 1)[0]
        if not path.exists():
            fail(f"citation {citation['label']} references missing file {citation['uri']}")
    if len(seen_labels) != len(metadata["source_citations"]):
        fail("source citation labels must be unique")

    checks = metadata["checks"]
    if not isinstance(checks, list) or not checks:
        fail("metadata.checks must be a non-empty list")
    if len(set(checks)) != len(checks):
        fail("metadata.checks must be unique")
    for check_id in checks:
        if not isinstance(check_id, str) or not check_id:
            fail("metadata.checks entries must be non-empty strings")


def validate_expected(pack_dir: Path, metadata: dict[str, Any], expected: dict[str, Any]) -> None:
    require_keys(
        "expected",
        expected,
        {"schema_version", "pack_id", "parameters", "sample_domain", "witnesses", "checks"},
    )
    if expected["schema_version"] != 1:
        fail("expected.schema_version must be 1")
    if expected["pack_id"] != metadata["id"]:
        fail("expected.pack_id must match metadata.id")

    citations = {citation["label"] for citation in metadata["source_citations"]}
    pack_id = metadata["id"]
    if pack_id == "benefit_eligibility_v0":
        witness_ids = validate_benefit_expected(expected, citations)
    elif pack_id == "authorization_policy_v0":
        witness_ids = validate_authorization_expected(expected, citations)
    else:
        fail(f"unsupported rules-as-code pack id {pack_id}")

    checks = {check["id"]: check for check in expected["checks"]}
    if set(checks) != set(metadata["checks"]):
        fail("expected.checks must match metadata.checks")
    for check_id, check in checks.items():
        require_keys(
            f"checks.{check_id}",
            check,
            {"id", "expected_result", "validation", "proof_status"},
        )
        if check["expected_result"] not in {"sat", "unsat", "unknown"}:
            fail(f"{check_id}.expected_result is invalid")
        if check["proof_status"] == "proof-gap" and "proof_gap" not in check:
            fail(f"{check_id} marks proof-gap without proof_gap text")
        for citation in check.get("source_citations", []):
            if citation not in citations:
                fail(f"{check_id} cites unknown label {citation}")
        for witness_id in check.get("witnesses", []):
            if witness_id not in witness_ids:
                fail(f"{check_id} references unknown witness {witness_id}")
        if check["proof_status"] == "checked":
            validate_solver_fixture(pack_dir, check)


def validate_benefit_expected(expected: dict[str, Any], citations: set[str]) -> set[str]:
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
        expected_eligible = require_bool(
            f"{witness_id}.expected_eligible", witness["expected_eligible"]
        )
        facts = benefit_facts_from_json(f"{witness_id}.facts", witness["facts"])
        actual = benefit_eligible(facts, params)
        if actual != expected_eligible:
            fail(f"{witness_id} replay mismatch: expected {expected_eligible}, got {actual}")
        validate_citations(witness_id, witness["source_citations"], citations)

    validate_benefit_finite_sample(expected["sample_domain"], params)
    return witness_ids


def validate_authorization_expected(expected: dict[str, Any], citations: set[str]) -> set[str]:
    params = expected["parameters"]
    require_keys("parameters", params, {"policy_versions", "roles", "actions", "tenants"})
    if params["policy_versions"] != [1, 2]:
        fail("authorization parameters.policy_versions must be [1, 2]")
    if params["roles"] != ["analyst", "admin"]:
        fail("authorization parameters.roles must be ['analyst', 'admin']")
    if params["actions"] != ["read", "export", "delete"]:
        fail("authorization parameters.actions must be ['read', 'export', 'delete']")
    if params["tenants"] != [1, 2]:
        fail("authorization parameters.tenants must be [1, 2]")

    witness_ids: set[str] = set()
    for index, witness in enumerate(expected["witnesses"]):
        require_keys(
            f"witnesses[{index}]",
            witness,
            {"id", "facts", "expected_allow", "source_citations", "explanation"},
        )
        witness_id = witness["id"]
        if witness_id in witness_ids:
            fail(f"duplicate witness id {witness_id}")
        witness_ids.add(witness_id)
        expected_allow = require_bool(
            f"{witness_id}.expected_allow", witness["expected_allow"]
        )
        facts = authorization_facts_from_json(f"{witness_id}.facts", witness["facts"])
        actual = authorization_allows(facts)
        if actual != expected_allow:
            fail(f"{witness_id} replay mismatch: expected {expected_allow}, got {actual}")
        validate_citations(witness_id, witness["source_citations"], citations)

    validate_authorization_finite_sample(expected["sample_domain"], params)
    return witness_ids


def validate_citations(context: str, labels: Any, citations: set[str]) -> None:
    if not isinstance(labels, list):
        fail(f"{context}.source_citations must be a list")
    missing = sorted(set(labels) - citations)
    if missing:
        fail(f"{context} cites unknown labels: {', '.join(missing)}")


def validate_solver_fixture(pack_dir: Path, check: dict[str, Any]) -> None:
    check_id = check["id"]
    if check["expected_result"] != "unsat":
        fail(f"{check_id} checked solver fixture must be unsat")
    if check["validation"] != "bool_qf_lia_solver_regression":
        fail(f"{check_id} must use bool_qf_lia_solver_regression validation")
    data = check.get("data")
    if not isinstance(data, dict):
        fail(f"{check_id} checked solver fixture must include data")
    artifact = check_repo_path(f"{check_id}.data.smt2_artifact", data.get("smt2_artifact"))
    artifact_path = ROOT / artifact
    if pack_dir not in artifact_path.parents:
        fail(f"{check_id}.data.smt2_artifact must live under the rule pack")
    regression = require_string(
        f"{check_id}.data.proof_regression", data.get("proof_regression")
    )
    if "rules_as_code_examples" not in regression:
        fail(f"{check_id}.data.proof_regression must link rules_as_code_examples")
    certificate = require_string(f"{check_id}.data.certificate", data.get("certificate"))
    if "certified evidence" not in certificate or "Evidence::check" not in certificate:
        fail(f"{check_id}.data.certificate must document checked evidence")


def validate_benefit_finite_sample(sample_domain: dict[str, Any], params: dict[str, Any]) -> None:
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
                            facts = BenefitFacts(
                                age, income, resident, veteran, sanctioned, date
                            )
                            is_eligible = benefit_eligible(facts, params)
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
                            facts = BenefitFacts(
                                age, income, resident, veteran, sanctioned, date
                            )
                            is_eligible = benefit_eligible(facts, params)
                            if prior_ineligible and is_eligible:
                                fail(f"monotonicity failed for {facts}")
                            if not is_eligible:
                                prior_ineligible = True

    if checked == 0:
        fail("benefit finite sample was empty")


def validate_authorization_finite_sample(
    sample_domain: dict[str, Any], params: dict[str, Any]
) -> None:
    require_keys(
        "sample_domain",
        sample_domain,
        {"user_tenants", "resource_tenants", "roles", "actions", "policy_versions", "booleans"},
    )
    if sample_domain["booleans"] != [False, True]:
        fail("authorization sample_domain.booleans must be [false, true]")

    checked = 0
    for user_tenant in sample_domain["user_tenants"]:
        for resource_tenant in sample_domain["resource_tenants"]:
            for role in sample_domain["roles"]:
                for action in sample_domain["actions"]:
                    for explicit_deny in sample_domain["booleans"]:
                        previous = None
                        for policy_version in sample_domain["policy_versions"]:
                            facts = AuthorizationFacts(
                                user_tenant,
                                resource_tenant,
                                role,
                                action,
                                explicit_deny,
                                policy_version,
                            )
                            allow = authorization_allows(facts)
                            if user_tenant != resource_tenant and allow:
                                fail(f"tenant isolation failed for {facts}")
                            if explicit_deny and allow:
                                fail(f"explicit deny precedence failed for {facts}")
                            if role == "admin" and user_tenant != resource_tenant and allow:
                                fail(f"admin tenant guard failed for {facts}")
                            if previous is not None and previous != allow:
                                intended = (
                                    role == "analyst"
                                    and action == "export"
                                    and not explicit_deny
                                    and user_tenant == resource_tenant
                                )
                                if not intended:
                                    fail(f"unintended version delta for {facts}")
                            previous = allow
                            checked += 1

    for key in ("roles", "actions", "policy_versions"):
        if sample_domain[key] != params[key]:
            fail(f"authorization sample_domain.{key} must match parameters.{key}")
    if checked == 0:
        fail("authorization finite sample was empty")


def validate_pack(pack_dir: Path) -> str:
    metadata_path = pack_dir / "metadata.json"
    expected_path = pack_dir / "expected.json"
    metadata = load_json(metadata_path)
    expected = load_json(expected_path)
    if not isinstance(metadata, dict) or not isinstance(expected, dict):
        fail("metadata and expected artifacts must be JSON objects")
    validate_metadata(pack_dir, metadata)
    validate_expected(pack_dir, metadata, expected)
    return metadata["id"]


def main() -> int:
    load_json(SCHEMA)
    pack_dirs = sorted(path.parent for path in EXAMPLES_ROOT.glob("*/metadata.json"))
    if not pack_dirs:
        fail("no rules-as-code example packs found")
    pack_ids = [validate_pack(pack_dir) for pack_dir in pack_dirs]
    print(f"validated {len(pack_ids)} rules-as-code pack(s): {', '.join(pack_ids)}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except ValidationError as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(1)
