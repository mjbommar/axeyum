#!/usr/bin/env python3
"""Validate Rules-as-Code Verification Lab example packs."""

from __future__ import annotations

import json
import re
import sys
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
SCHEMA = ROOT / "artifacts" / "ontology" / "rules-core.schema.json"
EXAMPLES_ROOT = ROOT / "docs" / "rules-as-code" / "examples"
GENERATED_QUERIES_ROOT = ROOT / "docs" / "rules-as-code" / "generated" / "queries"


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


def require_rational(context: str, value: Any) -> Fraction:
    if isinstance(value, bool):
        fail(f"{context} must not be a boolean")
    if isinstance(value, int):
        return Fraction(value, 1)
    if not isinstance(value, str) or not re.fullmatch(r"-?\d+(?:/[1-9]\d*)?", value):
        fail(f"{context} must be an integer or rational string")
    return Fraction(value)


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


@dataclass(frozen=True)
class TaxBenefitFacts:
    income: int
    household_size: int
    application_date: str


@dataclass(frozen=True)
class ProcurementFacts:
    bid_amount: int
    quality_score: int
    small_business: bool
    debarred: bool
    received_date: str


@dataclass(frozen=True)
class GrantAllocationFacts:
    shelter_share: Fraction
    clinic_share: Fraction
    admin_share: Fraction


@dataclass(frozen=True)
class CategoryEquivalenceFacts:
    applicant_category: str
    program: str


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


def tax_benefit_facts_from_json(context: str, value: Any) -> TaxBenefitFacts:
    if not isinstance(value, dict):
        fail(f"{context} must be an object")
    require_keys(context, value, {"income", "household_size", "application_date"})
    return TaxBenefitFacts(
        income=require_int(f"{context}.income", value["income"]),
        household_size=require_int(f"{context}.household_size", value["household_size"]),
        application_date=require_date(
            f"{context}.application_date", value["application_date"]
        ),
    )


def procurement_facts_from_json(context: str, value: Any) -> ProcurementFacts:
    if not isinstance(value, dict):
        fail(f"{context} must be an object")
    require_keys(
        context,
        value,
        {
            "bid_amount",
            "quality_score",
            "small_business",
            "debarred",
            "received_date",
        },
    )
    return ProcurementFacts(
        bid_amount=require_int(f"{context}.bid_amount", value["bid_amount"]),
        quality_score=require_int(f"{context}.quality_score", value["quality_score"]),
        small_business=require_bool(
            f"{context}.small_business", value["small_business"]
        ),
        debarred=require_bool(f"{context}.debarred", value["debarred"]),
        received_date=require_date(f"{context}.received_date", value["received_date"]),
    )


def grant_allocation_facts_from_json(context: str, value: Any) -> GrantAllocationFacts:
    if not isinstance(value, dict):
        fail(f"{context} must be an object")
    require_keys(context, value, {"shelter_share", "clinic_share", "admin_share"})
    return GrantAllocationFacts(
        shelter_share=require_rational(f"{context}.shelter_share", value["shelter_share"]),
        clinic_share=require_rational(f"{context}.clinic_share", value["clinic_share"]),
        admin_share=require_rational(f"{context}.admin_share", value["admin_share"]),
    )


def category_equivalence_facts_from_json(
    context: str, value: Any
) -> CategoryEquivalenceFacts:
    if not isinstance(value, dict):
        fail(f"{context} must be an object")
    require_keys(context, value, {"applicant_category", "program"})
    return CategoryEquivalenceFacts(
        applicant_category=require_string(
            f"{context}.applicant_category", value["applicant_category"]
        ),
        program=require_string(f"{context}.program", value["program"]),
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


def tax_phase_start(date: str, params: dict[str, Any]) -> int:
    return (
        params["phase_start_before"]
        if date < params["change_date"]
        else params["phase_start_after"]
    )


def tax_benefit(facts: TaxBenefitFacts, params: dict[str, Any]) -> int:
    if facts.household_size < 1 or facts.household_size > params["max_household_size"]:
        fail(f"household_size out of bounded domain: {facts.household_size}")
    if facts.income < 0:
        fail(f"income must be nonnegative: {facts.income}")

    phase_start = tax_phase_start(facts.application_date, params)
    base = params["base_credit"] + params["household_adjustment"] * (
        facts.household_size - 1
    )
    capped_base = min(base, params["credit_cap"])
    phaseout = params["phaseout_rate"] * max(0, facts.income - phase_start)
    return max(0, capped_base - phaseout)


def procurement_award(facts: ProcurementFacts, params: dict[str, Any]) -> bool:
    if facts.bid_amount < 0:
        fail(f"bid_amount must be nonnegative: {facts.bid_amount}")
    if facts.quality_score < params["min_quality_score"]:
        fail(f"quality_score below bounded domain: {facts.quality_score}")
    if facts.quality_score > params["max_quality_score"]:
        fail(f"quality_score above bounded domain: {facts.quality_score}")

    adjusted_score = facts.quality_score
    if facts.small_business:
        adjusted_score += params["small_business_bonus"]
    return (
        not facts.debarred
        and facts.received_date <= params["deadline"]
        and facts.bid_amount <= params["max_bid"]
        and adjusted_score >= params["award_threshold"]
    )


def grant_allocation_compliant(
    facts: GrantAllocationFacts, params: dict[str, Any]
) -> bool:
    return (
        facts.shelter_share + facts.clinic_share + facts.admin_share
        == require_rational("parameters.total_share", params["total_share"])
        and facts.shelter_share
        >= require_rational("parameters.shelter_minimum", params["shelter_minimum"])
        and facts.clinic_share
        >= require_rational("parameters.clinic_minimum", params["clinic_minimum"])
        and facts.admin_share <= require_rational("parameters.admin_cap", params["admin_cap"])
        and facts.shelter_share >= 0
        and facts.clinic_share >= 0
        and facts.admin_share >= 0
    )


def category_canonical(category: str, params: dict[str, Any]) -> str:
    for left, right in params["equivalence_pairs"]:
        if category in {left, right}:
            return f"equiv:{left}:{right}"
    return f"atom:{category}"


def category_priority_review(
    facts: CategoryEquivalenceFacts, params: dict[str, Any]
) -> bool:
    categories = set(params["categories"])
    programs = set(params["programs"])
    if facts.applicant_category not in categories:
        fail(f"unknown applicant_category: {facts.applicant_category}")
    if facts.program not in programs:
        fail(f"unknown program: {facts.program}")
    local_canonical = category_canonical(params["equivalence_pairs"][0][0], params)
    return (
        category_canonical(facts.applicant_category, params) == local_canonical
        and facts.program == params["priority_program"]
    )


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
    elif pack_id == "tax_benefit_arithmetic_v0":
        witness_ids = validate_tax_benefit_expected(expected, citations)
    elif pack_id == "procurement_scoring_v0":
        witness_ids = validate_procurement_expected(expected, citations)
    elif pack_id == "grant_allocation_v0":
        witness_ids = validate_grant_allocation_expected(expected, citations)
    elif pack_id == "category_equivalence_v0":
        witness_ids = validate_category_equivalence_expected(expected, citations)
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
        if check["validation"] == "qf_uf_alethe_gap":
            validate_qf_uf_gap_fixture(pack_dir, check)


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


def validate_tax_benefit_expected(expected: dict[str, Any], citations: set[str]) -> set[str]:
    params = expected["parameters"]
    require_keys(
        "parameters",
        params,
        {
            "change_date",
            "phase_start_before",
            "phase_start_after",
            "base_credit",
            "household_adjustment",
            "credit_cap",
            "max_household_size",
            "phaseout_rate",
        },
    )
    require_date("parameters.change_date", params["change_date"])
    for key in (
        "phase_start_before",
        "phase_start_after",
        "base_credit",
        "household_adjustment",
        "credit_cap",
        "max_household_size",
        "phaseout_rate",
    ):
        if not isinstance(params[key], int) or params[key] < 0:
            fail(f"parameters.{key} must be a non-negative integer")
    if params["max_household_size"] < 1:
        fail("parameters.max_household_size must be at least 1")
    if params["phaseout_rate"] == 0:
        fail("parameters.phaseout_rate must be positive")

    witness_ids: set[str] = set()
    for index, witness in enumerate(expected["witnesses"]):
        require_keys(
            f"witnesses[{index}]",
            witness,
            {"id", "facts", "expected_benefit", "source_citations", "explanation"},
        )
        witness_id = witness["id"]
        if witness_id in witness_ids:
            fail(f"duplicate witness id {witness_id}")
        witness_ids.add(witness_id)
        expected_benefit = require_int(
            f"{witness_id}.expected_benefit", witness["expected_benefit"]
        )
        facts = tax_benefit_facts_from_json(f"{witness_id}.facts", witness["facts"])
        actual = tax_benefit(facts, params)
        if actual != expected_benefit:
            fail(f"{witness_id} replay mismatch: expected {expected_benefit}, got {actual}")
        validate_citations(witness_id, witness["source_citations"], citations)

    validate_tax_benefit_finite_sample(expected["sample_domain"], params)
    return witness_ids


def validate_procurement_expected(
    expected: dict[str, Any], citations: set[str]
) -> set[str]:
    params = expected["parameters"]
    require_keys(
        "parameters",
        params,
        {
            "deadline",
            "max_bid",
            "award_threshold",
            "small_business_bonus",
            "min_quality_score",
            "max_quality_score",
        },
    )
    require_date("parameters.deadline", params["deadline"])
    for key in (
        "max_bid",
        "award_threshold",
        "small_business_bonus",
        "min_quality_score",
        "max_quality_score",
    ):
        if not isinstance(params[key], int) or params[key] < 0:
            fail(f"parameters.{key} must be a non-negative integer")
    if params["min_quality_score"] > params["max_quality_score"]:
        fail("parameters.min_quality_score must not exceed max_quality_score")

    witness_ids: set[str] = set()
    for index, witness in enumerate(expected["witnesses"]):
        require_keys(
            f"witnesses[{index}]",
            witness,
            {"id", "facts", "expected_award", "source_citations", "explanation"},
        )
        witness_id = witness["id"]
        if witness_id in witness_ids:
            fail(f"duplicate witness id {witness_id}")
        witness_ids.add(witness_id)
        expected_award = require_bool(
            f"{witness_id}.expected_award", witness["expected_award"]
        )
        facts = procurement_facts_from_json(f"{witness_id}.facts", witness["facts"])
        actual = procurement_award(facts, params)
        if actual != expected_award:
            fail(f"{witness_id} replay mismatch: expected {expected_award}, got {actual}")
        validate_citations(witness_id, witness["source_citations"], citations)

    validate_procurement_finite_sample(expected["sample_domain"], params)
    return witness_ids


def validate_grant_allocation_expected(
    expected: dict[str, Any], citations: set[str]
) -> set[str]:
    params = expected["parameters"]
    require_keys(
        "parameters",
        params,
        {"total_share", "shelter_minimum", "clinic_minimum", "admin_cap"},
    )
    for key in ("total_share", "shelter_minimum", "clinic_minimum", "admin_cap"):
        value = require_rational(f"parameters.{key}", params[key])
        if value < 0:
            fail(f"parameters.{key} must be non-negative")

    witness_ids: set[str] = set()
    for index, witness in enumerate(expected["witnesses"]):
        require_keys(
            f"witnesses[{index}]",
            witness,
            {"id", "facts", "expected_compliant", "source_citations", "explanation"},
        )
        witness_id = witness["id"]
        if witness_id in witness_ids:
            fail(f"duplicate witness id {witness_id}")
        witness_ids.add(witness_id)
        expected_compliant = require_bool(
            f"{witness_id}.expected_compliant", witness["expected_compliant"]
        )
        facts = grant_allocation_facts_from_json(f"{witness_id}.facts", witness["facts"])
        actual = grant_allocation_compliant(facts, params)
        if actual != expected_compliant:
            fail(
                f"{witness_id} replay mismatch: expected {expected_compliant}, got {actual}"
            )
        validate_citations(witness_id, witness["source_citations"], citations)

    validate_grant_allocation_finite_sample(expected["sample_domain"], params)
    return witness_ids


def validate_category_equivalence_expected(
    expected: dict[str, Any], citations: set[str]
) -> set[str]:
    params = expected["parameters"]
    require_keys(
        "parameters",
        params,
        {"categories", "programs", "equivalence_pairs", "priority_program"},
    )
    categories = params["categories"]
    programs = params["programs"]
    if categories != ["resident", "in_state", "nonresident"]:
        fail("category equivalence parameters.categories must be the fixed v0 list")
    if programs != ["emergency_housing", "standard_benefit"]:
        fail("category equivalence parameters.programs must be the fixed v0 list")
    if params["priority_program"] not in programs:
        fail("category equivalence priority_program must be in parameters.programs")
    pairs = params["equivalence_pairs"]
    if pairs != [["resident", "in_state"]]:
        fail("category equivalence parameters.equivalence_pairs must be fixed v0 pairs")

    witness_ids: set[str] = set()
    for index, witness in enumerate(expected["witnesses"]):
        require_keys(
            f"witnesses[{index}]",
            witness,
            {
                "id",
                "facts",
                "expected_priority_review",
                "source_citations",
                "explanation",
            },
        )
        witness_id = witness["id"]
        if witness_id in witness_ids:
            fail(f"duplicate witness id {witness_id}")
        witness_ids.add(witness_id)
        expected_priority = require_bool(
            f"{witness_id}.expected_priority_review",
            witness["expected_priority_review"],
        )
        facts = category_equivalence_facts_from_json(
            f"{witness_id}.facts", witness["facts"]
        )
        actual = category_priority_review(facts, params)
        if actual != expected_priority:
            fail(
                f"{witness_id} replay mismatch: expected {expected_priority}, got {actual}"
            )
        validate_citations(witness_id, witness["source_citations"], citations)

    validate_category_equivalence_finite_sample(expected["sample_domain"], params)
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
    if check["validation"] not in {
        "bool_qf_lia_solver_regression",
        "qf_lra_farkas_solver_regression",
        "qf_uf_alethe_solver_regression",
    }:
        fail(
            f"{check_id} must use bool_qf_lia_solver_regression "
            "or qf_lra_farkas_solver_regression "
            "or qf_uf_alethe_solver_regression validation"
        )
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
    if check["validation"] == "qf_uf_alethe_solver_regression":
        if "prove_qf_uf_unsat_alethe" not in certificate:
            fail(f"{check_id}.data.certificate must name prove_qf_uf_unsat_alethe")
        if "checked_alethe" not in regression:
            fail(f"{check_id}.data.proof_regression must name the Alethe regression")


def validate_qf_uf_gap_fixture(pack_dir: Path, check: dict[str, Any]) -> None:
    check_id = check["id"]
    if check["expected_result"] != "unsat":
        fail(f"{check_id} QF_UF/Alethe gap must be an unsat obligation")
    if check["proof_status"] != "proof-gap":
        fail(f"{check_id} qf_uf_alethe_gap must remain proof-gap until checked")
    proof_gap = require_string(f"{check_id}.proof_gap", check.get("proof_gap"))
    if "QF_UF" not in proof_gap and "Alethe" not in proof_gap:
        fail(f"{check_id}.proof_gap must name the QF_UF/Alethe route")
    data = check.get("data")
    if not isinstance(data, dict):
        fail(f"{check_id} QF_UF/Alethe gap must include data")
    artifact = check_repo_path(f"{check_id}.data.smt2_artifact", data.get("smt2_artifact"))
    artifact_path = ROOT / artifact
    if pack_dir not in artifact_path.parents:
        fail(f"{check_id}.data.smt2_artifact must live under the rule pack")
    intended = require_string(
        f"{check_id}.data.intended_regression", data.get("intended_regression")
    )
    if "rules_as_code_examples" not in intended:
        fail(f"{check_id}.data.intended_regression must name rules_as_code_examples")
    certificate = require_string(f"{check_id}.data.certificate", data.get("certificate"))
    if "prove_qf_uf_unsat_alethe" not in certificate or "Evidence::check" not in certificate:
        fail(f"{check_id}.data.certificate must name the future checked route")


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


def validate_tax_benefit_finite_sample(
    sample_domain: dict[str, Any], params: dict[str, Any]
) -> None:
    require_keys("sample_domain", sample_domain, {"incomes", "household_sizes", "dates"})
    incomes = sorted(sample_domain["incomes"])
    household_sizes = sorted(sample_domain["household_sizes"])
    dates = sample_domain["dates"]
    if household_sizes != list(range(1, params["max_household_size"] + 1)):
        fail("tax benefit sample_domain.household_sizes must cover 1..max_household_size")
    for income in incomes:
        if not isinstance(income, int) or income < 0:
            fail("tax benefit sample_domain.incomes must be non-negative integers")
    for date in dates:
        require_date("sample_domain.dates[]", date)

    checked = 0
    for date in dates:
        for household_size in household_sizes:
            previous_benefit = None
            for income in incomes:
                facts = TaxBenefitFacts(income, household_size, date)
                benefit = tax_benefit(facts, params)
                if benefit < 0:
                    fail(f"non-negative benefit failed for {facts}")
                if benefit > params["credit_cap"]:
                    fail(f"benefit cap failed for {facts}")
                if previous_benefit is not None and benefit > previous_benefit:
                    fail(f"phase-out monotonicity failed for {facts}")
                previous_benefit = benefit
                checked += 1

    if checked == 0:
        fail("tax benefit finite sample was empty")


def validate_procurement_finite_sample(
    sample_domain: dict[str, Any], params: dict[str, Any]
) -> None:
    require_keys(
        "sample_domain",
        sample_domain,
        {"bid_amounts", "quality_scores", "dates", "booleans"},
    )
    bid_amounts = sorted(sample_domain["bid_amounts"])
    quality_scores = sorted(sample_domain["quality_scores"])
    dates = sample_domain["dates"]
    booleans = sample_domain["booleans"]
    if booleans != [False, True]:
        fail("procurement sample_domain.booleans must be [false, true]")
    for bid_amount in bid_amounts:
        if not isinstance(bid_amount, int) or bid_amount < 0:
            fail("procurement sample_domain.bid_amounts must be non-negative integers")
    for quality_score in quality_scores:
        if (
            not isinstance(quality_score, int)
            or quality_score < params["min_quality_score"]
            or quality_score > params["max_quality_score"]
        ):
            fail("procurement sample_domain.quality_scores out of bounded range")
    for date in dates:
        require_date("sample_domain.dates[]", date)

    checked = 0
    for bid_amount in bid_amounts:
        for quality_score in quality_scores:
            for date in dates:
                for small_business in booleans:
                    for debarred in booleans:
                        facts = ProcurementFacts(
                            bid_amount,
                            quality_score,
                            small_business,
                            debarred,
                            date,
                        )
                        award = procurement_award(facts, params)
                        if debarred and award:
                            fail(f"debarment exclusion failed for {facts}")
                        if date > params["deadline"] and award:
                            fail(f"late-submission exclusion failed for {facts}")
                        if bid_amount > params["max_bid"] and award:
                            fail(f"bid-cap exclusion failed for {facts}")
                        checked += 1

    for bid_amount in bid_amounts:
        for date in dates:
            for small_business in booleans:
                for debarred in booleans:
                    previous_award = False
                    for quality_score in quality_scores:
                        facts = ProcurementFacts(
                            bid_amount,
                            quality_score,
                            small_business,
                            debarred,
                            date,
                        )
                        award = procurement_award(facts, params)
                        if previous_award and not award:
                            fail(f"score monotonicity failed for {facts}")
                        if award:
                            previous_award = True

    if checked == 0:
        fail("procurement finite sample was empty")


def validate_grant_allocation_finite_sample(
    sample_domain: dict[str, Any], params: dict[str, Any]
) -> None:
    require_keys("sample_domain", sample_domain, {"shares"})
    shares = sample_domain["shares"]
    if not isinstance(shares, list) or not shares:
        fail("grant allocation sample_domain.shares must be a non-empty list")
    parsed_shares = [require_rational("sample_domain.shares[]", share) for share in shares]
    if sorted(parsed_shares) != parsed_shares:
        fail("grant allocation sample_domain.shares must be sorted")
    if any(share < 0 for share in parsed_shares):
        fail("grant allocation sample_domain.shares must be non-negative")

    checked = 0
    compliant_count = 0
    noncompliant_count = 0
    for shelter in parsed_shares:
        for clinic in parsed_shares:
            for admin in parsed_shares:
                facts = GrantAllocationFacts(shelter, clinic, admin)
                compliant = grant_allocation_compliant(facts, params)
                if compliant:
                    compliant_count += 1
                else:
                    noncompliant_count += 1
                checked += 1

    if checked == 0:
        fail("grant allocation finite sample was empty")
    if compliant_count == 0 or noncompliant_count == 0:
        fail("grant allocation sample must contain compliant and noncompliant rows")


def validate_category_equivalence_finite_sample(
    sample_domain: dict[str, Any], params: dict[str, Any]
) -> None:
    require_keys("sample_domain", sample_domain, {"categories", "programs"})
    categories = sample_domain["categories"]
    programs = sample_domain["programs"]
    if categories != params["categories"]:
        fail("category equivalence sample_domain.categories must match parameters")
    if programs != params["programs"]:
        fail("category equivalence sample_domain.programs must match parameters")

    checked = 0
    priority_count = 0
    nonpriority_count = 0
    for category in categories:
        for program in programs:
            facts = CategoryEquivalenceFacts(category, program)
            priority = category_priority_review(facts, params)
            if priority:
                priority_count += 1
            else:
                nonpriority_count += 1
            checked += 1

    for left, right in params["equivalence_pairs"]:
        if left not in categories or right not in categories:
            fail("category equivalence pair must reference known categories")
        for program in programs:
            left_priority = category_priority_review(
                CategoryEquivalenceFacts(left, program), params
            )
            right_priority = category_priority_review(
                CategoryEquivalenceFacts(right, program), params
            )
            if left_priority != right_priority:
                fail(f"category equivalence failed for {left}, {right}, {program}")

    if checked == 0:
        fail("category equivalence finite sample was empty")
    if priority_count == 0 or nonpriority_count == 0:
        fail("category equivalence sample must contain priority and nonpriority rows")


def validate_generated_queries(
    pack_dir: Path, metadata: dict[str, Any], expected: dict[str, Any]
) -> None:
    query_path = GENERATED_QUERIES_ROOT / f"{pack_dir.name}.json"
    payload = load_json(query_path)
    if not isinstance(payload, dict):
        fail(f"{query_path.relative_to(ROOT)} must be a JSON object")
    require_keys(
        "generated query payload",
        payload,
        {
            "schema_version",
            "generated_by",
            "pack_id",
            "pack_title",
            "source_pack",
            "query_families",
        },
    )
    if payload["schema_version"] != 1:
        fail("generated query schema_version must be 1")
    if payload["generated_by"] != "python3 scripts/gen-rules-as-code-dashboard.py":
        fail("generated query generated_by must name the generator")
    if payload["pack_id"] != metadata["id"]:
        fail("generated query pack_id must match metadata.id")
    if payload["pack_title"] != metadata["title"]:
        fail("generated query pack_title must match metadata.title")
    source_pack = f"docs/rules-as-code/examples/{pack_dir.name}"
    if payload["source_pack"] != source_pack:
        fail("generated query source_pack must point at the rule pack")

    families = require_query_family_map(payload)
    pack_id = metadata["id"]
    if pack_id == "benefit_eligibility_v0":
        validate_benefit_generated_queries(expected, families)
    elif pack_id == "authorization_policy_v0":
        validate_authorization_generated_queries(expected, families)
    elif pack_id == "tax_benefit_arithmetic_v0":
        validate_tax_benefit_generated_queries(expected, families)
    elif pack_id == "procurement_scoring_v0":
        validate_procurement_generated_queries(expected, families)
    elif pack_id == "grant_allocation_v0":
        validate_grant_allocation_generated_queries(expected, families)
    elif pack_id == "category_equivalence_v0":
        validate_category_equivalence_generated_queries(expected, families)
    else:
        fail(f"unsupported generated query pack id {pack_id}")


def require_query_family_map(payload: dict[str, Any]) -> dict[str, dict[str, Any]]:
    query_families = payload["query_families"]
    if not isinstance(query_families, list) or not query_families:
        fail("generated query_families must be a non-empty list")
    families: dict[str, dict[str, Any]] = {}
    for index, family in enumerate(query_families):
        if not isinstance(family, dict):
            fail(f"generated query_families[{index}] must be an object")
        require_keys(
            f"generated query_families[{index}]",
            family,
            {"id", "description", "row_count", "rows"},
        )
        family_id = require_string(f"generated query_families[{index}].id", family["id"])
        if family_id in families:
            fail(f"duplicate generated query family {family_id}")
        description = require_string(
            f"generated query_families[{index}].description", family["description"]
        )
        if not description.endswith("."):
            fail(f"generated query family {family_id} description must be a sentence")
        rows = family["rows"]
        if not isinstance(rows, list):
            fail(f"generated query family {family_id} rows must be a list")
        row_count = require_int(f"generated query family {family_id}.row_count", family["row_count"])
        if row_count != len(rows):
            fail(f"generated query family {family_id}.row_count must match rows")
        seen_row_ids: set[str] = set()
        for row_index, row in enumerate(rows):
            if not isinstance(row, dict):
                fail(f"generated query family {family_id} row {row_index} must be an object")
            row_id = require_string(
                f"generated query family {family_id} row {row_index}.id",
                row.get("id"),
            )
            if row_id in seen_row_ids:
                fail(f"duplicate generated row id {family_id}.{row_id}")
            seen_row_ids.add(row_id)
        families[family_id] = family
    return families


def require_exact_families(
    context: str, families: dict[str, dict[str, Any]], expected_ids: set[str]
) -> None:
    actual_ids = set(families)
    if actual_ids != expected_ids:
        fail(
            f"{context} generated families mismatch: expected {sorted(expected_ids)}, got {sorted(actual_ids)}"
        )


def validate_benefit_generated_queries(
    expected: dict[str, Any], families: dict[str, dict[str, Any]]
) -> None:
    require_exact_families(
        "benefit",
        families,
        {"coverage", "income_monotonicity_adjacent"},
    )
    params = expected["parameters"]
    sample = expected["sample_domain"]
    coverage_rows = families["coverage"]["rows"]
    expected_coverage = (
        len(sample["ages"])
        * len(sample["incomes"])
        * len(sample["dates"])
        * len(sample["booleans"])
        * len(sample["booleans"])
        * len(sample["booleans"])
    )
    if len(coverage_rows) != expected_coverage:
        fail("benefit coverage generated row count mismatch")
    for index, row in enumerate(coverage_rows):
        if row["id"] != f"coverage-{index:04d}":
            fail("benefit coverage generated row ids must be sequential")
        facts = benefit_facts_from_json(f"generated benefit coverage {index}.facts", row.get("facts"))
        expected_eligible = require_bool(
            f"generated benefit coverage {index}.expected_eligible",
            row.get("expected_eligible"),
        )
        if benefit_eligible(facts, params) != expected_eligible:
            fail(f"generated benefit coverage row {index} replay mismatch")

    monotonicity_rows = families["income_monotonicity_adjacent"]["rows"]
    expected_monotonicity = (
        len(sample["ages"])
        * len(sample["dates"])
        * len(sample["booleans"])
        * len(sample["booleans"])
        * len(sample["booleans"])
        * max(len(sample["incomes"]) - 1, 0)
    )
    if len(monotonicity_rows) != expected_monotonicity:
        fail("benefit monotonicity generated row count mismatch")
    adjacent = set(zip(sample["incomes"], sample["incomes"][1:]))
    for index, row in enumerate(monotonicity_rows):
        if row["id"] != f"income-monotonicity-{index:04d}":
            fail("benefit monotonicity generated row ids must be sequential")
        lower = benefit_facts_from_json(
            f"generated benefit monotonicity {index}.lower_facts",
            row.get("lower_facts"),
        )
        higher = benefit_facts_from_json(
            f"generated benefit monotonicity {index}.higher_facts",
            row.get("higher_facts"),
        )
        if (lower.income, higher.income) not in adjacent:
            fail(f"generated benefit monotonicity row {index} must use adjacent incomes")
        lower_key = (lower.age, lower.resident, lower.veteran, lower.sanctioned, lower.application_date)
        higher_key = (
            higher.age,
            higher.resident,
            higher.veteran,
            higher.sanctioned,
            higher.application_date,
        )
        if lower_key != higher_key:
            fail(f"generated benefit monotonicity row {index} changed non-income facts")
        lower_eligible = require_bool(
            f"generated benefit monotonicity {index}.lower_eligible",
            row.get("lower_eligible"),
        )
        higher_eligible = require_bool(
            f"generated benefit monotonicity {index}.higher_eligible",
            row.get("higher_eligible"),
        )
        if benefit_eligible(lower, params) != lower_eligible:
            fail(f"generated benefit monotonicity row {index} lower replay mismatch")
        if benefit_eligible(higher, params) != higher_eligible:
            fail(f"generated benefit monotonicity row {index} higher replay mismatch")
        holds = require_bool(
            f"generated benefit monotonicity {index}.nonincreasing_holds",
            row.get("nonincreasing_holds"),
        )
        if holds != (not (not lower_eligible and higher_eligible)):
            fail(f"generated benefit monotonicity row {index} has wrong holds flag")
        if not holds:
            fail(f"generated benefit monotonicity row {index} violates monotonicity")


def validate_authorization_generated_queries(
    expected: dict[str, Any], families: dict[str, dict[str, Any]]
) -> None:
    require_exact_families(
        "authorization",
        families,
        {"bounded_requests", "version_delta_adjacent"},
    )
    sample = expected["sample_domain"]
    request_rows = families["bounded_requests"]["rows"]
    expected_requests = (
        len(sample["user_tenants"])
        * len(sample["resource_tenants"])
        * len(sample["roles"])
        * len(sample["actions"])
        * len(sample["policy_versions"])
        * len(sample["booleans"])
    )
    if len(request_rows) != expected_requests:
        fail("authorization request generated row count mismatch")
    for index, row in enumerate(request_rows):
        if row["id"] != f"request-{index:04d}":
            fail("authorization request generated row ids must be sequential")
        facts = authorization_facts_from_json(
            f"generated authorization request {index}.facts",
            row.get("facts"),
        )
        expected_allow = require_bool(
            f"generated authorization request {index}.expected_allow",
            row.get("expected_allow"),
        )
        if authorization_allows(facts) != expected_allow:
            fail(f"generated authorization request row {index} replay mismatch")

    version_rows = families["version_delta_adjacent"]["rows"]
    expected_versions = (
        len(sample["user_tenants"])
        * len(sample["resource_tenants"])
        * len(sample["roles"])
        * len(sample["actions"])
        * len(sample["booleans"])
        * max(len(sample["policy_versions"]) - 1, 0)
    )
    if len(version_rows) != expected_versions:
        fail("authorization version-delta generated row count mismatch")
    adjacent = set(zip(sample["policy_versions"], sample["policy_versions"][1:]))
    for index, row in enumerate(version_rows):
        if row["id"] != f"version-delta-{index:04d}":
            fail("authorization version-delta generated row ids must be sequential")
        before = authorization_facts_from_json(
            f"generated authorization version {index}.before_facts",
            row.get("before_facts"),
        )
        after = authorization_facts_from_json(
            f"generated authorization version {index}.after_facts",
            row.get("after_facts"),
        )
        if (before.policy_version, after.policy_version) not in adjacent:
            fail(f"generated authorization version row {index} must use adjacent versions")
        before_key = (
            before.user_tenant,
            before.resource_tenant,
            before.role,
            before.action,
            before.explicit_deny,
        )
        after_key = (
            after.user_tenant,
            after.resource_tenant,
            after.role,
            after.action,
            after.explicit_deny,
        )
        if before_key != after_key:
            fail(f"generated authorization version row {index} changed non-version facts")
        before_allow = require_bool(
            f"generated authorization version {index}.before_allow",
            row.get("before_allow"),
        )
        after_allow = require_bool(
            f"generated authorization version {index}.after_allow",
            row.get("after_allow"),
        )
        if authorization_allows(before) != before_allow:
            fail(f"generated authorization version row {index} before replay mismatch")
        if authorization_allows(after) != after_allow:
            fail(f"generated authorization version row {index} after replay mismatch")
        intended_delta = require_bool(
            f"generated authorization version {index}.intended_delta",
            row.get("intended_delta"),
        )
        computed_intended = (
            before.user_tenant == before.resource_tenant
            and before.role == "analyst"
            and before.action == "export"
            and not before.explicit_deny
        )
        if intended_delta != computed_intended:
            fail(f"generated authorization version row {index} has wrong intended flag")
        if before_allow != after_allow and not intended_delta:
            fail(f"generated authorization version row {index} has unintended delta")


def validate_tax_benefit_generated_queries(
    expected: dict[str, Any], families: dict[str, dict[str, Any]]
) -> None:
    require_exact_families(
        "tax benefit",
        families,
        {"bounded_benefits", "income_phaseout_adjacent"},
    )
    params = expected["parameters"]
    sample = expected["sample_domain"]
    benefit_rows = families["bounded_benefits"]["rows"]
    expected_benefits = (
        len(sample["incomes"]) * len(sample["household_sizes"]) * len(sample["dates"])
    )
    if len(benefit_rows) != expected_benefits:
        fail("tax benefit generated row count mismatch")
    for index, row in enumerate(benefit_rows):
        if row["id"] != f"benefit-{index:04d}":
            fail("tax benefit generated row ids must be sequential")
        facts = tax_benefit_facts_from_json(
            f"generated tax benefit {index}.facts",
            row.get("facts"),
        )
        expected_benefit = require_int(
            f"generated tax benefit {index}.expected_benefit",
            row.get("expected_benefit"),
        )
        if tax_benefit(facts, params) != expected_benefit:
            fail(f"generated tax benefit row {index} replay mismatch")

    monotonicity_rows = families["income_phaseout_adjacent"]["rows"]
    expected_monotonicity = (
        len(sample["household_sizes"])
        * len(sample["dates"])
        * max(len(sample["incomes"]) - 1, 0)
    )
    if len(monotonicity_rows) != expected_monotonicity:
        fail("tax benefit phaseout generated row count mismatch")
    adjacent = set(zip(sample["incomes"], sample["incomes"][1:]))
    for index, row in enumerate(monotonicity_rows):
        if row["id"] != f"phaseout-monotonicity-{index:04d}":
            fail("tax benefit phaseout generated row ids must be sequential")
        lower = tax_benefit_facts_from_json(
            f"generated tax phaseout {index}.lower_facts",
            row.get("lower_facts"),
        )
        higher = tax_benefit_facts_from_json(
            f"generated tax phaseout {index}.higher_facts",
            row.get("higher_facts"),
        )
        if (lower.income, higher.income) not in adjacent:
            fail(f"generated tax phaseout row {index} must use adjacent incomes")
        lower_key = (lower.household_size, lower.application_date)
        higher_key = (higher.household_size, higher.application_date)
        if lower_key != higher_key:
            fail(f"generated tax phaseout row {index} changed non-income facts")
        lower_benefit = require_int(
            f"generated tax phaseout {index}.lower_benefit",
            row.get("lower_benefit"),
        )
        higher_benefit = require_int(
            f"generated tax phaseout {index}.higher_benefit",
            row.get("higher_benefit"),
        )
        if tax_benefit(lower, params) != lower_benefit:
            fail(f"generated tax phaseout row {index} lower replay mismatch")
        if tax_benefit(higher, params) != higher_benefit:
            fail(f"generated tax phaseout row {index} higher replay mismatch")
        holds = require_bool(
            f"generated tax phaseout {index}.nonincreasing_holds",
            row.get("nonincreasing_holds"),
        )
        if holds != (higher_benefit <= lower_benefit):
            fail(f"generated tax phaseout row {index} has wrong holds flag")
        if not holds:
            fail(f"generated tax phaseout row {index} violates phaseout monotonicity")


def validate_procurement_generated_queries(
    expected: dict[str, Any], families: dict[str, dict[str, Any]]
) -> None:
    require_exact_families(
        "procurement",
        families,
        {"bounded_awards", "quality_monotonicity_adjacent"},
    )
    params = expected["parameters"]
    sample = expected["sample_domain"]
    award_rows = families["bounded_awards"]["rows"]
    expected_awards = (
        len(sample["bid_amounts"])
        * len(sample["quality_scores"])
        * len(sample["dates"])
        * len(sample["booleans"])
        * len(sample["booleans"])
    )
    if len(award_rows) != expected_awards:
        fail("procurement award generated row count mismatch")
    for index, row in enumerate(award_rows):
        if row["id"] != f"award-{index:04d}":
            fail("procurement award generated row ids must be sequential")
        facts = procurement_facts_from_json(
            f"generated procurement award {index}.facts",
            row.get("facts"),
        )
        expected_award = require_bool(
            f"generated procurement award {index}.expected_award",
            row.get("expected_award"),
        )
        if procurement_award(facts, params) != expected_award:
            fail(f"generated procurement award row {index} replay mismatch")

    monotonicity_rows = families["quality_monotonicity_adjacent"]["rows"]
    expected_monotonicity = (
        len(sample["bid_amounts"])
        * len(sample["dates"])
        * len(sample["booleans"])
        * len(sample["booleans"])
        * max(len(sample["quality_scores"]) - 1, 0)
    )
    if len(monotonicity_rows) != expected_monotonicity:
        fail("procurement quality monotonicity generated row count mismatch")
    adjacent = set(zip(sample["quality_scores"], sample["quality_scores"][1:]))
    for index, row in enumerate(monotonicity_rows):
        if row["id"] != f"quality-monotonicity-{index:04d}":
            fail("procurement quality monotonicity generated row ids must be sequential")
        lower = procurement_facts_from_json(
            f"generated procurement monotonicity {index}.lower_facts",
            row.get("lower_facts"),
        )
        higher = procurement_facts_from_json(
            f"generated procurement monotonicity {index}.higher_facts",
            row.get("higher_facts"),
        )
        if (lower.quality_score, higher.quality_score) not in adjacent:
            fail(
                f"generated procurement monotonicity row {index} "
                "must use adjacent quality scores"
            )
        lower_key = (
            lower.bid_amount,
            lower.small_business,
            lower.debarred,
            lower.received_date,
        )
        higher_key = (
            higher.bid_amount,
            higher.small_business,
            higher.debarred,
            higher.received_date,
        )
        if lower_key != higher_key:
            fail(
                f"generated procurement monotonicity row {index} "
                "changed non-quality facts"
            )
        lower_award = require_bool(
            f"generated procurement monotonicity {index}.lower_award",
            row.get("lower_award"),
        )
        higher_award = require_bool(
            f"generated procurement monotonicity {index}.higher_award",
            row.get("higher_award"),
        )
        if procurement_award(lower, params) != lower_award:
            fail(f"generated procurement monotonicity row {index} lower replay mismatch")
        if procurement_award(higher, params) != higher_award:
            fail(f"generated procurement monotonicity row {index} higher replay mismatch")
        holds = require_bool(
            f"generated procurement monotonicity {index}.nondecreasing_holds",
            row.get("nondecreasing_holds"),
        )
        if holds != (not (lower_award and not higher_award)):
            fail(f"generated procurement monotonicity row {index} has wrong holds flag")
        if not holds:
            fail(f"generated procurement monotonicity row {index} violates monotonicity")


def validate_grant_allocation_generated_queries(
    expected: dict[str, Any], families: dict[str, dict[str, Any]]
) -> None:
    require_exact_families(
        "grant allocation",
        families,
        {"bounded_allocations", "balanced_budget_allocations"},
    )
    params = expected["parameters"]
    sample = expected["sample_domain"]
    shares = sample["shares"]
    allocation_rows = families["bounded_allocations"]["rows"]
    expected_allocations = len(shares) ** 3
    if len(allocation_rows) != expected_allocations:
        fail("grant allocation generated row count mismatch")
    for index, row in enumerate(allocation_rows):
        if row["id"] != f"allocation-{index:04d}":
            fail("grant allocation generated row ids must be sequential")
        facts = grant_allocation_facts_from_json(
            f"generated grant allocation {index}.facts",
            row.get("facts"),
        )
        expected_compliant = require_bool(
            f"generated grant allocation {index}.expected_compliant",
            row.get("expected_compliant"),
        )
        if grant_allocation_compliant(facts, params) != expected_compliant:
            fail(f"generated grant allocation row {index} replay mismatch")

    balanced_rows = families["balanced_budget_allocations"]["rows"]
    total_share = require_rational("parameters.total_share", params["total_share"])
    expected_balanced = 0
    for shelter in shares:
        for clinic in shares:
            for admin in shares:
                if (
                    require_rational("sample_domain.shares[]", shelter)
                    + require_rational("sample_domain.shares[]", clinic)
                    + require_rational("sample_domain.shares[]", admin)
                    == total_share
                ):
                    expected_balanced += 1
    if len(balanced_rows) != expected_balanced:
        fail("grant allocation balanced generated row count mismatch")
    for index, row in enumerate(balanced_rows):
        if row["id"] != f"balanced-allocation-{index:04d}":
            fail("grant allocation balanced row ids must be sequential")
        facts = grant_allocation_facts_from_json(
            f"generated grant balanced {index}.facts",
            row.get("facts"),
        )
        if facts.shelter_share + facts.clinic_share + facts.admin_share != total_share:
            fail(f"generated grant balanced row {index} does not balance")
        expected_compliant = require_bool(
            f"generated grant balanced {index}.expected_compliant",
            row.get("expected_compliant"),
        )
        if grant_allocation_compliant(facts, params) != expected_compliant:
            fail(f"generated grant balanced row {index} replay mismatch")
        shelter_floor = require_bool(
            f"generated grant balanced {index}.shelter_floor_holds",
            row.get("shelter_floor_holds"),
        )
        clinic_floor = require_bool(
            f"generated grant balanced {index}.clinic_floor_holds",
            row.get("clinic_floor_holds"),
        )
        admin_cap = require_bool(
            f"generated grant balanced {index}.admin_cap_holds",
            row.get("admin_cap_holds"),
        )
        if shelter_floor != (
            facts.shelter_share
            >= require_rational("parameters.shelter_minimum", params["shelter_minimum"])
        ):
            fail(f"generated grant balanced row {index} has wrong shelter floor flag")
        if clinic_floor != (
            facts.clinic_share
            >= require_rational("parameters.clinic_minimum", params["clinic_minimum"])
        ):
            fail(f"generated grant balanced row {index} has wrong clinic floor flag")
        if admin_cap != (
            facts.admin_share <= require_rational("parameters.admin_cap", params["admin_cap"])
        ):
            fail(f"generated grant balanced row {index} has wrong admin cap flag")


def validate_category_equivalence_generated_queries(
    expected: dict[str, Any], families: dict[str, dict[str, Any]]
) -> None:
    require_exact_families(
        "category equivalence",
        families,
        {"bounded_category_rows", "equivalence_pair_rows"},
    )
    params = expected["parameters"]
    sample = expected["sample_domain"]
    categories = sample["categories"]
    programs = sample["programs"]
    category_rows = families["bounded_category_rows"]["rows"]
    expected_rows = len(categories) * len(programs)
    if len(category_rows) != expected_rows:
        fail("category equivalence generated row count mismatch")
    for index, row in enumerate(category_rows):
        if row["id"] != f"category-row-{index:04d}":
            fail("category equivalence generated row ids must be sequential")
        facts = category_equivalence_facts_from_json(
            f"generated category equivalence {index}.facts",
            row.get("facts"),
        )
        expected_priority = require_bool(
            f"generated category equivalence {index}.expected_priority_review",
            row.get("expected_priority_review"),
        )
        if category_priority_review(facts, params) != expected_priority:
            fail(f"generated category equivalence row {index} replay mismatch")
        canonical = require_string(
            f"generated category equivalence {index}.canonical_category",
            row.get("canonical_category"),
        )
        if canonical != category_canonical(facts.applicant_category, params):
            fail(f"generated category equivalence row {index} canonical mismatch")

    pair_rows = families["equivalence_pair_rows"]["rows"]
    expected_pairs = len(params["equivalence_pairs"]) * len(programs)
    if len(pair_rows) != expected_pairs:
        fail("category equivalence pair generated row count mismatch")
    for index, row in enumerate(pair_rows):
        if row["id"] != f"equivalence-pair-{index:04d}":
            fail("category equivalence pair row ids must be sequential")
        left = category_equivalence_facts_from_json(
            f"generated category pair {index}.left_facts",
            row.get("left_facts"),
        )
        right = category_equivalence_facts_from_json(
            f"generated category pair {index}.right_facts",
            row.get("right_facts"),
        )
        if left.program != right.program:
            fail(f"generated category pair {index} changed program")
        if [left.applicant_category, right.applicant_category] not in params[
            "equivalence_pairs"
        ]:
            fail(f"generated category pair {index} must use an equivalence pair")
        left_priority = require_bool(
            f"generated category pair {index}.left_priority_review",
            row.get("left_priority_review"),
        )
        right_priority = require_bool(
            f"generated category pair {index}.right_priority_review",
            row.get("right_priority_review"),
        )
        if category_priority_review(left, params) != left_priority:
            fail(f"generated category pair {index} left replay mismatch")
        if category_priority_review(right, params) != right_priority:
            fail(f"generated category pair {index} right replay mismatch")
        congruent = require_bool(
            f"generated category pair {index}.congruent_priority_holds",
            row.get("congruent_priority_holds"),
        )
        if congruent != (left_priority == right_priority):
            fail(f"generated category pair {index} has wrong congruence flag")
        if not congruent:
            fail(f"generated category pair {index} violates category congruence")


def validate_pack(pack_dir: Path) -> str:
    metadata_path = pack_dir / "metadata.json"
    expected_path = pack_dir / "expected.json"
    metadata = load_json(metadata_path)
    expected = load_json(expected_path)
    if not isinstance(metadata, dict) or not isinstance(expected, dict):
        fail("metadata and expected artifacts must be JSON objects")
    validate_metadata(pack_dir, metadata)
    validate_expected(pack_dir, metadata, expected)
    validate_generated_queries(pack_dir, metadata, expected)
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
