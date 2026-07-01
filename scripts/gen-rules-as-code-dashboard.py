#!/usr/bin/env python3
"""Generate the Rules-as-Code bounded query dashboard."""

from __future__ import annotations

import json
from collections import Counter
from fractions import Fraction
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
EXAMPLES_ROOT = ROOT / "docs" / "rules-as-code" / "examples"
OUT_DIR = ROOT / "docs" / "rules-as-code" / "generated"
OUT_PATH = OUT_DIR / "rules-query-dashboard.md"
QUERY_DIR = OUT_DIR / "queries"


def load_json(path: Path) -> Any:
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def product(values: list[int]) -> int:
    result = 1
    for value in values:
        result *= value
    return result


def parse_rational(value: Any) -> Fraction:
    if isinstance(value, bool):
        raise TypeError(f"rational value must not be a boolean: {value!r}")
    if isinstance(value, int):
        return Fraction(value, 1)
    if not isinstance(value, str):
        raise TypeError(f"rational value must be a string or integer: {value!r}")
    return Fraction(value)


def check_counts(expected: dict[str, Any]) -> Counter[str]:
    return Counter(check["proof_status"] for check in expected["checks"])


def witness_count(expected: dict[str, Any], check_ids: set[str]) -> int:
    total = 0
    for check in expected["checks"]:
        if check["id"] in check_ids:
            total += len(check.get("witnesses", []))
    return total


def standard_threshold(date: str, params: dict[str, Any]) -> int:
    if date < params["change_date"]:
        return params["standard_threshold_before"]
    return params["standard_threshold_after"]


def benefit_eligible(facts: dict[str, Any], params: dict[str, Any]) -> bool:
    standard = standard_threshold(facts["application_date"], params)
    veteran_threshold = standard + params["veteran_bonus"]
    return (
        facts["resident"]
        and facts["age"] >= 18
        and not facts["sanctioned"]
        and (
            facts["income"] <= standard
            or (facts["veteran"] and facts["income"] <= veteran_threshold)
        )
    )


def authorization_allows(facts: dict[str, Any]) -> bool:
    if facts["explicit_deny"]:
        return False
    if facts["user_tenant"] != facts["resource_tenant"]:
        return False
    if facts["role"] == "admin":
        return facts["action"] in {"read", "export"}
    if facts["role"] == "analyst":
        if facts["action"] == "read":
            return True
        if facts["action"] == "export":
            return facts["policy_version"] >= 2
    return False


def tax_phase_start(date: str, params: dict[str, Any]) -> int:
    if date < params["change_date"]:
        return params["phase_start_before"]
    return params["phase_start_after"]


def tax_benefit(facts: dict[str, Any], params: dict[str, Any]) -> int:
    phase_start = tax_phase_start(facts["application_date"], params)
    base = params["base_credit"] + params["household_adjustment"] * (
        facts["household_size"] - 1
    )
    capped_base = min(base, params["credit_cap"])
    phaseout = params["phaseout_rate"] * max(0, facts["income"] - phase_start)
    return max(0, capped_base - phaseout)


def procurement_award(facts: dict[str, Any], params: dict[str, Any]) -> bool:
    adjusted_score = facts["quality_score"]
    if facts["small_business"]:
        adjusted_score += params["small_business_bonus"]
    return (
        not facts["debarred"]
        and facts["received_date"] <= params["deadline"]
        and facts["bid_amount"] <= params["max_bid"]
        and adjusted_score >= params["award_threshold"]
    )


def grant_allocation_compliant(facts: dict[str, Any], params: dict[str, Any]) -> bool:
    shelter = parse_rational(facts["shelter_share"])
    clinic = parse_rational(facts["clinic_share"])
    admin = parse_rational(facts["admin_share"])
    return (
        shelter + clinic + admin == parse_rational(params["total_share"])
        and shelter >= parse_rational(params["shelter_minimum"])
        and clinic >= parse_rational(params["clinic_minimum"])
        and admin <= parse_rational(params["admin_cap"])
        and shelter >= 0
        and clinic >= 0
        and admin >= 0
    )


def category_canonical(category: str, params: dict[str, Any]) -> str:
    for left, right in params["equivalence_pairs"]:
        if category in {left, right}:
            return f"equiv:{left}:{right}"
    return f"atom:{category}"


def category_priority_review(facts: dict[str, Any], params: dict[str, Any]) -> bool:
    local_canonical = category_canonical(params["equivalence_pairs"][0][0], params)
    return (
        category_canonical(facts["applicant_category"], params) == local_canonical
        and facts["program"] == params["priority_program"]
    )


def workflow_transition(
    facts: dict[str, Any], params: dict[str, Any]
) -> tuple[bool, str]:
    if (
        facts["current_state"] == params["initial_state"]
        and facts["action"] == "request_review"
    ):
        return True, params["review_state"]
    if (
        facts["current_state"] == params["review_state"]
        and facts["action"] == "approve"
        and facts["supervisor_review"]
    ):
        return True, params["approved_state"]
    if facts["current_state"] == params["review_state"] and facts["action"] == "reject":
        return True, params["rejected_state"]
    return False, facts["current_state"]


def benefit_metrics(expected: dict[str, Any]) -> tuple[int, list[tuple[str, int]], str]:
    sample = expected["sample_domain"]
    booleans = len(sample["booleans"])
    rows = product(
        [
            len(sample["ages"]),
            len(sample["incomes"]),
            len(sample["dates"]),
            booleans,
            booleans,
            booleans,
        ]
    )
    context_count = len(sample["ages"]) * len(sample["dates"]) * booleans * booleans * booleans
    monotonicity_scans = context_count * max(len(sample["incomes"]) - 1, 0)
    families = [
        ("complete eligibility coverage rows", rows),
        ("income monotonicity adjacent scans", monotonicity_scans),
        ("threshold/temporal replay witnesses", witness_count(expected, {"threshold_cliff", "temporal_transition"})),
        ("checked Bool/QF_LIA fixtures", check_counts(expected)["checked"]),
    ]
    return rows, families, "Generate coverage and equivalence fixtures across the full bounded applicant domain."


def authorization_metrics(expected: dict[str, Any]) -> tuple[int, list[tuple[str, int]], str]:
    sample = expected["sample_domain"]
    rows = product(
        [
            len(sample["user_tenants"]),
            len(sample["resource_tenants"]),
            len(sample["roles"]),
            len(sample["actions"]),
            len(sample["policy_versions"]),
            len(sample["booleans"]),
        ]
    )
    delta_pairs = product(
        [
            len(sample["user_tenants"]),
            len(sample["resource_tenants"]),
            len(sample["roles"]),
            len(sample["actions"]),
            max(len(sample["policy_versions"]) - 1, 0),
            len(sample["booleans"]),
        ]
    )
    families = [
        ("bounded role/action/version rows", rows),
        ("adjacent version-delta comparisons", delta_pairs),
        ("version-delta replay witnesses", witness_count(expected, {"version_delta"})),
        ("checked Bool/QF_LIA fixtures", check_counts(expected)["checked"]),
    ]
    return rows, families, "Generate tenant/action/version coverage and equivalence queries across the bounded request domain."


def tax_benefit_metrics(expected: dict[str, Any]) -> tuple[int, list[tuple[str, int]], str]:
    sample = expected["sample_domain"]
    rows = product(
        [len(sample["incomes"]), len(sample["household_sizes"]), len(sample["dates"])]
    )
    monotonicity_scans = (
        max(len(sample["incomes"]) - 1, 0)
        * len(sample["household_sizes"])
        * len(sample["dates"])
    )
    families = [
        ("bounded benefit replay rows", rows),
        ("income phase-out adjacent scans", monotonicity_scans),
        ("threshold/temporal replay witnesses", witness_count(expected, {"threshold_cliff", "temporal_transition"})),
        ("checked Bool/QF_LIA fixtures", check_counts(expected)["checked"]),
    ]
    return rows, families, "Generate threshold, cap, and phase-out fixtures across the bounded income/date/household domain."


def procurement_metrics(expected: dict[str, Any]) -> tuple[int, list[tuple[str, int]], str]:
    sample = expected["sample_domain"]
    rows = product(
        [
            len(sample["bid_amounts"]),
            len(sample["quality_scores"]),
            len(sample["dates"]),
            len(sample["booleans"]),
            len(sample["booleans"]),
        ]
    )
    monotonicity_scans = (
        len(sample["bid_amounts"])
        * len(sample["dates"])
        * len(sample["booleans"])
        * len(sample["booleans"])
        * max(len(sample["quality_scores"]) - 1, 0)
    )
    families = [
        ("bounded procurement award rows", rows),
        ("quality-score adjacent scans", monotonicity_scans),
        ("bonus-threshold replay witnesses", witness_count(expected, {"score_bonus_threshold"})),
        ("checked Bool/QF_LIA fixtures", check_counts(expected)["checked"]),
    ]
    return rows, families, "Generate debarment, deadline, bid-cap, bonus-threshold, and score-monotonicity fixtures across the bounded procurement domain."


def grant_allocation_metrics(expected: dict[str, Any]) -> tuple[int, list[tuple[str, int]], str]:
    sample = expected["sample_domain"]
    shares = sample["shares"]
    rows = len(shares) ** 3
    total_share = parse_rational(expected["parameters"]["total_share"])
    balanced_rows = 0
    for shelter in shares:
        for clinic in shares:
            for admin in shares:
                if (
                    parse_rational(shelter)
                    + parse_rational(clinic)
                    + parse_rational(admin)
                    == total_share
                ):
                    balanced_rows += 1
    families = [
        ("bounded rational allocation rows", rows),
        ("balanced-budget allocation rows", balanced_rows),
        ("allocation replay witnesses", witness_count(expected, {"allocation_witnesses"})),
        ("checked QF_LRA/Farkas fixtures", check_counts(expected)["checked"]),
    ]
    return rows, families, "Generate rational allocation coverage and balanced-budget query rows across the bounded share domain."


def category_equivalence_metrics(
    expected: dict[str, Any]
) -> tuple[int, list[tuple[str, int]], str]:
    sample = expected["sample_domain"]
    rows = len(sample["categories"]) * len(sample["programs"])
    pair_rows = len(expected["parameters"]["equivalence_pairs"]) * len(sample["programs"])
    families = [
        ("bounded category/program rows", rows),
        ("equivalence-pair congruence rows", pair_rows),
        ("category replay witnesses", witness_count(expected, {"category_witnesses"})),
        ("checked QF_UF/Alethe fixtures", check_counts(expected)["checked"]),
    ]
    return rows, families, "Generate category-normalization and equivalence-pair query rows across the bounded policy domain."


def workflow_metrics(expected: dict[str, Any]) -> tuple[int, list[tuple[str, int]], str]:
    sample = expected["sample_domain"]
    states = sample["states"]
    actions = sample["actions"]
    booleans = sample["booleans"]
    rows = len(states) * len(actions) * len(booleans)
    two_step_rows = rows * len(actions) * len(booleans)
    terminal_rows = len(expected["parameters"]["terminal_states"]) * len(actions) * len(
        booleans
    )
    families = [
        ("bounded workflow transition rows", rows),
        ("two-step reachability rows", two_step_rows),
        ("terminal-state transition rows", terminal_rows),
        ("transition replay witnesses", witness_count(expected, {"transition_witnesses"})),
        ("checked Bool/QF_LIA fixtures", check_counts(expected)["checked"]),
    ]
    return rows, families, "Generate workflow transition, terminal-state, and two-step reachability rows across the bounded state graph."


def generic_metrics(expected: dict[str, Any]) -> tuple[int, list[tuple[str, int]], str]:
    sample = expected.get("sample_domain", {})
    rows = product([len(value) for value in sample.values() if isinstance(value, list)])
    families = [
        ("bounded sample rows", rows),
        ("replay witnesses", len(expected.get("witnesses", []))),
        ("checked fixtures", check_counts(expected)["checked"]),
    ]
    return rows, families, "Classify generated query families for this pack."


def benefit_query_families(expected: dict[str, Any]) -> list[dict[str, Any]]:
    params = expected["parameters"]
    sample = expected["sample_domain"]
    booleans = sample["booleans"]
    coverage_rows = []
    for age in sample["ages"]:
        for income in sample["incomes"]:
            for date in sample["dates"]:
                for resident in booleans:
                    for veteran in booleans:
                        for sanctioned in booleans:
                            facts = {
                                "age": age,
                                "income": income,
                                "resident": resident,
                                "veteran": veteran,
                                "sanctioned": sanctioned,
                                "application_date": date,
                            }
                            coverage_rows.append(
                                {
                                    "id": f"coverage-{len(coverage_rows):04d}",
                                    "facts": facts,
                                    "expected_eligible": benefit_eligible(facts, params),
                                }
                            )

    monotonicity_rows = []
    incomes = sample["incomes"]
    for age in sample["ages"]:
        for date in sample["dates"]:
            for resident in booleans:
                for veteran in booleans:
                    for sanctioned in booleans:
                        for lower_income, higher_income in zip(incomes, incomes[1:]):
                            lower_facts = {
                                "age": age,
                                "income": lower_income,
                                "resident": resident,
                                "veteran": veteran,
                                "sanctioned": sanctioned,
                                "application_date": date,
                            }
                            higher_facts = {
                                **lower_facts,
                                "income": higher_income,
                            }
                            lower_eligible = benefit_eligible(lower_facts, params)
                            higher_eligible = benefit_eligible(higher_facts, params)
                            monotonicity_rows.append(
                                {
                                    "id": f"income-monotonicity-{len(monotonicity_rows):04d}",
                                    "lower_facts": lower_facts,
                                    "higher_facts": higher_facts,
                                    "lower_eligible": lower_eligible,
                                    "higher_eligible": higher_eligible,
                                    "nonincreasing_holds": not (
                                        not lower_eligible and higher_eligible
                                    ),
                                }
                            )

    return [
        {
            "id": "coverage",
            "description": "Complete bounded applicant fact patterns with replayed eligibility output.",
            "rows": coverage_rows,
        },
        {
            "id": "income_monotonicity_adjacent",
            "description": "Adjacent income pairs for fixed non-income facts; increasing income must not turn ineligible into eligible.",
            "rows": monotonicity_rows,
        },
    ]


def authorization_query_families(expected: dict[str, Any]) -> list[dict[str, Any]]:
    sample = expected["sample_domain"]
    request_rows = []
    for user_tenant in sample["user_tenants"]:
        for resource_tenant in sample["resource_tenants"]:
            for role in sample["roles"]:
                for action in sample["actions"]:
                    for policy_version in sample["policy_versions"]:
                        for explicit_deny in sample["booleans"]:
                            facts = {
                                "user_tenant": user_tenant,
                                "resource_tenant": resource_tenant,
                                "role": role,
                                "action": action,
                                "explicit_deny": explicit_deny,
                                "policy_version": policy_version,
                            }
                            request_rows.append(
                                {
                                    "id": f"request-{len(request_rows):04d}",
                                    "facts": facts,
                                    "expected_allow": authorization_allows(facts),
                                }
                            )

    version_rows = []
    versions = sample["policy_versions"]
    for user_tenant in sample["user_tenants"]:
        for resource_tenant in sample["resource_tenants"]:
            for role in sample["roles"]:
                for action in sample["actions"]:
                    for explicit_deny in sample["booleans"]:
                        for before_version, after_version in zip(versions, versions[1:]):
                            before_facts = {
                                "user_tenant": user_tenant,
                                "resource_tenant": resource_tenant,
                                "role": role,
                                "action": action,
                                "explicit_deny": explicit_deny,
                                "policy_version": before_version,
                            }
                            after_facts = {
                                **before_facts,
                                "policy_version": after_version,
                            }
                            intended_delta = (
                                user_tenant == resource_tenant
                                and role == "analyst"
                                and action == "export"
                                and not explicit_deny
                            )
                            version_rows.append(
                                {
                                    "id": f"version-delta-{len(version_rows):04d}",
                                    "before_facts": before_facts,
                                    "after_facts": after_facts,
                                    "before_allow": authorization_allows(before_facts),
                                    "after_allow": authorization_allows(after_facts),
                                    "intended_delta": intended_delta,
                                }
                            )

    return [
        {
            "id": "bounded_requests",
            "description": "Complete bounded role/action/tenant/version requests with replayed allow output.",
            "rows": request_rows,
        },
        {
            "id": "version_delta_adjacent",
            "description": "Adjacent policy-version pairs; only same-tenant analyst export may change.",
            "rows": version_rows,
        },
    ]


def tax_benefit_query_families(expected: dict[str, Any]) -> list[dict[str, Any]]:
    params = expected["parameters"]
    sample = expected["sample_domain"]
    benefit_rows = []
    for income in sample["incomes"]:
        for household_size in sample["household_sizes"]:
            for date in sample["dates"]:
                facts = {
                    "income": income,
                    "household_size": household_size,
                    "application_date": date,
                }
                benefit_rows.append(
                    {
                        "id": f"benefit-{len(benefit_rows):04d}",
                        "facts": facts,
                        "expected_benefit": tax_benefit(facts, params),
                    }
                )

    monotonicity_rows = []
    incomes = sample["incomes"]
    for household_size in sample["household_sizes"]:
        for date in sample["dates"]:
            for lower_income, higher_income in zip(incomes, incomes[1:]):
                lower_facts = {
                    "income": lower_income,
                    "household_size": household_size,
                    "application_date": date,
                }
                higher_facts = {
                    **lower_facts,
                    "income": higher_income,
                }
                lower_benefit = tax_benefit(lower_facts, params)
                higher_benefit = tax_benefit(higher_facts, params)
                monotonicity_rows.append(
                    {
                        "id": f"phaseout-monotonicity-{len(monotonicity_rows):04d}",
                        "lower_facts": lower_facts,
                        "higher_facts": higher_facts,
                        "lower_benefit": lower_benefit,
                        "higher_benefit": higher_benefit,
                        "nonincreasing_holds": higher_benefit <= lower_benefit,
                    }
                )

    return [
        {
            "id": "bounded_benefits",
            "description": "Complete bounded income/household/date rows with replayed benefit amount.",
            "rows": benefit_rows,
        },
        {
            "id": "income_phaseout_adjacent",
            "description": "Adjacent income pairs for fixed household/date rows; benefit must not increase as income rises.",
            "rows": monotonicity_rows,
        },
    ]


def procurement_query_families(expected: dict[str, Any]) -> list[dict[str, Any]]:
    params = expected["parameters"]
    sample = expected["sample_domain"]
    booleans = sample["booleans"]
    award_rows = []
    for bid_amount in sample["bid_amounts"]:
        for quality_score in sample["quality_scores"]:
            for date in sample["dates"]:
                for small_business in booleans:
                    for debarred in booleans:
                        facts = {
                            "bid_amount": bid_amount,
                            "quality_score": quality_score,
                            "small_business": small_business,
                            "debarred": debarred,
                            "received_date": date,
                        }
                        award_rows.append(
                            {
                                "id": f"award-{len(award_rows):04d}",
                                "facts": facts,
                                "expected_award": procurement_award(facts, params),
                            }
                        )

    monotonicity_rows = []
    quality_scores = sample["quality_scores"]
    for bid_amount in sample["bid_amounts"]:
        for date in sample["dates"]:
            for small_business in booleans:
                for debarred in booleans:
                    for lower_score, higher_score in zip(
                        quality_scores, quality_scores[1:]
                    ):
                        lower_facts = {
                            "bid_amount": bid_amount,
                            "quality_score": lower_score,
                            "small_business": small_business,
                            "debarred": debarred,
                            "received_date": date,
                        }
                        higher_facts = {
                            **lower_facts,
                            "quality_score": higher_score,
                        }
                        lower_award = procurement_award(lower_facts, params)
                        higher_award = procurement_award(higher_facts, params)
                        monotonicity_rows.append(
                            {
                                "id": f"quality-monotonicity-{len(monotonicity_rows):04d}",
                                "lower_facts": lower_facts,
                                "higher_facts": higher_facts,
                                "lower_award": lower_award,
                                "higher_award": higher_award,
                                "nondecreasing_holds": not (
                                    lower_award and not higher_award
                                ),
                            }
                        )

    return [
        {
            "id": "bounded_awards",
            "description": "Complete bounded bid/score/date/exclusion rows with replayed award output.",
            "rows": award_rows,
        },
        {
            "id": "quality_monotonicity_adjacent",
            "description": "Adjacent quality-score pairs for fixed non-score facts; higher quality must not lose an award already won.",
            "rows": monotonicity_rows,
        },
    ]


def grant_allocation_query_families(expected: dict[str, Any]) -> list[dict[str, Any]]:
    params = expected["parameters"]
    sample = expected["sample_domain"]
    shares = sample["shares"]
    allocation_rows = []
    balanced_rows = []
    total_share = parse_rational(params["total_share"])
    for shelter in shares:
        for clinic in shares:
            for admin in shares:
                facts = {
                    "shelter_share": shelter,
                    "clinic_share": clinic,
                    "admin_share": admin,
                }
                compliant = grant_allocation_compliant(facts, params)
                allocation_rows.append(
                    {
                        "id": f"allocation-{len(allocation_rows):04d}",
                        "facts": facts,
                        "expected_compliant": compliant,
                    }
                )
                if (
                    parse_rational(shelter)
                    + parse_rational(clinic)
                    + parse_rational(admin)
                    == total_share
                ):
                    balanced_rows.append(
                        {
                            "id": f"balanced-allocation-{len(balanced_rows):04d}",
                            "facts": facts,
                            "shelter_floor_holds": parse_rational(shelter)
                            >= parse_rational(params["shelter_minimum"]),
                            "clinic_floor_holds": parse_rational(clinic)
                            >= parse_rational(params["clinic_minimum"]),
                            "admin_cap_holds": parse_rational(admin)
                            <= parse_rational(params["admin_cap"]),
                            "expected_compliant": compliant,
                        }
                    )

    return [
        {
            "id": "bounded_allocations",
            "description": "Complete bounded rational allocation triples with replayed compliance output.",
            "rows": allocation_rows,
        },
        {
            "id": "balanced_budget_allocations",
            "description": "Balanced-budget allocation triples, exposing floor and cap outcomes separately.",
            "rows": balanced_rows,
        },
    ]


def category_equivalence_query_families(expected: dict[str, Any]) -> list[dict[str, Any]]:
    params = expected["parameters"]
    sample = expected["sample_domain"]
    category_rows = []
    for category in sample["categories"]:
        for program in sample["programs"]:
            facts = {
                "applicant_category": category,
                "program": program,
            }
            category_rows.append(
                {
                    "id": f"category-row-{len(category_rows):04d}",
                    "facts": facts,
                    "canonical_category": category_canonical(category, params),
                    "expected_priority_review": category_priority_review(facts, params),
                }
            )

    pair_rows = []
    for left, right in params["equivalence_pairs"]:
        for program in sample["programs"]:
            left_facts = {
                "applicant_category": left,
                "program": program,
            }
            right_facts = {
                "applicant_category": right,
                "program": program,
            }
            left_priority = category_priority_review(left_facts, params)
            right_priority = category_priority_review(right_facts, params)
            pair_rows.append(
                {
                    "id": f"equivalence-pair-{len(pair_rows):04d}",
                    "left_facts": left_facts,
                    "right_facts": right_facts,
                    "left_priority_review": left_priority,
                    "right_priority_review": right_priority,
                    "congruent_priority_holds": left_priority == right_priority,
                }
            )

    return [
        {
            "id": "bounded_category_rows",
            "description": "Complete bounded category/program rows with replayed priority-review output.",
            "rows": category_rows,
        },
        {
            "id": "equivalence_pair_rows",
            "description": "Equivalent-category pairs for each program; priority-review outputs must agree.",
            "rows": pair_rows,
        },
    ]


def workflow_query_families(expected: dict[str, Any]) -> list[dict[str, Any]]:
    params = expected["parameters"]
    sample = expected["sample_domain"]
    transition_rows = []
    for state in sample["states"]:
        for action in sample["actions"]:
            for supervisor in sample["booleans"]:
                facts = {
                    "current_state": state,
                    "action": action,
                    "supervisor_review": supervisor,
                }
                allowed, next_state = workflow_transition(facts, params)
                transition_rows.append(
                    {
                        "id": f"transition-row-{len(transition_rows):04d}",
                        "facts": facts,
                        "expected_allowed": allowed,
                        "expected_next_state": next_state,
                        "terminal_state": state in params["terminal_states"],
                    }
                )

    two_step_rows = []
    for state in sample["states"]:
        for first_action in sample["actions"]:
            for second_action in sample["actions"]:
                for first_supervisor in sample["booleans"]:
                    for second_supervisor in sample["booleans"]:
                        first_facts = {
                            "current_state": state,
                            "action": first_action,
                            "supervisor_review": first_supervisor,
                        }
                        first_allowed, first_next = workflow_transition(
                            first_facts, params
                        )
                        second_facts = {
                            "current_state": first_next,
                            "action": second_action,
                            "supervisor_review": second_supervisor,
                        }
                        second_allowed, final_state = workflow_transition(
                            second_facts, params
                        )
                        two_step_rows.append(
                            {
                                "id": f"two-step-row-{len(two_step_rows):04d}",
                                "first_facts": first_facts,
                                "second_facts": second_facts,
                                "first_allowed": first_allowed,
                                "second_allowed": second_allowed,
                                "final_state": final_state,
                                "reached_approved": final_state
                                == params["approved_state"],
                            }
                        )

    return [
        {
            "id": "bounded_transition_rows",
            "description": "Complete bounded one-step workflow transitions with replayed allow and next-state outputs.",
            "rows": transition_rows,
        },
        {
            "id": "two_step_reachability_rows",
            "description": "Two-step workflow paths obtained by composing the bounded transition relation.",
            "rows": two_step_rows,
        },
    ]


METRIC_DISPATCH = {
    "benefit_eligibility_v0": benefit_metrics,
    "authorization_policy_v0": authorization_metrics,
    "tax_benefit_arithmetic_v0": tax_benefit_metrics,
    "procurement_scoring_v0": procurement_metrics,
    "grant_allocation_v0": grant_allocation_metrics,
    "category_equivalence_v0": category_equivalence_metrics,
    "workflow_reachability_v0": workflow_metrics,
}

QUERY_DISPATCH = {
    "benefit_eligibility_v0": benefit_query_families,
    "authorization_policy_v0": authorization_query_families,
    "tax_benefit_arithmetic_v0": tax_benefit_query_families,
    "procurement_scoring_v0": procurement_query_families,
    "grant_allocation_v0": grant_allocation_query_families,
    "category_equivalence_v0": category_equivalence_query_families,
    "workflow_reachability_v0": workflow_query_families,
}


def table_cell(value: str) -> str:
    return value.replace("\n", " ").replace("|", "\\|")


def load_packs() -> list[dict[str, Any]]:
    packs = []
    for metadata_path in sorted(EXAMPLES_ROOT.glob("*/metadata.json")):
        metadata = load_json(metadata_path)
        expected = load_json(metadata_path.parent / "expected.json")
        metric_fn = METRIC_DISPATCH.get(metadata["id"], generic_metrics)
        sample_rows, families, next_step = metric_fn(expected)
        query_fn = QUERY_DISPATCH[metadata["id"]]
        query_families = query_fn(expected)
        query_rows = sum(len(family["rows"]) for family in query_families)
        packs.append(
            {
                "dir": metadata_path.parent.name,
                "metadata": metadata,
                "expected": expected,
                "sample_rows": sample_rows,
                "families": families,
                "next_step": next_step,
                "query_families": query_families,
                "query_rows": query_rows,
            }
        )
    return packs


def write_query_files(packs: list[dict[str, Any]]) -> None:
    QUERY_DIR.mkdir(parents=True, exist_ok=True)
    for pack in packs:
        metadata = pack["metadata"]
        payload = {
            "schema_version": 1,
            "generated_by": "python3 scripts/gen-rules-as-code-dashboard.py",
            "pack_id": metadata["id"],
            "pack_title": metadata["title"],
            "source_pack": f"docs/rules-as-code/examples/{pack['dir']}",
            "query_families": [
                {
                    "id": family["id"],
                    "description": family["description"],
                    "row_count": len(family["rows"]),
                    "rows": family["rows"],
                }
                for family in pack["query_families"]
            ],
        }
        query_path = QUERY_DIR / f"{pack['dir']}.json"
        query_path.write_text(render_query_payload(payload), encoding="utf-8")


def render_query_payload(payload: dict[str, Any]) -> str:
    lines = [
        "{",
        f'  "schema_version": {json.dumps(payload["schema_version"])},',
        f'  "generated_by": {json.dumps(payload["generated_by"])},',
        f'  "pack_id": {json.dumps(payload["pack_id"])},',
        f'  "pack_title": {json.dumps(payload["pack_title"])},',
        f'  "source_pack": {json.dumps(payload["source_pack"])},',
        '  "query_families": [',
    ]
    families = payload["query_families"]
    for family_index, family in enumerate(families):
        family_comma = "," if family_index + 1 < len(families) else ""
        lines.extend(
            [
                "    {",
                f'      "id": {json.dumps(family["id"])},',
                f'      "description": {json.dumps(family["description"])},',
                f'      "row_count": {json.dumps(family["row_count"])},',
                '      "rows": [',
            ]
        )
        rows = family["rows"]
        for row_index, row in enumerate(rows):
            row_comma = "," if row_index + 1 < len(rows) else ""
            lines.append(
                "        "
                + json.dumps(row, separators=(",", ":"))
                + row_comma
            )
        lines.extend(["      ]", f"    }}{family_comma}"])
    lines.extend(["  ]", "}", ""])
    return "\n".join(lines)


def render(packs: list[dict[str, Any]]) -> str:
    proof_counts = Counter()
    result_counts = Counter()
    total_rows = 0
    generated_query_rows = 0
    for pack in packs:
        total_rows += pack["sample_rows"]
        generated_query_rows += pack["query_rows"]
        proof_counts.update(check_counts(pack["expected"]))
        result_counts.update(check["expected_result"] for check in pack["expected"]["checks"])

    lines = [
        "# Rules-As-Code Generated Query Dashboard",
        "",
        "Generated by `python3 scripts/gen-rules-as-code-dashboard.py`.",
        "",
        "This dashboard turns the current rule-pack JSON into a bounded query",
        "planning surface. It is not a legal corpus and not a solver-performance",
        "benchmark; it records which finite rule domains can be expanded into",
        "generated coverage, equivalence, threshold, cap, or monotonicity checks.",
        "It now also includes rational-allocation rows for QF_LRA/Farkas,",
        "checked category-equivalence rows for QF_UF/Alethe, and bounded",
        "workflow-reachability rows over a finite state graph.",
        "",
        "## Summary",
        "",
        f"- Rule packs: {len(packs)}",
        f"- Bounded sample rows: {total_rows}",
        f"- Generated query rows: {generated_query_rows}",
        f"- Check results: {', '.join(f'{key}:{result_counts[key]}' for key in sorted(result_counts))}",
        f"- Proof statuses: {', '.join(f'{key}:{proof_counts[key]}' for key in sorted(proof_counts))}",
        "",
        "## Pack Query Surface",
        "",
        "| Pack | Bounded Rows | Generated Query Rows | Query Artifact | Generated Query Families | Current Evidence | Next Generated Step |",
        "|---|---:|---:|---|---|---|---|",
    ]

    for pack in packs:
        metadata = pack["metadata"]
        expected = pack["expected"]
        counts = check_counts(expected)
        evidence = ", ".join(f"{key}:{counts[key]}" for key in sorted(counts))
        families = "<br>".join(f"{name}: {count}" for name, count in pack["families"])
        link = f"[{metadata['title']}](../examples/{pack['dir']}/README.md)"
        query_link = f"[queries/{pack['dir']}.json](queries/{pack['dir']}.json)"
        lines.append(
            "| "
            + " | ".join(
                [
                    link,
                    str(pack["sample_rows"]),
                    str(pack["query_rows"]),
                    query_link,
                    table_cell(families),
                    table_cell(evidence),
                    table_cell(pack["next_step"]),
                ]
            )
            + " |"
        )

    lines.extend(
        [
            "",
            "## Trust Boundary",
            "",
            "- The source rule text and formal model remain human-authored inputs.",
            "- Generated rows are useful only when each row cites the source pack and",
            "  replays against the original rule model.",
            "- The JSON files under `generated/queries/` are deterministic derived",
            "  artifacts; the validator replays them from the committed pack models.",
            "- Checked `unsat` rows must keep source-linked SMT-LIB fixtures and the",
            "  `rules_as_code_examples` certified-evidence regression.",
            "- Proof-gap `unsat` rows must keep source-linked artifacts and name the",
            "  missing proof route before they can graduate to checked evidence.",
            "- These bounded domains do not prove compliance with real law and should",
            "  not be used as solver parity benchmarks.",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> int:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    packs = load_packs()
    write_query_files(packs)
    OUT_PATH.write_text(render(packs), encoding="utf-8")
    print(f"generated {OUT_PATH.relative_to(ROOT)}")
    print(f"generated {len(packs)} rules-as-code query artifacts")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
