#!/usr/bin/env python3
"""Generate the Rules-as-Code bounded query dashboard."""

from __future__ import annotations

import json
from collections import Counter
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
EXAMPLES_ROOT = ROOT / "docs" / "rules-as-code" / "examples"
OUT_DIR = ROOT / "docs" / "rules-as-code" / "generated"
OUT_PATH = OUT_DIR / "rules-query-dashboard.md"


def load_json(path: Path) -> Any:
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def product(values: list[int]) -> int:
    result = 1
    for value in values:
        result *= value
    return result


def check_counts(expected: dict[str, Any]) -> Counter[str]:
    return Counter(check["proof_status"] for check in expected["checks"])


def witness_count(expected: dict[str, Any], check_ids: set[str]) -> int:
    total = 0
    for check in expected["checks"]:
        if check["id"] in check_ids:
            total += len(check.get("witnesses", []))
    return total


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


def generic_metrics(expected: dict[str, Any]) -> tuple[int, list[tuple[str, int]], str]:
    sample = expected.get("sample_domain", {})
    rows = product([len(value) for value in sample.values() if isinstance(value, list)])
    families = [
        ("bounded sample rows", rows),
        ("replay witnesses", len(expected.get("witnesses", []))),
        ("checked fixtures", check_counts(expected)["checked"]),
    ]
    return rows, families, "Classify generated query families for this pack."


METRIC_DISPATCH = {
    "benefit_eligibility_v0": benefit_metrics,
    "authorization_policy_v0": authorization_metrics,
    "tax_benefit_arithmetic_v0": tax_benefit_metrics,
}


def table_cell(value: str) -> str:
    return value.replace("\n", " ").replace("|", "\\|")


def render() -> str:
    packs = []
    for metadata_path in sorted(EXAMPLES_ROOT.glob("*/metadata.json")):
        metadata = load_json(metadata_path)
        expected = load_json(metadata_path.parent / "expected.json")
        metric_fn = METRIC_DISPATCH.get(metadata["id"], generic_metrics)
        sample_rows, families, next_step = metric_fn(expected)
        packs.append(
            {
                "dir": metadata_path.parent.name,
                "metadata": metadata,
                "expected": expected,
                "sample_rows": sample_rows,
                "families": families,
                "next_step": next_step,
            }
        )

    proof_counts = Counter()
    result_counts = Counter()
    total_rows = 0
    for pack in packs:
        total_rows += pack["sample_rows"]
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
        "",
        "## Summary",
        "",
        f"- Rule packs: {len(packs)}",
        f"- Bounded sample rows: {total_rows}",
        f"- Check results: {', '.join(f'{key}:{result_counts[key]}' for key in sorted(result_counts))}",
        f"- Proof statuses: {', '.join(f'{key}:{proof_counts[key]}' for key in sorted(proof_counts))}",
        "",
        "## Pack Query Surface",
        "",
        "| Pack | Bounded Rows | Generated Query Families | Current Evidence | Next Generated Step |",
        "|---|---:|---|---|---|",
    ]

    for pack in packs:
        metadata = pack["metadata"]
        expected = pack["expected"]
        counts = check_counts(expected)
        evidence = ", ".join(f"{key}:{counts[key]}" for key in sorted(counts))
        families = "<br>".join(f"{name}: {count}" for name, count in pack["families"])
        link = f"[{metadata['title']}](../examples/{pack['dir']}/README.md)"
        lines.append(
            "| "
            + " | ".join(
                [
                    link,
                    str(pack["sample_rows"]),
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
            "- Checked `unsat` rows must keep source-linked SMT-LIB fixtures and the",
            "  `rules_as_code_examples` certified-evidence regression.",
            "- These bounded domains do not prove compliance with real law and should",
            "  not be used as solver parity benchmarks.",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> int:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    OUT_PATH.write_text(render(), encoding="utf-8")
    print(f"generated {OUT_PATH.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
