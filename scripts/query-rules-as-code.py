#!/usr/bin/env python3
"""Query the Rules-as-Code Verification Lab JSON boundary."""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
EXAMPLES_ROOT = ROOT / "docs" / "rules-as-code" / "examples"
GENERATED_QUERIES_ROOT = ROOT / "docs" / "rules-as-code" / "generated" / "queries"


class QueryError(Exception):
    pass


def load_json(path: Path) -> Any:
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def text_blob(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).lower()


def matches_text(value: Any, needle: str | None) -> bool:
    if not needle:
        return True
    return needle.lower() in text_blob(value)


def table_cell(value: Any) -> str:
    if isinstance(value, (list, tuple, set)):
        text = ", ".join(str(item) for item in value)
    elif isinstance(value, dict):
        text = json.dumps(value, sort_keys=True, separators=(",", ":"))
    else:
        text = str(value)
    return text.replace("\n", " ").replace("|", "\\|")


def count_text(counter: Counter[str]) -> str:
    if not counter:
        return "-"
    return ",".join(f"{key}:{counter[key]}" for key in sorted(counter))


def emit_table(headers: list[str], rows: list[list[Any]]) -> None:
    print("| " + " | ".join(headers) + " |")
    print("|" + "|".join("---" for _ in headers) + "|")
    for row in rows:
        print("| " + " | ".join(table_cell(value) for value in row) + " |")


def load_packs() -> list[dict[str, Any]]:
    packs: list[dict[str, Any]] = []
    for metadata_path in sorted(EXAMPLES_ROOT.glob("*/metadata.json")):
        pack_dir = metadata_path.parent
        expected_path = pack_dir / "expected.json"
        query_path = GENERATED_QUERIES_ROOT / f"{pack_dir.name}.json"
        metadata = load_json(metadata_path)
        expected = load_json(expected_path)
        generated = load_json(query_path) if query_path.exists() else None
        packs.append(
            {
                "dir": pack_dir.name,
                "path": f"docs/rules-as-code/examples/{pack_dir.name}",
                "metadata": metadata,
                "expected": expected,
                "generated": generated,
            }
        )
    if not packs:
        raise QueryError("no rules-as-code packs found")
    return packs


def pack_matches(pack: dict[str, Any], pack_filter: str | None) -> bool:
    if not pack_filter:
        return True
    return pack_filter in {pack["dir"], pack["metadata"]["id"]}


def filter_packs(args: argparse.Namespace, packs: list[dict[str, Any]]) -> list[dict[str, Any]]:
    rows = []
    for pack in packs:
        metadata = pack["metadata"]
        expected = pack["expected"]
        if args.pack and not pack_matches(pack, args.pack):
            continue
        if args.domain and metadata["domain"] != args.domain:
            continue
        if args.fragment and args.fragment not in metadata["axeyum_fragments"]:
            continue
        if args.proof_status:
            statuses = {check["proof_status"] for check in expected["checks"]}
            if args.proof_status not in statuses:
                continue
        if args.expected_result:
            results = {check["expected_result"] for check in expected["checks"]}
            if args.expected_result not in results:
                continue
        if not matches_text({"metadata": metadata, "expected": expected}, args.text):
            continue
        rows.append(pack)
    return rows


def generated_row_count(pack: dict[str, Any]) -> int:
    generated = pack["generated"]
    if generated:
        return sum(family["row_count"] for family in generated["query_families"])

    sample = pack["expected"].get("sample_domain", {})
    sample_count = 1
    for value in sample.values():
        if isinstance(value, list):
            sample_count *= len(value)
    return sample_count


def generated_family_count(pack: dict[str, Any]) -> int:
    generated = pack["generated"]
    return len(generated["query_families"]) if generated else 0


def bounded_sample_row_count(pack: dict[str, Any]) -> int:
    generated = pack["generated"]
    if generated:
        return generated["query_families"][0]["row_count"]
    return generated_row_count(pack)


def check_required(args: argparse.Namespace, rows: list[Any]) -> None:
    if args.require_any and not rows:
        raise QueryError("query returned no rows")


def command_summary(args: argparse.Namespace) -> None:
    packs = load_packs()
    check_results: dict[str, int] = {}
    proof_statuses: dict[str, int] = {}
    generated_rows = 0
    bounded_rows = 0
    for pack in packs:
        expected = pack["expected"]
        generated = pack["generated"]
        bounded_rows += bounded_sample_row_count(pack)
        for check in expected["checks"]:
            check_results[check["expected_result"]] = (
                check_results.get(check["expected_result"], 0) + 1
            )
            proof_statuses[check["proof_status"]] = (
                proof_statuses.get(check["proof_status"], 0) + 1
            )
        if generated:
            generated_rows += sum(
                family["row_count"] for family in generated["query_families"]
            )

    payload = {
        "rule_packs": len(packs),
        "bounded_sample_rows": bounded_rows,
        "generated_query_rows": generated_rows,
        "check_results": dict(sorted(check_results.items())),
        "proof_statuses": dict(sorted(proof_statuses.items())),
    }
    if args.format == "json":
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        for key, value in payload.items():
            print(f"{key}={value}")


def command_packs(args: argparse.Namespace) -> None:
    packs = filter_packs(args, load_packs())
    check_required(args, packs)
    if args.format == "json":
        print(json.dumps(packs, indent=2, sort_keys=True))
        return
    rows = []
    for pack in packs:
        metadata = pack["metadata"]
        expected = pack["expected"]
        rows.append(
            [
                metadata["id"],
                metadata["domain"],
                pack["dir"],
                len(expected["checks"]),
                ", ".join(sorted({check["proof_status"] for check in expected["checks"]})),
                ", ".join(metadata["axeyum_fragments"]),
            ]
        )
    emit_table(["Pack", "Domain", "Directory", "Checks", "Proof Statuses", "Fragments"], rows)


def iter_checks(packs: list[dict[str, Any]]) -> list[dict[str, Any]]:
    rows = []
    for pack in packs:
        for check in pack["expected"]["checks"]:
            rows.append(
                {
                    "pack_id": pack["metadata"]["id"],
                    "pack_dir": pack["dir"],
                    **check,
                }
            )
    return rows


def command_checks(args: argparse.Namespace) -> None:
    packs = [pack for pack in load_packs() if pack_matches(pack, args.pack)]
    rows = []
    for row in iter_checks(packs):
        if args.expected_result and row["expected_result"] != args.expected_result:
            continue
        if args.proof_status and row["proof_status"] != args.proof_status:
            continue
        if args.validation and row["validation"] != args.validation:
            continue
        if not matches_text(row, args.text):
            continue
        rows.append(row)
    check_required(args, rows)
    if args.format == "json":
        print(json.dumps(rows, indent=2, sort_keys=True))
        return
    emit_table(
        ["Pack", "Check", "Result", "Proof", "Validation", "Witnesses"],
        [
            [
                row["pack_id"],
                row["id"],
                row["expected_result"],
                row["proof_status"],
                row["validation"],
                ", ".join(row.get("witnesses", [])),
            ]
            for row in rows
        ],
    )


def iter_families(packs: list[dict[str, Any]]) -> list[dict[str, Any]]:
    rows = []
    for pack in packs:
        generated = pack["generated"]
        if not generated:
            continue
        for family in generated["query_families"]:
            rows.append(
                {
                    "pack_id": pack["metadata"]["id"],
                    "pack_dir": pack["dir"],
                    **family,
                }
            )
    return rows


def command_families(args: argparse.Namespace) -> None:
    packs = [pack for pack in load_packs() if pack_matches(pack, args.pack)]
    rows = []
    for row in iter_families(packs):
        if args.family and row["id"] != args.family:
            continue
        if not matches_text(row, args.text):
            continue
        rows.append(row)
    check_required(args, rows)
    if args.format == "json":
        print(json.dumps(rows, indent=2, sort_keys=True))
        return
    emit_table(
        ["Pack", "Family", "Rows", "Description"],
        [
            [row["pack_id"], row["id"], row["row_count"], row["description"]]
            for row in rows
        ],
    )


def command_rows(args: argparse.Namespace) -> None:
    if args.limit < 1:
        raise QueryError("--limit must be positive")
    packs = [pack for pack in load_packs() if pack_matches(pack, args.pack)]
    rows = []
    for family in iter_families(packs):
        if args.family and family["id"] != args.family:
            continue
        for row in family["rows"]:
            payload = {
                "pack_id": family["pack_id"],
                "family_id": family["id"],
                **row,
            }
            if not matches_text(payload, args.text):
                continue
            rows.append(payload)
    check_required(args, rows)
    rows = rows[: args.limit]
    if args.format == "json":
        print(json.dumps(rows, indent=2, sort_keys=True))
        return
    emit_table(
        ["Pack", "Family", "Row", "Payload"],
        [
            [
                row["pack_id"],
                row["family_id"],
                row["id"],
                {key: value for key, value in row.items() if key not in {"pack_id", "family_id", "id"}},
            ]
            for row in rows
        ],
    )


def group_keys(pack: dict[str, Any], by: str) -> list[str]:
    metadata = pack["metadata"]
    checks = pack["expected"]["checks"]
    if by == "domain":
        return [metadata["domain"]]
    if by == "fragment":
        return list(metadata["axeyum_fragments"])
    if by == "validation":
        return sorted({check["validation"] for check in checks})
    if by == "proof-status":
        return sorted({check["proof_status"] for check in checks})
    raise QueryError(f"unsupported coverage group: {by}")


def checks_for_group(checks: list[dict[str, Any]], by: str, key: str) -> list[dict[str, Any]]:
    if by == "validation":
        return [check for check in checks if check["validation"] == key]
    if by == "proof-status":
        return [check for check in checks if check["proof_status"] == key]
    return checks


def command_coverage(args: argparse.Namespace) -> None:
    groups: dict[str, dict[str, Any]] = {}
    for pack in load_packs():
        metadata = pack["metadata"]
        checks = pack["expected"]["checks"]
        if args.domain and metadata["domain"] != args.domain:
            continue
        if args.fragment and args.fragment not in metadata["axeyum_fragments"]:
            continue
        if not matches_text({"metadata": metadata, "expected": pack["expected"]}, args.text):
            continue

        for key in group_keys(pack, args.by):
            matching_checks = checks_for_group(checks, args.by, key)
            group = groups.setdefault(
                key,
                {
                    "group": key,
                    "packs": set(),
                    "checks": 0,
                    "generated_families": 0,
                    "generated_rows": 0,
                    "results": Counter(),
                    "proof_statuses": Counter(),
                    "validations": Counter(),
                    "fragments": set(),
                },
            )
            group["packs"].add(metadata["id"])
            group["checks"] += len(matching_checks)
            group["generated_families"] += generated_family_count(pack)
            group["generated_rows"] += generated_row_count(pack)
            group["fragments"].update(metadata["axeyum_fragments"])
            for check in matching_checks:
                group["results"][check["expected_result"]] += 1
                group["proof_statuses"][check["proof_status"]] += 1
                group["validations"][check["validation"]] += 1

    rows = []
    for group in groups.values():
        packs = sorted(group["packs"])
        row = {
            "group": group["group"],
            "packs": len(packs),
            "checks": group["checks"],
            "generated_families": group["generated_families"],
            "generated_rows": group["generated_rows"],
            "results": dict(sorted(group["results"].items())),
            "proof_statuses": dict(sorted(group["proof_statuses"].items())),
            "validations": dict(sorted(group["validations"].items())),
            "fragments": sorted(group["fragments"]),
            "sample_packs": packs[:5],
        }
        rows.append(row)
    rows.sort(key=lambda row: row["group"])
    check_required(args, rows)

    if args.format == "json":
        print(json.dumps(rows, indent=2, sort_keys=True))
        return
    emit_table(
        [
            "Group",
            "Packs",
            "Checks",
            "Generated Families",
            "Generated Rows",
            "Proof Statuses",
            "Validations",
            "Sample Packs",
        ],
        [
            [
                row["group"],
                row["packs"],
                row["checks"],
                row["generated_families"],
                row["generated_rows"],
                count_text(Counter(row["proof_statuses"])),
                count_text(Counter(row["validations"])),
                ", ".join(row["sample_packs"]),
            ]
            for row in rows
        ],
    )


def add_common_filters(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--pack", help="metadata id or directory name")
    parser.add_argument("--text", help="case-insensitive JSON text search")
    parser.add_argument("--require-any", action="store_true", help="fail if no rows match")
    parser.add_argument("--format", choices=["table", "json"], default="table")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    summary = subparsers.add_parser("summary", help="print aggregate counts")
    summary.add_argument("--format", choices=["table", "json"], default="table")
    summary.set_defaults(func=command_summary)

    packs = subparsers.add_parser("packs", help="list rule packs")
    add_common_filters(packs)
    packs.add_argument("--domain")
    packs.add_argument("--fragment")
    packs.add_argument("--proof-status")
    packs.add_argument("--expected-result")
    packs.set_defaults(func=command_packs)

    checks = subparsers.add_parser("checks", help="list expected-result checks")
    add_common_filters(checks)
    checks.add_argument("--expected-result", choices=["sat", "unsat", "unknown"])
    checks.add_argument("--proof-status")
    checks.add_argument("--validation")
    checks.set_defaults(func=command_checks)

    families = subparsers.add_parser("families", help="list generated query families")
    add_common_filters(families)
    families.add_argument("--family")
    families.set_defaults(func=command_families)

    rows = subparsers.add_parser("rows", help="list generated query rows")
    add_common_filters(rows)
    rows.add_argument("--family")
    rows.add_argument("--limit", type=int, default=10)
    rows.set_defaults(func=command_rows)

    coverage = subparsers.add_parser("coverage", help="summarize rule coverage groups")
    coverage.add_argument(
        "--by",
        choices=["domain", "fragment", "validation", "proof-status"],
        default="domain",
        help="coverage grouping dimension",
    )
    coverage.add_argument("--domain", help="exact metadata domain")
    coverage.add_argument("--fragment", help="exact axeyum fragment")
    coverage.add_argument("--text", help="case-insensitive JSON text search")
    coverage.add_argument("--require-any", action="store_true", help="fail if no rows match")
    coverage.add_argument("--format", choices=["table", "json"], default="table")
    coverage.set_defaults(func=command_coverage)

    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    try:
        args.func(args)
    except QueryError as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
