#!/usr/bin/env python3
"""Validate and render the committed SMT-LIB/API conformance manifest.

The manifest deliberately separates syntax acceptance from execution and output.
That prevents a direct Rust helper, a parse-time no-op, or a single-query value
from being reported as an interactive SMT-LIB implementation.  Source assertions
and exact test names make the document drift when the implementation changes.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "docs" / "plan" / "smtlib-api-conformance-v1.json"
OUT_MD = ROOT / "docs" / "plan" / "generated" / "smtlib-api-conformance.md"

PARSE_STATES = {
    "absent",
    "accepted-noop",
    "recorded-global",
    "recorded-at-command-point",
    "semantic",
    "rejected",
}
EXECUTION_STATES = {
    "none",
    "direct-api-only",
    "parse-time-semantics",
    "single-query-helper",
    "incremental-query",
    "optimization-helper",
}
OUTPUT_STATES = {
    "none",
    "rust-value",
    "canonical-text-artifact",
    "interactive-session-text",
}
ASSURANCE_STATES = {
    "none",
    "evaluator",
    "model-replay",
    "solver-recheck",
    "internal-proof-check",
    "external-proof-check",
    "verify-before-return",
}

PARSE_LABELS = {
    "absent": "absent",
    "accepted-noop": "accepted/no-op",
    "recorded-global": "recorded globally",
    "recorded-at-command-point": "command-point",
    "semantic": "semantic",
    "rejected": "rejected",
}
EXECUTION_LABELS = {
    "none": "none",
    "direct-api-only": "direct API only",
    "parse-time-semantics": "parse-time semantics",
    "single-query-helper": "single-query helper",
    "incremental-query": "incremental query",
    "optimization-helper": "optimization helper",
}
OUTPUT_LABELS = {
    "none": "none",
    "rust-value": "Rust value",
    "canonical-text-artifact": "canonical text artifact",
    "interactive-session-text": "interactive session text",
}


def relative(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def load_manifest() -> dict:
    with MANIFEST.open(encoding="utf-8") as handle:
        return json.load(handle)


def validate_enum(row: dict, key: str, allowed: set[str], failures: list[str]) -> None:
    value = row.get(key)
    if value not in allowed:
        failures.append(
            f"{row.get('id', '<unknown>')}: invalid {key} {value!r}; "
            f"expected one of {sorted(allowed)}"
        )


def validate_manifest(data: dict) -> list[str]:
    failures: list[str] = []
    if data.get("version") != 1:
        failures.append("manifest version must be 1")
    rows = data.get("rows")
    if not isinstance(rows, list) or not rows:
        return failures + ["manifest rows must be a non-empty list"]

    ids = [row.get("id") for row in rows]
    duplicates = sorted(value for value, count in Counter(ids).items() if count > 1)
    if duplicates:
        failures.append(f"duplicate row ids: {duplicates}")

    source_cache: dict[Path, str] = {}
    for row in rows:
        row_id = row.get("id", "<unknown>")
        for key in ("id", "surface", "syntax", "scope", "residual"):
            if not row.get(key):
                failures.append(f"{row_id}: missing non-empty {key}")
        validate_enum(row, "parse", PARSE_STATES, failures)
        validate_enum(row, "execution", EXECUTION_STATES, failures)
        validate_enum(row, "output", OUTPUT_STATES, failures)

        assurance = row.get("assurance")
        if not isinstance(assurance, list) or not assurance:
            failures.append(f"{row_id}: assurance must be a non-empty list")
        else:
            bad = sorted(set(assurance) - ASSURANCE_STATES)
            if bad:
                failures.append(f"{row_id}: invalid assurance values {bad}")

        tests = row.get("tests", [])
        if not isinstance(tests, list):
            failures.append(f"{row_id}: tests must be a list")
            tests = []
        for test in tests:
            test_path = ROOT / test.get("path", "")
            test_name = test.get("name", "")
            if not test_path.is_file():
                failures.append(f"{row_id}: missing test file {test_path}")
                continue
            text = source_cache.setdefault(
                test_path, test_path.read_text(encoding="utf-8")
            )
            if not re.search(rf"\bfn\s+{re.escape(test_name)}\s*\(", text):
                failures.append(
                    f"{row_id}: test {test_name!r} not found in {relative(test_path)}"
                )

        assertions = row.get("source_assertions", [])
        if not isinstance(assertions, list) or not assertions:
            failures.append(f"{row_id}: source_assertions must be a non-empty list")
            continue
        for assertion in assertions:
            source_path = ROOT / assertion.get("path", "")
            if not source_path.is_file():
                failures.append(f"{row_id}: missing source file {source_path}")
                continue
            text = source_cache.setdefault(
                source_path, source_path.read_text(encoding="utf-8")
            )
            contains = assertion.get("contains", [])
            excludes = assertion.get("excludes", [])
            if not contains and not excludes:
                failures.append(
                    f"{row_id}: source assertion for {relative(source_path)} has no check"
                )
            for marker in contains:
                if marker not in text:
                    failures.append(
                        f"{row_id}: {relative(source_path)} missing marker {marker!r}"
                    )
            for marker in excludes:
                if marker in text:
                    failures.append(
                        f"{row_id}: {relative(source_path)} unexpectedly contains {marker!r}"
                    )

        if row["parse"] == "absent" and not any(
            assertion.get("excludes") for assertion in assertions
        ):
            failures.append(f"{row_id}: absent parser row needs a negative source assertion")
        if row["output"] == "interactive-session-text":
            failures.append(
                f"{row_id}: no interactive-session-text row is currently admitted; "
                "add a session runner and conformance test before changing this invariant"
            )

    return failures


def md_escape(value: str) -> str:
    return value.replace("|", "\\|").replace("\n", " ")


def code_list(values: list[str]) -> str:
    if not values:
        return "-"
    return ", ".join(f"`{value}`" for value in values)


def render(data: dict) -> str:
    rows = data["rows"]
    parse_counts = Counter(row["parse"] for row in rows)
    execution_counts = Counter(row["execution"] for row in rows)
    output_counts = Counter(row["output"] for row in rows)
    tested = sum(bool(row.get("tests")) for row in rows)
    absent = [row for row in rows if row["parse"] == "absent"]
    accepted_noop = [row for row in rows if row["parse"] == "accepted-noop"]

    lines = [
        "# SMT-LIB and Rust API conformance matrix",
        "",
        "> **Generated; do not edit by hand.** Source: "
        "[`docs/plan/smtlib-api-conformance-v1.json`](../smtlib-api-conformance-v1.json). "
        "Regenerate with `python3 scripts/gen-smtlib-api-conformance.py`; use "
        "`--check` in validation.",
        "",
        "This is a command/protocol matrix, not a theory-support matrix. It keeps "
        "syntax acceptance, execution semantics, returned representation, and "
        "assurance separate so a parser no-op or direct Rust API cannot be mistaken "
        "for an interactive SMT-LIB implementation.",
        "",
        "## Snapshot",
        "",
        f"- {len(rows)} high-value command/API rows; {tested} name exact tests.",
        "- Parse states: "
        + ", ".join(
            f"{PARSE_LABELS[state]} {parse_counts[state]}"
            for state in PARSE_LABELS
            if parse_counts[state]
        )
        + ".",
        "- Execution states: "
        + ", ".join(
            f"{EXECUTION_LABELS[state]} {execution_counts[state]}"
            for state in EXECUTION_LABELS
            if execution_counts[state]
        )
        + ".",
        "- Output states: "
        + ", ".join(
            f"{OUTPUT_LABELS[state]} {output_counts[state]}"
            for state in OUTPUT_LABELS
            if output_counts[state]
        )
        + ".",
        "- **Zero rows provide an interactive textual command session.** Existing "
        "helpers return Rust values or a proof string from a complete script.",
        "",
        "## State definitions",
        "",
        "- **Parse:** `semantic` changes declarations/terms immediately; "
        "`command-point` preserves ordering; `recorded globally` loses command-point "
        "ordering; `accepted/no-op` validates shape but retains no request; `rejected` "
        "fails explicitly; `absent` falls through to unsupported-command handling.",
        "- **Execution:** a direct API is not textual command execution; a single-query "
        "helper cannot preserve a multi-query transcript; incremental query execution "
        "does preserve assertion-stack behavior at each check.",
        "- **Output:** `Rust value` means typed library data, while `canonical text "
        "artifact` means a standalone artifact such as Alethe. Neither is a complete "
        "SMT-LIB stdout transcript.",
        "",
        "## Matrix",
        "",
        "| Surface | Syntax | Parse | Execution | Output | Assurance | Scope | Evidence | Residual |",
        "|---|---|---|---|---|---|---|---|---|",
    ]
    for row in rows:
        tests = [test["name"] for test in row.get("tests", [])]
        apis = row.get("api_symbols", [])
        evidence = []
        if apis:
            evidence.append("API " + code_list(apis))
        if tests:
            evidence.append("tests " + code_list(tests))
        if not evidence:
            evidence.append("source assertions only")
        lines.append(
            "| "
            + " | ".join(
                md_escape(value)
                for value in (
                    row["surface"],
                    code_list(row["syntax"]),
                    PARSE_LABELS[row["parse"]],
                    EXECUTION_LABELS[row["execution"]],
                    OUTPUT_LABELS[row["output"]],
                    ", ".join(row["assurance"]),
                    row["scope"],
                    "; ".join(evidence),
                    row["residual"],
                )
            )
            + " |"
        )

    lines.extend(
        [
            "",
            "## Negative controls",
            "",
            "These rows are deliberately kept visible. Their source assertions fail "
            "the generator when the named parser command appears, forcing the matrix "
            "and its evidence to be updated together.",
            "",
        ]
    )
    for row in absent:
        lines.append(
            f"- **{row['surface']}:** {row['residual']}"
        )

    lines.extend(
        [
            "",
            "## Accepted-but-not-executed controls",
            "",
        ]
    )
    for row in accepted_noop:
        lines.append(f"- **{row['surface']}:** {row['residual']}")

    lines.extend(
        [
            "",
            "## Planning consequence",
            "",
            "The immediate compatibility project is an ordered textual session runner, "
            "not another theory engine. It should consume one command stream, emit one "
            "response per output command at the exact command point, enforce option "
            "preconditions, and reuse the existing helpers without re-solving or losing "
            "scope. Textual interpolation, Horn, and abduction commands should expose "
            "the existing verify-before-return direct APIs only after that runner gives "
            "their responses a precise ordering and error contract.",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--check",
        action="store_true",
        help="fail if the committed generated Markdown is stale",
    )
    args = parser.parse_args()

    data = load_manifest()
    failures = validate_manifest(data)
    if failures:
        for failure in failures:
            print(f"SMTLIB_CONFORMANCE_ERROR|{failure}", file=sys.stderr)
        return 1

    rendered = render(data)
    if args.check:
        if not OUT_MD.is_file():
            print(f"missing generated file: {relative(OUT_MD)}", file=sys.stderr)
            return 1
        if OUT_MD.read_text(encoding="utf-8") != rendered:
            print(
                f"stale generated file: {relative(OUT_MD)}; run "
                "python3 scripts/gen-smtlib-api-conformance.py",
                file=sys.stderr,
            )
            return 1
    else:
        OUT_MD.parent.mkdir(parents=True, exist_ok=True)
        OUT_MD.write_text(rendered, encoding="utf-8")

    counts = Counter(row["parse"] for row in data["rows"])
    print(
        "SMTLIB_CONFORMANCE|"
        f"rows={len(data['rows'])}|tested={sum(bool(row.get('tests')) for row in data['rows'])}|"
        f"absent={counts['absent']}|accepted_noop={counts['accepted-noop']}|"
        "interactive_session_text=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
