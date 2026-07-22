#!/usr/bin/env python3
"""Validate and render the Lean compatibility assurance contract.

The contract keeps parsing, translation, independent admission, official
admission, source elaboration, proof checking, workflow reproduction, and
runtime reproduction distinct.  Its validator deliberately rejects assurance
combinations that would let an upstream parser or oracle grant independent
checking credit.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "docs" / "plan" / "lean-compatibility-v1.json"
OUT_MD = ROOT / "docs" / "plan" / "generated" / "lean-compatibility.md"

ASSURANCE_FIELDS = (
    "parsed",
    "translated",
    "admitted",
    "official_admitted",
    "source_elaborated",
    "proof_checked",
    "workflow_reproduced",
    "runtime_reproduced",
)
STATES = {
    "not_applicable",
    "not_attempted",
    "succeeded",
    "declined",
    "failed",
}
STATE_LABELS = {
    "not_applicable": "n/a",
    "not_attempted": "not attempted",
    "succeeded": "passed",
    "declined": "declined",
    "failed": "failed",
}
PROFILE_IDS = (
    "K0-checker",
    "K1-import",
    "K2-source",
    "K3-proof",
    "K4-workflow",
    "K5-runtime",
    "K6-ecosystem",
)
ARTIFACT_KINDS = {
    "native-core",
    "lean4export-stream",
    "lean-source-family",
    "planned-system-profile",
}
EVIDENCE_KINDS = {"document", "fixture", "plan", "source", "test"}
KEBAB = re.compile(r"^[a-z0-9]+(?:-[a-z0-9]+)*$")
HEX40 = re.compile(r"^[0-9a-f]{40}$")


def relative(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def load_manifest() -> dict[str, Any]:
    with MANIFEST.open(encoding="utf-8") as handle:
        return json.load(handle)


def profile_map(data: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {profile["id"]: profile for profile in data["profiles"]}


def profile_satisfied(row: dict[str, Any], profiles: dict[str, dict[str, Any]]) -> bool:
    required = profiles[row["profile"]]["requires"]
    return all(row["states"][field] == "succeeded" for field in required)


def validate_target(data: dict[str, Any], failures: list[str]) -> None:
    target = data.get("target")
    if not isinstance(target, dict):
        failures.append("target must be an object")
        return
    expected = {
        "lean_version": "4.30.0",
        "exporter": "lean4export",
        "exporter_version": "3.1.0",
    }
    for key, value in expected.items():
        if target.get(key) != value:
            failures.append(f"target {key} must be {value!r}")
    for key in ("lean_commit", "exporter_commit"):
        if not HEX40.fullmatch(str(target.get(key, ""))):
            failures.append(f"target {key} must be a lowercase 40-hex commit")


def validate_profiles(data: dict[str, Any], failures: list[str]) -> None:
    profiles = data.get("profiles")
    if not isinstance(profiles, list):
        failures.append("profiles must be a list")
        return
    ids = tuple(profile.get("id") for profile in profiles)
    if ids != PROFILE_IDS:
        failures.append(f"profile ids/order must be {PROFILE_IDS!r}")
    for profile in profiles:
        profile_id = profile.get("id", "<unknown>")
        if not profile.get("label"):
            failures.append(f"{profile_id}: profile label is required")
        requires = profile.get("requires")
        if not isinstance(requires, list) or not requires:
            failures.append(f"{profile_id}: requires must be a non-empty list")
            continue
        unknown = sorted(set(requires) - set(ASSURANCE_FIELDS))
        if unknown:
            failures.append(f"{profile_id}: unknown required fields {unknown}")
        if len(set(requires)) != len(requires):
            failures.append(f"{profile_id}: duplicate required fields")


def validate_decline_codes(
    data: dict[str, Any], failures: list[str]
) -> set[str]:
    entries = data.get("decline_codes")
    if not isinstance(entries, list) or not entries:
        failures.append("decline_codes must be a non-empty list")
        return set()
    codes = [entry.get("code") for entry in entries]
    if codes != sorted(codes):
        failures.append("decline_codes must be sorted by code")
    if len(set(codes)) != len(codes):
        failures.append("decline_codes must be unique")
    source_cache: dict[Path, str] = {}
    for entry in entries:
        code = entry.get("code", "<unknown>")
        if not KEBAB.fullmatch(str(code)):
            failures.append(f"invalid decline code {code!r}")
        for key in ("meaning", "owner", "source_path", "source_marker"):
            if not entry.get(key):
                failures.append(f"{code}: missing non-empty {key}")
        path = ROOT / str(entry.get("source_path", ""))
        if not path.is_file():
            failures.append(f"{code}: missing source path {path}")
            continue
        text = source_cache.setdefault(path, path.read_text(encoding="utf-8"))
        marker = str(entry.get("source_marker", ""))
        if marker and marker not in text:
            failures.append(f"{code}: {relative(path)} missing marker {marker!r}")
    return {str(code) for code in codes}


def validate_state_dependencies(row: dict[str, Any], failures: list[str]) -> None:
    row_id = row.get("id", "<unknown>")
    states = row["states"]

    if states["translated"] in {"succeeded", "declined", "failed"} and states[
        "parsed"
    ] != "succeeded":
        failures.append(f"{row_id}: translation outcome requires parsed=succeeded")
    if states["source_elaborated"] == "succeeded" and states["parsed"] != "succeeded":
        failures.append(f"{row_id}: source elaboration requires parsed=succeeded")
    if states["official_admitted"] == "succeeded" and states[
        "source_elaborated"
    ] != "succeeded":
        failures.append(
            f"{row_id}: official admission requires source_elaborated=succeeded"
        )
    if states["admitted"] == "succeeded" and not (
        states["translated"] == "succeeded" or row["artifact_kind"] == "native-core"
    ):
        failures.append(
            f"{row_id}: independent admission requires translated=succeeded or native-core"
        )
    if states["proof_checked"] == "succeeded" and states["admitted"] != "succeeded":
        failures.append(f"{row_id}: proof checking requires admitted=succeeded")
    if states["workflow_reproduced"] == "succeeded" and not (
        states["source_elaborated"] == "succeeded"
        and states["admitted"] == "succeeded"
    ):
        failures.append(
            f"{row_id}: workflow reproduction requires source elaboration and admission"
        )
    if states["runtime_reproduced"] == "succeeded" and states[
        "source_elaborated"
    ] != "succeeded":
        failures.append(
            f"{row_id}: runtime reproduction requires source_elaborated=succeeded"
        )


def validate_rows(
    data: dict[str, Any], registered_codes: set[str], failures: list[str]
) -> None:
    rows = data.get("rows")
    if not isinstance(rows, list) or not rows:
        failures.append("rows must be a non-empty list")
        return
    ids = [row.get("id") for row in rows]
    if ids != sorted(ids):
        failures.append("rows must be sorted by id")
    if len(set(ids)) != len(ids):
        failures.append("row ids must be unique")

    profiles = profile_map(data)
    for row in rows:
        row_id = row.get("id", "<unknown>")
        if not KEBAB.fullmatch(str(row_id)):
            failures.append(f"invalid row id {row_id!r}")
        for key in ("subject", "artifact_kind", "profile", "residual"):
            if not row.get(key):
                failures.append(f"{row_id}: missing non-empty {key}")
        if row.get("artifact_kind") not in ARTIFACT_KINDS:
            failures.append(f"{row_id}: invalid artifact_kind {row.get('artifact_kind')!r}")
        if row.get("profile") not in profiles:
            failures.append(f"{row_id}: invalid profile {row.get('profile')!r}")

        states = row.get("states")
        if not isinstance(states, dict):
            failures.append(f"{row_id}: states must be an object")
            continue
        if set(states) != set(ASSURANCE_FIELDS):
            missing = sorted(set(ASSURANCE_FIELDS) - set(states))
            extra = sorted(set(states) - set(ASSURANCE_FIELDS))
            failures.append(f"{row_id}: assurance fields missing={missing} extra={extra}")
            continue
        bad_states = {field: value for field, value in states.items() if value not in STATES}
        if bad_states:
            failures.append(f"{row_id}: invalid assurance states {bad_states}")
            continue
        validate_state_dependencies(row, failures)

        codes = row.get("decline_codes")
        if not isinstance(codes, list):
            failures.append(f"{row_id}: decline_codes must be a list")
            codes = []
        if codes != sorted(set(codes)):
            failures.append(f"{row_id}: decline_codes must be sorted and unique")
        unknown_codes = sorted(set(codes) - registered_codes)
        if unknown_codes:
            failures.append(f"{row_id}: unregistered decline codes {unknown_codes}")
        has_decline = "declined" in states.values()
        if has_decline and not codes:
            failures.append(f"{row_id}: declined assurance requires a decline code")
        if codes and not has_decline:
            failures.append(f"{row_id}: decline code without a declined assurance")

        evidence = row.get("evidence")
        if not isinstance(evidence, list) or not evidence:
            failures.append(f"{row_id}: evidence must be a non-empty list")
            continue
        for item in evidence:
            kind = item.get("kind")
            path = ROOT / str(item.get("path", ""))
            if kind not in EVIDENCE_KINDS:
                failures.append(f"{row_id}: invalid evidence kind {kind!r}")
            if not path.is_file():
                failures.append(f"{row_id}: missing evidence path {path}")
            if not item.get("detail"):
                failures.append(f"{row_id}: evidence detail is required")


def validate_manifest(data: dict[str, Any]) -> list[str]:
    failures: list[str] = []
    if data.get("version") != 1:
        failures.append("manifest version must be 1")
    if not data.get("title") or not data.get("as_of"):
        failures.append("title and as_of are required")
    if tuple(data.get("assurance_fields", ())) != ASSURANCE_FIELDS:
        failures.append(f"assurance_fields/order must be {ASSURANCE_FIELDS!r}")
    definitions = data.get("state_definitions")
    if not isinstance(definitions, dict) or set(definitions) != STATES:
        failures.append(f"state_definitions must define exactly {sorted(STATES)}")
    elif any(not value for value in definitions.values()):
        failures.append("state definitions must be non-empty")

    validate_target(data, failures)
    validate_profiles(data, failures)
    registered_codes = validate_decline_codes(data, failures)
    if isinstance(data.get("profiles"), list):
        validate_rows(data, registered_codes, failures)
    return failures


def md_escape(value: str) -> str:
    return value.replace("|", "\\|").replace("\n", " ")


def code_list(values: list[str]) -> str:
    return "-" if not values else ", ".join(f"`{value}`" for value in values)


def render(data: dict[str, Any]) -> str:
    rows = data["rows"]
    profiles = profile_map(data)
    satisfied = Counter(
        row["profile"] for row in rows if profile_satisfied(row, profiles)
    )
    totals = Counter(row["profile"] for row in rows)
    state_counts = {
        field: Counter(row["states"][field] for row in rows)
        for field in ASSURANCE_FIELDS
    }
    target = data["target"]
    lines = [
        "# Lean compatibility assurance matrix",
        "",
        "> **Generated; do not edit by hand.** Source: "
        "[`docs/plan/lean-compatibility-v1.json`](../lean-compatibility-v1.json). "
        "Regenerate with `python3 scripts/gen-lean-compatibility.py`; use `--check` "
        "in validation.",
        "",
        "This matrix refuses to collapse parsing, translation, independent kernel "
        "admission, official admission, source elaboration, proof checking, workflow "
        "reproduction, and runtime reproduction into one word such as `supported`.",
        "",
        "## Pinned target",
        "",
        f"- Lean `{target['lean_version']}` at `{target['lean_commit']}`.",
        f"- `{target['exporter']}` `{target['exporter_version']}` at "
        f"`{target['exporter_commit']}`.",
        f"- {len(rows)} exact artifact/profile rows and "
        f"{len(data['decline_codes'])} registered unsupported-construct codes.",
        "",
        "## Profile gates",
        "",
        "A row satisfies its target profile only when every listed field is "
        "`succeeded`; lower-profile evidence never fills a higher-profile field.",
        "",
        "| Profile | Meaning | Required assurance | Satisfied rows | Total rows |",
        "|---|---|---|---:|---:|",
    ]
    for profile in data["profiles"]:
        profile_id = profile["id"]
        lines.append(
            f"| `{profile_id}` | {md_escape(profile['label'])} | "
            f"{code_list(profile['requires'])} | {satisfied[profile_id]} | "
            f"{totals[profile_id]} |"
        )

    lines.extend(
        [
            "",
            "## Assurance-state snapshot",
            "",
            "| Assurance field | Passed | Declined | Failed | Not attempted | N/A |",
            "|---|---:|---:|---:|---:|---:|",
        ]
    )
    for field in ASSURANCE_FIELDS:
        counts = state_counts[field]
        lines.append(
            f"| `{field}` | {counts['succeeded']} | {counts['declined']} | "
            f"{counts['failed']} | {counts['not_attempted']} | "
            f"{counts['not_applicable']} |"
        )

    lines.extend(
        [
            "",
            "## Artifact matrix",
            "",
            "| Subject | Target | Gate | Parsed | Translated | Admitted | Official | "
            "Source elaborated | Proof checked | Workflow | Runtime | Declines | "
            "Evidence | Residual |",
            "|---|---|---|---|---|---|---|---|---|---|---|---|---|---|",
        ]
    )
    for row in rows:
        states = row["states"]
        evidence = "; ".join(
            f"[{item['kind']}]({Path('../../..') / item['path']})"
            for item in row["evidence"]
        )
        gate = "pass" if profile_satisfied(row, profiles) else "open"
        values = (
            row["subject"],
            row["profile"],
            gate,
            STATE_LABELS[states["parsed"]],
            STATE_LABELS[states["translated"]],
            STATE_LABELS[states["admitted"]],
            STATE_LABELS[states["official_admitted"]],
            STATE_LABELS[states["source_elaborated"]],
            STATE_LABELS[states["proof_checked"]],
            STATE_LABELS[states["workflow_reproduced"]],
            STATE_LABELS[states["runtime_reproduced"]],
            code_list(row["decline_codes"]),
            evidence,
            row["residual"],
        )
        lines.append("| " + " | ".join(md_escape(value) for value in values) + " |")

    lines.extend(
        [
            "",
            "## Registered decline codes",
            "",
            "These are fail-closed unsupported-construct results, not failed proofs "
            "and not permission to convert a decline into `unknown` or admission.",
            "",
            "| Code | Owner | Meaning | Source |",
            "|---|---|---|---|",
        ]
    )
    for entry in data["decline_codes"]:
        source = f"[source](../../../{entry['source_path']})"
        lines.append(
            f"| `{entry['code']}` | `{entry['owner']}` | "
            f"{md_escape(entry['meaning'])} | {source} |"
        )

    lines.extend(
        [
            "",
            "## Enforced implications",
            "",
            "- Translation success, decline, or failure requires successful parsing.",
            "- Independent admission requires successful translation, except for a "
            "native-core artifact that starts inside the kernel boundary.",
            "- Official admission requires successful source elaboration; it never "
            "implies independent admission.",
            "- Proof checking requires independent admission.",
            "- Workflow reproduction requires source elaboration and independent "
            "admission; runtime reproduction requires source elaboration.",
            "- Every declined assurance names at least one registered code, and codes "
            "cannot appear on a row with no decline.",
            "- Every row carries a retained evidence path and an explicit residual.",
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
            print(f"LEAN_COMPATIBILITY_ERROR|{failure}", file=sys.stderr)
        return 1

    rendered = render(data)
    if args.check:
        if not OUT_MD.is_file():
            print(f"missing generated file: {relative(OUT_MD)}", file=sys.stderr)
            return 1
        if OUT_MD.read_text(encoding="utf-8") != rendered:
            print(
                f"stale generated file: {relative(OUT_MD)}; run "
                "python3 scripts/gen-lean-compatibility.py",
                file=sys.stderr,
            )
            return 1
    else:
        OUT_MD.parent.mkdir(parents=True, exist_ok=True)
        OUT_MD.write_text(rendered, encoding="utf-8")

    profiles = profile_map(data)
    passed = sum(profile_satisfied(row, profiles) for row in data["rows"])
    declined = sum("declined" in row["states"].values() for row in data["rows"])
    print(
        "LEAN_COMPATIBILITY|"
        f"rows={len(data['rows'])}|profile_pass={passed}|declined={declined}|"
        f"decline_codes={len(data['decline_codes'])}|fields={len(ASSURANCE_FIELDS)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
