#!/usr/bin/env python3
"""Generate the contributor-facing G0-G10 ownership map."""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "docs" / "plan" / "gap-ownership-v1.json"
OUTPUT = ROOT / "docs" / "contributor-guide" / "gap-ownership.md"
EXPECTED_IDS = [f"G{i}" for i in range(11)]
ALLOWED_STATES = {"open", "prototype-landed", "partially-landed", "closed"}


def load_manifest() -> dict:
    with MANIFEST.open(encoding="utf-8") as handle:
        return json.load(handle)


def validate(manifest: dict) -> list[str]:
    errors: list[str] = []
    if manifest.get("schema_version") != 1:
        errors.append("schema_version must be 1")

    gaps = manifest.get("gaps")
    if not isinstance(gaps, list):
        return errors + ["gaps must be a list"]
    ids = [gap.get("id") for gap in gaps]
    if ids != EXPECTED_IDS:
        errors.append(f"gap IDs must be exactly {EXPECTED_IDS}, got {ids}")

    source_rel = manifest.get("source_gap_doc")
    source_path = ROOT / source_rel if isinstance(source_rel, str) else None
    source_titles: dict[str, str] = {}
    if source_path is None or not source_path.is_file():
        errors.append(f"source_gap_doc does not exist: {source_rel!r}")
    else:
        for match in re.finditer(
            r"^### (G\d+) — (.+)$", source_path.read_text(encoding="utf-8"), re.MULTILINE
        ):
            source_titles[match.group(1)] = match.group(2)

    for gap in gaps:
        gap_id = gap.get("id", "<missing>")
        if gap.get("state") not in ALLOWED_STATES:
            errors.append(f"{gap_id}: invalid state {gap.get('state')!r}")
        if source_titles.get(gap_id) != gap.get("title"):
            errors.append(
                f"{gap_id}: title drift: manifest={gap.get('title')!r}, "
                f"source={source_titles.get(gap_id)!r}"
            )
        for key in ("question", "next_action"):
            if not isinstance(gap.get(key), str) or not gap[key].strip():
                errors.append(f"{gap_id}: {key} must be a nonempty string")
        for key in ("owner_paths", "evidence_paths", "gate_commands", "decision_paths"):
            values = gap.get(key)
            if not isinstance(values, list) or not all(
                isinstance(value, str) and value.strip() for value in values
            ):
                errors.append(f"{gap_id}: {key} must be a list of nonempty strings")
                continue
            if key in {"owner_paths", "evidence_paths", "gate_commands"} and not values:
                errors.append(f"{gap_id}: {key} must not be empty")
            if key.endswith("_paths"):
                for value in values:
                    path = Path(value)
                    if path.is_absolute() or ".." in path.parts:
                        errors.append(f"{gap_id}: unsafe repository path {value!r}")
                    elif not (ROOT / path).exists():
                        errors.append(f"{gap_id}: missing repository path {value!r}")
        for value in gap.get("decision_paths", []):
            if not value.startswith("docs/research/09-decisions/adr-"):
                errors.append(f"{gap_id}: decision path is not an ADR: {value!r}")

    return errors


def link(path: str) -> str:
    return f"[`{path}`](../../{path})"


def render(manifest: dict) -> str:
    lines = [
        "# Measured-gap ownership map",
        "",
        "> **Generated; do not edit by hand.** Source: "
        "[`docs/plan/gap-ownership-v1.json`](../plan/gap-ownership-v1.json). "
        "Regenerate with `python3 scripts/gen-gap-ownership.py`; use `--check` in validation.",
        "",
        "This is the contributor routing layer for the current G0-G10 gap program. "
        "It names the first code owner, committed evidence, executable gate, decision "
        "anchor, and next safe action. An absent gap-specific ADR is shown explicitly; "
        "it is decision debt, not permission to decide silently in code.",
        "",
        "## Quick routing",
        "",
        "| Gap | Research question | State | First owner |",
        "|---|---|---|---|",
    ]
    for gap in manifest["gaps"]:
        lines.append(
            f"| [{gap['id']}](#{gap['id'].lower()}) "
            f"| {gap['question']} | `{gap['state']}` | {link(gap['owner_paths'][0])} |"
        )

    lines.extend(["", "## Detailed ownership", ""])
    for gap in manifest["gaps"]:
        lines.extend(
            [
                f"<a id=\"{gap['id'].lower()}\"></a>",
                "",
                f"### {gap['id']} — {gap['title']}",
                "",
                f"**State:** `{gap['state']}`",
                "",
                f"**Question:** {gap['question']}",
                "",
                "**Owner paths:**",
                "",
                *[f"- {link(path)}" for path in gap["owner_paths"]],
                "",
                "**Evidence:**",
                "",
                *[f"- {link(path)}" for path in gap["evidence_paths"]],
                "",
                "**Executable gates:**",
                "",
                *[f"- `{command}`" for command in gap["gate_commands"]],
                "",
                "**Decision anchors:**",
                "",
            ]
        )
        if gap["decision_paths"]:
            lines.extend(f"- {link(path)}" for path in gap["decision_paths"])
        else:
            lines.append("- No gap-specific ADR yet; use the source gap section and open an ADR before changing public behavior.")
        lines.extend(["", f"**Next safe action:** {gap['next_action']}", ""])

    return "\n".join(lines).rstrip() + "\n"

def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()

    manifest = load_manifest()
    errors = validate(manifest)
    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1

    rendered = render(manifest)
    if args.check:
        if not OUTPUT.is_file() or OUTPUT.read_text(encoding="utf-8") != rendered:
            print(f"ERROR: {OUTPUT.relative_to(ROOT)} is stale", file=sys.stderr)
            return 1
    else:
        OUTPUT.write_text(rendered, encoding="utf-8")

    print(
        "GAP_OWNERSHIP|"
        f"gaps={len(manifest['gaps'])}|"
        f"with_adrs={sum(bool(gap['decision_paths']) for gap in manifest['gaps'])}|"
        f"without_adrs={sum(not gap['decision_paths'] for gap in manifest['gaps'])}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
