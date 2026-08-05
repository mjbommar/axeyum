#!/usr/bin/env python3
"""Fail closed when project-level planning authority splits again."""

from __future__ import annotations

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def read(relative: str) -> str:
    return (ROOT / relative).read_text(encoding="utf-8")


def main() -> int:
    errors: list[str] = []
    plan_path = ROOT / "PLAN.md"
    status_path = ROOT / "STATUS.md"
    exploration_status_path = ROOT / "docs/plan/exploration-track/STATUS.md"

    plan = read("PLAN.md")
    status = read("STATUS.md")
    exploration_status = read("docs/plan/exploration-track/STATUS.md")

    required_plan_text = (
        "Canonical project tracker",
        "## Status",
        "## Next Actions",
        "## Workstream state",
        "## Resume protocol",
        "## Planning rules",
    )
    for marker in required_plan_text:
        if marker not in plan:
            errors.append(f"PLAN.md is missing required marker: {marker!r}")

    if plan_path.stat().st_size > 50_000:
        errors.append("PLAN.md exceeds 50 KB; move journal/detail to a result note")
    if status_path.stat().st_size > 1_500:
        errors.append("STATUS.md is no longer a compact compatibility pointer")
    if exploration_status_path.stat().st_size > 2_000:
        errors.append("exploration-track/STATUS.md is no longer a compact pointer")
    if (ROOT / "TODO.md").exists():
        errors.append("root TODO.md must not exist; use PLAN.md Next Actions")

    for relative, text in (
        ("STATUS.md", status),
        ("docs/plan/exploration-track/STATUS.md", exploration_status),
    ):
        if "compatibility pointer" not in text:
            errors.append(f"{relative} does not identify itself as a compatibility pointer")
        if "## Current focus" in text or "## Next Actions" in text:
            errors.append(f"{relative} contains a competing live queue")

    active_surfaces = (
        "AGENTS.md",
        "CLAUDE.md",
        "README.md",
        "docs/README.md",
        "docs/contributor-guide/README.md",
        "docs/plan/README.md",
        "docs/research/08-planning/roadmap.md",
    )
    forbidden = (
        "STATUS.md) (live state)",
        "Live status & changelog | [STATUS.md]",
        "Current live tracker: [STATUS.md]",
        "STATUS.md framed as an **active work queue**",
    )
    for relative in active_surfaces:
        text = read(relative)
        if "PLAN.md" not in text:
            errors.append(f"{relative} does not point readers to PLAN.md")
        for phrase in forbidden:
            if phrase in text:
                errors.append(f"{relative} restores forbidden split authority: {phrase!r}")

    for relative in ("AGENTS.md", "CLAUDE.md"):
        if "It is the only file with mutable session" not in read(relative):
            errors.append(f"{relative} does not declare PLAN.md the only mutable session file")

    if errors:
        for error in errors:
            print(f"plan-authority: ERROR: {error}")
        return 1

    print(
        "plan-authority: OK — PLAN.md is the single mutable project tracker; "
        "STATUS pointers are bounded and root TODO.md is absent"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
