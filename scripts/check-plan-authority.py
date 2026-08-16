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

    # PLAN.md is generated (scripts/gen-plan.py); the writing happens in
    # docs/plan/global/ and docs/plan/status/, so the no-journal-growth ceiling
    # is measured there.  The number moved from 50,000 to 52,000 because the
    # split itself costs bytes that are structure, not journal: at the moment
    # of the split PLAN.md was 49,997 bytes and its sources 50,741 — +744 for
    # nine lane headings and sixteen section markers.  `gen-plan.py --check`
    # keeps PLAN.md equal to those sources, so this still bounds PLAN.md.
    # `README.md` in each directory documents the format and is not emitted
    # into PLAN.md, so it is not journal either.
    sources = [
        path
        for directory in ("docs/plan/global", "docs/plan/status")
        for path in sorted((ROOT / directory).glob("*.md"))
        if path.name != "README.md"
    ]
    authored = sum(path.stat().st_size for path in sources)
    if authored > 52_000:
        # Report the SCOPE, not just the verdict. This gate used to emit one
        # total and the instruction "move journal/detail to a result note",
        # which does not say which of 54 files to move or how much is enough --
        # so the number grew 0 -> 54,398 -> 98,180 -> 233,888 in two days
        # without anyone being told where. Naming the largest sources and the
        # global/status split makes the failure actionable, which is
        # docs/refactor-2026-08/04-gates-and-truth.md T1 applied to this gate.
        by_dir: dict[str, int] = {}
        for path in sources:
            by_dir[path.parent.name] = by_dir.get(path.parent.name, 0) + path.stat().st_size
        worst = sorted(sources, key=lambda p: p.stat().st_size, reverse=True)[:5]
        detail = "; ".join(
            f"{p.relative_to(ROOT)} {p.stat().st_size}" for p in worst
        )
        split = ", ".join(f"{d}/ {n}" for d, n in sorted(by_dir.items()))
        errors.append(
            f"PLAN.md sources total {authored} bytes (>52 KB) across "
            f"{len(sources)} files ({split}); move journal/detail to a result "
            f"note. Largest: {detail}"
        )
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
