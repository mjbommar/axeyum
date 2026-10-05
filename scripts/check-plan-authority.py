#!/usr/bin/env python3
"""Fail closed when project-level planning authority splits again."""

from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def read(relative: str) -> str:
    return (ROOT / relative).read_text(encoding="utf-8")


# PLAN.md is generated (scripts/gen-plan.py) from docs/plan/global/ and every
# file in docs/plan/status/, so the no-journal-growth bound is measured there.
#
# HISTORY OF THIS BOUND, because each version failed differently. A flat 52,000
# shared by every lane was red for days (no single edit caused it, so no single
# edit fixed it). Its replacement -- 3,000 per lane plus a ceiling DERIVED from
# the lane count -- could never force anything out: every new lane raised the
# ceiling by its own cap. By 2026-10-05 it was red at 635 over-cap lanes, PLAN.md
# had reached 75,717 lines from 770 lane files, and 601 of them were DONE.
#
# So the bound is now on what is ACTIVE:
#   * each lane file keeps its own 3,000-byte cap (attributable, names the lane);
#   * docs/plan/global/ keeps a 32,000-byte total, because it is shared;
#   * a lane whose status token says DONE must be archived
#     (`scripts/archive-plan-lane.py <lane>`), so finished work leaves the plan;
#   * at most MAX_ACTIVE_LANES lane files exist, so the total is FIXED
#     (GLOBAL_CAP + LANE_CAP x MAX_ACTIVE_LANES), not derived from the count.
# Detail belongs in docs/plan/notes/<lane>.md (`scripts/archive-plan-status.py`);
# finished lanes in docs/plan/archive/lanes/, indexed by docs/plan/CATALOG.md.
LANE_CAP = 3_000
GLOBAL_CAP = 32_000
MAX_ACTIVE_LANES = 25
LANE_STATUS_TOKEN = re.compile(r"\(\s*`([A-Za-z][A-Za-z -]*)`\s*,")
DONE_PREFIXES = ("DONE", "LANDED", "COMPLETE", "CLOSED", "MERGED", "SHIPPED")


def budget_errors(root: Path) -> list[str]:
    errors: list[str] = []
    lane_sources = [
        path for path in sorted((root / "docs/plan/status").glob("*.md"))
        if path.name != "README.md"
    ]
    global_sources = [
        path for path in sorted((root / "docs/plan/global").glob("*.md"))
        if path.name != "README.md"
    ]
    for path in sorted(lane_sources, key=lambda p: -p.stat().st_size):
        size = path.stat().st_size
        if size > LANE_CAP:
            errors.append(
                f"{path.relative_to(root)} is {size} bytes (> {LANE_CAP}); move the "
                f"detail to docs/plan/notes/{path.name} -- "
                "`python3 scripts/archive-plan-status.py --apply` does it without "
                "losing anything"
            )
    for path in lane_sources:
        match = LANE_STATUS_TOKEN.search(path.read_text(encoding="utf-8")[:1200])
        if match and match.group(1).strip().upper().startswith(DONE_PREFIXES):
            errors.append(
                f"{path.relative_to(root)} says `{match.group(1).strip()}`; a finished "
                f"lane leaves the plan -- `python3 scripts/archive-plan-lane.py "
                f"{path.stem}` moves it to docs/plan/archive/lanes/ and keeps every link"
            )
    if len(lane_sources) > MAX_ACTIVE_LANES:
        errors.append(
            f"{len(lane_sources)} lane files in docs/plan/status/ (> {MAX_ACTIVE_LANES} "
            "active); archive finished or abandoned lanes with "
            "`scripts/archive-plan-lane.py`"
        )
    global_bytes = sum(path.stat().st_size for path in global_sources)
    if global_bytes > GLOBAL_CAP:
        biggest = sorted(global_sources, key=lambda p: -p.stat().st_size)[:3]
        detail = "; ".join(f"{p.name} {p.stat().st_size}" for p in biggest)
        errors.append(
            f"docs/plan/global/ totals {global_bytes} bytes (> {GLOBAL_CAP}); "
            f"largest: {detail}"
        )
    plan = root / "PLAN.md"
    ceiling = GLOBAL_CAP + LANE_CAP * MAX_ACTIVE_LANES
    if plan.exists() and plan.stat().st_size > ceiling:
        errors.append(
            f"PLAN.md is {plan.stat().st_size} bytes (> {ceiling} = {GLOBAL_CAP} "
            f"global + {LANE_CAP} x {MAX_ACTIVE_LANES} active lanes)"
        )
    return errors


def instruction_sync_errors(root: Path) -> list[str]:
    """CLAUDE.md and AGENTS.md carry one text; only the title and first line differ.

    They were two hand-maintained copies, and by 2026-10-05 AGENTS.md still
    described BatSat solving and a Layout missing half the crates. One body
    cannot drift.
    """
    claude, agents = (root / "CLAUDE.md"), (root / "AGENTS.md")
    if not (claude.exists() and agents.exists()):
        return []
    body = lambda path: path.read_text(encoding="utf-8").splitlines()[3:]  # noqa: E731
    if body(claude) != body(agents):
        return ["CLAUDE.md and AGENTS.md differ below their title lines; edit both together"]
    return []


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

    errors.extend(budget_errors(ROOT))
    errors.extend(instruction_sync_errors(ROOT))
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
