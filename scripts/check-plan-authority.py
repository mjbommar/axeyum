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
    # is measured there.  `README.md` in each directory documents the format and
    # is not emitted into PLAN.md, so it is not journal either.
    #
    # THE CEILING USED TO BE A FLAT 52,000 ACROSS ALL LANES, AND THAT IS WHY IT
    # WAS RED FOR DAYS.  Its own comment records the growth as 0 -> 54,398 ->
    # 98,180 -> 233,888 in two days; on 2026-08-18 it stood at 177,878, 3.4x
    # over, and every lane had learned to scroll past it.  A budget shared by 25
    # lanes is nobody's to fix: no single edit causes the failure, so no single
    # edit repairs it.  That is the same shared-append-point defect the per-lane
    # split was created to remove (CLAUDE.md: per-lane state belongs in per-lane
    # paths, never in one file every lane writes) — reappearing one level up, in
    # the BUDGET rather than the file.
    #
    # So the bound is now attributable:
    #   * each lane file gets its own cap, and a violation names the lane;
    #   * docs/plan/global/ keeps a total, because it genuinely is shared;
    #   * the overall ceiling is DERIVED from those two, so adding a 27th lane
    #     cannot red the gate on its own — which the flat number did.
    # Detail that does not fit belongs in docs/plan/notes/<lane>.md, which
    # gen-plan.py does not read and this gate does not count.
    # `scripts/archive-plan-status.py` performs the move without losing a byte.
    LANE_CAP = 3_000
    GLOBAL_CAP = 32_000
    lane_sources = [
        path for path in sorted((ROOT / "docs/plan/status").glob("*.md"))
        if path.name != "README.md"
    ]
    global_sources = [
        path for path in sorted((ROOT / "docs/plan/global").glob("*.md"))
        if path.name != "README.md"
    ]
    global_bytes = sum(path.stat().st_size for path in global_sources)
    lane_bytes = sum(path.stat().st_size for path in lane_sources)
    authored = global_bytes + lane_bytes
    derived_ceiling = GLOBAL_CAP + LANE_CAP * len(lane_sources)

    over = [
        (path, path.stat().st_size)
        for path in lane_sources
        if path.stat().st_size > LANE_CAP
    ]
    for path, size in sorted(over, key=lambda pair: -pair[1]):
        errors.append(
            f"{path.relative_to(ROOT)} is {size} bytes (> {LANE_CAP}); move the "
            f"detail to docs/plan/notes/{path.name} — "
            f"`python3 scripts/archive-plan-status.py --apply` does it without "
            "losing anything, and skips files another lane has uncommitted"
        )
    if global_bytes > GLOBAL_CAP:
        biggest = sorted(global_sources, key=lambda p: -p.stat().st_size)[:3]
        detail = "; ".join(f"{p.name} {p.stat().st_size}" for p in biggest)
        errors.append(
            f"docs/plan/global/ totals {global_bytes} bytes (> {GLOBAL_CAP}); "
            f"largest: {detail}"
        )
    if authored > derived_ceiling:
        errors.append(
            f"PLAN.md sources total {authored} bytes (> {derived_ceiling} = "
            f"{GLOBAL_CAP} global + {LANE_CAP} x {len(lane_sources)} lanes); "
            f"global/ {global_bytes}, status/ {lane_bytes}"
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
